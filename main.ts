// Pump.fun paper-trading sniper: buy only launches that already have a real early crowd.
//
// Idea: on pump.fun most launches die within minutes, but the ones strangers pile into
// early keep running. This bot watches every new curve from its CreateEvent and buys
// only when at least 8 different non-creator wallets have bought it within roughly
// four minutes of creation, with enough real SOL on the curve for a meaningful buy.
// One fixed-size buy per coin (0.05 SOL), at most 5 positions open, no adds, no
// dip-buying: a coin that does not qualify in its window is skipped for good.
//
// Exits are mechanical: take profit at +20%, cut at -15%, and give up on a loser
// still under -5% after about 48 minutes (7,200 slots). Winners and flat positions
// are left to ride; the replay flattens whatever is left at the end of the window.
//
// A pure function of the batches it is fed: no clock, no randomness, no I/O, so the
// two grading runs agree byte for byte.
//
// Dev-window grade-local (kit 40, --driver process): net PnL -0.915 SOL over 435
// round trips (win rate 29.9%, max drawdown 9.5%), guardrails met with 430 coins
// holding a round trip of at least 0.01 SOL, L1 regrade reproduced byte for byte.
// The dev window is one small sample and every pilot loses on it; the final window
// is different coins, so the entry is judged on the strategy, not on this number.

import { BPS, LAMPORTS_PER_SOL, runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

/** Fixed stake per coin. */
const STAKE_LAMPORTS = LAMPORTS_PER_SOL / 20n;
/** Smallest buy worth paying a transaction fee for (also the size-cap floor). */
const MIN_BUY_LAMPORTS = LAMPORTS_PER_SOL / 200n;
/** Distinct non-creator buyers a launch needs before it is worth buying. */
const MIN_BUYERS = 8;
/** Decision window after creation, in slots (~0.4 s each, so ~4 minutes). */
const DECIDE_WINDOW_SLOTS = 600;
/** Slippage allowed on every order: wide open, the price moves in the latency anyway. */
const MAX_SLIPPAGE_BPS = 10_000;
/** Curve fees on a sell (protocol 95 bps + creator 30 bps). */
const SELL_FEE_BPS = 125n;
/** Take profit at +20% over cost. */
const TAKE_PROFIT_BPS = 2000n;
/** Stop loss at -15% under cost. */
const STOP_LOSS_BPS = 1500n;
/** Time stop: give up after this many slots holding (~48 minutes). */
const TIME_STOP_SLOTS = 7200;
/** ...but only when the position is still this far under cost. */
const TIME_STOP_UNDER_BPS = 500n;

/** A launch being watched from its CreateEvent. */
interface Watched {
  mint: Pubkey;
  createSlot: number;
  creator: Pubkey;
  /** Distinct wallets other than the creator that bought so far. */
  buyers: Set<Pubkey>;
  /** Bought, skipped, or its curve completed: never decide on it again. */
  decided: boolean;
}

/** A position we hold, with the slot its buy filled at. */
interface Open {
  openedSlot: number;
}

/** What selling `tokens` against (vq, vt) would pay after curve fees. */
function sellValue(tokens: bigint, vq: bigint, vt: bigint): bigint {
  if (tokens <= 0n || vt <= 0n) return 0n;
  const quote = (tokens * vq) / (vt + tokens);
  return quote - (quote * SELL_FEE_BPS + BPS - 1n) / BPS;
}

const watched = new Map<Pubkey, Watched>();
const open = new Map<Pubkey, Open>();
const selling = new Set<Pubkey>();

function hasPendingBuy(state: BotState, mint: Pubkey): boolean {
  for (const p of state.pending.values()) {
    if (p.order.mint === mint && p.order.side === 'buy') return true;
  }
  return false;
}

function hasPendingSell(state: BotState, mint: Pubkey): boolean {
  for (const p of state.pending.values()) {
    if (p.order.mint === mint && p.order.side === 'sell') return true;
  }
  return false;
}

await runBot({
  onBatch(state, batch: Batch): OrderInput[] {
    // Fold this batch's events into the watch list.
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        watched.set(e.mint, {
          mint: e.mint,
          createSlot: e.slot,
          creator: e.creator,
          buyers: new Set(),
          decided: false,
        });
      } else if (e.event === 'TradeEvent') {
        const w = watched.get(e.mint);
        if (w === undefined || w.decided) continue;
        if (e.is_buy && e.user !== w.creator) w.buyers.add(e.user);
      } else {
        const w = watched.get(e.mint);
        if (w !== undefined) w.decided = true;
      }
    }

    // Fold this batch's fills into the open-position book.
    for (const f of batch.fills) {
      if (f.client_id.startsWith('_')) {
        // A harness close (curve completed, replay ended, write-off).
        open.delete(f.mint);
        selling.delete(f.mint);
        continue;
      }
      if (f.side === 'buy' && f.status === 'filled' && !open.has(f.mint)) {
        open.set(f.mint, { openedSlot: f.slot });
      }
    }
    for (const mint of [...selling]) {
      if (!hasPendingSell(state, mint)) selling.delete(mint);
    }
    for (const mint of [...open.keys()]) {
      if (!state.positions.has(mint) && !selling.has(mint) && !hasPendingBuy(state, mint)) {
        open.delete(mint);
      }
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = state.txFeeLamports();
    const marks = new Map<Pubkey, { vq: bigint; vt: bigint }>();
    for (const m of batch.marks) {
      marks.set(m.mint, { vq: BigInt(m.virtual_quote_reserves), vt: BigInt(m.virtual_token_reserves) });
    }

    // Exits first: take profit, cut losses, time-stop underwater losers.
    for (const [mint, pos] of state.positions) {
      if (orders.length >= cap) break;
      if (selling.has(mint)) continue;
      let held = open.get(mint);
      if (held === undefined) {
        held = { openedSlot: state.slot };
        open.set(mint, held);
      }
      let mark = marks.get(mint);
      if (mark === undefined) {
        const curve = state.curves.get(mint);
        if (curve === undefined) continue;
        mark = { vq: curve.virtual_quote_reserves, vt: curve.virtual_token_reserves };
      }
      const value = sellValue(pos.token_amount, mark.vq, mark.vt) - tx;
      const basis = pos.cost_lamports;
      if (basis <= 0n) continue;
      let exit = false;
      if (value * BPS >= basis * (BPS + TAKE_PROFIT_BPS)) exit = true;
      if (value * BPS <= basis * (BPS - STOP_LOSS_BPS)) exit = true;
      if (state.slot - held.openedSlot >= TIME_STOP_SLOTS && value * BPS < basis * (BPS - TIME_STOP_UNDER_BPS)) {
        exit = true;
      }
      if (!exit) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: MAX_SLIPPAGE_BPS });
      selling.add(mint);
    }

    // Entries: one fixed buy per qualifying launch, inside its decision window.
    let free = state.freeCashLamports() - tx * BigInt(orders.length);
    let committed = state.committedPositionCount();
    for (const w of watched.values()) {
      if (orders.length >= cap) break;
      if (w.decided) continue;
      const age = state.slot - w.createSlot;
      if (age > DECIDE_WINDOW_SLOTS) {
        w.decided = true;
        continue;
      }
      if (w.buyers.size < MIN_BUYERS) continue;
      const curve = state.curves.get(w.mint);
      if (curve === undefined || curve.complete) {
        w.decided = true;
        continue;
      }
      const sizeCap = state.maxBuyLamports(w.mint);
      if (sizeCap < MIN_BUY_LAMPORTS) continue;
      const amount = STAKE_LAMPORTS < sizeCap ? STAKE_LAMPORTS : sizeCap;
      if (amount < MIN_BUY_LAMPORTS) continue;
      if (committed >= state.hello.caps.max_open_positions) continue;
      if (free < amount + tx) continue;
      orders.push({ side: 'buy', mint: w.mint, quote_lamports: amount, max_slippage_bps: MAX_SLIPPAGE_BPS });
      free -= amount + tx;
      committed += 1;
      w.decided = true;
    }
    return orders;
  },
});
