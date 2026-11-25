// Pump.fun paper-trading sprinter: buy only launches with a real early crowd AND
// a live burst of fresh net buying, then get out fast.
//
// Entry needs three things inside a ~4-minute decision window (600 slots at
// ~0.4 s each) after the CreateEvent:
//   1. Crowd: at least 10 distinct non-creator wallets have bought the launch.
//   2. BOOST: the replay protocol has no boost field, so BOOST is modelled as
//      observed buy pressure - at least 6 distinct non-creator buyers in the
//      last 75 slots (~30 seconds) whose buys total at least 0.8 SOL in that
//      same window. A launch whose crowd arrived minutes ago but has gone
//      quiet does not qualify; the buying has to still be happening.
//   3. Net pressure: inside that same BOOST window, non-creator buy SOL must
//      exceed non-creator sell SOL, so a burst being sold into does not count.
// Two vetoes cancel a launch for good at the moment those three first hold:
// a single non-creator wallet supplying over half the BOOST-window buy SOL
// (a whale, not a crowd), or a curve price already more than 80% above the
// first observed curve price (the first TradeEvent's post-trade reserves, or
// the first mark's) - the pump has already happened and little room is left.
// If the creator sells at any point before entry, the launch is cancelled for
// good. One fixed-size position per coin (0.05 SOL), at most 5 positions open,
// no adds, no averaging: a coin that does not qualify in its window is skipped
// for good. A buy rejected for slippage keeps its watch entry while the window
// lasts and may be re-sent on a later batch, but never with another buy for
// the same mint already in flight and never after a fill.
//
// Exits are mechanical and short-horizon: take profit at +30% over cost, cut
// at -30% under cost, and sell unconditionally once a position has been held
// for 300 slots (~120 seconds), whatever its P&L. A position held at least
// 100 slots with no non-creator buy trade in the last 60 slots and valued
// below cost is also sold early: the momentum that justified entry is dead,
// so there is no reason to wait for the time exit. Valuation marks a position
// at what selling it now would pay after the 125 bps curve fee (protocol 95 +
// creator 30) minus one transaction fee, so the +30% / -30% lines are net of
// exit costs, not gross price moves.
//
// Every order carries max_slippage_bps 255 (a 2.55% tolerance): a fill whose
// output is worse than the decision-time reserves by more than that is
// rejected rather than chased. A rejected exit stays decided and is retried
// next batch until it fills or the harness closes the position.
//
// A pure function of the batches it is fed: no clock, no randomness, no I/O,
// so the two grading runs agree byte for byte. Speed: a launch is deleted
// from the watch list once it is finally decided (buy filled, window expired,
// curve completed, creator sold, whale or chased-price veto, or buy failed /
// rejected for a reason other than slippage); while a buy is pending it stays
// watched but is skipped, and the BOOST window is a head-index queue pruned in
// amortized O(1) per trade,
// so per-batch work stays proportional to undecided launches and open
// positions only.

import { BPS, LAMPORTS_PER_SOL, runBot } from './vendor/makefun-bot.ts';

/** Fixed stake per coin: 0.05 SOL. */
const STAKE_LAMPORTS = LAMPORTS_PER_SOL / 20n;
/** Smallest buy worth paying a transaction fee for (also the size-cap floor). */
const MIN_BUY_LAMPORTS = LAMPORTS_PER_SOL / 200n;
/** Distinct non-creator buyers a launch needs before it is worth buying. */
const MIN_BUYERS = 10;
/** Decision window after creation, in slots (~0.4 s each, so ~4 minutes). */
const DECIDE_WINDOW_SLOTS = 600;
/** BOOST window: buys count as fresh pressure only inside the last 75 slots (~30 s). */
const BOOST_WINDOW_SLOTS = 75;
/** BOOST needs at least this many distinct non-creator buyers inside the window. */
const BOOST_MIN_BUYERS = 6;
/** BOOST needs at least this much non-creator buy volume inside the window: 0.8 SOL. */
const BOOST_MIN_SOL_LAMPORTS = (LAMPORTS_PER_SOL * 4n) / 5n;
/** Cancel entry when the curve price is more than 80% above its first observed price. */
const MAX_ENTRY_RISE_BPS = 8000n;
/** Dead-momentum exit applies only once a position has been held this many slots. */
const DEAD_MOMENTUM_MIN_HOLD_SLOTS = 100;
/** Dead-momentum exit needs this many slots with no non-creator buy trade. */
const DEAD_MOMENTUM_QUIET_SLOTS = 60;
/** Slippage tolerance on every order, buys and sells alike: 255 bps = 2.55%. */
const MAX_SLIPPAGE_BPS = 255;
/** Curve fees on a sell (protocol 95 bps + creator 30 bps). */
const SELL_FEE_BPS = 125n;
/** Take profit at +30% over cost, valued net of sell fee and tx fee. */
const TAKE_PROFIT_BPS = 3000n;
/** Stop loss at -30% under cost, valued net of sell fee and tx fee. */
const STOP_LOSS_BPS = 3000n;
/** Hard time exit: sell after holding this many slots (~120 s), whatever the P&L. */
const MAX_HOLD_SLOTS = 300;

/** What selling `tokens` against (vq, vt) would pay after curve fees. */
function sellValue(tokens, vq, vt) {
  if (tokens <= 0n || vt <= 0n) return 0n;
  const quote = (tokens * vq) / (vt + tokens);
  return quote - (quote * SELL_FEE_BPS + BPS - 1n) / BPS;
}

/**
 * Drop BOOST-window trades older than the window. Trades sit in arrival order
 * behind a head index, so each trade is pruned exactly once; the running
 * distinct-buyer counts, per-buyer buy SOL and buy/sell SOL totals stay exact
 * without rescanning.
 */
function pruneBoost(w, nowSlot) {
  const cutoff = nowSlot - BOOST_WINDOW_SLOTS;
  while (w.recentHead < w.recent.length && w.recent[w.recentHead].slot <= cutoff) {
    const r = w.recent[w.recentHead];
    w.recentHead += 1;
    if (r.isBuy) {
      w.recentSol -= r.sol;
      const left = w.recentUsers.get(r.user) - 1;
      if (left <= 0) w.recentUsers.delete(r.user);
      else w.recentUsers.set(r.user, left);
      const leftSol = w.recentUserSol.get(r.user) - r.sol;
      if (leftSol <= 0n) w.recentUserSol.delete(r.user);
      else w.recentUserSol.set(r.user, leftSol);
    } else {
      w.recentSellSol -= r.sol;
    }
  }
  if (w.recentHead >= 64 && w.recentHead * 2 >= w.recent.length) {
    w.recent = w.recent.slice(w.recentHead);
    w.recentHead = 0;
  }
}

/** Launches still inside their decision window, by mint. Deleted once decided. */
const watched = new Map();
/** Positions we hold, by mint, with fill slot and last non-creator buy slot. */
const open = new Map();
/** Mints whose exit is decided: a rejected sell stays here and is re-sent. */
const selling = new Set();

await runBot({
  onBatch(state, batch) {
    // Fold this batch's events into the watch list. Decided launches are gone
    // from the map, so a trade for one is simply a lookup that misses.
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        watched.set(e.mint, {
          mint: e.mint,
          createSlot: e.slot,
          creator: e.creator,
          buyers: new Set(),
          recent: [],
          recentHead: 0,
          recentUsers: new Map(),
          recentUserSol: new Map(),
          recentSol: 0n,
          recentSellSol: 0n,
          firstVq: null,
          firstVt: null,
          lastBuySlot: e.slot,
        });
      } else if (e.event === 'TradeEvent') {
        if (e.is_buy && e.user !== e.creator) {
          const heldPos = open.get(e.mint);
          if (heldPos !== undefined && (heldPos.lastBuySlot === undefined || e.slot > heldPos.lastBuySlot)) {
            heldPos.lastBuySlot = e.slot;
          }
        }
        const w = watched.get(e.mint);
        if (w === undefined) continue;
        if (!e.is_buy && e.user === w.creator) {
          watched.delete(e.mint);
          continue;
        }
        if (w.firstVq === null) {
          w.firstVq = BigInt(e.virtual_quote_reserves);
          w.firstVt = BigInt(e.virtual_token_reserves);
        }
        if (e.user !== w.creator) {
          const sol = BigInt(e.quote_amount);
          w.recent.push({ slot: e.slot, user: e.user, sol, isBuy: e.is_buy });
          if (e.is_buy) {
            w.buyers.add(e.user);
            w.recentUsers.set(e.user, (w.recentUsers.get(e.user) || 0) + 1);
            w.recentUserSol.set(e.user, (w.recentUserSol.get(e.user) || 0n) + sol);
            w.recentSol += sol;
            if (e.slot > w.lastBuySlot) w.lastBuySlot = e.slot;
          } else {
            w.recentSellSol += sol;
          }
        }
      } else {
        watched.delete(e.mint);
      }
    }

    // A mark can be the first curve price observed for a watched launch.
    for (const m of batch.marks) {
      const w = watched.get(m.mint);
      if (w !== undefined && w.firstVq === null) {
        w.firstVq = BigInt(m.virtual_quote_reserves);
        w.firstVt = BigInt(m.virtual_token_reserves);
      }
    }

    // Mints with an order still in flight, built once per batch.
    const pendingBuy = new Set();
    const pendingSell = new Set();
    for (const p of state.pending.values()) {
      if (p.order.side === 'buy') pendingBuy.add(p.order.mint);
      else pendingSell.add(p.order.mint);
    }

    // Fold this batch's fills into the open-position book.
    for (const f of batch.fills) {
      if (f.client_id.startsWith('_')) {
        // A harness close (curve completed, replay ended, write-off).
        open.delete(f.mint);
        selling.delete(f.mint);
        continue;
      }
      if (f.side === 'buy') {
        if (f.status === 'filled') {
          if (!open.has(f.mint)) {
            const w = watched.get(f.mint);
            open.set(f.mint, { openedSlot: f.slot, lastBuySlot: w === undefined ? f.slot : w.lastBuySlot });
          }
          watched.delete(f.mint);
        } else if (f.status === 'failed' || f.reason !== 'max_slippage') {
          watched.delete(f.mint);
        }
        // A slippage-rejected buy leaves the launch watched while its window
        // lasts; pendingBuy below blocks a duplicate while one is in flight.
      } else if (f.status === 'filled' || f.status === 'failed') {
        selling.delete(f.mint);
      }
      // A rejected sell leaves the mint in `selling`: the exit stays decided
      // and is re-sent below until it fills or the harness closes it.
    }
    for (const mint of selling) {
      if (!state.positions.has(mint)) selling.delete(mint);
    }
    for (const mint of open.keys()) {
      if (!state.positions.has(mint) && !selling.has(mint) && !pendingBuy.has(mint)) {
        open.delete(mint);
      }
    }

    const orders = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = state.txFeeLamports();
    const marks = new Map();
    for (const m of batch.marks) {
      marks.set(m.mint, { vq: BigInt(m.virtual_quote_reserves), vt: BigInt(m.virtual_token_reserves) });
    }

    // Exits first: +30% take profit, -30% stop loss, dead-momentum early exit,
    // 300-slot hard time exit.
    // A mint already in `selling` had its sell rejected: re-send it without
    // re-testing the exit lines, unless that sell is still in flight.
    for (const [mint, pos] of state.positions) {
      if (orders.length >= cap) break;
      if (pendingSell.has(mint)) continue;
      let held = open.get(mint);
      if (held === undefined) {
        held = { openedSlot: state.slot, lastBuySlot: state.slot };
        open.set(mint, held);
      }
      let exit = selling.has(mint) || state.slot - held.openedSlot >= MAX_HOLD_SLOTS;
      if (!exit) {
        let mark = marks.get(mint);
        if (mark === undefined) {
          const curve = state.curves.get(mint);
          if (curve === undefined) continue;
          mark = { vq: curve.virtual_quote_reserves, vt: curve.virtual_token_reserves };
        }
        const basis = pos.cost_lamports;
        if (basis <= 0n) continue;
        const value = sellValue(pos.token_amount, mark.vq, mark.vt) - tx;
        if (value * BPS >= basis * (BPS + TAKE_PROFIT_BPS)) exit = true;
        if (value * BPS <= basis * (BPS - STOP_LOSS_BPS)) exit = true;
        const lastBuySlot = held.lastBuySlot === undefined ? held.openedSlot : held.lastBuySlot;
        if (
          state.slot - held.openedSlot >= DEAD_MOMENTUM_MIN_HOLD_SLOTS &&
          state.slot - lastBuySlot >= DEAD_MOMENTUM_QUIET_SLOTS &&
          value < basis
        ) {
          exit = true;
        }
      }
      if (!exit) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: MAX_SLIPPAGE_BPS });
      selling.add(mint);
    }

    // Entries: one fixed position per qualifying launch, inside its decision
    // window, crowd, BOOST and net buy pressure all required, whale and
    // chased-price vetoes applied. The map only holds undecided launches, so
    // this scan stays tiny.
    let free = state.freeCashLamports() - tx * BigInt(orders.length);
    let committed = state.committedPositionCount();
    for (const [mint, w] of watched) {
      if (orders.length >= cap) break;
      const age = state.slot - w.createSlot;
      if (age > DECIDE_WINDOW_SLOTS) {
        watched.delete(mint);
        continue;
      }
      if (pendingBuy.has(mint)) continue;
      if (state.positions.has(mint) || open.has(mint)) {
        watched.delete(mint);
        continue;
      }
      if (w.buyers.size < MIN_BUYERS) continue;
      pruneBoost(w, state.slot);
      if (w.recentUsers.size < BOOST_MIN_BUYERS) continue;
      if (w.recentSol < BOOST_MIN_SOL_LAMPORTS) continue;
      if (w.recentSol <= w.recentSellSol) continue;
      let whaleSol = 0n;
      for (const sol of w.recentUserSol.values()) {
        if (sol > whaleSol) whaleSol = sol;
      }
      if (whaleSol * 2n > w.recentSol) {
        watched.delete(mint);
        continue;
      }
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) {
        watched.delete(mint);
        continue;
      }
      if (w.firstVq !== null && w.firstVt !== null && w.firstVt > 0n && curve.virtual_token_reserves > 0n) {
        const chased =
          curve.virtual_quote_reserves * w.firstVt * BPS >
          w.firstVq * curve.virtual_token_reserves * (BPS + MAX_ENTRY_RISE_BPS);
        if (chased) {
          watched.delete(mint);
          continue;
        }
      }
      const sizeCap = state.maxBuyLamports(mint);
      if (sizeCap < MIN_BUY_LAMPORTS) continue;
      const amount = STAKE_LAMPORTS < sizeCap ? STAKE_LAMPORTS : sizeCap;
      if (amount < MIN_BUY_LAMPORTS) continue;
      if (committed >= state.hello.caps.max_open_positions) continue;
      if (free < amount + tx) continue;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: MAX_SLIPPAGE_BPS });
      free -= amount + tx;
      committed += 1;
      // Keep the watch entry: pendingBuy blocks a duplicate while this buy is
      // in flight, a fill deletes it above, and a slippage rejection leaves
      // it here for a later retry inside the window.
    }
    return orders;
  },
});
