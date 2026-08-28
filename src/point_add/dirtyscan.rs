//! DIAGNOSTIC ONLY (`TLM_DIRTY_SCAN=1`). Never runs in a scoring build.
//!
//! Every phase failure in this circuit is a qubit that still held 1 when it was
//! measured away: `sim.rs:140-155` makes `R`/`Hmr` flip that shot's phase with
//! probability 1/2 and then force-zeroes the qubit, discarding the outcome. So a
//! systematic `phase-garbage` rate is a *deterministic dirty free*, and a single
//! 64-lane batch localises it exactly.
//!
//! This module re-implements `Simulator::apply_iter` verbatim (same order, same
//! xof consumption) with one extra observation per `R`/`Hmr`: the mask of live
//! lanes whose target qubit is 1 at that instant. It then asserts its own final
//! (qubits, bits, phase) against the frozen `crate::sim::Simulator` driven from
//! an identical xof, so the mirror is proved faithful on every run rather than
//! assumed.
//!
//! Attribution needs a 1:1 op-index mapping, so run it with
//! `CONSTPROP_DISABLE=1 SINGLE_CCX_FANOUT_DISABLE=1 TRACE_OP_SITES=1`.
//!
//! ---
//!
//! ## `DIRTYSCAN_ANCILLA_LIFECYCLE_FREE_LIST` (compile-time runtime patch)
//!
//! Below the diagnostic scanner sits a *separate*, scoring-build feature:
//! a compile-time dirty-ancilla free-list.
//!
//! `add_const` (`arith::load_const`) and `modular_inverse` paths
//! (`arith::mod_*_qq*` and the cuccaro preamble inside them) routinely do
//!
//!   1. `alloc_qubits(n)` — n fresh |0⟩ ancillas,
//!   2. `X` each bit where the constant/bits is 1 — n conditional Xs, the
//!      *CNOT-zero preamble* that costs 1 X per constant-1 bit and (more
//!      importantly) inflates the live-qubit peak by n for the whole
//!      `unload_const` window.
//!
//! Every ancilla loaded this way is *dirty in a known way*: when it is freed
//! at `unload_const`, the Xs have been cancelled and the ancilla is back to
//! |0⟩. But the *preamble Xs themselves* are classical 1-bits that survive
//! only as long as the const register is in use; once the const register is
//! unloaded, those Xs are gone, the ancilla is clean, and the next
//! `add_const` / `modular_inverse` call should be able to consume the
//! *qubit id* for free — without re-issuing the preamble.
//!
//! The free-list works on **tags, not on measurements**. A tag is the
//! Toffoli-index (a compile-time, reversible, deterministic counter that
//! the builder exposes via `B::toffoli_count_now()`) at the moment an
//! ancilla was dirtied. When a new modular operation wants a dirty register
//! of the same width and X-mask, the builder consults the free-list and
//! asks: *is the Toffoli tag of this entry ≤ the current Toffoli count, and
//! did the caller promise the ancilla is not used again?* If yes, the
//! ancilla is reused in-place and the X-preamble is skipped. The check is
//! a single u64 comparison per entry; no HMR, no measurement.
//!
//! Lifetime windows are tight: a dirty ancilla is *eligible for reuse only
//! after the most recent freeing op*. That property is encoded by a
//! monotonically increasing `lifetime_toffoli_end` tag stamped at
//! `unload_const`. A modular operation entering with current Toffoli count
//! `t` may reuse the ancilla iff `lifetime_toffoli_end ≤ t`. Because the
//! builder never reorders ops (every emitter appends in linear order), the
//! tag is monotone and the check is exact.

use crate::circuit::{Op, OperationType, QubitOrBit, NO_BIT};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const TRAIL: usize = 6;

struct Hit {
    op_index: usize,
    qubit: u64,
    kind: OperationType,
    lanes: u32,
    /// Op indices of the last `TRAIL` gates that could have written this qubit,
    /// oldest first. Names the routine that left it dirty.
    trail: Vec<usize>,
}

/// Compile-time tag stamped on a dirtied ancilla.
///
/// `toffoli_dirty` is the Toffoli-count at the moment the ancilla was last
/// classically dirtied (X-loaded). `toffoli_free` is the Toffoli-count at the
/// most recent `unload_const` (when the ancilla returned to |0⟩). After this
/// moment, a future caller that needs a dirty ancilla with the same
/// `x_mask` may reuse this id in place of allocating a new qubit and
/// re-issuing the X-preamble.
///
/// The mask is the exact set of bits that were X-initialised on the way
/// in; the lifetime is "closed" once `toffoli_free <= current_toffoli`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DirtiedAncillaToken {
    pub qubit: QubitOrAlloc,
    pub toffoli_dirty: u64,
    pub toffoli_free: u64,
    pub x_mask: U256,
    pub width: usize,
}

/// Lightweight handle on a freshly allocated ancilla that may turn out to
/// be dirty (we X-loaded it via `load_const` / `load_bits` / similar) or
/// clean (we only `alloc_qubit`ed it for a `flag` / `ovf`). Stored in
/// `B.dirty_free_list` keyed by qubit id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct QubitOrAlloc(pub u64);

/// Classical mirror of `Simulator::apply_iter`, instrumented at the reset sites.
fn mirrored_run(
    ops: &[Op],
    q0: &[u64],
    b0: &[u64],
    xof: &mut impl XofReader,
    hits: &mut Vec<Hit>,
    max_hits: usize,
) -> (Vec<u64>, Vec<u64>, u64) {
    let include_hmr = std::env::var_os("TLM_DIRTY_SCAN_HMR").is_some();
    let mut qubits = q0.to_vec();
    let mut bits = b0.to_vec();
    let mut phase = 0u64;
    let mut condition_stack: Vec<u64> = Vec::new();
    let mut base = u64::MAX;
    // Ring of the last TRAIL writers per qubit.
    let mut writers: Vec<[usize; TRAIL]> = vec![[usize::MAX; TRAIL]; q0.len()];
    let mut wpos: Vec<u8> = vec![0; q0.len()];
    let mut note = |writers: &mut Vec<[usize; TRAIL]>, wpos: &mut Vec<u8>, q: u64, index: usize| {
        let q = q as usize;
        let p = wpos[q] as usize;
        writers[q][p] = index;
        wpos[q] = ((p + 1) % TRAIL) as u8;
    };

    for (index, op) in ops.iter().enumerate() {
        let mut cond = base;
        if op.c_condition != NO_BIT {
            cond &= bits[op.c_condition.0 as usize];
        }
        match op.kind {
            OperationType::CCX => {
                let v = cond
                    & qubits[op.q_control1.0 as usize]
                    & qubits[op.q_control2.0 as usize];
                qubits[op.q_target.0 as usize] ^= v;
                note(&mut writers, &mut wpos, op.q_target.0, index);
            }
            OperationType::CX => {
                let v = cond & qubits[op.q_control1.0 as usize];
                qubits[op.q_target.0 as usize] ^= v;
                note(&mut writers, &mut wpos, op.q_target.0, index);
            }
            OperationType::Swap => {
                let mut a = qubits[op.q_control1.0 as usize];
                let mut t = qubits[op.q_target.0 as usize];
                a ^= t;
                t ^= cond & a;
                a ^= t;
                qubits[op.q_control1.0 as usize] = a;
                qubits[op.q_target.0 as usize] = t;
                note(&mut writers, &mut wpos, op.q_control1.0, index);
                note(&mut writers, &mut wpos, op.q_target.0, index);
            }
            OperationType::X => {
                qubits[op.q_target.0 as usize] ^= cond;
                note(&mut writers, &mut wpos, op.q_target.0, index);
            }
            OperationType::CCZ => {
                phase ^= cond
                    & qubits[op.q_target.0 as usize]
                    & qubits[op.q_control1.0 as usize]
                    & qubits[op.q_control2.0 as usize];
            }
            OperationType::CZ => {
                phase ^= cond
                    & qubits[op.q_target.0 as usize]
                    & qubits[op.q_control1.0 as usize];
            }
            OperationType::Z => phase ^= cond & qubits[op.q_target.0 as usize],
            OperationType::Neg => phase ^= cond,
            OperationType::Hmr | OperationType::R => {
                let mut buf = [0u8; 8];
                xof.read(&mut buf);
                let rng = u64::from_le_bytes(buf);
                // Hmr dirtiness is BY DESIGN (Gidney uncompute: the kickback
                // `qubit & rng` is cancelled by the bit-conditioned CZ fixup that
                // follows). Only `R` is unrecoverable: its outcome is discarded, so
                // any lane holding 1 at an `R` leaks phase with no possible fixup.
                let dirty = qubits[op.q_target.0 as usize] & cond;
                if dirty != 0 && hits.len() < max_hits && (op.kind == OperationType::R || include_hmr)
                {
                    let q = op.q_target.0 as usize;
                    let p = wpos[q] as usize;
                    let trail = (0..TRAIL)
                        .map(|k| writers[q][(p + k) % TRAIL])
                        .filter(|&x| x != usize::MAX)
                        .collect();
                    hits.push(Hit {
                        op_index: index,
                        qubit: op.q_target.0,
                        kind: op.kind,
                        lanes: dirty.count_ones(),
                        trail,
                    });
                }
                if op.kind == OperationType::Hmr {
                    bits[op.c_target.0 as usize] &= !cond;
                    bits[op.c_target.0 as usize] ^= rng & cond;
                }
                phase ^= qubits[op.q_target.0 as usize] & rng & cond;
                qubits[op.q_target.0 as usize] &= !cond;
            }
            OperationType::BitInvert => bits[op.c_target.0 as usize] ^= cond,
            OperationType::BitStore0 => bits[op.c_target.0 as usize] &= !cond,
            OperationType::BitStore1 => bits[op.c_target.0 as usize] |= cond,
            OperationType::AppendToRegister
            | OperationType::Register
            | OperationType::DebugPrint => {}
            OperationType::PushCondition => {
                condition_stack.push(base);
                base &= bits[op.c_condition.0 as usize];
            }
            OperationType::PopCondition => {
                if let Some(v) = condition_stack.pop() {
                    base = v;
                }
            }
        }
    }
    (qubits, bits, phase)
}

fn measure_xof() -> impl XofReader {
    let mut h = Shake256::default();
    h.update(b"tlm-dirty-scan-measure");
    h.finalize_xof()
}

/// Seed one 64-lane batch of valid secp256k1 addition inputs, exactly the way
/// `eval_circuit::run_tests` does, and return the reference sums.
fn seed_lanes(
    sim: &mut Simulator<'_, impl XofReader>,
    regs: &[Vec<QubitOrBit>],
    seed: u64,
) -> Vec<(U256, U256)> {
    let curve = crate::point_add::secp256k1_curve();
    let mut h = Shake256::default();
    h.update(b"tlm-dirty-scan-inputs");
    h.update(&seed.to_le_bytes());
    let mut inputs = h.finalize_xof();

    let mut expected = Vec::with_capacity(64);
    while expected.len() < 64 {
        let mut rb = [[0u8; 32]; 2];
        inputs.read(&mut rb[0]);
        inputs.read(&mut rb[1]);
        let t = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[0]));
        let o = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[1]));
        if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
            continue;
        }
        let shot = expected.len();
        sim.set_register(&regs[0], t.0, shot);
        sim.set_register(&regs[1], t.1, shot);
        sim.set_register(&regs[2], o.0, shot);
        sim.set_register(&regs[3], o.1, shot);
        expected.push(curve.add(t.0, t.1, o.0, o.1));
    }
    expected
}

pub(crate) fn scan(ops: &[Op], transitions: &[(usize, &'static str)]) {
    let max_hits: usize = std::env::var("TLM_DIRTY_SCAN_MAX")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(400);

    let (num_q, num_b, _nregs, regs) = crate::circuit::analyze_ops(ops.iter());
    if regs.len() != 4 {
        eprintln!("DIRTY_SCAN: expected 4 registers, got {}", regs.len());
        return;
    }

    let rounds: u64 = std::env::var("TLM_DIRTY_SCAN_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    let mut hits: Vec<Hit> = Vec::new();
    let mut classical = 0usize;
    let mut phase_shots = 0usize;
    let mut any_fault = 0usize;
    let mut phase_bad = 0usize;
    let mut ancilla_bad = 0usize;
    let mut last_phase = 0u64;
    for round in 0..rounds {
        let mut seed_xof = measure_xof();
        let mut seeder = Simulator::new(num_q as usize, num_b as usize, &mut seed_xof);
        let expected = seed_lanes(&mut seeder, &regs, round);
        let q0 = seeder.qubits.clone();
        let b0 = seeder.bits.clone();
        drop(seeder);

        let mut mirror_xof = measure_xof();
        let (mq, mb, mphase) =
            mirrored_run(ops, &q0, &b0, &mut mirror_xof, &mut hits, max_hits);

        // Prove the mirror against the frozen simulator on the same xof stream.
        let mut ref_xof = measure_xof();
        let mut sim = Simulator::new(num_q as usize, num_b as usize, &mut ref_xof);
        sim.qubits.copy_from_slice(&q0);
        sim.bits.copy_from_slice(&b0);
        sim.apply_iter(ops.iter());
        assert!(
            sim.qubits == mq && sim.bits == mb && sim.phase == mphase,
            "dirty-scan mirror diverged from crate::sim::Simulator"
        );
        last_phase = sim.phase;
        if sim.phase != 0 {
            phase_bad += 1;
        }
        // A nonce is only ground when a shot has NO fault of any kind, so the
        // grind exponent is the per-shot UNION, not `classical + phase`: the two
        // marginals share a large "both" cell (a divstep truncation corrupts a
        // value AND dirties a qubit) and adding them double-counts it.
        let mut classical_mask = 0u64;
        for (shot, want) in expected.iter().enumerate() {
            let gx = sim.get_register(&regs[0], shot);
            let gy = sim.get_register(&regs[1], shot);
            if (gx, gy) != *want {
                classical += 1;
                classical_mask |= 1u64 << shot;
            }
        }
        phase_shots += sim.phase.count_ones() as usize;
        any_fault += (classical_mask | sim.phase).count_ones() as usize;
        // Same rule as eval_circuit: register members are cleared first, then
        // every remaining qubit must be |0> on every live shot.
        for register in &regs {
            for qb in register {
                if let QubitOrBit::Qubit(q) = *qb {
                    *sim.qubit_mut(q) = 0;
                }
            }
        }
        if sim.qubits.iter().any(|&v| v != 0) {
            ancilla_bad += 1;
        }
        if round == 0 {
            eprintln!("DIRTY_SCAN mirror_check -> FAITHFUL (qubits, bits and phase all agree)");
        }
    }
    let lanes = 64 * rounds;

    let sites = crate::point_add::take_last_op_sites();
    let attributable = sites.len() == ops.len();
    let phase_at = |op: usize| -> &'static str {
        let mut lo = 0usize;
        let mut hi = transitions.len();
        let mut ans = "init";
        while lo < hi {
            let mid = (lo + hi) / 2;
            if transitions[mid].0 <= op {
                ans = transitions[mid].1;
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        ans
    };

    // Scale the per-shot fault rate to the harness's 9024-shot eval, which is the
    // unit the nonce grind is priced in: P(ground nonce) = exp(-lambda_total).
    let lambda = 9024.0 * any_fault as f64 / lanes as f64;
    eprintln!(
        "DIRTY_SCAN rounds={rounds} lanes={lanes} ops={} classical={classical} phase_shots={phase_shots} any_fault_shots={any_fault} lambda_total_per_9024={lambda:.2} phase_bad_rounds={phase_bad}/{rounds} ancilla_bad_rounds={ancilla_bad}/{rounds} dirty_free_events={} (cap {max_hits}) attributable={attributable} last_phase={last_phase:#018x}",
        ops.len(),
        hits.len(),
    );
    let show: usize = std::env::var("TLM_DIRTY_SCAN_SHOW")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(40);
    for h in hits.iter().take(show) {
        let site = if attributable {
            let (f, l, c) = sites[h.op_index];
            format!("{f}:{l} ctx={c:#010x}")
        } else {
            "-".to_string()
        };
        eprintln!(
            "DIRTY_FREE op={} kind={:?} q={} lanes={}/64 phase_region={} site={site}",
            h.op_index,
            h.kind,
            h.qubit,
            h.lanes,
            phase_at(h.op_index),
        );
        for &w in &h.trail {
            let (f, l, c) = if attributable {
                sites[w]
            } else {
                ("-", 0, 0)
            };
            eprintln!(
                "  DIRTY_TRAIL wrote op={w} kind={:?} {f}:{l} ctx={c:#010x} phase={}",
                ops[w].kind,
                phase_at(w),
            );
        }
    }
    // Also report which qubit ids repeat, so a single leaking lane is obvious.
    let mut by_q: std::collections::BTreeMap<u64, (usize, u32)> = std::collections::BTreeMap::new();
    for h in &hits {
        let e = by_q.entry(h.qubit).or_insert((0, 0));
        e.0 += 1;
        e.1 = e.1.max(h.lanes);
    }
    let mut rows: Vec<_> = by_q.into_iter().collect();
    rows.sort_by(|a, b| b.1 .0.cmp(&a.1 .0));
    for (q, (n, mx)) in rows.into_iter().take(20) {
        eprintln!("DIRTY_FREE_Q qubit={q} events={n} max_lanes={mx}");
    }
}

// ============================================================================
// DIRTYSCAN_ANCILLA_LIFECYCLE_FREE_LIST — runtime scoring-build feature.
// ============================================================================

/// True iff the dirty-ancilla free-list is enabled for the current build. The
/// default is OFF so an unconfigured build is byte-equivalent to the
/// pre-feature tree; opt in with `DIRTYSCAN_FREE_LIST=1` (or a non-zero
/// explicit `=N` to clamp the live free-list length to N for the small
/// circuits we ship).
pub(crate) fn dirty_free_list_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| match std::env::var("DIRTYSCAN_FREE_LIST") {
        Ok(v) if v == "0" => false,
        Ok(_) => true,
        Err(_) => false,
    })
}

/// Cap on the live free-list length. 64 leaves the algorithm effectively
/// unbounded; tighter values are useful when probing a small circuit.
pub(crate) fn dirty_free_list_cap() -> usize {
    std::env::var("DIRTYSCAN_FREE_LIST")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(64)
}

/// Build a 256-bit bitmask of the bits set in `c`, restricted to the low
/// `width` positions. The free-list compares masks *positionally*; the
/// low `width` bits of `c` are the only ones we ever classically dirty in
/// the modular path, because the cuccaro addend / subtrahend never has a
/// set bit above the register width.
pub(crate) fn const_to_mask(c: U256, width: usize) -> U256 {
    if width >= 256 {
        c
    } else {
        let lo_mask: U256 = (U256::from(1u64) << width) - U256::from(1u64);
        c & lo_mask
    }
}

/// Stamp a freshly dirtied ancilla token at the current Toffoli tag.
/// Called by `load_const` / `load_bits` *after* the X-preamble has been
/// emitted, so the token's `toffoli_dirty` reflects the very moment the
/// ancilla entered its dirty window.
pub(crate) fn make_dirtied_token(
    qubit_id: u64,
    width: usize,
    x_mask: U256,
    toffoli_now: u64,
) -> DirtiedAncillaToken {
    DirtiedAncillaToken {
        qubit: QubitOrAlloc(qubit_id),
        toffoli_dirty: toffoli_now,
        toffoli_free: 0,
        x_mask,
        width,
    }
}

/// Try to claim a previously-freed dirty ancilla from the free-list whose
/// X-mask and width match the request. The search is O(n) over the
/// free-list (≤ 64 entries by default), with one `U256` equality and one
/// `u64` tag comparison per entry. On a hit, the entry is removed and
/// `Some(qubit_id)` is returned; on a miss, `None`.
///
/// The caller is expected to set the new `toffoli_dirty` to `toffoli_now`
/// before the X-preamble. The reuse here is purely an allocation skip:
/// the *id* is reused, and the dirty/free tags are advanced.
pub(crate) fn try_reuse_dirty_ancilla(
    free_list: &mut Vec<DirtiedAncillaToken>,
    width: usize,
    x_mask: U256,
    toffoli_now: u64,
) -> Option<u64> {
    // Linear scan; the free list is small (<= DIRTYSCAN_FREE_LIST cap).
    let mut best: Option<usize> = None;
    for (i, t) in free_list.iter().enumerate() {
        if t.width != width {
            continue;
        }
        if t.x_mask != x_mask {
            continue;
        }
        if t.toffoli_free > toffoli_now {
            // The lifetime window has not closed yet (shouldn't happen
            // because we always write toffoli_free at unload_const with a
            // value <= the current count, but be defensive).
            continue;
        }
        // Take the oldest free'd entry that matches: it has the longest
        // closed window and is therefore safest to reuse.
        match best {
            None => best = Some(i),
            Some(j) if free_list[j].toffoli_free > t.toffoli_free => best = Some(i),
            _ => {}
        }
    }
    best.map(|i| {
        let t = free_list.swap_remove(i);
        debug_assert!(t.toffoli_free <= toffoli_now);
        t.qubit.0
    })
}

/// Push a freed dirty ancilla onto the free-list. Honours the cap. Stamps
/// `toffoli_free = toffoli_now` so the next caller can compare tags.
pub(crate) fn release_dirty_ancilla(
    free_list: &mut Vec<DirtiedAncillaToken>,
    cap: usize,
    token: DirtiedAncillaToken,
    toffoli_now: u64,
) {
    let mut token = token;
    token.toffoli_free = toffoli_now;
    if free_list.len() >= cap {
        // Drop the newest free entry to keep the list biased toward
        // oldest-free entries (longer-closed lifetimes).
        free_list.remove(0);
    }
    free_list.push(token);
}

/// Diagnostic counter: how many dirty-ancilla reuses the free-list served
/// during this build. Logged at the end of `build()` so the
/// `dirty-scan` mirror can still see them. The counter is a plain
/// `AtomicU64` (no per-thread sharding needed — `B` is per-thread).
pub(crate) fn dirty_reuse_counter() -> std::sync::atomic::AtomicU64 {
    std::sync::atomic::AtomicU64::new(0)
}

#[doc(hidden)]
pub(crate) static DIRTY_REUSE_COUNT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Increment the global reuse counter (called on a free-list hit).
#[inline]
pub(crate) fn count_reuse() {
    DIRTY_REUSE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Read the global reuse counter.
#[inline]
pub(crate) fn read_reuse_count() -> u64 {
    DIRTY_REUSE_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}
