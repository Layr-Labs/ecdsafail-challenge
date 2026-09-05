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
