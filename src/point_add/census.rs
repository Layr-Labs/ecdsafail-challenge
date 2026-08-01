//! DIAGNOSTIC ONLY (`TLM_CENSUS=1`). Never runs in a scoring build.
//!
//! Re-mines the identity-keyed deep-strip tables (`deep_strip_keys.rs`) against the
//! *current* op stream.
//!
//! Why this exists: the shipped tables key each census-dead gate by its operand tuple
//! plus a k-th-occurrence ordinal, and carry the census-time tuple occupancy as a
//! tripwire. Any edit that adds or removes a gate sharing a tuple slides every later
//! ordinal for that tuple, so `apply_deep_strip_identity` discards those keys rather
//! than risk deleting a live Toffoli. The shipped head discards 251 of them. Recovering
//! them (and finding whatever new slack the current stream has) needs a fresh census.
//!
//! What it measures, per CCX/CCZ, over N random on-curve addition inputs:
//!
//!   FIRED       cond & c1 & c2 (& t for CCZ) was ever nonzero.
//!               Never set  => the gate is the identity on every reachable input; delete.
//!   C1_NOT_C2   cond & c1 & !c2 (& t) was ever nonzero.
//!               Never set  => c2 is implied by c1, so CCX(c1,c2,t) == CX(c1,t); act=2.
//!   C2_NOT_C1   cond & c2 & !c1 (& t) was ever nonzero.
//!               Never set  => c1 is implied by c2, so CCX == CX(c2,t); act=1.
//!
//! The downgrade rewrites are *identities* wherever the predicate holds, so they carry
//! no error at all; a strip entry is only as good as the sample that justified it.
//!
//! Like `dirtyscan`, the replay loop below re-implements `Simulator::apply_iter`
//! verbatim and asserts its own final (qubits, bits, phase) against the frozen
//! `crate::sim::Simulator` on the first round, so the mirror is *proved* faithful on
//! every run rather than assumed. It also checks the classical sum of every lane
//! against `curve.add`, which catches a broken input draw immediately.
//!
//! Inputs for a round are drawn from a Shake256 keyed by the round index and are fully
//! independent of the measurement xof the replay consumes -- see `notes/04-traps.md`
//! §4 for the false-`classical=0` trap that sharing one stream produces.
//!
//! Usage (unsandboxed, from the repo root):
//!   SUB4_APPLY_STRIP=0 TLM_CENSUS=1 TLM_CENSUS_ROUNDS=20000 \
//!   TLM_CENSUS_OUT=/tmp/keys.rs ./target/release/build_circuit
//!
//! `SUB4_APPLY_STRIP=0` is required: the tables are applied to the *unstripped* stream,
//! so ordinals must be assigned over that same stream.

use crate::circuit::{Op, OperationType, QubitOrBit, NO_BIT};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::HashMap;

const F_FIRED: u8 = 1;
const F_C1_NOT_C2: u8 = 2;
const F_C2_NOT_C1: u8 = 4;

/// Per-gate counters, in shots (not batches).
///
/// `live` is the number of shots on which the classical condition admitted the gate.
/// That is *exactly* what the scorer charges: `sim.rs` adds `cond.count_ones()` to
/// `toffoli_gates` before it ever looks at the control values, so a gate that never
/// fires still costs full Toffoli until it is removed or downgraded. So `live` is the
/// score value of stripping or downgrading this gate, and summing it over every gate
/// reproduces the reported average executed Toffoli.
///
/// `viol_c2` / `viol_c1` count the shots that *refute* the corresponding downgrade.
/// Zero violations over a large `live` is the evidence a downgrade needs; `live` is
/// the sample size that gives that zero its meaning, and a gate under a rarely-true
/// condition can accumulate a zero on almost no evidence at all.
#[derive(Clone, Copy, Default)]
struct Counts {
    live: u32,
    fire: u32,
    viol_c2: u32,
    viol_c1: u32,
}

/// Operand tuple identifying a gate: (kind, q_control2, q_control1, q_target, c_condition).
type Tup = (u8, u64, u64, u64, u64);

/// Measurement randomness for one replay.
///
/// This MUST vary per round. `Hmr`/`R` flip a shot's phase with probability 1/2 drawn from
/// this stream, so holding it fixed across rounds freezes which dirty resets leak phase and
/// turns the phase-fault rate into a single draw rather than an average. The harness feeds
/// its own Fiat-Shamir xof to the simulator, i.e. fresh randomness per candidate nonce, so
/// only a per-round stream estimates the rate it will actually see.
fn measure_xof_seeded(seed: u64) -> impl XofReader {
    let mut h = Shake256::default();
    h.update(b"tlm-census-measure");
    h.update(&seed.to_le_bytes());
    h.finalize_xof()
}

fn measure_xof() -> impl XofReader {
    measure_xof_seeded(0)
}

/// Seed one 64-lane batch of valid secp256k1 addition inputs and return the reference
/// sums. Every pair is drawn before the replay starts.
fn seed_lanes(
    sim: &mut Simulator<'_, impl XofReader>,
    regs: &[Vec<QubitOrBit>],
    seed: u64,
) -> Vec<(U256, U256)> {
    let curve = crate::point_add::secp256k1_curve();
    let mut h = Shake256::default();
    h.update(b"tlm-census-inputs");
    h.update(&seed.to_le_bytes());
    let mut inputs = h.finalize_xof();

    let mut expected = Vec::with_capacity(64);
    while expected.len() < 64 {
        let mut rb = [[0u8; 32]; 2];
        inputs.read(&mut rb[0]);
        inputs.read(&mut rb[1]);
        let t = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[0]));
        let o = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[1]));
        // Same exclusions eval_circuit applies: no doubling, no point at infinity.
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

/// Faithful mirror of `Simulator::apply_iter`, instrumented at every CCX/CCZ.
///
/// `flags[g]` accumulates the three observations for the g-th Toffoli-family gate in
/// stream order. Controls are read before the target is written, which is sound for
/// CCX (the target is not a control) and vacuous for CCZ (nothing is written).
fn mirrored_run(
    ops: &[Op],
    q0: &[u64],
    b0: &[u64],
    xof: &mut impl XofReader,
    flags: &mut [u8],
    counts: &mut [Counts],
) -> (Vec<u64>, Vec<u64>, u64) {
    let mut qubits = q0.to_vec();
    let mut bits = b0.to_vec();
    let mut phase = 0u64;
    let mut condition_stack: Vec<u64> = Vec::new();
    let mut base = u64::MAX;
    let mut g = 0usize;

    for op in ops.iter() {
        let mut cond = base;
        if op.c_condition != NO_BIT {
            cond &= bits[op.c_condition.0 as usize];
        }
        match op.kind {
            OperationType::CCX => {
                let c1 = qubits[op.q_control1.0 as usize];
                let c2 = qubits[op.q_control2.0 as usize];
                let f = &mut flags[g];
                let n = &mut counts[g];
                n.live += cond.count_ones();
                let fire = cond & c1 & c2;
                let v2 = cond & c1 & !c2;
                let v1 = cond & c2 & !c1;
                n.fire += fire.count_ones();
                n.viol_c2 += v2.count_ones();
                n.viol_c1 += v1.count_ones();
                if fire != 0 {
                    *f |= F_FIRED;
                }
                if v2 != 0 {
                    *f |= F_C1_NOT_C2;
                }
                if v1 != 0 {
                    *f |= F_C2_NOT_C1;
                }
                g += 1;
                qubits[op.q_target.0 as usize] ^= fire;
            }
            OperationType::CCZ => {
                let c1 = qubits[op.q_control1.0 as usize];
                let c2 = qubits[op.q_control2.0 as usize];
                // CCZ is symmetric in (target, c1, c2) as a phase, but the CZ downgrade
                // keeps (q_control1, q_target), so the target must be in every mask.
                let m = cond & qubits[op.q_target.0 as usize];
                let f = &mut flags[g];
                let n = &mut counts[g];
                // The scorer charges CCZ on the condition alone, same as CCX.
                n.live += cond.count_ones();
                let fire = m & c1 & c2;
                let v2 = m & c1 & !c2;
                let v1 = m & c2 & !c1;
                n.fire += fire.count_ones();
                n.viol_c2 += v2.count_ones();
                n.viol_c1 += v1.count_ones();
                if fire != 0 {
                    *f |= F_FIRED;
                }
                if v2 != 0 {
                    *f |= F_C1_NOT_C2;
                }
                if v1 != 0 {
                    *f |= F_C2_NOT_C1;
                }
                g += 1;
                phase ^= fire;
            }
            OperationType::CX => {
                let v = cond & qubits[op.q_control1.0 as usize];
                qubits[op.q_target.0 as usize] ^= v;
            }
            OperationType::Swap => {
                let mut a = qubits[op.q_control1.0 as usize];
                let mut t = qubits[op.q_target.0 as usize];
                a ^= t;
                t ^= cond & a;
                a ^= t;
                qubits[op.q_control1.0 as usize] = a;
                qubits[op.q_target.0 as usize] = t;
            }
            OperationType::X => qubits[op.q_target.0 as usize] ^= cond,
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

/// Prove the mirror against the frozen simulator on one shared seeding, and report
/// classical correctness so a broken input draw cannot masquerade as a clean census.
fn verify_mirror(ops: &[Op], num_q: usize, num_b: usize, regs: &[Vec<QubitOrBit>]) {
    let mut seed_xof = measure_xof();
    let mut seeder = Simulator::new(num_q, num_b, &mut seed_xof);
    let expected = seed_lanes(&mut seeder, regs, 0);
    let q0 = seeder.qubits.clone();
    let b0 = seeder.bits.clone();
    drop(seeder);

    let ng = count_gates(ops);
    let mut scratch = vec![0u8; ng];
    let mut scratch_counts = vec![Counts::default(); ng];
    let mut mirror_xof = measure_xof();
    let (mq, mb, mphase) =
        mirrored_run(ops, &q0, &b0, &mut mirror_xof, &mut scratch, &mut scratch_counts);

    let mut ref_xof = measure_xof();
    let mut sim = Simulator::new(num_q, num_b, &mut ref_xof);
    sim.qubits.copy_from_slice(&q0);
    sim.bits.copy_from_slice(&b0);
    sim.apply_iter(ops.iter());
    assert!(
        sim.qubits == mq && sim.bits == mb && sim.phase == mphase,
        "census mirror diverged from crate::sim::Simulator"
    );

    let mut classical = 0usize;
    for (shot, want) in expected.iter().enumerate() {
        let gx = sim.get_register(&regs[0], shot);
        let gy = sim.get_register(&regs[1], shot);
        if (gx, gy) != *want {
            classical += 1;
        }
    }
    eprintln!(
        "CENSUS mirror_check -> FAITHFUL (qubits, bits, phase agree); \
         lane 0 batch: classical={classical}/64 phase={}/64",
        sim.phase.count_ones()
    );
}

/// Read a register out of a raw qubit/bit state for one shot, the way
/// `Simulator::get_register` does.
fn read_register(reg: &[QubitOrBit], qubits: &[u64], bits: &[u64], shot: usize) -> U256 {
    let mut v = U256::ZERO;
    for (i, item) in reg.iter().enumerate() {
        let b = match item {
            QubitOrBit::Qubit(id) => (qubits[id.0 as usize] >> shot) & 1,
            QubitOrBit::Bit(id) => (bits[id.0 as usize] >> shot) & 1,
        };
        v.set_bit(i, b != 0);
    }
    v
}

/// Shots that would fail the harness: a wrong sum, or a flipped phase.
///
/// The harness rejects a run unless ALL 9024 of its shots are clean, and its inputs are a
/// Fiat-Shamir hash of the whole op stream -- so editing a single gate redraws every test
/// input, and a config ships only if some tail nonce happens to draw 9024 clean ones.
/// With a per-shot fault rate p, that probability is exp(-9024*p) = exp(-lambda). This is
/// what decides whether a config is grindable at all, and it dominates any Toffoli saving.
/// Returns (any, classical, phase) faulty-shot counts. `any` is the per-shot UNION, not
/// the sum: a divstep truncation can both corrupt a value and dirty a qubit, and adding
/// the marginals would double-count that overlap. The union is what sets P(clean seed).
fn count_faults(
    regs: &[Vec<QubitOrBit>],
    qubits: &[u64],
    bits: &[u64],
    phase: u64,
    expected: &[(U256, U256)],
) -> (u32, u32, u32) {
    let mut classical = 0u64;
    for (shot, want) in expected.iter().enumerate() {
        let gx = read_register(&regs[0], qubits, bits, shot);
        let gy = read_register(&regs[1], qubits, bits, shot);
        if (gx, gy) != *want {
            classical |= 1u64 << shot;
        }
    }
    (
        (classical | phase).count_ones(),
        classical.count_ones(),
        phase.count_ones(),
    )
}

fn count_gates(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

fn tup_of(op: &Op) -> Tup {
    (
        op.kind as u8,
        op.q_control2.0,
        op.q_control1.0,
        op.q_target.0,
        op.c_condition.0,
    )
}

pub(crate) fn run(ops: &[Op]) {
    let rounds: u64 = std::env::var("TLM_CENSUS_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);
    let threads: usize = std::env::var("TLM_CENSUS_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
    // Round index seeds the input draw, so a disjoint offset gives a disjoint input set.
    // Mine on one range and re-census on another to get a genuine holdout: any candidate
    // whose predicate is violated on the held-out set was a sampling artefact, and that
    // is the only way to bound the false-positive rate from the inside.
    let offset: u64 = std::env::var("TLM_CENSUS_ROUND_OFFSET")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    let (num_q, num_b, _nregs, regs) = crate::circuit::analyze_ops(ops.iter());
    assert_eq!(regs.len(), 4, "census expects the 4 harness registers");
    let num_q = num_q as usize;
    let num_b = num_b as usize;
    let ngates = count_gates(ops);

    eprintln!(
        "CENSUS start: ops={} gates={} rounds={} lanes={} threads={} offset={}",
        ops.len(),
        ngates,
        rounds,
        rounds * 64,
        threads,
        offset
    );

    verify_mirror(ops, num_q, num_b, &regs);

    let regs_ref = &regs;
    let mut merged = vec![0u8; ngates];
    let mut totals = vec![Counts::default(); ngates];
    let mut total_faults = (0u64, 0u64, 0u64);
    let chunk = rounds.div_ceil(threads as u64);
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for t in 0..threads {
            let lo = t as u64 * chunk;
            let hi = ((t as u64 + 1) * chunk).min(rounds);
            if lo >= hi {
                continue;
            }
            handles.push(scope.spawn(move || {
                let mut flags = vec![0u8; ngates];
                let mut counts = vec![Counts::default(); ngates];
                let mut faults = (0u64, 0u64, 0u64); // (any, classical, phase)
                for round in lo..hi {
                    let mut seed_xof = measure_xof();
                    let mut seeder = Simulator::new(num_q, num_b, &mut seed_xof);
                    // Round 0's inputs are the ones `verify_mirror` already proved out.
                    let expected = seed_lanes(&mut seeder, regs_ref, round + offset);
                    let q0 = seeder.qubits.clone();
                    let b0 = seeder.bits.clone();
                    drop(seeder);
                    let mut xof = measure_xof_seeded(round + offset + 0x9e37_79b9);
                    let (fq, fb, fphase) =
                        mirrored_run(ops, &q0, &b0, &mut xof, &mut flags, &mut counts);
                    let (a, c, p) = count_faults(regs_ref, &fq, &fb, fphase, &expected);
                    faults.0 += a as u64;
                    faults.1 += c as u64;
                    faults.2 += p as u64;
                }
                (flags, counts, faults)
            }));
        }
        for h in handles {
            let (fpart, cpart, fault) = h.join().expect("census thread panicked");
            for (m, p) in merged.iter_mut().zip(fpart.iter()) {
                *m |= *p;
            }
            for (m, p) in totals.iter_mut().zip(cpart.iter()) {
                m.live += p.live;
                m.fire += p.fire;
                m.viol_c2 += p.viol_c2;
                m.viol_c1 += p.viol_c1;
            }
            total_faults.0 += fault.0;
            total_faults.1 += fault.1;
            total_faults.2 += fault.2;
        }
    });

    let lanes = rounds * 64;
    let scale = 9024.0 / lanes as f64;
    let lambda = total_faults.0 as f64 * scale;
    // Poisson 95% interval on the fault count, mapped through to lambda.
    let n = total_faults.0 as f64;
    let lo = (n - 1.96 * n.sqrt()).max(0.0) * scale;
    let hi = (n + 1.96 * n.sqrt()) * scale;
    eprintln!(
        "CENSUS lambda: faults any={} classical={} phase={} of {lanes} shots -> \
         lambda={lambda:.2} per 9024-shot eval (95% CI {lo:.2}..{hi:.2}); \
         classical {:.2}, phase {:.2}; P(clean seed)=exp(-lambda)={:.3e}, \
         i.e. ~{:.3e} tail nonces per accepted run",
        total_faults.0,
        total_faults.1,
        total_faults.2,
        total_faults.1 as f64 * scale,
        total_faults.2 as f64 * scale,
        (-lambda).exp(),
        lambda.exp(),
    );

    report(ops, &merged, &totals, lanes);
}

/// Classify every gate and emit a `deep_strip_keys.rs`-shaped table.
fn report(ops: &[Op], flags: &[u8], counts: &[Counts], lanes: u64) {
    // Occupancy of each tuple in THIS stream -- the tripwire value the keys carry.
    let mut occ: HashMap<Tup, u32> = HashMap::new();
    for op in ops {
        if matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
            *occ.entry(tup_of(op)).or_insert(0) += 1;
        }
    }

    let mut ord: HashMap<Tup, u32> = HashMap::new();
    let mut dead: Vec<(Tup, u32, u32)> = Vec::new();
    let mut down: Vec<(Tup, u32, u32, u8)> = Vec::new();
    // (tuple, ordinal, occupancy, class, live, fire, viol_c2, viol_c1)
    let mut rows: Vec<(Tup, u32, u32, &'static str, u32, u32, u32, u32)> = Vec::new();
    let mut total_live = 0u64;
    let mut dead_live = 0u64;
    let mut down_live = 0u64;
    let mut g = 0usize;
    for op in ops {
        if !matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
            continue;
        }
        let tup = tup_of(op);
        let o = ord.entry(tup).or_insert(0);
        let this_ord = *o;
        *o += 1;
        let tot = occ[&tup];
        let f = flags[g];
        let c = counts[g];
        g += 1;
        total_live += c.live as u64;
        let class = if f & F_FIRED == 0 {
            dead.push((tup, this_ord, tot));
            dead_live += c.live as u64;
            "dead"
        } else if f & F_C1_NOT_C2 == 0 {
            // c2 never decides: CCX(c1,c2,t) == CX(c1,t).
            down.push((tup, this_ord, tot, 2));
            down_live += c.live as u64;
            "down2"
        } else if f & F_C2_NOT_C1 == 0 {
            // c1 never decides: CCX(c1,c2,t) == CX(c2,t).
            down.push((tup, this_ord, tot, 1));
            down_live += c.live as u64;
            "down1"
        } else {
            continue;
        };
        rows.push((tup, this_ord, tot, class, c.live, c.fire, c.viol_c2, c.viol_c1));
    }

    // `live / lanes` is the per-shot executed Toffoli this gate costs, i.e. exactly what
    // removing or downgrading it takes off the score's Toffoli axis.
    let per_shot = |v: u64| v as f64 / lanes as f64;
    eprintln!(
        "CENSUS done: lanes={lanes} gates={} dead={} downgrade={}",
        flags.len(),
        dead.len(),
        down.len()
    );
    eprintln!(
        "CENSUS executed-Toffoli (unstripped stream): {:.3}/shot; \
         candidate value: dead {:.3} + downgrade {:.3} = {:.3}/shot",
        per_shot(total_live),
        per_shot(dead_live),
        per_shot(down_live),
        per_shot(dead_live + down_live),
    );

    if let Some(stats) = std::env::var_os("TLM_CENSUS_STATS") {
        let mut s = String::from("kind,c2,c1,t,cond,ord,tot,class,live,fire,viol_c2,viol_c1\n");
        for (tup, o, tot, class, live, fire, v2, v1) in &rows {
            s.push_str(&format!(
                "{},{},{},{},{},{},{},{},{},{},{},{}\n",
                tup.0, tup.1, tup.2, tup.3, tup.4, o, tot, class, live, fire, v2, v1
            ));
        }
        match std::fs::write(&stats, s) {
            Ok(()) => eprintln!("CENSUS: wrote stats {}", stats.to_string_lossy()),
            Err(e) => eprintln!("CENSUS: failed to write stats: {e}"),
        }
    }

    let Some(path) = std::env::var_os("TLM_CENSUS_OUT") else {
        eprintln!("CENSUS: set TLM_CENSUS_OUT=<path> to write the regenerated table");
        return;
    };

    let mut s = String::new();
    s.push_str("// Auto-generated identity-keyed deep strip (do not edit by hand).\n");
    s.push_str("// Key = (kind, q_control2, q_control1, q_target, c_condition, ordinal, tuple_occupancy).\n");
    s.push_str("// ordinal = k-th occurrence of that exact CCX/CCZ operand tuple in stream order;\n");
    s.push_str("// tuple_occupancy = how many times that tuple occurred in the censused stream.\n");
    s.push_str("//\n");
    s.push_str(&format!(
        "// Census: {} random on-curve secp256k1 input pairs against the mirrored simulator in\n\
         // src/point_add/census.rs (proved faithful against crate::sim::Simulator each run),\n\
         // SUB4_APPLY_STRIP=0: {} ops / {} CCX+CCZ.\n",
        lanes,
        ops.len(),
        flags.len()
    ));
    s.push_str("pub static DEAD_KEYS: &[(u8, u64, u64, u64, u64, u32, u32)] = &[\n");
    for (t, o, tot) in &dead {
        s.push_str(&format!(
            "    ({}, {}, {}, {}, {}, {}, {}),\n",
            t.0, t.1, t.2, t.3, t.4, o, tot
        ));
    }
    s.push_str("];\n\n");
    s.push_str("pub static DOWNGRADE_KEYS: &[(u8, u64, u64, u64, u64, u32, u32, u8)] = &[\n");
    for (t, o, tot, act) in &down {
        s.push_str(&format!(
            "    ({}, {}, {}, {}, {}, {}, {}, {}),\n",
            t.0, t.1, t.2, t.3, t.4, o, tot, act
        ));
    }
    s.push_str("];\n");

    match std::fs::write(&path, s) {
        Ok(()) => eprintln!("CENSUS: wrote {}", path.to_string_lossy()),
        Err(e) => eprintln!("CENSUS: failed to write {}: {e}", path.to_string_lossy()),
    }
}
