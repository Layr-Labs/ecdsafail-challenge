//! Bounded native tests; no full point-addition emission or benchmark inputs.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op, OperationType, QubitId, NO_BIT};
use crate::sim::{SimStats, Simulator};
use alloy_primitives::U256;
use sha3::digest::XofReader;

#[path = "checkpoint4_reference.rs"]
mod original4;

struct Env(Vec<(&'static str, Option<String>)>);
impl Env {
    fn configure() -> Self {
        let pairs = [
            ("HYBRID_QCAP", "1120"),
            ("HYBRID_MARGIN_SUPPORT", ""),
            ("MIDQ_NARROW_COEFFICIENTS", "1"),
            ("MIDQ_MEASURE_COMPARE", "1"),
            ("MIDQ_DIRTY_CONST", "1"),
            ("MIDQ_COMPACT_CONST_CARRY", "1"),
            ("MIDQ_CELL_FOLDS", "1"),
            ("MIDQ_CELL_SUM", "1"),
            ("MIDQ_CELL_RECURSIVE_CARRY", "1"),
            ("MIDQ_CELL_COST_SELECT", "1"),
            ("MIDQ_ROTATED_HALVES", "1"),
            ("MIDQ_DIRTY_CHECKPOINT_LOOKUP", "1"),
            ("MIDQ_INPLACE_CHECKPOINT_SIGN", "1"),
            ("MIDQ_INPLACE_ENDPOINT_SIGNS", "1"),
            ("MIDQ_SIX_BIT_CHECKPOINT", "1"),
            ("MIDQ_CHECKPOINT_CAP_AWARE", "1"),
            ("MIDQ_CELL_QCAP", "1120"),
            ("MIDQ_CHECKPOINT_QCAP", "1120"),
            ("MIDQ_CONTROLLED_ADD_QCAP", "1120"),
            ("MIDQ_CHUNK_COMPARE_QCAP", "1120"),
            ("MIDQ_ZERO_SCRATCH_QCAP", "1120"),
        ];
        let old = pairs
            .iter()
            .map(|&(name, _)| (name, std::env::var(name).ok()))
            .collect();
        for (name, value) in pairs {
            std::env::set_var(name, value);
        }
        Self(old)
    }
}
impl Drop for Env {
    fn drop(&mut self) {
        for (name, value) in &self.0 {
            if let Some(value) = value {
                std::env::set_var(name, value);
            } else {
                std::env::remove_var(name);
            }
        }
    }
}

struct Outcomes {
    mode: u8,
    state: u64,
    reads: u64,
}
impl Outcomes {
    fn new(mode: u8) -> Self {
        Self {
            mode,
            state: 0x6539_a5c3_9e07_f1b9,
            reads: 0,
        }
    }
}
impl XofReader for Outcomes {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        self.reads += 1;
        let value = match self.mode {
            0 => 0,
            1 => u64::MAX,
            2 => {
                self.state ^= self.state << 13;
                self.state ^= self.state >> 7;
                self.state ^= self.state << 17;
                self.state
            }
            _ => 0xa55a_c33c_6996_0ff0u64.rotate_left((self.reads % 64) as u32),
        };
        out.copy_from_slice(&value.to_le_bytes());
    }
}

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}
fn put(sim: &mut Simulator<'_, Outcomes>, reg: &[QubitId], lane: usize, value: U256) {
    for (i, &q) in reg.iter().enumerate() {
        if i < 256 && value.bit(i) {
            *sim.qubit_mut(q) |= 1u64 << lane;
        }
    }
}
fn get(sim: &Simulator<'_, Outcomes>, reg: &[QubitId], lane: usize) -> U256 {
    reg.iter().enumerate().fold(U256::ZERO, |v, (i, &q)| {
        if i < 256 && sim.qubit(q) >> lane & 1 != 0 {
            v | (U256::from(1) << i)
        } else {
            v
        }
    })
}

// Preserve the literal native simulator. An extra private observer bit holds
// the effective condition for each operation; original condition-stack
// boundaries are handled explicitly because apply_iter otherwise resets them.
fn apply_checked(sim: &mut Simulator<'_, Outcomes>, ops: &[Op], observer: BitId) -> usize {
    let mut condition = u64::MAX;
    let mut stack = Vec::new();
    let mut resets = 0;
    for (i, op) in ops.iter().enumerate() {
        match op.kind {
            OperationType::PushCondition => {
                stack.push(condition);
                condition &= sim.bit(op.c_condition);
                continue;
            }
            OperationType::PopCondition => {
                condition = stack.pop().expect("unbalanced condition");
                continue;
            }
            OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {
                sim.apply_iter(std::iter::once(op));
                continue;
            }
            _ => {}
        }
        let mask = condition
            & if op.c_condition == NO_BIT {
                u64::MAX
            } else {
                sim.bit(op.c_condition)
            };
        if op.kind == OperationType::R {
            assert_eq!(
                sim.qubit(op.q_target) & mask,
                0,
                "dirty pre-reset at local op{i} q{}",
                op.q_target.0
            );
            resets += 1;
        }
        let mut gated = *op;
        *sim.bit_mut(observer) = mask;
        gated.c_condition = observer;
        sim.apply_iter(std::iter::once(&gated));
    }
    assert!(stack.is_empty(), "component boundary inside condition");
    resets
}

#[cfg_attr(test, test)]
fn checkpoint14_geometry_gate() {
    let mut w = [4u8; 25];
    assert!(extension_gate::eligible(&w, 24, 14));
    w[10] = 5; // N-14 is part of the required constant-width suffix.
    assert!(!extension_gate::eligible(&w, 24, 14));
    w[10] = 4;
    w[9] = 5; // Earlier widths may be larger; no trimming is performed.
    assert!(extension_gate::eligible(&w, 24, 14));
    assert!(!extension_gate::eligible(&w[..24], 24, 14));
    assert!(!extension_gate::eligible(&[4u8; 21], 20, 14));
    assert!(!extension_gate::eligible(&w, 24, 13));
    if ROUNDS == 4 {
        assert_eq!(
            START,
            super::super::hybrid_profile::SELECTED.checkpoint_start
        );
    }
    eprintln!("CHECKPOINT14_GEOMETRY PASS requested={} actual_rounds={} actual_start={} default_arrays_preserved=true", extension_gate::REQUESTED, ROUNDS, START);
}

fn require_extension() {
    assert_eq!(ROUNDS, 14, "build an eligible profile with HYBRID_CHECKPOINT_ROUNDS=14; zero-test/disabled runs are not validation");
}

#[cfg_attr(test, test)]
fn checkpoint14_default_ops_unchanged() {
    if ROUNDS != 4 {
        eprintln!(
            "CHECKPOINT14_DEFAULT_REFERENCE skipped: run this test in the separate default/4 build"
        );
        return;
    }
    let _env = Env::configure();
    let emit = |new: bool| {
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("a", 3);
        let b = c.alloc_qreg_bits("b", 3);
        let mut ca = c.alloc_qreg_bits("ca", 256);
        let mut cb = c.alloc_qreg_bits("cb", 256);
        if new {
            encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, false);
            encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, true);
        } else {
            original4::encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, false);
            original4::encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, true);
        }
        c.b.ops
    };
    let old = emit(false);
    let new = emit(true);
    assert!(!old.is_empty());
    assert_eq!(old, new, "default four-round operation bytes changed");
    eprintln!(
        "CHECKPOINT14_DEFAULT_OPS PASS literal_forward_inverse_ops={} byte_identical=true",
        old.len()
    );
}

#[cfg_attr(test, test)]
fn checkpoint14_full_lookup_and_cache_native() {
    require_extension();
    let _env = Env::configure();
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("a", 3);
    let b = c.alloc_qreg_bits("b", 3);
    let output = c.alloc_qreg("out");
    let initial_live = c.b.active_qubits;
    with_stable_sign(&mut c, &a, &b, |c, sign| c.cx(sign, &output));
    let middle = c.b.ops.len();
    let cache_peak = c.b.peak_qubits;
    with_stable_sign(&mut c, &a, &b, |c, sign| c.cx(sign, &output));
    assert_eq!(c.b.active_qubits, initial_live);
    assert_eq!(cache_peak, initial_live + 1);
    let ccx = c.b.ops[..middle]
        .iter()
        .filter(|op| op.kind == OperationType::CCX)
        .count();
    assert_eq!(ccx, 62);
    let regs = [ids(&a), ids(&b), ids(std::slice::from_ref(&output))];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    assert_eq!(nq, 8);
    for mode in 0..4 {
        let mut rng = Outcomes::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for old in 0..2 {
            sim.clear_for_shot();
            for code in 0..64 {
                put(&mut sim, &regs[0], code, U256::from(code & 7));
                put(&mut sim, &regs[1], code, U256::from(code >> 3));
                put(&mut sim, &regs[2], code, U256::from(old));
            }
            apply_checked(&mut sim, &c.b.ops[..middle], BitId(nb));
            assert_eq!(sim.phase, 0);
            for code in 0..64 {
                assert_eq!(get(&sim, &regs[0], code), U256::from(code & 7));
                assert_eq!(get(&sim, &regs[1], code), U256::from(code >> 3));
                assert_eq!(
                    get(&sim, &regs[2], code),
                    U256::from(
                        old ^ trajectory(code)
                            .0
                            .get(4)
                            .copied()
                            .expect("checkpoint14 cache test requires a fifth sign")
                            as usize
                    )
                );
            }
            apply_checked(&mut sim, &c.b.ops[middle..], BitId(nb));
            assert_eq!(sim.phase, 0);
            for code in 0..64 {
                assert_eq!(get(&sim, &regs[2], code), U256::from(old));
            }
            for q in 0..nq as usize {
                if !regs.iter().any(|r| r.contains(&QubitId(q as u64))) {
                    assert_eq!(sim.qubits[q], 0);
                }
            }
        }
    }
    // Existing lookup test now covers all14 decision bits and eight endpoint
    // bits for every wrapping input, plus exact lookup phase/roundtrip.
    super::tests::checkpoint_lookup_exhaustive_values_signs_and_phase();
    super::tests::checkpoint_endpoint_sign_in_place();
    super::tests::checkpoint_value_model_matches_emitted_overflow_behavior();
    eprintln!("CHECKPOINT14_LOOKUP_NATIVE PASS cache_cases=512 all64_wrapping_inputs=true all14_signs=true endpoint_phase=true dirty_donors_restored=true cache_extraQ=1 lookup_cleanQ=0 compute_clear_CCX=62");
}

#[derive(Clone, Copy, Debug)]
enum Kind {
    Raw14,
    Original10Plus4,
    Cached14,
}

struct Component {
    ops: Vec<Op>,
    middle: usize,
    initial: [Vec<QubitId>; 4],
    terminal: [Vec<QubitId>; 4],
    final_regs: [Vec<QubitId>; 4],
    tape: Vec<QubitId>,
    world: Vec<QubitId>,
    allocator_peak: u64,
    entry_live: u64,
    middle_live: u64,
    exit_live: u64,
}

fn ordinary(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &[QReg],
    cb: &[QReg],
    tape: &mut Vec<QReg>,
    first: usize,
    last: usize,
    inverse: bool,
) {
    use super::super::midq_odd_values;
    for index in 0..last - first {
        let round = if inverse {
            last - 1 - index
        } else {
            first + index
        };
        if inverse {
            let sign = tape.pop().unwrap();
            if round % 2 == 0 {
                midq_mod_signed_add_halve(c, cb, ca, &sign, true);
                midq_odd_values::backward(c, a, b, sign, 4, 0);
            } else {
                midq_mod_signed_add_halve(c, ca, cb, &sign, true);
                midq_odd_values::backward(c, b, a, sign, 4, 0);
            }
        } else {
            let sign = c.alloc_qreg("reference.sign");
            if round % 2 == 0 {
                midq_odd_values::forward(c, a, b, &sign, 4, 0);
                midq_mod_signed_add_halve(c, cb, ca, &sign, false);
            } else {
                midq_odd_values::forward(c, b, a, &sign, 4, 0);
                midq_mod_signed_add_halve(c, ca, cb, &sign, false);
            }
            tape.push(sign);
        }
    }
}

fn component(kind: Kind, world_count: usize) -> Component {
    require_extension();
    let mut c = Circuit::new();
    let world = c.alloc_qreg_bits("world.spectator", world_count);
    let mut a = c.alloc_qreg_bits("checkpoint.a", 3);
    let mut b = c.alloc_qreg_bits("checkpoint.b", 3);
    let mut ca = c.alloc_qreg_bits("ca", 256);
    let mut cb = c.alloc_qreg_bits("cb", 256);
    let mut tape = Vec::new();
    let initial = [ids(&a), ids(&b), ids(&ca), ids(&cb)];
    let entry_live = c.b.active_qubits as u64;
    match kind {
        Kind::Raw14 => ordinary(
            &mut c,
            &mut a,
            &mut b,
            &ca,
            &cb,
            &mut tape,
            START,
            MIDQ_TAIL_ROUNDS,
            false,
        ),
        Kind::Original10Plus4 => {
            ordinary(
                &mut c,
                &mut a,
                &mut b,
                &ca,
                &cb,
                &mut tape,
                START,
                START + 10,
                false,
            );
            original4::encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, false);
        }
        Kind::Cached14 => encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, false),
    }
    c.flush_pending_frees();
    let middle = c.b.ops.len();
    let middle_live = c.b.active_qubits as u64;
    let terminal = [ids(&a), ids(&b), ids(&ca), ids(&cb)];
    let tape_ids = ids(&tape);
    match kind {
        Kind::Raw14 => ordinary(
            &mut c,
            &mut a,
            &mut b,
            &ca,
            &cb,
            &mut tape,
            START,
            MIDQ_TAIL_ROUNDS,
            true,
        ),
        Kind::Original10Plus4 => {
            original4::encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, true);
            ordinary(
                &mut c,
                &mut a,
                &mut b,
                &ca,
                &cb,
                &mut tape,
                START,
                START + 10,
                true,
            );
        }
        Kind::Cached14 => encoded_rounds(&mut c, &a, &b, &mut ca, &mut cb, true),
    }
    c.flush_pending_frees();
    let exit_live = c.b.active_qubits as u64;
    Component {
        middle,
        initial,
        terminal,
        final_regs: [ids(&a), ids(&b), ids(&ca), ids(&cb)],
        tape: tape_ids,
        world: ids(&world),
        allocator_peak: c.b.peak_qubits as u64,
        entry_live,
        middle_live,
        exit_live,
        ops: c.b.ops,
    }
}

fn value_after(code: usize, steps: usize) -> [usize; 2] {
    let mut pair = [
        signed(((code & 7) * 2 + 1) as i16, 4),
        signed(((code >> 3) * 2 + 1) as i16, 4),
    ];
    for k in 0..steps {
        let sign = ((pair[0] ^ pair[1]) >> 1) & 1;
        let target = if (START + k) % 2 == 0 { 1 } else { 0 };
        pair[target] = signed(
            pair[target]
                + if sign == 0 {
                    pair[1 - target]
                } else {
                    -pair[1 - target]
                },
            4,
        ) / 2;
    }
    [(pair[0] as usize & 15) >> 1, (pair[1] as usize & 15) >> 1]
}
fn p() -> U256 {
    U256::MAX - U256::from(0x1000003d0u64)
}
fn add(a: U256, b: U256) -> U256 {
    if a >= p() - b {
        a - (p() - b)
    } else {
        a + b
    }
}
fn sub(a: U256, b: U256) -> U256 {
    if a >= b {
        a - b
    } else {
        p() - (b - a)
    }
}
fn expected_coefficients(mut coeff: [U256; 2], code: usize, inverse: bool) -> [U256; 2] {
    let signs = trajectory(code).0;
    for index in 0..ROUNDS {
        let k = if inverse { ROUNDS - 1 - index } else { index };
        let target = if (START + k) % 2 == 0 { 1 } else { 0 };
        let source = coeff[1 - target];
        coeff[target] = if inverse {
            let doubled = add(coeff[target], coeff[target]);
            if signs[k] == 0 {
                sub(doubled, source)
            } else {
                add(doubled, source)
            }
        } else {
            let sum = if signs[k] == 0 {
                add(coeff[target], source)
            } else {
                sub(coeff[target], source)
            };
            if sum.bit(0) {
                (sum >> 1) + (p() >> 1) + U256::from(1)
            } else {
                sum >> 1
            }
        };
    }
    coeff
}
fn fixture(code: usize, batch: usize) -> [U256; 2] {
    let u = U256::from((code + 1 + batch * 73) as u64);
    [(u << 192) + (u << 65) + u, p() - (u << 128) - u]
}
fn initialize(
    sim: &mut Simulator<'_, Outcomes>,
    case: &Component,
    kind: Kind,
    batch: usize,
    inverse: bool,
) {
    sim.clear_for_shot();
    sim.stats = SimStats::default();
    let regs = if inverse {
        &case.terminal
    } else {
        &case.initial
    };
    for code in 0..64 {
        let pair = if !inverse {
            [code & 7, code >> 3]
        } else {
            match kind {
                Kind::Raw14 => value_after(code, 14),
                Kind::Original10Plus4 => value_after(code, 10),
                Kind::Cached14 => [code & 7, code >> 3],
            }
        };
        for j in 0..2 {
            put(sim, &regs[j], code, U256::from(pair[j]));
        }
        let coeff = fixture(code, batch);
        for j in 0..2 {
            put(sim, &regs[j + 2], code, coeff[j]);
        }
        if inverse {
            let signs = trajectory(code).0;
            let bits = signs[..case.tape.len()]
                .iter()
                .enumerate()
                .fold(0usize, |v, (k, &b)| v | ((b as usize) << k));
            put(sim, &case.tape, code, U256::from(bits));
        }
    }
    for (i, &q) in case.world.iter().enumerate() {
        *sim.qubit_mut(q) = 0xa55a_6996_c33c_0ff0u64.rotate_left((i % 64) as u32);
    }
}
fn check_clean(sim: &Simulator<'_, Outcomes>, live: &[&[QubitId]]) {
    for (q, &value) in sim.qubits.iter().enumerate() {
        if !live.iter().any(|r| r.contains(&QubitId(q as u64))) {
            assert_eq!(value, 0, "dirty scratch q{q}");
        }
    }
}

fn run_components(world_count: usize, batches: usize, modes: std::ops::Range<u8>) -> usize {
    let mut checks = 0;
    for kind in [Kind::Raw14, Kind::Original10Plus4, Kind::Cached14] {
        let case = component(kind, world_count);
        let (nq, nb, _, _) = analyze_ops(case.ops.iter());
        assert_eq!(case.entry_live, world_count as u64 + 518);
        assert_eq!(case.exit_live, case.entry_live);
        let retained = match kind {
            Kind::Raw14 => 14,
            Kind::Original10Plus4 => 10,
            Kind::Cached14 => 0,
        };
        assert_eq!(case.middle_live, case.entry_live + retained);
        let raw_forward = case.ops[..case.middle]
            .iter()
            .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
            .count();
        let raw_inverse = case.ops[case.middle..]
            .iter()
            .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
            .count();
        let mut measured = Vec::new();
        let mut reset_ops = 0;
        for mode in modes.clone() {
            let mut rng = Outcomes::new(mode);
            let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
            for batch in 0..batches {
                initialize(&mut sim, &case, kind, batch, false);
                reset_ops += apply_checked(&mut sim, &case.ops[..case.middle], BitId(nb));
                assert_eq!(
                    sim.phase, 0,
                    "forward phase {kind:?} mode{mode} batch{batch}"
                );
                for code in 0..64 {
                    let wanted = expected_coefficients(fixture(code, batch), code, false);
                    for j in 0..2 {
                        assert_eq!(
                            get(&sim, &case.terminal[j + 2], code),
                            wanted[j],
                            "forward coefficient {kind:?} lane{code}"
                        );
                    }
                    let values = match kind {
                        Kind::Raw14 => value_after(code, 14),
                        Kind::Original10Plus4 => value_after(code, 10),
                        Kind::Cached14 => [code & 7, code >> 3],
                    };
                    for j in 0..2 {
                        assert_eq!(
                            get(&sim, &case.terminal[j], code),
                            U256::from(values[j]),
                            "midpoint value code {kind:?} lane{code}"
                        );
                    }
                    let expected_tape = trajectory(code).0[..case.tape.len()]
                        .iter()
                        .enumerate()
                        .fold(0usize, |v, (j, &s)| v | ((s as usize) << j));
                    assert_eq!(
                        get(&sim, &case.tape, code),
                        U256::from(expected_tape),
                        "midpoint tape {kind:?} lane{code}"
                    );
                }
                check_clean(
                    &sim,
                    &[
                        &case.terminal[0],
                        &case.terminal[1],
                        &case.terminal[2],
                        &case.terminal[3],
                        &case.tape,
                        &case.world,
                    ],
                );
                measured.push(("forward", sim.stats.toffoli_gates as f64 / 64.0));
                reset_ops += apply_checked(&mut sim, &case.ops[case.middle..], BitId(nb));
                assert_eq!(sim.phase, 0, "roundtrip phase {kind:?}");
                for code in 0..64 {
                    for j in 0..2 {
                        assert_eq!(
                            get(&sim, &case.final_regs[j + 2], code),
                            fixture(code, batch)[j]
                        );
                    }
                    assert_eq!(get(&sim, &case.final_regs[0], code), U256::from(code & 7));
                    assert_eq!(get(&sim, &case.final_regs[1], code), U256::from(code >> 3));
                }
                check_clean(
                    &sim,
                    &[
                        &case.final_regs[0],
                        &case.final_regs[1],
                        &case.final_regs[2],
                        &case.final_regs[3],
                        &case.world,
                    ],
                );
                initialize(&mut sim, &case, kind, batch, true);
                reset_ops += apply_checked(&mut sim, &case.ops[case.middle..], BitId(nb));
                assert_eq!(sim.phase, 0, "standalone inverse phase {kind:?} mode{mode}");
                for code in 0..64 {
                    let wanted = expected_coefficients(fixture(code, batch), code, true);
                    for j in 0..2 {
                        assert_eq!(
                            get(&sim, &case.final_regs[j + 2], code),
                            wanted[j],
                            "inverse coefficient {kind:?} lane{code}"
                        );
                    }
                    assert_eq!(get(&sim, &case.final_regs[0], code), U256::from(code & 7));
                    assert_eq!(get(&sim, &case.final_regs[1], code), U256::from(code >> 3));
                }
                check_clean(
                    &sim,
                    &[
                        &case.final_regs[0],
                        &case.final_regs[1],
                        &case.final_regs[2],
                        &case.final_regs[3],
                        &case.world,
                    ],
                );
                for (i, &q) in case.world.iter().enumerate() {
                    assert_eq!(
                        sim.qubit(q),
                        0xa55a_6996_c33c_0ff0u64.rotate_left((i % 64) as u32)
                    );
                }
                measured.push(("inverse", sim.stats.toffoli_gates as f64 / 64.0));
                checks += 64;
            }
        }
        let mean = |label| {
            let xs: Vec<_> = measured
                .iter()
                .filter_map(|&(k, v)| (k == label).then_some(v))
                .collect();
            xs.iter().sum::<f64>() / xs.len() as f64
        };
        eprintln!("CHECKPOINT14_COMPONENT kind={kind:?} world={world_count} input_coeff_bits=512 checkpoint_input_bits=6 entry_live={} midpoint_live={} exit_live={} allocator_peak={} analyzed_Q={nq} raw_forward_T={raw_forward} raw_inverse_T={raw_inverse} executed_forward_T={} executed_inverse_T={} checked_clean_R_ops={reset_ops} padding_loans_in_reference=false original_arrays_preserved=true",
            case.entry_live,case.middle_live,case.exit_live,case.allocator_peak,mean("forward"),mean("inverse"));
    }
    checks
}

#[cfg_attr(test, test)]
fn checkpoint14_coefficients_native_all64() {
    require_extension();
    let _env = Env::configure();
    let checked = run_components(0, 8, 0..4);
    assert_eq!(checked, 6144);
    eprintln!("CHECKPOINT14_COEFFICIENT_NATIVE PASS cases={checked} all64_wrapping_states=true full_width_fixtures=8 paths=raw14,original10plus4,cached14 forward=true standalone_inverse=true roundtrip=true phase=true every_R_prechecked=true");
}

#[cfg_attr(test, test)]
fn checkpoint14_scoped_resource_profile() {
    require_extension();
    let _env = Env::configure();
    let metadata = 12usize;
    let world = 256 + START + metadata;
    assert!(world + 518 + 2 <= 1120,
        "checkpoint14 release resource fixture does not fit1120; use the designated cut340/14 diagnostic build, not a zero-case pass");
    let checked = run_components(world, 1, 2..3);
    assert_eq!(checked, 192);
    eprintln!("CHECKPOINT14_RESOURCE_NATIVE PASS cases={checked} world=field256+prefix_tape{START}+assumed_metadata{metadata}; local_window_only=true earlier_tail_peak_not_included=true");
}

pub(super) fn run() {
    checkpoint14_geometry_gate();
    if ROUNDS == 4 {
        checkpoint14_default_ops_unchanged();
        eprintln!("CHECKPOINT14_RELEASE_NATIVE PASS mode=default4 default_identity=true native_harness=release_hook no_cfg_test=true");
        return;
    }
    require_extension();
    checkpoint14_full_lookup_and_cache_native();
    checkpoint14_coefficients_native_all64();
    checkpoint14_scoped_resource_profile();
    eprintln!("CHECKPOINT14_RELEASE_NATIVE PASS mode=extension14 cache_cases=512 coefficient_cases=6144 resource_cases=192 native_harness=release_hook no_cfg_test=true");
}
