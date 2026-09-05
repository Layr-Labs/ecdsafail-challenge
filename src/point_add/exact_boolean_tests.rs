//! Local diagnostics only. Both a prefix checker and the unchanged Simulator
//! consume the actual original/replacement operations, including all phases.
use super::*;
use crate::circuit::{QubitId, RegisterId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

fn gate(kind: K, qs: &[u64]) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    if !qs.is_empty() {
        op.q_target = QubitId(qs[0]);
    }
    if qs.len() > 1 {
        op.q_control1 = QubitId(qs[1]);
    }
    if qs.len() > 2 {
        op.q_control2 = QubitId(qs[2]);
    }
    op
}

fn conditioned(mut op: Op, bit: u64) -> Op {
    op.c_condition = BitId(bit);
    op
}

fn bit_gate(kind: K, bit: u64) -> Op {
    let mut op = gate(kind, &[]);
    op.c_target = BitId(bit);
    op
}

fn hmr(q: u64, bit: u64) -> Op {
    let mut op = gate(K::Hmr, &[q]);
    op.c_target = BitId(bit);
    op
}

fn inputs(dirty: bool) -> Vec<Op> {
    let mut ops = Vec::new();
    for q in 0..6 {
        if q == 5 || (q == 2 && !dirty) {
            continue;
        }
        let mut op = gate(K::AppendToRegister, &[q]);
        op.r_target = RegisterId(0);
        ops.push(op);
    }
    for b in 0..2 {
        let mut op = bit_gate(K::AppendToRegister, b);
        op.r_target = RegisterId(1);
        ops.push(op);
    }
    ops
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    q: Vec<u64>,
    b: Vec<u64>,
    phase: u64,
    stack: Vec<u64>,
    cond: u64,
}

impl State {
    fn apply(&mut self, op: &Op, measurement: u64) {
        let mask = self.cond
            & if op.c_condition == NO_BIT {
                u64::MAX
            } else {
                self.b[op.c_condition.0 as usize]
            };
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let b = op.q_control2.0 as usize;
        match op.kind {
            K::X => self.q[t] ^= mask,
            K::CX => self.q[t] ^= mask & self.q[a],
            K::CCX => self.q[t] ^= mask & self.q[a] & self.q[b],
            K::Swap => {
                let delta = mask & (self.q[t] ^ self.q[a]);
                self.q[t] ^= delta;
                self.q[a] ^= delta;
            }
            K::Z => self.phase ^= mask & self.q[t],
            K::CZ => self.phase ^= mask & self.q[t] & self.q[a],
            K::CCZ => self.phase ^= mask & self.q[t] & self.q[a] & self.q[b],
            K::Neg => self.phase ^= mask,
            K::R | K::Hmr => {
                self.phase ^= mask & measurement & self.q[t];
                self.q[t] &= !mask;
                if op.kind == K::Hmr {
                    let bit = &mut self.b[op.c_target.0 as usize];
                    *bit = (*bit & !mask) | (measurement & mask);
                }
            }
            K::BitStore0 => self.b[op.c_target.0 as usize] &= !mask,
            K::BitStore1 => self.b[op.c_target.0 as usize] |= mask,
            K::BitInvert => self.b[op.c_target.0 as usize] ^= mask,
            K::PushCondition => {
                self.stack.push(self.cond);
                self.cond = mask;
            }
            K::PopCondition => self.cond = self.stack.pop().unwrap(),
            K::Register | K::AppendToRegister | K::DebugPrint => {}
        }
    }
}

struct Tape<'a> {
    words: &'a [u64],
    cursor: usize,
}
impl XofReader for Tape<'_> {
    fn read(&mut self, bytes: &mut [u8]) {
        assert_eq!(bytes.len(), 8);
        bytes.copy_from_slice(&self.words[self.cursor].to_le_bytes());
        self.cursor += 1;
    }
}

fn random_word(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn reference(ops: &[Op], initial: &State, words: &[u64]) -> State {
    let mut tape = Tape { words, cursor: 0 };
    let mut sim = Simulator::new(initial.q.len(), initial.b.len(), &mut tape);
    sim.qubits.clone_from(&initial.q);
    sim.bits.clone_from(&initial.b);
    sim.phase = initial.phase;
    sim.apply_iter(ops.iter());
    let result = State {
        q: sim.qubits,
        b: sim.bits,
        phase: sim.phase,
        stack: Vec::new(),
        cond: u64::MAX,
    };
    assert_eq!(tape.cursor, words.len());
    result
}

fn check(body: &[Op], dirty: bool, expected_ands: Option<usize>) -> usize {
    let mut cases = 0;
    for aliases in [false, true] {
        for late_metadata in [false, true] {
            cases += check_mode(body, dirty, expected_ands, aliases, late_metadata);
        }
    }
    cases
}

fn check_mode(
    body: &[Op],
    dirty: bool,
    expected_ands: Option<usize>,
    aliases: bool,
    late_metadata: bool,
) -> usize {
    let mut source = if late_metadata {
        Vec::new()
    } else {
        inputs(dirty)
    };
    source.extend_from_slice(body);
    if late_metadata {
        source.extend(inputs(dirty));
    }
    let mut segments = Vec::new();
    let (output, stats) = transform(source.clone(), aliases, |_, replacement| {
        segments.push(replacement.len());
    });
    if let Some(expected) = expected_ands {
        assert_eq!(stats.measured_ands, expected, "{source:?}");
    }
    for op in &output {
        op.validate();
    }
    let (_, nb, _, _) = analyze_ops(output.iter());
    let mut nq_inputs = vec![0, 1, 3, 4];
    if dirty {
        nq_inputs.push(2);
    }
    let cases = 1usize << (nq_inputs.len() + 2);
    let mut checked = 0;
    for base in (0..cases).step_by(64) {
        let mut initial = State {
            q: vec![0; 6],
            b: vec![0; nb as usize],
            phase: 0xa55a_c33c_9669_f00f,
            stack: Vec::new(),
            cond: u64::MAX,
        };
        for lane in 0..64 {
            let bits = base + lane;
            for (j, &q) in nq_inputs.iter().enumerate() {
                initial.q[q] |= (((bits >> j) & 1) as u64) << lane;
            }
            for b in 0..2 {
                initial.b[b] |= (((bits >> (nq_inputs.len() + b)) & 1) as u64) << lane;
            }
        }
        // Enumerate independent zero/one assignments for old and inserted
        // measurements, then deterministic random masks for all 64 basis lanes.
        for mode in 0..5 {
            let mut old = initial.clone();
            let mut new = initial.clone();
            let mut old_tape = Vec::new();
            let mut new_tape = Vec::new();
            let mut seed = 0x932c_781f_508d_a46bu64;
            let mut cursor = 0;
            for (index, op) in source.iter().enumerate() {
                let end = cursor + segments[index];
                let replaced = &output[cursor..end];
                let old_m = if mode == 4 {
                    random_word(&mut seed)
                } else if mode & 1 == 0 {
                    0
                } else {
                    u64::MAX
                };
                let added_m = if mode == 4 {
                    random_word(&mut seed)
                } else if mode & 2 == 0 {
                    0
                } else {
                    u64::MAX
                };
                // Equality is checked BEFORE every source R/HMR as well as at
                // every other source boundary. Dirty resets cannot hide a bug.
                assert_eq!(old.q, new.q, "pre-op qubits {index}: {op:?}");
                assert_eq!(old.phase, new.phase, "pre-op phase {index}: {op:?}");
                if matches!(op.kind, K::R | K::Hmr) {
                    old_tape.push(old_m);
                }
                old.apply(op, old_m);
                for replacement in replaced {
                    let inserted = replacement.kind == K::Hmr && replacement.c_target.0 >= 2;
                    let measurement = if inserted { added_m } else { old_m };
                    if matches!(replacement.kind, K::R | K::Hmr) {
                        new_tape.push(measurement);
                    }
                    new.apply(replacement, measurement);
                }
                assert_eq!(old.q, new.q, "post-op qubits {index}: {op:?}; {body:?}");
                assert_eq!(
                    old.phase, new.phase,
                    "post-op phase {index}: {op:?}; {body:?}"
                );
                assert_eq!(old.b[..2], new.b[..2], "classical output");
                assert_eq!(old.stack, new.stack);
                assert_eq!(old.cond, new.cond);
                cursor = end;
            }
            assert_eq!(old, reference(&source, &initial, &old_tape));
            assert_eq!(new, reference(&output, &initial, &new_tape));
            checked += 64;
        }
    }
    checked
}

pub(super) fn selftest() {
    let compute = gate(K::CCX, &[2, 0, 1]);
    let witness = gate(K::CX, &[3, 2]);
    let mut cases = 0;
    cases += check(&[compute, witness, compute], false, Some(1));
    cases += check(&[compute, witness, compute], true, Some(0));
    for mutation in [
        gate(K::X, &[0]),
        gate(K::X, &[1]),
        gate(K::X, &[2]),
        gate(K::CX, &[0, 4]),
        gate(K::CCX, &[1, 3, 4]),
        gate(K::Swap, &[0, 4]),
        gate(K::Swap, &[4, 1]),
    ] {
        cases += check(
            &[compute, mutation, mutation, witness, compute],
            false,
            Some(0),
        );
    }
    // Running the new pass first would turn an adjacent CCX pair into one CCX
    // plus a measurement, blocking the existing cancellation's two-gate win.
    let mut pair = inputs(false);
    pair.extend([compute, compute]);
    let early = super::super::cancel_adjacent_toffoli(transform(pair.clone(), false, |_, _| {}).0);
    let late = transform(
        super::super::cancel_adjacent_toffoli(pair),
        false,
        |_, _| {},
    )
    .0;
    let count_t = |ops: &[Op]| {
        ops.iter()
            .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
            .count()
    };
    assert_eq!(count_t(&early), 1);
    assert_eq!(count_t(&late), 0);
    // Mutate either control, the target, or either side of SWAP, including
    // mutate-then-restore sequences: version equality is deliberately stricter
    // than functional equality. Diagonal use of any wire must preserve phases.
    let mut gates = vec![gate(K::Neg, &[]), gate(K::DebugPrint, &[])];
    for t in 0..6 {
        for kind in [K::X, K::Z, K::R] {
            gates.push(gate(kind, &[t]));
        }
        gates.push(hmr(t, 0));
        for a in 0..6 {
            if a == t {
                continue;
            }
            for kind in [K::CX, K::CZ, K::Swap] {
                gates.push(gate(kind, &[t, a]));
            }
            for b in (a + 1)..6 {
                if b == t {
                    continue;
                }
                for kind in [K::CCX, K::CCZ] {
                    gates.push(gate(kind, &[t, a, b]));
                }
            }
        }
    }
    for b in 0..2 {
        for kind in [K::BitInvert, K::BitStore0, K::BitStore1] {
            gates.push(bit_gate(kind, b));
        }
    }
    for &middle in &gates {
        cases += check(&[compute, middle, witness, compute], false, None);
        cases += check(&[compute, middle, middle, witness, compute], false, None);
        cases += check(
            &[compute, conditioned(middle, 0), witness, compute],
            false,
            Some(0),
        );
        cases += check(&[middle, compute, witness, compute], true, None);
    }
    // Constant zero/one propagation over every pair of small gates, with a
    // controlled witness left live. No final R is appended to clear scratch.
    for &a in &gates {
        for &b in &gates {
            cases += check(&[a, b, compute, witness, compute], false, None);
        }
    }
    let push0 = conditioned(gate(K::PushCondition, &[]), 0);
    let push1 = conditioned(gate(K::PushCondition, &[]), 1);
    let pop = gate(K::PopCondition, &[]);
    cases += check(
        &[
            compute,
            push0,
            push1,
            gate(K::X, &[0]),
            conditioned(gate(K::Neg, &[]), 1),
            pop,
            bit_gate(K::BitInvert, 0),
            pop,
            witness,
            compute,
        ],
        false,
        Some(0),
    );
    cases += check(&[push0, compute, witness, compute, pop], false, Some(0));
    for q in 0..6 {
        for measure in [gate(K::R, &[q]), hmr(q, 0)] {
            cases += check(&[compute, measure, witness, compute], false, Some(0));
            cases += check(
                &[gate(K::X, &[q]), measure, compute, witness, compute],
                false,
                None,
            );
            cases += check(
                &[
                    push0,
                    conditioned(measure, 1),
                    pop,
                    compute,
                    witness,
                    compute,
                ],
                true,
                Some(0),
            );
        }
    }
    // The source negative phase is observable even when AND controls are
    // constant. Test independently conditioned phase gates on the clean product.
    for phase in [
        gate(K::Neg, &[]),
        gate(K::Z, &[2]),
        gate(K::CZ, &[2, 0]),
        gate(K::CCZ, &[2, 0, 3]),
    ] {
        cases += check(&[compute, phase, witness, compute], false, Some(1));
        cases += check(
            &[compute, conditioned(phase, 0), witness, compute],
            false,
            Some(0),
        );
    }
    let two_aliases = [
        gate(K::CX, &[2, 0]),
        gate(K::CX, &[2, 1]),
        gate(K::CX, &[5, 0]),
        gate(K::CX, &[5, 1]),
    ];
    for extra in [
        Vec::new(),
        vec![gate(K::X, &[5])],
        vec![gate(K::CX, &[2, 3])],
        vec![gate(K::R, &[4])],
        vec![conditioned(gate(K::Z, &[4]), 0)],
        vec![gate(K::Swap, &[2, 4])],
    ] {
        let mut body = two_aliases.to_vec();
        body.extend(extra);
        body.push(gate(K::CCX, &[3, 2, 5]));
        cases += check(&body, false, None);
    }
    let mut alias_case = inputs(false);
    alias_case.extend(two_aliases);
    alias_case.push(gate(K::CCX, &[3, 2, 5]));
    assert_eq!(transform(alias_case, true, |_, _| {}).1.alias_toffoli, 1);
    let mut random = 0x731c_d92a_f408_6be5;
    for _ in 0..512 {
        let body: Vec<_> = (0..128)
            .map(|_| gates[random_word(&mut random) as usize % gates.len()])
            .collect();
        cases += check(&body, false, None);
        cases += check(&body, true, None);
    }
    coherent_witness();
    eprintln!("MIDQ_EXACT_BOOLEAN_SELFTEST PASS: {cases} basis/measurement cases; input declarations at beginning AND end; all source boundaries incl. pre-reset garbage; unchanged Simulator; controlled witness; phases and classical outputs; no final scratch resets");
}

fn coherent_witness() {
    let compute = gate(K::CCX, &[2, 0, 1]);
    let bodies = [
        vec![
            compute,
            gate(K::CX, &[3, 2]),
            gate(K::Z, &[2]),
            gate(K::CZ, &[2, 4]),
            compute,
        ],
        vec![
            gate(K::X, &[2]),
            gate(K::R, &[2]),
            compute,
            gate(K::CX, &[3, 2]),
            gate(K::CCZ, &[2, 0, 4]),
            compute,
        ],
        vec![
            hmr(4, 0),
            compute,
            gate(K::CX, &[3, 2]),
            gate(K::Z, &[2]),
            compute,
        ],
    ];
    let mut branches = 0;
    for body in bodies {
        let mut source = inputs(false);
        source.extend(body);
        for aliases in [false, true] {
            let (output, stats) = transform(source.clone(), aliases, |_, _| {});
            assert_eq!(stats.measured_ands, 1);
            let original_measurements = source
                .iter()
                .filter(|op| matches!(op.kind, K::R | K::Hmr))
                .count();
            let (_, nb, _, _) = analyze_ops(output.iter());
            for branch in 0..(1 << (original_measurements + stats.measured_ands)) {
                let wave = |ops: &[Op]| {
                    let mut state = State {
                        q: vec![0; 6],
                        b: vec![0; nb as usize],
                        phase: 0,
                        stack: Vec::new(),
                        cond: u64::MAX,
                    };
                    // Tabulate the linear operator on all basis states. Only
                    // amplitudes on the declared clean-ancilla subspace are used.
                    for basis in 0..64 {
                        for q in 0..6 {
                            state.q[q] |= (((basis >> q) & 1) as u64) << basis;
                        }
                    }
                    let mut old_m = 0;
                    let mut fresh_m = original_measurements;
                    let mut measurements = 0;
                    for op in ops {
                        let mut m = 0;
                        if matches!(op.kind, K::R | K::Hmr) {
                            let index = if op.kind == K::Hmr && op.c_target.0 >= 2 {
                                let index = fresh_m;
                                fresh_m += 1;
                                index
                            } else {
                                let index = old_m;
                                old_m += 1;
                                index
                            };
                            m = if branch & (1 << index) == 0 {
                                0
                            } else {
                                u64::MAX
                            };
                            measurements += 1;
                        }
                        state.apply(op, m);
                    }
                    let mut wave = [[0.0f64; 2]; 64];
                    let scale = 2.0f64.powf(-(measurements as f64) / 2.0);
                    for basis in 0usize..64 {
                        // a and witness start entangled; b and d carry complex
                        // amplitudes. No cleanup/reset of the witness is allowed.
                        if basis & ((1 << 2) | (1 << 5)) != 0 || (basis & 1) != ((basis >> 3) & 1) {
                            continue;
                        }
                        let target = (0..6).fold(0, |acc, q| {
                            acc | (((state.q[q] >> basis) & 1) as usize) << q
                        });
                        let sign = if (state.phase >> basis) & 1 == 0 {
                            1.0
                        } else {
                            -1.0
                        };
                        wave[target][0] += sign * scale * (1 + (basis & 3)) as f64;
                        wave[target][1] += sign * scale * (1 + ((basis >> 4) & 1)) as f64;
                    }
                    wave
                };
                let old = wave(&source);
                let new = wave(&output);
                // Every fresh measurement is an independent fair branch whose
                // correction leaves the original quantum instrument unchanged.
                let normalization = 2.0f64.powf(stats.measured_ands as f64 / 2.0);
                for (a, b) in old.into_iter().flatten().zip(new.into_iter().flatten()) {
                    assert!(
                        (a - b * normalization).abs() < 1e-12,
                        "entangled branch {branch}"
                    );
                }
                branches += 1;
            }
        }
    }
    eprintln!("MIDQ_EXACT_BOOLEAN_COHERENT PASS: {branches} complete measurement branches, complex entangled witness amplitudes (including global phase), explicit Kraus normalization");
}

/// One bounded 64-lane production regression. It is not an official evaluator
/// or a nonce search. All source measurements retain their own RNG tape; new,
/// exactly corrected HMR outcomes use an independent tape. This coupling is
/// necessary: using the same sequential RNG seed would shift all later draws.
pub(super) fn profile(source: Vec<Op>, aliases: bool) -> Vec<Op> {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use alloy_primitives::U256;
    let curve = WeierstrassEllipticCurve {
        modulus: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap(),
        a: U256::ZERO,
        b: U256::from(7),
        gx: U256::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap(),
        gy: U256::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap(),
        order: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .unwrap(),
    };
    let (nq, nb, _, regs) = analyze_ops(source.iter());
    assert_eq!(regs.len(), 4);
    let mut seed = 0xc4b2_ea17_f963_850du64;
    let mut initial = State {
        q: vec![0; nq as usize],
        b: vec![0; nb as usize],
        phase: 0,
        stack: Vec::new(),
        cond: u64::MAX,
    };
    let mut expected = Vec::new();
    for lane in 0..64 {
        let k1 = U256::from_limbs(std::array::from_fn(|_| random_word(&mut seed)));
        let k2 = U256::from_limbs(std::array::from_fn(|_| random_word(&mut seed)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        assert_ne!(t.0, o.0);
        expected.push(curve.add(t.0, t.1, o.0, o.1));
        for (reg, val) in regs.iter().zip([t.0, t.1, o.0, o.1]) {
            for (j, wire) in reg.iter().enumerate() {
                let word = match wire {
                    QubitOrBit::Qubit(q) => &mut initial.q[q.0 as usize],
                    QubitOrBit::Bit(b) => &mut initial.b[b.0 as usize],
                };
                *word |= (val.bit(j) as u64) << lane;
            }
        }
    }
    let mut old = initial.clone();
    let mut new = initial.clone();
    let mut old_tape = Vec::new();
    let mut new_tape = Vec::new();
    let mut old_t = 0u64;
    let mut new_t = 0u64;
    let mut index = 0usize;
    let mut dirty_resets = 0usize;
    let mut old_rng = 0x981f_765d_a02e_3cb4u64;
    let mut new_rng = 0x397e_054b_812c_f6dau64;
    let count = |state: &State, op: &Op| -> u64 {
        if !matches!(op.kind, K::CCX | K::CCZ) {
            return 0;
        }
        (state.cond
            & if op.c_condition == NO_BIT {
                u64::MAX
            } else {
                state.b[op.c_condition.0 as usize]
            })
        .count_ones() as u64
    };
    let started = std::time::Instant::now();
    let (output, stats) = transform(source.clone(), aliases, |op, replacements| {
        let measurement = if matches!(op.kind, K::R | K::Hmr) {
            let word = random_word(&mut old_rng);
            old_tape.push(word);
            assert_eq!(
                old.q[op.q_target.0 as usize], new.q[op.q_target.0 as usize],
                "pre-measurement target at {index}"
            );
            if op.kind == K::R && old.q[op.q_target.0 as usize] != 0 {
                dirty_resets += 1;
            }
            word
        } else {
            0
        };
        old_t += count(&old, op);
        old.apply(op, measurement);
        for replacement in replacements {
            let m = if replacement.kind == K::Hmr && replacement.c_target.0 >= nb {
                new.b.resize(replacement.c_target.0 as usize + 1, 0);
                random_word(&mut new_rng)
            } else {
                measurement
            };
            if matches!(replacement.kind, K::R | K::Hmr) {
                new_tape.push(m);
            }
            new_t += count(&new, replacement);
            new.apply(replacement, m);
        }
        // All possibly changed source wires are compared. By induction this
        // checks the complete state at every source boundary in O(ops), not O(Q*ops).
        for q in [op.q_target, op.q_control1, op.q_control2] {
            if q != NO_QUBIT {
                assert_eq!(
                    old.q[q.0 as usize], new.q[q.0 as usize],
                    "quantum mismatch at {index}: {op:?}"
                );
            }
        }
        if op.c_target != NO_BIT {
            assert_eq!(old.b[op.c_target.0 as usize], new.b[op.c_target.0 as usize]);
        }
        assert_eq!(old.phase, new.phase, "phase mismatch at {index}: {op:?}");
        assert_eq!(old.cond, new.cond);
        index += 1;
    });
    assert_eq!(old.q, new.q);
    assert_eq!(old.b, new.b[..nb as usize]);
    assert_eq!(old.stack, new.stack);
    assert_eq!(
        old_t - new_t,
        64 * (stats.constant_toffoli + stats.alias_toffoli + stats.measured_ands) as u64
    );
    let mut failures = 0;
    for (lane, &(x, y)) in expected.iter().enumerate() {
        for (reg, val) in regs[..2].iter().zip([x, y]) {
            for (j, wire) in reg.iter().enumerate() {
                let word = match wire {
                    QubitOrBit::Qubit(q) => old.q[q.0 as usize],
                    QubitOrBit::Bit(b) => old.b[b.0 as usize],
                };
                if ((word >> lane) & 1 != 0) != val.bit(j) {
                    failures |= 1u64 << lane;
                }
            }
        }
    }
    let mut ancilla_mask = 0;
    let mut registered = vec![false; nq as usize];
    for wire in regs.iter().flatten() {
        if let QubitOrBit::Qubit(q) = wire {
            registered[q.0 as usize] = true;
        }
    }
    for (q, &value) in old.q.iter().enumerate() {
        if !registered[q] {
            ancilla_mask |= value;
        }
    }
    assert_eq!(old, reference(&source, &initial, &old_tape));
    initial.b.resize(new.b.len(), 0);
    assert_eq!(new, reference(&output, &initial, &new_tape));
    eprintln!("MIDQ_EXACT_BOOLEAN_PROFILE PASS: shots=64 source_ops={} output_ops={} Q={nq} original_bits={nb} output_bits={} old_total_T={old_t} new_total_T={new_t} saved_per_shot={} old_avg_T={} new_avg_T={} pre_reset_dirty_events={dirty_resets} baseline_cls_mask={failures:016x} baseline_phase_mask={:016x} baseline_anc_mask={ancilla_mask:016x} seconds={:.3} {stats:?}",
        source.len(), output.len(), new.b.len(), (old_t-new_t)/64,
        old_t as f64 / 64.0, new_t as f64 / 64.0, old.phase, started.elapsed().as_secs_f64());
    output
}
