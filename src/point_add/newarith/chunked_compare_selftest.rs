//! Tests execute the unmodified crate::sim::Simulator. The reset auditor also
//! flattens classical conditions, then cross-checks the complete native run.

use super::*;
use crate::circuit::{analyze_ops, Op, OperationType as K, NO_BIT, NO_QUBIT, NO_REG};
use crate::point_add::B;
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Measurements<R> {
    mode: u8,
    rng: R,
}
impl<R: XofReader> XofReader for Measurements<R> {
    fn read(&mut self, bytes: &mut [u8]) {
        match self.mode {
            0 => bytes.fill(0),
            1 => bytes.fill(255),
            _ => self.rng.read(bytes),
        }
    }
}

fn rng(label: &[u8]) -> impl XofReader {
    let mut s = Shake256::default();
    s.update(label);
    s.finalize_xof()
}

fn count(b: &B) -> usize {
    b.ops
        .iter()
        .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
        .count()
}

fn validate_ops(ops: &[Op]) {
    let mut stack = Vec::new();
    for op in ops {
        op.validate();
        let nq = match op.kind {
            K::Neg | K::PushCondition | K::PopCondition => 0,
            K::X | K::Z | K::R | K::Hmr => 1,
            K::CX | K::CZ => 2,
            K::CCX | K::CCZ => 3,
            _ => panic!("unexpected component op {op:?}"),
        };
        let qs = [op.q_target, op.q_control1, op.q_control2];
        for i in 0..3 {
            assert_eq!(qs[i] != NO_QUBIT, i < nq, "invalid quantum slot {op:?}");
            if i < nq {
                assert!(!qs[..i].contains(&qs[i]), "aliased gate {op:?}");
            }
        }
        assert_eq!(op.r_target, NO_REG);
        assert_eq!(op.c_target != NO_BIT, op.kind == K::Hmr);
        match op.kind {
            K::PushCondition => {
                assert_ne!(op.c_condition, NO_BIT);
                assert!(!stack.contains(&op.c_condition), "shared-flag nested loop");
                stack.push(op.c_condition);
            }
            K::PopCondition => {
                assert!(stack.pop().is_some());
            }
            _ => {}
        }
    }
    assert!(stack.is_empty());
}

fn evaluate(b: &B, inputs: &[u64], bits: &[u64], mode: u8) -> (Vec<u64>, u64, u64) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let nq = (nq as usize).max(b.next_qubit as usize).max(inputs.len());
    let nb = (nb as usize).max(bits.len()).max(b.next_bit as usize);
    let mut r1 = Measurements {
        mode,
        rng: rng(b"chunk-measurements-v1"),
    };
    let mut r2 = Measurements {
        mode,
        rng: rng(b"chunk-measurements-v1"),
    };
    let mut native = Simulator::new(nq, nb, &mut r1);
    let mut audit = Simulator::new(nq, nb + 1, &mut r2);
    for s in [&mut native, &mut audit] {
        s.qubits[..inputs.len()].copy_from_slice(inputs);
        // Deliberately stale HMR bits outside the enclosing condition.
        s.bits[..nb].fill(u64::MAX);
        s.bits[..bits.len()].copy_from_slice(bits);
    }
    native.apply_iter(b.ops.iter());
    let mut stack = Vec::new();
    let mut base = u64::MAX;
    for (index, op) in b.ops.iter().enumerate() {
        match op.kind {
            K::PushCondition => {
                stack.push(base);
                base &= audit.bit(op.c_condition);
            }
            K::PopCondition => {
                base = stack.pop().unwrap();
            }
            _ => {
                let cond = base
                    & if op.c_condition == NO_BIT {
                        u64::MAX
                    } else {
                        audit.bit(op.c_condition)
                    };
                if op.kind == K::R {
                    // Stronger than checking just active lanes: reused slots must
                    // be globally zero, including outside nested replay blocks.
                    assert_eq!(
                        audit.qubit(op.q_target),
                        0,
                        "dirty pre-reset at {index}: {op:?}"
                    );
                }
                let mut flat = *op;
                flat.c_condition = crate::circuit::BitId(nb as u64);
                audit.bits[nb] = cond;
                audit.apply_iter(std::iter::once(&flat));
            }
        }
    }
    assert_eq!(
        audit.qubits, native.qubits,
        "native nested-condition values"
    );
    assert_eq!(audit.phase, native.phase, "native nested-condition phase");
    assert_eq!(
        audit.stats, native.stats,
        "native nested-condition resources"
    );
    assert_eq!(&audit.bits[..nb], &native.bits[..]);
    assert!(
        native.qubits[inputs.len()..].iter().all(|&v| v == 0),
        "dirty scratch"
    );
    (
        native.qubits[..inputs.len()].to_vec(),
        native.phase,
        native.stats.toffoli_gates,
    )
}

#[derive(Clone, Copy, Debug)]
enum Action {
    Xor,
    Phase,
    Pair,
    Integrated,
    OldPair,
}

fn build(
    n: usize,
    k: usize,
    initial: bool,
    complement: bool,
    action: Action,
    nested: bool,
    replay: bool,
    padding: usize,
) -> B {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let b = c.alloc_qreg_bits("test.b", n);
    let out = c.alloc_qreg("test.out");
    let witness = c.alloc_qreg("test.witness");
    let _padding = c.alloc_qreg_bits("test.padding", padding);
    let ar: Vec<_> = a.iter().collect();
    let br: Vec<_> = b.iter().collect();
    let c0 = c.alloc_bit();
    let c1 = c.alloc_bit();
    let body = |c: &mut Circuit| match action {
        Action::Xor | Action::Phase => emit(
            c,
            &ar,
            &br,
            initial,
            complement,
            if matches!(action, Action::Xor) {
                Endpoint::Xor(&out)
            } else {
                Endpoint::Phase
            },
            k,
            replay,
        ),
        Action::Pair => {
            emit(
                c,
                &ar,
                &br,
                initial,
                complement,
                Endpoint::Xor(&out),
                k,
                replay,
            );
            c.cx(&out, &witness);
            let m = c.alloc_bit();
            c.hmr(&out, m);
            c.with_condition(m, |c| {
                emit(c, &ar, &br, initial, complement, Endpoint::Phase, k, replay)
            });
            c.free_bit(m);
        }
        Action::Integrated | Action::OldPair => {
            super::super::borrow_compare_refs(c, &br, &ar, &out);
            c.cx(&out, &witness);
            super::super::clear_borrow_compare_refs(c, &br, &ar, &out);
        }
    };
    if nested {
        c.with_conditions(&[c0, c1], body);
    } else {
        body(&mut c);
    }
    c.flush_pending_frees();
    // Inputs remain live for resource accounting and are not reset in this stream.
    let b = c.into_builder();
    validate_ops(&b.ops);
    b
}

fn expected(
    input: &[u64],
    n: usize,
    initial: bool,
    complement: bool,
    action: Action,
    active: u64,
) -> (Vec<u64>, u64) {
    // Independent high-to-low integer oracle: a+b+cin overflows iff
    // a > ~b, or a == ~b and cin=1. No carry recurrence is reused.
    let mut greater = 0;
    let mut equal = u64::MAX;
    for i in (0..n).rev() {
        let rhs = input[n + i] ^ if complement { 0 } else { u64::MAX };
        greater |= equal & input[i] & !rhs;
        equal &= !(input[i] ^ rhs);
    }
    let carry = greater | if initial { equal } else { 0 };
    let mut out = input.to_vec();
    let phase = if matches!(action, Action::Phase) {
        carry & active
    } else {
        0
    };
    match action {
        Action::Xor => out[2 * n] ^= carry & active,
        Action::Phase => {}
        _ => {
            out[2 * n] &= !active;
            out[2 * n + 1] ^= carry & active;
        }
    }
    (out, phase)
}

fn exhaustive() -> usize {
    let mut checked = 0;
    for n in 0..=5 {
        if std::env::var("MIDQ_VARIABLE_CHUNKS").ok().as_deref() == Some("1") {
            std::env::set_var("MIDQ_CHUNK_COMPARE_QCAP", (2 * n + 5).to_string());
        }
        for k in 1..=n.max(1) {
            for initial in [false, true] {
                for complement in [false, true] {
                    for action in [Action::Xor, Action::Phase, Action::Pair] {
                        for nested in [false, true] {
                            let b = build(n, k, initial, complement, action, nested, true, 0);
                            for first in (0..1usize << (2 * n + 2)).step_by(64) {
                                let mut input = vec![0u64; 2 * n + 2];
                                for (j, word) in input.iter_mut().enumerate() {
                                    for shot in 0..64 {
                                        *word |= ((((first + shot) >> j) & 1) as u64) << shot;
                                    }
                                }
                                if matches!(action, Action::Pair) {
                                    input[2 * n] = 0;
                                }
                                let bits = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc];
                                let active = if nested { bits[0] & bits[1] } else { u64::MAX };
                                let want = expected(&input, n, initial, complement, action, active);
                                for mode in 0..=2 {
                                    let (out, phase, _) = evaluate(&b, &input, &bits, mode);
                                    assert_eq!((out, phase), want, "n={n} k={k} initial={initial} complement={complement} action={action:?} nested={nested} mode={mode}");
                                    checked += 64;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    checked
}

fn full_width() -> usize {
    let mut r = rng(b"chunk-full-width-v1");
    let mut checked = 0;
    for n in [16, 24, 31, 32, 33, 64, 127, 255, 256, 257] {
        for k in [16, 24, 32] {
            for action in [Action::Xor, Action::Pair] {
                for initial in [false, true] {
                    let b = build(n, k, initial, true, action, true, true, 0);
                    assert_eq!(b.peak_qubits as usize, 2 * n + 2 + scratch_qubits(n, k));
                    for batch in 0..16 {
                        let mut input = vec![0u64; 2 * n + 2];
                        for word in &mut input {
                            let mut bytes = [0; 8];
                            r.read(&mut bytes);
                            *word = u64::from_le_bytes(bytes);
                        }
                        // Equality, all-zero/all-one and carry propagation across
                        // every chunk boundary, alongside unrestricted random lanes.
                        for i in 0..n {
                            input[n + i] = (input[n + i] & !15) | (input[i] & 1);
                            input[i] &= !6;
                            if i >= batch * n / 16 {
                                input[i] |= 2;
                            }
                            if i < batch * n / 16 {
                                input[n + i] |= 2;
                            }
                            input[i] |= 8;
                            input[n + i] |= 8;
                        }
                        if matches!(action, Action::Pair) {
                            input[2 * n] = 0;
                        }
                        let bits = [0xfafafafafafafafa, 0xcfcfcfcfcfcfcfcf];
                        let want = expected(&input, n, initial, true, action, bits[0] & bits[1]);
                        for mode in 0..=2 {
                            let (out, phase, _) = evaluate(&b, &input, &bits, mode);
                            assert_eq!(
                                (out, phase),
                                want,
                                "production n={n} k={k} action={action:?}"
                            );
                            checked += 64;
                        }
                    }
                }
            }
        }
    }
    checked
}

fn aliases() -> usize {
    let mut checked = 0;
    for complement in [false, true] {
        for initial in [false, true] {
            for k in [1, 2, 3, 5] {
                let mut c = Circuit::new();
                let q = c.alloc_qreg_bits("test.alias", 5);
                let out = c.alloc_qreg("test.out");
                let a = [&q[4], &q[0], &q[2], &q[0], &q[3]];
                let b = [&q[1], &q[0], &q[4], &q[3], &q[2]];
                emit(
                    &mut c,
                    &a,
                    &b,
                    initial,
                    complement,
                    Endpoint::Xor(&out),
                    k,
                    true,
                );
                let built = c.into_builder();
                validate_ops(&built.ops);
                let input: Vec<u64> = (0..6)
                    .map(|i| (0..64).fold(0, |m, s| m | (((s >> i) & 1) << s)))
                    .collect();
                let mut carry = if initial { u64::MAX } else { 0 };
                for (&ai, &bi) in [4, 0, 2, 0, 3].iter().zip(&[1, 0, 4, 3, 2]) {
                    let av = input[ai];
                    let bv = input[bi] ^ if complement { u64::MAX } else { 0 };
                    carry = (av & bv) ^ (av & carry) ^ (bv & carry);
                }
                let mut want = input.clone();
                want[5] ^= carry;
                for mode in 0..=2 {
                    let (out, phase, _) = evaluate(&built, &input, &[], mode);
                    assert_eq!((out, phase), (want.clone(), 0));
                    checked += 64;
                }
            }
        }
    }
    // Invalid target overlap and mismatched widths must fail before emitting.
    let mut c = Circuit::new();
    let q = c.alloc_qreg_bits("test.invalid", 3);
    for (a, b, out) in [
        (vec![&q[0]], vec![&q[1]], &q[0]),
        (vec![&q[0]], vec![], &q[2]),
    ] {
        let old = c.total_ops();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| emit(
                &mut c,
                &a,
                &b,
                false,
                true,
                Endpoint::Xor(out),
                1,
                true
            )))
            .is_err()
        );
        assert_eq!(c.total_ops(), old);
    }
    checked
}

fn resources_and_fallback() {
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    for n in [1, 16, 24, 32, 64, 128, 256, 257] {
        for k in [16, 24, 32] {
            let b = build(n, k, false, true, Action::Pair, false, true, 0);
            let replay = (n.div_ceil(k) - 1) * (k - 1);
            assert_eq!(count(&b), 2 * n - 1 + 2 * replay);
            let mut input = vec![0; 2 * n + 2];
            input[0] = u64::MAX;
            let (_, _, executed) = evaluate(&b, &input, &[], 2);
            let expected_t = 1.5 * n as f64 - 0.5 + 0.75 * replay as f64;
            eprintln!("CHUNK_RESOURCE n={n} k={k} emitted={} expected_T={expected_t:.3} measured_64_T={:.6} Q={} scratch={}",
                count(&b), executed as f64 / 64.0, b.peak_qubits, scratch_qubits(n, k));
        }
    }
    for k in [0, 1, 2, 16, 24, 32] {
        std::env::set_var("MIDQ_CHUNK_COMPARE", "0");
        let b = build(
            256,
            k.max(1),
            false,
            true,
            if k == 0 {
                Action::OldPair
            } else {
                Action::Pair
            },
            false,
            true,
            0,
        );
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut measurements = rng(b"chunk-resources-65536-v1");
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut measurements);
        for _ in 0..1024 {
            sim.clear_for_shot();
            sim.qubits[0] = u64::MAX;
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0);
            assert_eq!(sim.qubits[512], 0);
            assert_eq!(sim.qubits[513], u64::MAX);
            assert!(sim.qubits[514..].iter().all(|&q| q == 0));
        }
        eprintln!(
            "CHUNK_AVERAGE n=256 k={k} shots=65536 emitted={} executed={} avgT={:.9} Q={}",
            count(&b),
            sim.stats.toffoli_gates,
            sim.stats.toffoli_gates as f64 / 65536.0,
            b.peak_qubits
        );
    }
    assert_eq!(select_chunk(76, 40, 32), Some(2));
    assert_eq!(select_chunk(256, 256, 32), Some(1));
    for live in [514, 970, 982, 985, 990, 1000, 1018] {
        let n = 256;
        let pad = live - (2 * n + 2);
        std::env::set_var("MIDQ_CHUNK_COMPARE", "0");
        let old = build(n, 32, false, true, Action::OldPair, false, true, pad);
        std::env::set_var("MIDQ_CHUNK_COMPARE", "1");
        let new = build(n, 32, false, true, Action::Integrated, false, true, pad);
        let selected = select_chunk(n, QCAP - live, 32);
        assert!(new.peak_qubits as usize <= QCAP);
        if selected.is_none() {
            assert_eq!(old.ops, new.ops, "fallback changed old stream");
        }
        let mut input = vec![0; live];
        input[0] = u64::MAX;
        for mode in 0..=2 {
            let (out, phase, _) = evaluate(&new, &input, &[], mode);
            assert_eq!(
                (out, phase),
                expected(&input, n, false, true, Action::Integrated, u64::MAX)
            );
        }
        eprintln!(
            "CHUNK_CAP live={live} selected={selected:?} Q={} emitted={}",
            new.peak_qubits,
            count(&new)
        );
    }
    // Sizing is exact at both sides of the threshold, with no spare-bit guess.
    for n in 1..=257 {
        for k in [16, 24, 32] {
            let k = k.min(n);
            let s = scratch_qubits(n, k);
            let b = build(n, k, false, true, Action::Xor, false, true, 0);
            assert_eq!(b.peak_qubits as usize, 2 * n + 2 + s);
            assert!(select_chunk(n, s, k).is_some());
        }
    }
    // The unconditional replay reference has the same exact phase channel.
    for replay in [false, true] {
        let b = build(17, 4, true, true, Action::Pair, true, replay, 0);
        let input = vec![0; 36];
        for mode in 0..=2 {
            assert_eq!(evaluate(&b, &input, &[!0, !0], mode).1, 0);
        }
    }
    std::env::remove_var("MIDQ_CHUNK_COMPARE");
}

fn all_measurement_transcripts() -> usize {
    struct Transcript {
        words: Vec<u64>,
        index: usize,
    }
    impl XofReader for Transcript {
        fn read(&mut self, bytes: &mut [u8]) {
            assert_eq!(bytes.len(), 8);
            bytes.copy_from_slice(&self.words[self.index].to_le_bytes());
            self.index += 1;
        }
    }
    let mut checked = 0;
    for initial in [false, true] {
        for complement in [false, true] {
            let b = build(2, 1, initial, complement, Action::Pair, true, true, 0);
            let hmr = b.ops.iter().filter(|op| op.kind == K::Hmr).count();
            assert_eq!(hmr, 4);
            let (nq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut input: Vec<u64> = (0..6)
                .map(|i| (0..64).fold(0, |m, s| m | (((s >> i) & 1) << s)))
                .collect();
            input[4] = 0;
            let bits = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc];
            let want = expected(
                &input,
                2,
                initial,
                complement,
                Action::Pair,
                bits[0] & bits[1],
            );
            for transcript in 0..1usize << hmr {
                let mut index = 0;
                let words = b
                    .ops
                    .iter()
                    .filter_map(|op| match op.kind {
                        K::Hmr => {
                            let word = if transcript >> index & 1 != 0 {
                                u64::MAX
                            } else {
                                0
                            };
                            index += 1;
                            Some(word)
                        }
                        K::R => Some(u64::MAX),
                        _ => None,
                    })
                    .collect();
                let mut r = Transcript { words, index: 0 };
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut r);
                sim.qubits[..input.len()].copy_from_slice(&input);
                sim.bits.fill(u64::MAX);
                sim.bits[..2].copy_from_slice(&bits);
                sim.apply_iter(b.ops.iter());
                assert_eq!((&sim.qubits[..6], sim.phase), (want.0.as_slice(), want.1));
                assert!(sim.qubits[6..].iter().all(|&q| q == 0));
                checked += 64;
            }
        }
    }
    checked
}

fn integration_paths() -> usize {
    std::env::set_var("MIDQ_CHUNK_COMPARE", "1");
    let mut checked = 0;
    for measured in ["0", "1"] {
        std::env::set_var("MIDQ_MEASURE_COMPARE", measured);
        for n in 1..=6 {
            let b = build(n, 2, false, true, Action::Integrated, true, true, 0);
            for first in (0..1usize << (2 * n + 2)).step_by(64) {
                let mut input: Vec<u64> = (0..2 * n + 2)
                    .map(|i| (0..64).fold(0, |m, s| m | (((((first + s) >> i) & 1) as u64) << s)))
                    .collect();
                input[2 * n] = 0;
                let bits = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc];
                let want = expected(
                    &input,
                    n,
                    false,
                    true,
                    Action::Integrated,
                    bits[0] & bits[1],
                );
                for mode in 0..=2 {
                    let (out, phase, _) = evaluate(&b, &input, &bits, mode);
                    assert_eq!((out, phase), want, "integrated measured={measured} n={n}");
                    checked += 64;
                }
            }
        }
    }
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    for forward_tight in [false, true] {
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("test.a", 256);
        let b = c.alloc_qreg_bits("test.b", 256);
        let out = c.alloc_qreg("test.out");
        let witness = c.alloc_qreg("test.witness");
        let mut pad = c.alloc_qreg_bits("test.pad", if forward_tight { 476 } else { 0 });
        let ar: Vec<_> = a.iter().collect();
        let br: Vec<_> = b.iter().collect();
        super::super::borrow_compare_refs(&mut c, &br, &ar, &out);
        c.cx(&out, &witness);
        if forward_tight {
            for q in pad.drain(..) {
                c.zero_and_free(q);
            }
        } else {
            pad = c.alloc_qreg_bits("test.pad", 476);
        }
        super::super::clear_borrow_compare_refs(&mut c, &br, &ar, &out);
        let built = c.into_builder();
        validate_ops(&built.ops);
        let mut input = vec![0; 514];
        input[0] = u64::MAX;
        for mode in 0..=2 {
            let (out, phase, _) = evaluate(&built, &input, &[], mode);
            assert_eq!(
                (out, phase),
                expected(&input, 256, false, true, Action::Integrated, u64::MAX)
            );
            checked += 64;
        }
        drop(pad);
    }
    std::env::remove_var("MIDQ_CHUNK_COMPARE");
    checked
}

pub(crate) fn run() {
    std::env::remove_var("MIDQ_VARIABLE_CHUNKS");
    assert_ne!(
        std::env::var("POINT_ADD_COUNT_ONLY").ok().as_deref(),
        Some("1")
    );
    let small = exhaustive();
    eprintln!("CHUNK_EXHAUSTIVE PASS {small} basis/measurement cases");
    let full = full_width();
    eprintln!("CHUNK_FULL_WIDTH PASS {full} basis/measurement cases");
    let alias = aliases();
    eprintln!("CHUNK_ALIAS PASS {alias} basis/measurement cases");
    let transcripts = all_measurement_transcripts();
    eprintln!("CHUNK_TRANSCRIPTS PASS {transcripts} basis/measurement cases");
    let paths = integration_paths();
    eprintln!("CHUNK_INTEGRATION PASS {paths} basis/measurement cases");
    resources_and_fallback();
    std::env::set_var("MIDQ_VARIABLE_CHUNKS", "1");
    let variable = exhaustive();
    let mut random = rng(b"variable-chunk-full-width-v1");
    for n in [8usize, 16, 85, 256, 257] {
        for available in [8usize, 16, 32, 64, 100] {
            if crate::point_add::clean_chunk_plan::plan(n, available).is_none() { continue; }
            let cap = 2 * n + 2 + available;
            std::env::set_var("MIDQ_CHUNK_COMPARE_QCAP", cap.to_string());
            for action in [Action::Xor, Action::Phase, Action::Pair] {
                let b = build(n, 1, false, true, action, true, true, 0);
                assert!(b.peak_qubits as usize <= cap);
                for _ in 0..16 {
                    let mut input = vec![0u64; 2 * n + 2];
                    for word in &mut input {
                        let mut bytes = [0u8; 8];
                        random.read(&mut bytes);
                        *word = u64::from_le_bytes(bytes);
                    }
                    if matches!(action, Action::Pair) { input[2 * n] = 0; }
                    let bits = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc];
                    let want = expected(&input, n, false, true, action, bits[0] & bits[1]);
                    for mode in 0..=2 {
                        let (out, phase, _) = evaluate(&b, &input, &bits, mode);
                        assert_eq!((out, phase), want);
                    }
                }
            }
        }
    }
    std::env::remove_var("MIDQ_VARIABLE_CHUNKS");
    std::env::remove_var("MIDQ_CHUNK_COMPARE_QCAP");
    eprintln!("VARIABLE_CHUNK_COMPARE PASS: {variable} exhaustive cases plus full-width nested random batches");
    eprintln!("MIDQ_CHUNK_COMPARE_SELFTEST PASS: {} cases; value, phase, native nesting, slots, pre-reset, cap/fallback", small + full + alias + transcripts + paths);
}
