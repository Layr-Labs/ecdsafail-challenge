//! Emitted-op tests, not the port's stubbed contract simulator.
use super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId, NO_BIT};
use crate::sim::Simulator;
use ruint::Uint;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

type U512 = Uint<512, 8>;
type Case = [U512; 3];

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}

fn tof(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

fn apply<R: XofReader>(sim: &mut Simulator<'_, R>, ops: &[Op], mask: u64) {
    for (i, op) in ops.iter().enumerate() {
        assert_eq!(op.c_condition, NO_BIT);
        assert!(matches!(
            op.kind,
            OperationType::X | OperationType::CX | OperationType::CCX | OperationType::R
        ));
        if op.kind == OperationType::R {
            assert_eq!(
                sim.qubit(op.q_target) & mask,
                0,
                "dirty PRE-reset at local op {i}: {op:?}"
            );
        }
        sim.apply_iter(std::iter::once(op));
    }
}

fn set<R: XofReader>(sim: &mut Simulator<'_, R>, reg: &[QubitId], value: U512, shot: usize) {
    for (i, &id) in reg.iter().enumerate() {
        if value.bit(i) {
            *sim.qubit_mut(id) |= 1 << shot;
        }
    }
}

fn check<R: XofReader>(sim: &Simulator<'_, R>, regs: &[Vec<QubitId>], cases: &[Case], phase: u64) {
    let mask = u64::MAX >> (64 - cases.len());
    assert_eq!(sim.phase & mask, phase & mask, "phase changed");
    for (shot, values) in cases.iter().enumerate() {
        for (reg, value) in regs.iter().zip(values) {
            for (i, &id) in reg.iter().enumerate() {
                assert_eq!(
                    (sim.qubit(id) >> shot) & 1,
                    u64::from(value.bit(i)),
                    "wrong data shot={shot} wire={i} values={values:?}"
                );
            }
        }
    }
    for (i, &v) in sim.qubits.iter().enumerate() {
        if !regs.iter().any(|r| r.contains(&QubitId(i as u64))) {
            assert_eq!(v & mask, 0, "dirty scratch at boundary: {i}");
        }
    }
}

fn rng() -> impl XofReader {
    let mut hash = Shake256::default();
    hash.update(b"midq-quotient-code-components-v1");
    hash.finalize_xof()
}

fn code_exhaustive() {
    let mut c = Circuit::new();
    let q = c.alloc_qreg_bits("test.q", Q_BITS);
    let k = c.alloc_qreg_bits("test.k", CODE_BITS);
    let regs = vec![ids(&q), ids(&k), vec![]];
    xor_code(&mut c, &q, &k);
    let split = c.b.ops.len();
    xor_code(&mut c, &q, &k);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut random = rng();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut random);
    for first in (0usize..1 << Q_BITS).step_by(64) {
        sim.clear_for_shot();
        let phase = 0xa57a31b96c8de024;
        sim.phase = phase;
        let initial: Vec<_> = (first..first + 64)
            .map(|q| [U512::from(q), U512::from(q & 31), U512::ZERO])
            .collect();
        let expected: Vec<_> = (first..first + 64)
            .map(|q| {
                let code = if q == 0 {
                    Q_BITS
                } else {
                    q.trailing_zeros() as usize
                };
                [U512::from(q), U512::from((q & 31) ^ code), U512::ZERO]
            })
            .collect();
        for (shot, values) in initial.iter().enumerate() {
            for (reg, value) in regs.iter().zip(values) {
                set(&mut sim, reg, *value, shot);
            }
        }
        apply(&mut sim, &c.b.ops[..split], u64::MAX);
        check(&sim, &regs, &expected, phase);
        apply(&mut sim, &c.b.ops[split..], u64::MAX);
        check(&sim, &regs, &initial, phase);
    }
    eprintln!(
        "QCODE CTZ PASS inputs={} Q={nq} T_one={}",
        1 << Q_BITS,
        tof(&c.b.ops[..split])
    );
}

fn extractor_exhaustive(n: usize, m: usize) -> usize {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let b = c.alloc_qreg_bits("test.b", n);
    let k = c.alloc_qreg_bits("test.k", CODE_BITS);
    let q = c.alloc_qreg_bits("test.q", m);
    let ar = ids(&a);
    let br = ids(&b);
    let kr = ids(&k);
    let qr = ids(&q);
    xor_recovered(&mut c, &a, &b, &k, &q);
    let split = c.b.ops.len();
    xor_recovered(&mut c, &a, &b, &k, &q);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut random = rng();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut random);
    let count = (1 << (2 * n)) * (m + 1);
    let word_mask = (1usize << n) - 1;
    for first in (0..count).step_by(64) {
        sim.clear_for_shot();
        let valid = 64.min(count - first);
        let mask = u64::MAX >> (64 - valid);
        let phase = 0x123456789abcdef0;
        sim.phase = phase;
        let mut expect_q = Vec::new();
        for shot in 0..valid {
            let index = first + shot;
            let av = index & word_mask;
            let bv = (index >> n) & word_mask;
            let kv = index >> (2 * n);
            let old_q = (av ^ bv ^ kv) & ((1 << m) - 1);
            let div = if bv == 0 {
                (1 << m) - 1
            } else {
                (av / bv).min((1 << m) - 1)
            };
            let recovered = if kv == m { 0 } else { (div >> kv) << kv };
            for (reg, v) in [(&ar, av), (&br, bv), (&kr, kv), (&qr, old_q)] {
                set(&mut sim, reg, U512::from(v), shot);
            }
            expect_q.push(old_q ^ recovered);
        }
        let initial = sim.qubits.clone();
        apply(&mut sim, &c.b.ops[..split], mask);
        for (i, &v) in sim.qubits.iter().enumerate() {
            if let Some(bit) = qr.iter().position(|q| q.0 as usize == i) {
                let expected = expect_q
                    .iter()
                    .enumerate()
                    .fold(0, |s, (shot, q)| s | (((q >> bit) & 1) as u64) << shot);
                assert_eq!(
                    v & mask,
                    expected,
                    "extract n={n} m={m} first={first} bit={bit}"
                );
            } else {
                assert_eq!(v & mask, initial[i] & mask, "data/scratch i={i}");
            }
        }
        assert_eq!(sim.phase, phase);
        apply(&mut sim, &c.b.ops[split..], mask);
        assert_eq!(sim.qubits, initial);
        assert_eq!(sim.phase, phase);
    }
    eprintln!(
        "QCODE EXTRACT PASS n={n} m={m} inputs={count} Q={nq} T_one={}",
        tof(&c.b.ops[..split])
    );
    count
}

fn wide_cases() -> Vec<Case> {
    let one = U512::from(1);
    let max = (one << 257) - one;
    let p = (one << 256) - (one << 32) - U512::from(977);
    // Sentinel includes ratios much larger than q18 and zero divisor. The latter
    // is outside PZ support, but the sentinel circuit still must be an identity.
    let mut cases = vec![
        [U512::from(3), one, U512::ZERO],
        [max, one, U512::ZERO],
        [max, max, U512::ZERO],
        [max, U512::ZERO, U512::ZERO],
        [p, one, U512::ZERO],
    ];
    let mut random = rng();
    for k in 0..Q_BITS {
        for j in 0..256usize {
            let mut bytes = [0u8; 64];
            random.read(&mut bytes);
            let q = (((u64::from_le_bytes(bytes[..8].try_into().unwrap()) as usize)
                & ((1 << (Q_BITS - k)) - 1))
                | 1)
                << k;
            let d = j & ((1 << k) - 1);
            let factor = U512::from(q + d + 1);
            let ceiling = max / factor;
            let mut b = U512::from_le_bytes(bytes) % ceiling + one;
            if j & 1 == 0 {
                b = b.min((one << 248) - one);
            }
            if j < 4 {
                b = [one, U512::from(3), ceiling, ceiling - one][j];
            }
            let r = if j & 1 == 0 { U512::ZERO } else { b - one };
            let a = U512::from(d) * b + r;
            assert!(a + U512::from(q) * b <= max);
            cases.push([a, b, U512::from(q)]);
        }
    }
    cases
}

fn wide_roundtrip() {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", 257);
    let b = c.alloc_qreg_bits("test.b", 257);
    let mut q = c.alloc_qreg_bits("test.q", Q_BITS);
    let initial_regs = vec![ids(&a), ids(&b), ids(&q)];
    midq_flush_quotient(&mut c, &a, &b, &q, false);
    let after_flush = c.b.ops.len();
    let k = compress(&mut c, &a, &b, &mut q);
    let compressed_regs = vec![ids(&a), ids(&b), ids(&k)];
    let compressed_live = c.b.active_qubits;
    let compressed = c.b.ops.len();
    restore(&mut c, &a, &b, &mut q, k);
    let restored_regs = vec![ids(&a), ids(&b), ids(&q)];
    let restored = c.b.ops.len();
    midq_flush_quotient(&mut c, &a, &b, &q, true);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    for op in &c.b.ops {
        op.validate();
    }
    let mut random = rng();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut random);
    let cases = wide_cases();
    for chunk in cases.chunks(64) {
        sim.clear_for_shot();
        let mask = u64::MAX >> (64 - chunk.len());
        let phase = 0xc6b583901fed247a;
        sim.phase = phase;
        for (shot, values) in chunk.iter().enumerate() {
            for (reg, value) in initial_regs.iter().zip(values) {
                set(&mut sim, reg, *value, shot);
            }
        }
        let flushed: Vec<_> = chunk
            .iter()
            .map(|[a, b, q]| [*a + *q * *b, *b, *q])
            .collect();
        let coded: Vec<_> = flushed
            .iter()
            .map(|[a, b, q]| {
                [
                    *a,
                    *b,
                    U512::from(if *q == U512::ZERO {
                        Q_BITS
                    } else {
                        q.trailing_zeros()
                    }),
                ]
            })
            .collect();
        apply(&mut sim, &c.b.ops[..after_flush], mask);
        check(&sim, &initial_regs, &flushed, phase);
        apply(&mut sim, &c.b.ops[after_flush..compressed], mask);
        check(&sim, &compressed_regs, &coded, phase);
        apply(&mut sim, &c.b.ops[compressed..restored], mask);
        check(&sim, &restored_regs, &flushed, phase);
        apply(&mut sim, &c.b.ops[restored..], mask);
        check(&sim, &restored_regs, chunk, phase);
    }
    eprintln!("QCODE WIDE PASS inputs={} Q={nq} compressed_live={compressed_live} flush_T={} compress_T={} restore_T={} inverse_flush_T={}",
        cases.len(), tof(&c.b.ops[..after_flush]), tof(&c.b.ops[after_flush..compressed]),
        tof(&c.b.ops[compressed..restored]), tof(&c.b.ops[restored..]));
}

fn overflow_counterexample() {
    let one = U512::from(1);
    let mask = (one << 257) - one;
    let b: U512 = one << 247;
    let q1 = U512::from(1024);
    let q2 = U512::from(3072);
    assert_eq!(q1.trailing_zeros(), 10);
    assert_eq!(q2.trailing_zeros(), 10);
    assert_eq!((b * q1) & mask, U512::ZERO);
    assert_eq!((b * q2) & mask, U512::ZERO);
    assert!(q1.bit_len() <= Q_BITS && q2.bit_len() <= Q_BITS && b.bit_len() <= 248);
    eprintln!("QCODE NEGATIVE PASS: ca=0 cb=2^247 q=1024/3072 share k=10 and wrapped ca'=0; width-only support is insufficient");
}

pub(crate) fn run() {
    overflow_counterexample();
    code_exhaustive();
    let mut exhaustive = 0;
    for n in 2..=6 {
        for m in 1..=n.min(3) {
            exhaustive += extractor_exhaustive(n, m);
        }
    }
    wide_roundtrip();
    eprintln!("MIDQ_QUOTIENT_CODE_SELFTEST PASS: {exhaustive} exhaustive extractor inputs; overflow/zero/sentinel/reverse/phase/pre-reset checked");
}
