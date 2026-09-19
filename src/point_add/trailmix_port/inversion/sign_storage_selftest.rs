use super::super::{
    midq_field_neg, midq_tail_backward_with_parity, midq_tail_forward_with_parity,
    midq_value_round_backward, midq_value_round_forward, predicate_clear_selftest::checked_apply,
};
use super::*;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut hash = Shake256::default();
        hash.update(b"midq-sign-storage-v1");
        Self(
            [Some(0), Some(255), Some(0x55), None][mode],
            hash.finalize_xof(),
        )
    }
}
impl XofReader for Measurements {
    fn read(&mut self, bytes: &mut [u8]) {
        if let Some(v) = self.0 {
            bytes.fill(v);
        } else {
            self.1.read(bytes);
        }
    }
}
fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}
fn write<R: XofReader>(s: &mut Simulator<R>, ids: &[QubitId], lane: usize, value: U256) {
    for (i, &q) in ids.iter().enumerate().take(256) {
        if value.bit(i) {
            *s.qubit_mut(q) |= 1 << lane;
        }
    }
}
fn read<R: XofReader>(s: &Simulator<R>, ids: &[QubitId], lane: usize) -> U256 {
    let mut value = U256::ZERO;
    for (i, &q) in ids.iter().enumerate() {
        let bit = s.qubit(q) >> lane & 1;
        if i < 256 {
            value |= U256::from(bit) << i;
        } else {
            assert_eq!(bit, 0);
        }
    }
    value
}
fn apply<R: XofReader>(s: &mut Simulator<R>, ops: &[Op], mask: u64) {
    checked_apply(s, ops, mask);
    assert_eq!(s.phase & mask, 0, "component phase");
}
fn clean<R: XofReader>(s: &Simulator<R>, live: &[Vec<QubitId>], mask: u64) {
    for (i, &bits) in s.qubits.iter().enumerate() {
        if !live.iter().any(|r| r.contains(&QubitId(i as u64))) {
            assert_eq!(bits & mask, 0, "dirty scratch {i}");
        }
    }
}
fn signed(v: i32, w: usize) -> i32 {
    (v << (32 - w)) >> (32 - w)
}

fn value_equivariance() {
    let mut cases = 0;
    for width in 3..=8 {
        let mut c = Circuit::new();
        let mut a = c.alloc_qreg_bits("a", width);
        let mut b = c.alloc_qreg_bits("b", width);
        let sign = c.alloc_qreg("input.sign");
        let initial = [ids(&a), ids(&b), ids(std::slice::from_ref(&sign))];
        negate_odd_rows(&mut c, &sign, &a, &b);
        let decision = c.alloc_qreg("decision");
        midq_value_round_forward(&mut c, &mut a, &mut b, &decision, width);
        let mid = c.b.ops.len();
        let out = [ids(&a), ids(&b), ids(std::slice::from_ref(&decision))];
        midq_value_round_backward(&mut c, &mut a, &mut b, decision, width);
        negate_odd_rows(&mut c, &sign, &a, &b);
        let restored = [ids(&a), ids(&b), initial[2].clone()];
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        let total = 2usize << (2 * (width - 1));
        let maskw = (1usize << width) - 1;
        for mode in 0..4 {
            let mut rng = Measurements::new(mode);
            let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
            for first in (0..total).step_by(64) {
                sim.clear_for_shot();
                let len = 64.min(total - first);
                let mask = u64::MAX >> (64 - len);
                let mut rows = Vec::new();
                for lane in 0..len {
                    let code = first + lane;
                    let av = (code & ((1 << (width - 1)) - 1)) * 2 + 1;
                    let bv = ((code >> (width - 1)) & ((1 << (width - 1)) - 1)) * 2 + 1;
                    let sg = code >> (2 * (width - 1));
                    let row = [av, bv, sg];
                    for i in 0..3 {
                        write(&mut sim, &initial[i], lane, U256::from(row[i]));
                    }
                    rows.push(row);
                }
                apply(&mut sim, &c.b.ops[..mid], mask);
                for (lane, &[av, bv, sg]) in rows.iter().enumerate() {
                    let dec = ((av ^ bv) >> 1) & 1;
                    let sum = bv as i32 + if dec == 0 { av as i32 } else { -(av as i32) };
                    let half = signed(sum, width) >> 1;
                    let factor = if sg == 0 { 1 } else { -1 };
                    assert_eq!(
                        read(&sim, &out[0], lane),
                        U256::from(((av as i32 * factor) as usize) & maskw)
                    );
                    assert_eq!(
                        read(&sim, &out[1], lane),
                        U256::from(((half * factor) as usize) & maskw)
                    );
                    assert_eq!(read(&sim, &out[2], lane), U256::from(dec));
                }
                apply(&mut sim, &c.b.ops[mid..], mask);
                clean(&sim, &restored, mask);
                for (lane, row) in rows.iter().enumerate() {
                    for i in 0..3 {
                        assert_eq!(read(&sim, &restored[i], lane), U256::from(row[i]));
                    }
                    cases += 1;
                }
            }
        }
    }
    eprintln!("SIGN_VALUE PASS {cases} signed odd-pair/sign/measurement cases; wrap, transcript, inverse, phase, pre-reset");
}

fn parity_codec() {
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let mut values = vec![
        U256::ZERO,
        U256::from(1),
        (U256::from(1) << 248) - U256::from(1),
    ];
    for bit in 1..248 {
        values.push(U256::from(1) << bit);
    }
    let mut c = Circuit::new();
    let cb = c.alloc_qreg_bits("cb", 257);
    let dirty = c.alloc_qreg_bits("dirty", 257);
    let mut parity = Some(BorrowedQReg::Owned(c.alloc_qreg("parity")));
    let initial = [
        ids(&cb),
        ids(&dirty),
        ids(std::slice::from_ref(parity.as_deref().unwrap())),
    ];
    c.x(parity.as_deref().unwrap());
    midq_field_neg(&mut c, parity.as_deref().unwrap(), &cb, &dirty);
    c.x(parity.as_deref().unwrap());
    assert!(pack_parity(&mut c, &cb, 248, &mut parity));
    assert!(parity.is_none());
    // Force the released ID into a different live owner until reconstruction.
    let reuse = c.alloc_qreg("occupied former parity");
    c.x(&reuse);
    let mid = c.b.ops.len();
    restore_parity(&mut c, &cb, &mut parity);
    assert_ne!(parity.as_deref().unwrap().id(), reuse.id());
    c.x(&reuse);
    c.zero_and_free(reuse);
    c.x(parity.as_deref().unwrap());
    midq_field_neg(&mut c, parity.as_deref().unwrap(), &cb, &dirty);
    c.x(parity.as_deref().unwrap());
    let restored = [
        ids(&cb),
        ids(&dirty),
        ids(std::slice::from_ref(parity.as_deref().unwrap())),
    ];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut cases = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for first in (0..values.len() * 2).step_by(64) {
            sim.clear_for_shot();
            let len = 64.min(values.len() * 2 - first);
            let mask = u64::MAX >> (64 - len);
            for lane in 0..len {
                write(&mut sim, &initial[0], lane, values[(first + lane) / 2]);
                write(&mut sim, &initial[1], lane, p - U256::from(first + lane));
                write(&mut sim, &initial[2], lane, U256::from((first + lane) % 2));
            }
            apply(&mut sim, &c.b.ops[..mid], mask);
            for lane in 0..len {
                let v = values[(first + lane) / 2];
                assert_eq!(
                    read(&sim, &initial[0], lane),
                    if (first + lane) % 2 == 0 { p - v } else { v }
                );
            }
            apply(&mut sim, &c.b.ops[mid..], mask);
            clean(&sim, &restored, mask);
            for lane in 0..len {
                assert_eq!(read(&sim, &restored[0], lane), values[(first + lane) / 2]);
                assert_eq!(read(&sim, &restored[1], lane), p - U256::from(first + lane));
                assert_eq!(
                    read(&sim, &restored[2], lane),
                    U256::from((first + lane) % 2)
                );
                cases += 1;
            }
        }
    }
    eprintln!("SIGN_PARITY PASS {cases} full-width boundary cases; zero, powers, max248, dirty donor, fresh ownership, phase, pre-reset");
}

fn rejected_sign_motion_witness() {
    use crate::point_add::trailmix_port::rfold_mbu::mod_mul_rfold_mbu;
    let r = U256::from(0x1000003d1u64);
    let p = U256::MAX - r + U256::from(1);
    let high = (U256::from(1) << 255) + (U256::from(1) << 72) - U256::from(1);
    let original = p - high;
    let wanted = (U256::from(1) << 73) + r - U256::from(2);
    for moved in [false, true] {
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("mul.a", 257);
        let b = c.alloc_qreg_bits("mul.b", 257);
        let out = c.alloc_qreg_bits("mul.out", 257);
        let sign = c.alloc_qreg("mul.sign");
        let data = [
            ids(&a),
            ids(&b),
            ids(&out),
            ids(std::slice::from_ref(&sign)),
        ];
        if moved {
            midq_field_neg(&mut c, &sign, &a, &b);
        }
        mod_mul_rfold_mbu(&mut c, &out, &a, &b);
        if !moved {
            midq_field_neg(&mut c, &sign, &out, &a);
        }
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        for mode in 0..4 {
            let mut rng = Measurements::new(mode);
            let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
            write(&mut sim, &data[0], 0, original);
            write(&mut sim, &data[1], 0, U256::from(2));
            write(&mut sim, &data[3], 0, U256::from(1));
            if moved {
                // This intentionally invalid candidate may also fail phase cleanup.
                sim.apply_iter(c.b.ops.iter());
                assert_eq!(read(&sim, &data[2], 0), r - U256::from(2));
                assert_ne!(read(&sim, &data[2], 0), wanted);
            } else {
                apply(&mut sim, &c.b.ops, 1);
                assert_eq!(read(&sim, &data[2], 0), wanted);
            }
        }
    }
    eprintln!("SIGN_MOTION REJECTED: real multiplier gives N(M(a,2))=2^73+R-2 but M(N(a),2)=R-2 for a=p-(2^255+2^72-1), R=2^32+977; original clean, new classical failure");
}

fn full_tail(checkpoint: bool) {
    std::env::set_var("MIDQ_TAIL_CHECKPOINT", if checkpoint { "1" } else { "0" });
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", 85);
    let mut b = c.alloc_qreg_bits("b", 85);
    let mut ca = c.alloc_qreg_bits("ca", 257);
    let mut cb = c.alloc_qreg_bits("cb", 248);
    let mut q = c.alloc_qreg_bits("q", 18);
    let mut counter = c.alloc_qreg_bits("counter", 8);
    let mut parity = Some(BorrowedQReg::Owned(c.alloc_qreg("parity")));
    let sign = c.alloc_qreg("input.sign");
    let initial = [
        ids(&a),
        ids(&b),
        ids(&ca),
        ids(&cb),
        ids(&q),
        ids(&counter),
        ids(std::slice::from_ref(parity.as_deref().unwrap())),
        ids(std::slice::from_ref(&sign)),
    ];
    let state = midq_tail_forward_with_parity(
        &mut c,
        &mut a,
        &mut b,
        &mut ca,
        &mut cb,
        &mut q,
        &mut counter,
        &mut parity,
    );
    assert!(state.packed_parity && parity.is_none());
    let mid = c.b.ops.len();
    let result = ids(&ca);
    let tape = ids(&state.tape);
    midq_tail_backward_with_parity(
        &mut c,
        &mut a,
        &mut b,
        &mut ca,
        &mut cb,
        &mut q,
        &mut counter,
        &mut parity,
        state,
    );
    let restored = [
        ids(&a),
        ids(&b),
        ids(&ca),
        ids(&cb),
        ids(&q),
        ids(&counter),
        ids(std::slice::from_ref(parity.as_deref().unwrap())),
        initial[7].clone(),
    ];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let mut cases = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        // First 64 are nonterminal; the rest cover every terminal counter/sign/parity.
        for first in (0..1088).step_by(64) {
            sim.clear_for_shot();
            let mut rows = Vec::new();
            let mut expected = Vec::new();
            for lane in 0..64 {
                let n = first + lane;
                let terminal = n >= 64;
                let par = n % 2;
                let sgn = (n / 2) % 2;
                let count = if terminal { (n - 64) / 4 } else { 0 };
                let av = if terminal {
                    0
                } else {
                    [1usize, 2, 3, 4, 5, 6, 7, 8][n / 4 % 8]
                };
                let v = (U256::from(0x123456789abcdefu64) << 128) + U256::from(n + 1);
                let row = [
                    U256::from(av),
                    U256::from(1),
                    p - U256::from(av) * v,
                    v,
                    U256::ZERO,
                    U256::from(count),
                    U256::from(par),
                    U256::from(sgn),
                ];
                for i in 0..8 {
                    write(&mut sim, &initial[i], lane, row[i]);
                }
                expected.push(if par == 1 { v } else { p - v });
                rows.push(row);
            }
            apply(&mut sim, &c.b.ops[..mid], u64::MAX);
            for lane in 0..64 {
                assert_eq!(
                    read(&sim, &result, lane),
                    expected[lane],
                    "endpoint checkpoint={checkpoint}, batch={first}, lane={lane}"
                );
                if first != 0 {
                    assert_eq!(read(&sim, &tape[..8], lane), rows[lane][5]);
                }
            }
            apply(&mut sim, &c.b.ops[mid..], u64::MAX);
            clean(&sim, &restored, u64::MAX);
            for lane in 0..64 {
                for i in 0..8 {
                    assert_eq!(
                        read(&sim, &restored[i], lane),
                        rows[lane][i],
                        "restore register{i}"
                    );
                }
                cases += 1;
            }
        }
    }
    eprintln!("SIGN_FULL_TAIL PASS {cases} cases checkpoint={checkpoint}; both parities, sign spectator, even/odd handoff, all terminal counter states, 224 rounds, reverse, phase/pre-reset");
}

pub(super) fn run() {
    for (name, value) in [
        ("MIDQ_PACK_PZ_PARITY", "1"),
        ("MIDQ_COUNTER_TAPE", "1"),
        ("MIDQ_QUOTIENT_CODE", "1"),
        ("MIDQ_DIRTY_CONST", "1"),
        ("MIDQ_DIRTY_FIELD_NEG", "1"),
        ("MIDQ_COMPACT_CONST_CARRY", "1"),
        ("MIDQ_MEASURE_PREDICATE", "1"),
        ("MIDQ_MEASURE_GATE_AND", "1"),
        ("MIDQ_MEASURE_COMPARE", "1"),
        ("MIDQ_CHUNK_COMPARE", "1"),
        ("MIDQ_CHUNKED_PREFIX", "1"),
        ("MIDQ_CHUNK_COMPARE_QCAP", "1019"),
        ("MIDQ_PREFIX_QCAP", "1019"),
    ] {
        std::env::set_var(name, value);
    }
    value_equivariance();
    parity_codec();
    rejected_sign_motion_witness();
    full_tail(false);
    full_tail(true);
}
