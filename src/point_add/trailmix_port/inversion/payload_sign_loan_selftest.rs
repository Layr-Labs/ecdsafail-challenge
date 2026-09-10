use super::super::{midq_field_neg, predicate_clear_selftest::checked_apply};
use super::*;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::point_add::trailmix_port::rfold_mbu::{mod_mul_rfold_mbu, mod_mul_rfold_mbu_undo};
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
        hash.update(b"payload-sign-loan-measurements-v1");
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
fn write<R: XofReader>(s: &mut Simulator<R>, reg: &[QubitId], lane: usize, value: U256) {
    for (i, &q) in reg.iter().enumerate().take(256) {
        if value.bit(i) {
            *s.qubit_mut(q) |= 1 << lane;
        }
    }
}
fn read<R: XofReader>(s: &Simulator<R>, reg: &[QubitId], lane: usize) -> U256 {
    let mut v = U256::ZERO;
    for (i, &q) in reg.iter().enumerate() {
        let bit = s.qubit(q) >> lane & 1;
        if i < 256 {
            v |= U256::from(bit) << i;
        } else {
            assert_eq!(bit, 0, "canonical output high bit");
        }
    }
    v
}
fn apply<R: XofReader>(s: &mut Simulator<R>, ops: &[Op], mask: u64) {
    checked_apply(s, ops, mask);
    assert_eq!(s.phase & mask, 0, "phase");
}
fn clean<R: XofReader>(s: &Simulator<R>, live: &[Vec<QubitId>], mask: u64) {
    for (i, &v) in s.qubits.iter().enumerate() {
        if !live.iter().any(|r| r.contains(&QubitId(i as u64))) {
            assert_eq!(v & mask, 0, "scratch {i}");
        }
    }
}
fn assert_unused(ops: &[Op], q: &QReg) {
    let id = QubitId(q.id().into());
    for op in ops {
        assert!(
            op.q_target != id && op.q_control1 != id && op.q_control2 != id,
            "multiplier accessed high tag: {op:?}"
        );
    }
}
fn field_cases() -> Vec<[U256; 2]> {
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let mut hash = Shake256::default();
    hash.update(b"payload-sign-loan-field-inputs-v1");
    let mut rng = hash.finalize_xof();
    (0..64)
        .map(|_| {
            let mut bytes = [0; 32];
            rng.read(&mut bytes);
            let a = U256::from_le_bytes(bytes) % (p - U256::from(1)) + U256::from(1);
            rng.read(&mut bytes);
            let b = U256::from_le_bytes(bytes) % (p - U256::from(1)) + U256::from(1);
            [a, b]
        })
        .collect()
}

fn owned_slot() {
    std::env::set_var("MIDQ_PAYLOAD_SIGN_LOAN", "1");
    let mut c = Circuit::new();
    let mut b = c.alloc_qreg_bits("b", 257);
    let mut sign = Some(c.alloc_qreg("sign"));
    let old_high = b[256].id();
    let old_sign = sign.as_ref().unwrap().id();
    let original = [ids(&b), ids(std::slice::from_ref(sign.as_ref().unwrap()))];
    let before = c.b.active_qubits;
    assert!(begin(&mut c, &mut b, &mut sign));
    assert_eq!(c.b.active_qubits, before - 1);
    assert!(sign.is_none());
    assert_eq!(b[256].id(), old_sign);
    let canary = c.alloc_qreg("occupied.old.high");
    assert_eq!(canary.id(), old_high);
    c.x(&canary);
    finish(&mut b, &mut sign, true);
    assert_eq!(sign.as_ref().unwrap().id(), old_sign);
    let new_high = c.alloc_qreg("fresh.high");
    assert_ne!(new_high.id(), old_high);
    b.push(new_high);
    c.x(&canary);
    c.zero_and_free(canary);
    let restored = [ids(&b), ids(std::slice::from_ref(sign.as_ref().unwrap()))];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nq = nq.max(restored.iter().flatten().map(|q| q.0 + 1).max().unwrap());
    let mut rng = Measurements::new(3);
    let mut s = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for lane in 0..64 {
        write(
            &mut s,
            &original[0],
            lane,
            (U256::from(1) << lane) + U256::from(lane),
        );
        write(&mut s, &original[1], lane, U256::from(lane % 2));
    }
    apply(&mut s, &c.b.ops, u64::MAX);
    clean(&s, &restored, u64::MAX);
    for lane in 0..64 {
        assert_eq!(
            read(&s, &restored[0], lane),
            (U256::from(1) << lane) + U256::from(lane)
        );
        assert_eq!(read(&s, &restored[1], lane), U256::from(lane % 2));
    }
    eprintln!("PAYLOAD_SIGN_OWNERSHIP PASS 64 cases: one fewer live wire, original sign ID, occupied former padding, fresh canonical replacement, phase/pre-reset");
}

fn tagged_multiplier() {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("a", 257);
    let b = c.alloc_qreg_bits("b", 257);
    let result = c.alloc_qreg_bits("result", 257);
    let inputs = [ids(&a), ids(&b)];
    let start = c.b.ops.len();
    mod_mul_rfold_mbu(&mut c, &result, &a, &b);
    let middle = c.b.ops.len();
    mod_mul_rfold_mbu_undo(&mut c, &result, &a, &b);
    assert_unused(&c.b.ops[start..], &b[256]);
    let out = ids(&result);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let cases = field_cases();
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut s = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for offset in [0usize, 32] {
            s.clear_for_shot();
            for lane in 0..64 {
                let [av, bv] = cases[offset + lane / 2];
                write(&mut s, &inputs[0], lane, av);
                write(&mut s, &inputs[1], lane, bv);
                if lane % 2 == 1 {
                    *s.qubit_mut(inputs[1][256]) |= 1 << lane;
                }
            }
            apply(&mut s, &c.b.ops[..middle], u64::MAX);
            for lane in 0..64 {
                let [av, bv] = cases[offset + lane / 2];
                assert_eq!(read(&s, &out, lane), av.mul_mod(bv, p));
            }
            apply(&mut s, &c.b.ops[middle..], u64::MAX);
            clean(&s, &inputs, u64::MAX);
            for lane in 0..64 {
                let [av, bv] = cases[offset + lane / 2];
                assert_eq!(read(&s, &inputs[0], lane), av);
                assert_eq!(read(&s, &inputs[1][..256], lane), bv);
                assert_eq!(s.qubit(inputs[1][256]) >> lane & 1, (lane % 2) as u64);
                checked += 1;
            }
        }
    }
    eprintln!("PAYLOAD_SIGN_MULTIPLIER PASS {checked} full-width cases: tag0/tag1, actual forward+undo, coefficient donor/value/phase/pre-reset, structural no-read proof");
}

fn payload(loan: bool, cancel: bool) {
    std::env::set_var("MIDQ_PAYLOAD_SIGN_LOAN", if loan { "1" } else { "0" });
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("inverse", 257);
    let mut b = c.alloc_qreg_bits("numerator", 257);
    let mut sign = Some(c.alloc_qreg("sign"));
    let witness = c.alloc_qreg_bits(if cancel { "lambda" } else { "denominator" }, 257);
    let input = [
        ids(&a),
        ids(&b),
        ids(std::slice::from_ref(sign.as_ref().unwrap())),
        ids(&witness),
    ];
    let old_sign = sign.as_ref().unwrap().id();
    let mut lambda_ghosts = Vec::new();
    let mut denominator = None;
    if cancel {
        for q in &witness {
            lambda_ghosts.push(c.hmr_ghost(q));
        }
        for q in witness {
            c.zero_and_free(q);
        }
    } else {
        denominator = Some(witness);
    }
    let loaned = begin(&mut c, &mut b, &mut sign);
    assert_eq!(loaned, loan);
    let result = c.alloc_qreg_bits("result", 257);
    let start = c.b.ops.len();
    mod_mul_rfold_mbu(&mut c, &result, &a, &b);
    assert_unused(&c.b.ops[start..], &b[256]);
    midq_field_neg(&mut c, control(&b, &sign), &result, &a);
    let forward = c.b.ops.len();
    let result_ids = ids(&result);
    let restored;
    if cancel {
        for (g, q) in lambda_ghosts.into_iter().zip(result.iter()) {
            c.resolve_ghost(g, q);
        }
        midq_field_neg(&mut c, control(&b, &sign), &result, &a);
        let start = c.b.ops.len();
        mod_mul_rfold_mbu_undo(&mut c, &result, &a, &b);
        assert_unused(&c.b.ops[start..], &b[256]);
        finish(&mut b, &mut sign, loaned);
        for q in result {
            c.zero_and_free(q);
        }
        if loaned {
            b.push(c.alloc_qreg("restored.high"));
        }
        restored = vec![
            ids(&a),
            ids(&b),
            ids(std::slice::from_ref(sign.as_ref().unwrap())),
        ];
    } else {
        finish(&mut b, &mut sign, loaned);
        let mut ghosts = Vec::new();
        for q in &b {
            ghosts.push(c.hmr_ghost(q));
        }
        assert_eq!(ghosts.len(), if loaned { 256 } else { 257 });
        for q in b {
            c.zero_and_free(q);
        }
        let b_new = c.alloc_qreg_bits("restored.numerator", 257);
        let denominator = denominator.as_ref().unwrap();
        mod_mul_rfold_mbu(&mut c, &b_new, &result, denominator);
        for (g, q) in ghosts.into_iter().zip(b_new.iter()) {
            c.resolve_ghost(g, q);
        }
        restored = vec![
            ids(&a),
            ids(&b_new),
            ids(std::slice::from_ref(sign.as_ref().unwrap())),
            ids(denominator),
            result_ids.clone(),
        ];
    }
    assert_eq!(sign.as_ref().unwrap().id(), old_sign);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let cases = field_cases();
    let mut checked = 0;
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut s = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for offset in [0usize, 32] {
            s.clear_for_shot();
            let mut expected = Vec::new();
            for lane in 0..64 {
                let [av, bv] = cases[offset + lane / 2];
                let sign_value = lane % 2;
                let raw = av.mul_mod(bv, p);
                let product = if sign_value == 0 { raw } else { p - raw };
                let inv = av.inv_mod(p).unwrap();
                let x = if sign_value == 0 { inv } else { p - inv };
                for (reg, val) in input.iter().zip([
                    av,
                    bv,
                    U256::from(sign_value),
                    if cancel { product } else { x },
                ]) {
                    write(&mut s, reg, lane, val);
                }
                expected.push([av, bv, U256::from(sign_value), x, product]);
            }
            // A lambda ghost is not yet resolved at this boundary in cancel.
            checked_apply(&mut s, &c.b.ops[..forward], u64::MAX);
            for lane in 0..64 {
                assert_eq!(read(&s, &result_ids, lane), expected[lane][4]);
            }
            apply(&mut s, &c.b.ops[forward..], u64::MAX);
            clean(&s, &restored, u64::MAX);
            for lane in 0..64 {
                for (i, reg) in restored.iter().enumerate() {
                    assert_eq!(read(&s, reg, lane), expected[lane][i]);
                }
                checked += 1;
            }
        }
    }
    eprintln!("PAYLOAD_SIGN_GHOST PASS {checked} cases loan={loan} cancel={cancel}: actual multiplication/reconstruction, original negation positions, sign/donor/numerator restored, phase/pre-reset");
}

pub(super) fn run() {
    for (key, val) in [
        ("MIDQ_DIRTY_CONST", "1"),
        ("MIDQ_DIRTY_FIELD_NEG", "1"),
        ("MIDQ_COMPACT_CONST_CARRY", "1"),
        ("MIDQ_OUTER_DIRTY_CONST", "1"),
        ("MIDQ_MEASURE_COMPARE", "1"),
        ("MIDQ_MEASURE_PREDICATE", "1"),
        ("MIDQ_MEASURE_GATE_AND", "1"),
        ("MIDQ_CHUNK_COMPARE", "1"),
        ("MIDQ_CHUNKED_PREFIX", "1"),
        ("MIDQ_OUTER_VENT_QCAP", "1018"),
        ("MIDQ_PZ_VENT_QCAP", "1018"),
        ("MIDQ_PREFIX_QCAP", "1018"),
        ("MIDQ_CHUNK_COMPARE_QCAP", "1018"),
    ] {
        std::env::set_var(key, val);
    }
    owned_slot();
    tagged_multiplier();
    for loan in [false, true] {
        for cancel in [false, true] {
            payload(loan, cancel);
        }
    }
}
