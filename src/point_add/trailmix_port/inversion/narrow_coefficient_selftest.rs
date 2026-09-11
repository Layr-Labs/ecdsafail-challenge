//! Differential storage tests using the original simulator, including every
//! reset before it can conceal a dirty overflow or carry.

use super::{midq_field_neg, midq_mod_signed_add_halve, midq_restore_endpoint_widths,
    predicate_clear_selftest::checked_apply};
use crate::circuit::{analyze_ops, QubitId};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut seed = Shake256::default();
        seed.update(b"midq-narrow-coefficients-v1");
        Self([Some(0), Some(255), Some(0x55), None][mode], seed.finalize_xof())
    }
}
impl XofReader for Measurements {
    fn read(&mut self, bytes: &mut [u8]) {
        if let Some(byte) = self.0 { bytes.fill(byte); } else { self.1.read(bytes); }
    }
}

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}
fn write<R: XofReader>(sim: &mut Simulator<R>, reg: &[QubitId], lane: usize, value: U256) {
    for (i, &q) in reg.iter().enumerate().take(256) {
        if value.bit(i) { *sim.qubit_mut(q) |= 1 << lane; }
    }
}
fn read<R: XofReader>(sim: &Simulator<R>, reg: &[QubitId], lane: usize) -> U256 {
    let mut value = U256::ZERO;
    for (i, &q) in reg.iter().enumerate() {
        let bit = sim.qubit(q) >> lane & 1;
        if i == 256 { assert_eq!(bit, 0, "persistent overflow"); }
        else if bit != 0 { value |= U256::from(1) << i; }
    }
    value
}

fn check(width: usize, kind: usize, cases: &[(U256, U256, bool)], mode: usize) -> (Vec<U256>, Vec<bool>) {
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("target", width);
    let source = c.alloc_qreg_bits("source", width);
    let sign = c.alloc_qreg("sign");
    let data = [ids(&target), ids(&source), ids(std::slice::from_ref(&sign))];
    if kind == 2 { midq_field_neg(&mut c, &sign, &target, &source); }
    else { midq_mod_signed_add_halve(&mut c, &target, &source, &sign, kind == 1); }
    let mid = c.b.ops.len();
    if kind == 2 { midq_field_neg(&mut c, &sign, &target, &source); }
    else { midq_mod_signed_add_halve(&mut c, &target, &source, &sign, kind == 0); }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut rng = Measurements::new(mode);
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    let mut out = Vec::new();
    let mut phases = Vec::new();
    for batch in cases.chunks(64) {
        sim.clear_for_shot();
        let mask = u64::MAX >> (64 - batch.len());
        for (lane, &(a, b, s)) in batch.iter().enumerate() {
            write(&mut sim, &data[0], lane, a);
            write(&mut sim, &data[1], lane, b);
            if s { *sim.qubit_mut(data[2][0]) |= 1 << lane; }
        }
        for ops in [&c.b.ops[..mid], &c.b.ops[mid..]] {
            checked_apply(&mut sim, ops, mask);
            for (i, &bits) in sim.qubits.iter().enumerate() {
                if !data.iter().any(|reg| reg.contains(&QubitId(i as u64))) {
                    assert_eq!(bits & mask, 0, "scratch {i}");
                }
            }
            for (lane, &(_, b, s)) in batch.iter().enumerate() {
                assert_eq!(read(&sim, &data[1], lane), b, "source restoration");
                assert_eq!(sim.qubit(data[2][0]) >> lane & 1, u64::from(s));
                let value = read(&sim, &data[0], lane);
                out.push(value);
                phases.push(sim.phase >> lane & 1 != 0);
            }
        }
    }
    (out, phases)
}

fn endpoint_overflow_edges() {
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let mut values = vec![U256::ZERO, U256::from(1), p-U256::from(1), p, U256::MAX];
    for i in 0..=32 { values.push(p + (U256::from(1) << i)); }
    for i in 1..=256 { values.push(p + U256::from(i)); }
    for width in [256, 257] {
        let mut c = Circuit::new();
        let mut value = c.alloc_qreg_bits("endpoint.value", width);
        let mut donor = c.alloc_qreg_bits("endpoint.donor", width);
        let sign = c.alloc_qreg("endpoint.sign");
        let probe = c.alloc_qreg("endpoint.payload_probe");
        let input = [ids(&value), ids(&donor), ids(std::slice::from_ref(&sign)), ids(std::slice::from_ref(&probe))];
        midq_restore_endpoint_widths(&mut c, &mut value, &mut donor);
        midq_field_neg(&mut c, &sign, &value, &donor);
        if super::payload_sign_loan::compact_padding() {
            super::payload_sign_loan::park_signed_high(&mut c, &mut value, &sign);
            super::payload_sign_loan::restore_signed_high(&mut c, &mut value, &sign);
        }
        let full = ids(&value);
        // A payload-sensitive observable distinguishes all 257 bits. The
        // high bit is meaningful for p-u when u>p and must remain live.
        c.cx(&value[256], &probe);
        c.cz(&value[256], &sign);
        let mid = c.b.ops.len();
        c.cz(&value[256], &sign);
        midq_field_neg(&mut c, &sign, &value, &donor);
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        for mode in 0..4 {
            let mut rng = Measurements::new(mode);
            let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
            let cases: Vec<_> = values.iter().flat_map(|&u| [false, true].map(|s| (u,s))).collect();
            for batch in cases.chunks(64) {
                sim.clear_for_shot();
                let mask = u64::MAX >> (64-batch.len());
                let dirty = (U256::from(1) << 255) + U256::from(123);
                for (lane, &(u,s)) in batch.iter().enumerate() {
                    write(&mut sim, &input[0], lane, u);
                    write(&mut sim, &input[1], lane, dirty);
                    if s { *sim.qubit_mut(input[2][0]) |= 1 << lane; }
                }
                checked_apply(&mut sim, &c.b.ops[..mid], mask);
                for (lane, &(u,s)) in batch.iter().enumerate() {
                    let high = u64::from(s && u>p);
                    let low = if s { p.wrapping_sub(u) } else { u };
                    assert_eq!(read(&sim, &full[..256], lane), low);
                    assert_eq!(sim.qubit(full[256]) >> lane & 1, high, "p-u bit 256");
                    assert_eq!(sim.qubit(input[3][0]) >> lane & 1, high, "payload high-bit observable");
                    assert_eq!(sim.phase >> lane & 1, high, "payload phase observable");
                }
                checked_apply(&mut sim, &c.b.ops[mid..], mask);
                assert_eq!(sim.phase & mask, 0);
                let keep: Vec<_> = input.iter().flatten().copied().collect();
                for (i,&bits) in sim.qubits.iter().enumerate() {
                    if !keep.contains(&QubitId(i as u64)) { assert_eq!(bits & mask, 0, "endpoint scratch {i}"); }
                }
                for (lane, &(u,s)) in batch.iter().enumerate() {
                    assert_eq!(read(&sim, &full, lane), u, "full-width inverse endpoint");
                    assert_eq!(read(&sim, &input[1], lane), dirty);
                    assert_eq!(sim.qubit(input[2][0]) >> lane & 1, u64::from(s));
                    assert_eq!(sim.qubit(input[3][0]) >> lane & 1, u64::from(s && u>p));
                }
            }
        }
    }
    eprintln!("NARROW_ENDPOINT_OVERFLOW PASS {} values including u>=p x 2 signs x 4 streams x 2 entry layouts; full 257-bit p-u, payload bit/phase observable, reverse, pre-reset, scratch", values.len());
}

pub(crate) fn run() {
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_DIRTY_FIELD_NEG", "1");
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "1");
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    std::env::set_var("MIDQ_CHUNK_COMPARE", "1");
    endpoint_overflow_edges();
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let f = U256::from(0x1000003d1u64);
    let mut values = vec![U256::ZERO, U256::from(1), U256::from(2), f - U256::from(1), f,
        f + U256::from(1), p / U256::from(2), p / U256::from(2) + U256::from(1),
        p - U256::from(1), p - U256::from(2)];
    for i in [3, 16, 32, 64, 127, 128, 191, 224, 254, 255] {
        values.push(U256::from(1) << i);
        values.push(p - (U256::from(1) << i));
    }
    let mut cases = Vec::new();
    for &a in &values { for &b in &values { for sign in [false, true] { cases.push((a,b,sign)); } } }
    let mut seed = Measurements::new(3);
    for i in 0..1024 {
        let mut a = [0; 32]; let mut b = [0; 32];
        seed.read(&mut a); seed.read(&mut b);
        cases.push((U256::from_le_bytes(a) % p, U256::from_le_bytes(b) % p, i & 1 != 0));
    }
    let test_rotated = std::env::var_os("MIDQ_ROTATED_HALVES_SELFTEST").is_some();
    for kind in 0..3 {
        let mut cases = cases.clone();
        if test_rotated && kind < 2 {
            for a in [U256::MAX, p, p + U256::from(1), p + U256::from(2),
                f / U256::from(2), f / U256::from(2) - U256::from(1)] {
                for b in [U256::ZERO, U256::from(1), f, p, U256::MAX] {
                    for sign in [false, true] { cases.push((a, b, sign)); }
                }
            }
        }
        if test_rotated { std::env::set_var("MIDQ_ROTATED_HALVES", "0"); }
        // The inherited pseudo-Mersenne carry cleanup is approximate near
        // small edge operands. Record that support rather than asserting that
        // the baseline implements an exact field cell on arbitrary pairs.
        let (_, allowed_phase) = check(257, kind, &cases, 1);
        for mode in 0..4 {
            if test_rotated { std::env::set_var("MIDQ_ROTATED_HALVES", "0"); }
            let wide = check(257, kind, &cases, mode);
            if test_rotated { std::env::set_var("MIDQ_ROTATED_HALVES", "1"); }
            let narrow = check(256, kind, &cases, mode);
            assert_eq!(wide.0, narrow.0, "storage equivalence kind={kind} mode={mode}");
            if mode <= 1 { assert_eq!(wide.1, narrow.1, "forced-measurement phase equivalence"); }
            for ((old, new), allowed) in wide.1.iter().zip(&narrow.1).zip(&allowed_phase) {
                assert!(!(*old || *new) || *allowed, "new phase-support failure kind={kind} mode={mode}");
            }
        }
        eprintln!("NARROW_COEFFICIENT kind={kind} inherited_edge_phase_positions={}", allowed_phase.iter().filter(|&&x| x).count());
    }
    if test_rotated { eprintln!("ROTATED_HALVES PASS: differential original/new cells including noncanonical words, both signs and directions"); }
    eprintln!("NARROW_COEFFICIENT_SELFTEST PASS {} cases x 3 operations x 4 measurement streams x 2 widths, differential outputs at forward/reverse checkpoints, source/sign/phase-support/scratch/pre-reset", cases.len());
}
