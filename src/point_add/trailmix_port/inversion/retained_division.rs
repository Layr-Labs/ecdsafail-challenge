//! Exact shift bookkeeping with retained original operand bit lengths.
use super::*;

fn add_update(c: &mut Circuit, gate: &QReg, a: &[&QReg], b: &[&QReg], subtract: bool) {
    use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_hybrid_add_refs;
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};
    let budget = env_usize("MIDQ_PZ_VENT_QCAP", 0);
    if budget != 0 {
        let vents = budget.saturating_sub(c.b.active_qubits as usize);
        if subtract { for bit in a { c.x(bit); } }
        controlled_hybrid_add_refs(c, gate, a, b, vents);
        if subtract { for bit in a { c.x(bit); } }
    } else if subtract {
        ctrl_sub(c, gate, a, b);
    } else {
        ctrl_add(c, gate, a, b);
    }
}

fn toggle_offset(
    c: &mut Circuit, pa: &[QReg], pb: &[QReg], shift: &[QReg],
    lo_a: usize, lo_b: usize, active: GateControl<'_>, offset: &QReg,
) {
    // shift = active * (pos_a - pos_b + lo_a - lo_b) - offset.
    // The low bit recovers offset independently of the shifted operand.
    with_peak_gate_control(c, active, |c, gate| {
        for bit in [&pa[0], &pb[0], &shift[0]] {
            c.ccx(gate, bit, offset);
        }
        if (lo_a ^ lo_b) & 1 != 0 {
            c.cx(gate, offset);
        }
    });
}

fn ctz_shift(
    c: &mut Circuit, q: &[QReg], shift: &[QReg], active: GateControl<'_>,
    carry: Option<&QReg>, inverse: bool,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{
        ctrl_add, ctrl_sub,
    };
    let t = c.alloc_qreg_bits("dg.ctz", shift.len());
    xor_const(c, &t, q.len());
    let rev: Vec<&QReg> = q.iter().rev().collect();
    bit_length_ctz(c, active, &rev, &t, true, carry);
    let sr: Vec<&QReg> = shift.iter().collect();
    let tr: Vec<&QReg> = t.iter().collect();
    with_ctz_gate_control(c, active, |c, gate| {
        if inverse { ctrl_add(c, gate, &sr, &tr); }
        else { ctrl_sub(c, gate, &sr, &tr); }
    });
    bit_length_ctz(c, active, &rev, &t, false, carry);
    xor_const(c, &t, q.len());
    for bit in t { c.zero_and_free(bit); }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn division_substep_retained_lengths(
    c: &mut Circuit, a: &[QReg], b: &[QReg], q: &[QReg],
    shift: &[QReg], offset: &QReg, active: GateControl<'_>,
    carry: Option<&QReg>, lo_a: usize, lo_b: usize, rot_bits: usize,
    inverse: bool,
) {
    let rb = rot_bits.min(shift.len());
    let ar: Vec<&QReg> = a.iter().collect();
    let br: Vec<&QReg> = b.iter().collect();
    if let GateControl::Hybrid(control) = active { control.release(c); }
    // B is unshifted at both external boundaries.
    let pb = clz_deposit_a(c, b, shift.len(), lo_b);
    if inverse {
        ctz_shift(c, q, shift, active, carry, true);
        rotate_left(c, b, &shift[..rb]);
        with_gate_control(c, active, |c, gate| {
            set_bit_at_s_gated(c, q, shift, gate);
            add_update(c, gate, &ar, &br, false);
        });
    }
    if let GateControl::Hybrid(control) = active { control.release(c); }
    let pa = clz_deposit_a(c, a, shift.len(), lo_a);
    let mask_shift = |c: &mut Circuit| {
        without_gate_control(c, active, |c| {
            clz_diff_positions(c, &pa, &pb, lo_a, lo_b, carry,
                |c, diff| with_peak_gate_control(c, active, |c, gate| {
                    for (bit, target) in diff.iter().zip(shift) {
                        c.ccx(gate, bit, target);
                    }
                }));
        });
    };
    if !inverse {
        mask_shift(c);
        rotate_left(c, b, &shift[..rb]);
    } else {
        toggle_offset(c, &pa, &pb, shift, lo_a, lo_b, active, offset);
        ctrl_inc(c, offset, shift);
        rotate_left(c, b, std::slice::from_ref(offset));
    }
    let less = c.alloc_qreg("dg.offr");
    narrow_lt(c, a, b, &less, lo_a);
    with_gate_control(c, active, |c, gate| c.ccx(gate, &less, offset));
    clear_narrow_lt(c, a, b, &less, lo_a);
    c.zero_and_free(less);
    if !inverse {
        rotate_right(c, b, std::slice::from_ref(offset));
        ctrl_dec(c, offset, shift);
        toggle_offset(c, &pa, &pb, shift, lo_a, lo_b, active, offset);
    } else {
        rotate_right(c, b, &shift[..rb]);
        mask_shift(c);
    }
    without_gate_control(c, active, |c| clz_undeposit_a(c, pa, a, lo_a));
    if !inverse {
        with_gate_control(c, active, |c, gate| {
            add_update(c, gate, &ar, &br, true);
            set_bit_at_s_gated(c, q, shift, gate);
        });
        rotate_right(c, b, &shift[..rb]);
    }
    without_gate_control(c, active, |c| clz_undeposit_a(c, pb, b, lo_b));
    if !inverse { ctz_shift(c, q, shift, active, carry, false); }
}

pub(super) mod tests {
    use super::*;
    use crate::circuit::{analyze_ops, Op};
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update}, Shake256};

    fn circuit(n: usize, lo_a: usize, lo_b: usize, compact: bool, inverse: bool)
        -> (Vec<Op>, Vec<QubitId>)
    {
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("a", n);
        let b = c.alloc_qreg_bits("b", n);
        let q = c.alloc_qreg_bits("q", n + 1);
        let shift = c.alloc_qreg_bits("shift", 5);
        let offset = c.alloc_qreg("offset");
        let gate = c.alloc_qreg("active");
        let carry = c.alloc_qreg("carry");
        let ids = a.iter().chain(&b).chain(&q).chain([&gate])
            .map(|q| QubitId(q.id().into())).collect();
        let active = GateControl::Direct(&gate);
        if compact {
            division_substep_retained_lengths(&mut c, &a, &b, &q, &shift,
                &offset, active, Some(&carry), lo_a, lo_b, 5, inverse);
        } else if inverse {
            multiply_substep_windowed(&mut c, &a, &b, &q, &shift,
                &offset, active, Some(&carry), lo_a, lo_b, 5);
        } else {
            division_substep_windowed(&mut c, &a, &b, &q, &shift,
                &offset, active, Some(&carry), lo_a, lo_b, 5);
        }
        (c.b.ops.clone(), ids)
    }

    fn run(ops: &[Op], ids: &[QubitId], inputs: &[usize]) -> Vec<usize> {
        let (nq, nb, _, _) = analyze_ops(ops.iter());
        let mut seed = Shake256::default();
        seed.update(b"midq-retained-lengths-component-v1");
        seed.update(&inputs[0].to_le_bytes());
        let mut rng = seed.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for (bit, &id) in ids.iter().enumerate() {
            for (shot, &value) in inputs.iter().enumerate() {
                *sim.qubit_mut(id) |= (((value >> bit) & 1) as u64) << shot;
            }
        }
        let mask = u64::MAX >> (64 - inputs.len());
        super::super::predicate_clear_selftest::checked_apply(&mut sim, ops, mask);
        assert_eq!(sim.phase & mask, 0, "phase mismatch");
        let output = (0..inputs.len()).map(|shot| ids.iter().enumerate()
            .fold(0usize, |value, (bit, &id)|
                value | (((sim.qubit(id) >> shot) & 1) as usize) << bit)).collect();
        for &id in ids { *sim.qubit_mut(id) = 0; }
        assert!(sim.qubits.iter().all(|v| v & mask == 0), "dirty scratch");
        output
    }

    pub(crate) fn retained_lengths_match_original() {
        std::env::remove_var("MIDQ_RETAIN_DIV_LENGTHS");
        std::env::remove_var("MIDQ_RETAIN_MUL_LENGTHS");
        std::env::set_var("TRAILMIX_Q_TARGET", "684");
        std::env::set_var("LOWQ_CLZ_DIFF_CONST_FOLD", "1");
        std::env::set_var("LOWQ_ONE_A_ELIM", "1");
        std::env::set_var("LOWQ_BORROW_PASSENGER_CARRY", "1");
        std::env::set_var("LOWQ_COMPACT_KGANC", "1");
        std::env::set_var("TRAILMIX_FUSE_DIV_CLZ_A", "1");
        std::env::set_var("MIDQ_CLZ_OFFSET_PARITY", "1");
        std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
        let mut checked = 0;
        for n in 3..=8 {
            for (lo_a, lo_b) in [(0, 0), (n / 2, (n - 2) / 2)] {
                let reference = circuit(n, lo_a, lo_b, false, false);
                let candidate = circuit(n, lo_a, lo_b, true, false);
                let inverse = circuit(n, lo_a, lo_b, true, true);
                let multiply = circuit(n, lo_a, lo_b, false, true);
                let mut inputs = Vec::new();
                for a in 1usize << lo_a..1usize << n {
                    for b in 1usize << lo_b..=a {
                        for active in 0..=1 {
                            // Prior accepted quotient bits lie above the next shift.
                            for prior in [0, 1 << n] {
                                inputs.push(a | (b << n) | (prior << (2 * n))
                                    | (active << (3 * n + 1)));
                            }
                        }
                    }
                }
                for batch in inputs.chunks(64) {
                    let expected = run(&reference.0, &reference.1, batch);
                    let got = run(&candidate.0, &candidate.1, batch);
                    assert_eq!(got, expected, "n={n}, windows={lo_a}/{lo_b}");
                    assert_eq!(run(&inverse.0, &inverse.1, &got), batch);
                    assert_eq!(run(&multiply.0, &multiply.1, &got), batch,
                        "original multiply differs from inverse division");
                    checked += batch.len();
                }
            }
        }
        eprintln!("RETAIN_DIV_LENGTHS PASS: {checked} value/phase/ancilla cases and inverses");
    }
}
