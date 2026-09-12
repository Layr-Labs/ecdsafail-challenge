//! Shared full framed iteration, scoped to exact nonterminal fixed-q32 PZ.
//! No production driver activation is installed by this component candidate.
use super::*;

/// Raw -> framed. The caller supplies zero phi/R and enough physical B lanes.
pub(crate) fn enter(
    c: &mut Circuit,
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    phi: &[QReg],
    role: &QReg,
) {
    borrow_compare_refs(
        c,
        &ca.iter().collect::<Vec<_>>(),
        &cb.iter().collect::<Vec<_>>(),
        role,
    );
    d_alignment_prep::frame_xor(c, q, role, phi);
    rotate_left(c, b, phi);
}

/// Framed -> raw. phi/R are cleared; allocation/free remain caller-owned.
pub(crate) fn exit(
    c: &mut Circuit,
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    phi: &[QReg],
    role: &QReg,
) {
    rotate_right(c, b, phi);
    d_alignment_prep::frame_xor(c, q, role, phi);
    clear_borrow_compare_refs(
        c,
        &ca.iter().collect::<Vec<_>>(),
        &cb.iter().collect::<Vec<_>>(),
        role,
    );
}

fn swap(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    role: &QReg,
) {
    let source = if prefix_popcount::enabled(counter) {
        &counter[..prefix_popcount::BITS]
    } else {
        q
    };
    let zero = c.alloc_qreg("d_align.swap.qzero");
    or_is_zero(c, source, &zero);
    for (a, b) in a.iter().zip(b) {
        c.cswap(&zero, a, b);
    }
    for (a, b) in ca.iter().zip(cb) {
        c.cswap(&zero, a, b);
    }
    c.cx(&zero, parity);
    c.cx(&zero, role);
    clear_zero_predicate(c, source, &zero, false);
    c.zero_and_free(zero);
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn step(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    s_rot: &[QReg],
    offset: &QReg,
    carry: Option<&QReg>,
    phi: &[QReg],
    role: &QReg,
    i: usize,
    inverse: bool,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{
        reg_los, reg_widths, shift_bounds,
    };
    assert!(prefix_no_terminal_eligible(i) && lowq_hybrid_gate_hold_enabled());
    assert!(!lowq_inline_active_enabled() && !lowq_recompute_gate_predicate_enabled());
    assert_eq!(qretain::fixed_width(), Some(32));
    assert_eq!(q.len(), 32);
    assert_eq!(s_rot.len(), 5);
    assert_eq!(phi.len(), 5);
    let (wa, wb, wca, wcb, _) = reg_widths(i);
    let n = trailmix_ab_width(wa.max(wb));
    let (pa, pb, _, _, _) = reg_widths(i.saturating_sub(1));
    let previous = trailmix_ab_width(pa.max(pb));
    let v = n.max(previous);
    assert_eq!(ca.len(), trailmix_cacb_width(wca.max(wcb)));
    assert_eq!(cb.len(), ca.len());
    let (_, _, lca, lcb, _) = reg_los(i);
    let (_, sm) = shift_bounds(i);
    let rb = (usize::BITS - sm.max(1).leading_zeros()) as usize;
    if !inverse {
        shrunken_pz_resize(c, a, v, "A");
        shrunken_pz_resize(c, b, v, "B");
        d_alignment_prep::apply_profile(c, a, b, ca, cb, q, phi, role, s_rot, offset, false);
        shrunken_pz_resize(c, a, n, "A");
        shrunken_pz_resize(c, b, n, "B");
        let active = compute_active(c, &[]);
        if prefix_popcount::enabled(counter) {
            prefix_popcount::update(c, counter, role, &active, false);
        }
        let gate = HybridGateControl::new(&active, role);
        multiply_substep_windowed(
            c,
            ca,
            cb,
            q,
            s_rot,
            offset,
            GateControl::Hybrid(&gate),
            carry,
            lca,
            lcb,
            rb,
        );
        gate.release(c);
        c.x(role);
        let gate = HybridGateControl::new(&active, role);
        with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
            retained_division::add_update(
                c,
                g,
                &a.iter().collect::<Vec<_>>(),
                &b.iter().collect::<Vec<_>>(),
                true,
            );
            set_bit_at_s_gated(c, q, phi, g);
        });
        gate.release(c);
        swap(c, a, b, ca, cb, q, counter, parity, role);
        uncompute_active(c, &[], &active);
        c.zero_and_free(active);
    } else {
        // Output after original forward i fits n, even if the caller retained
        // extra zero lanes from the subsequent reverse iteration.
        shrunken_pz_resize(c, a, n, "A");
        shrunken_pz_resize(c, b, n, "B");
        swap(c, a, b, ca, cb, q, counter, parity, role);
        let active = compute_active(c, &[]);
        let gate = HybridGateControl::new(&active, role);
        with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
            set_bit_at_s_gated(c, q, phi, g);
            retained_division::add_update(
                c,
                g,
                &a.iter().collect::<Vec<_>>(),
                &b.iter().collect::<Vec<_>>(),
                false,
            );
        });
        gate.release(c);
        c.x(role);
        let gate = HybridGateControl::new(&active, role);
        multiply_substep_windowed_inv(
            c,
            ca,
            cb,
            q,
            s_rot,
            offset,
            GateControl::Hybrid(&gate),
            carry,
            lca,
            lcb,
            rb,
        );
        gate.release(c);
        if prefix_popcount::enabled(counter) {
            prefix_popcount::update(c, counter, role, &active, true);
        }
        uncompute_active(c, &[], &active);
        c.zero_and_free(active);
        shrunken_pz_resize(c, a, v, "A");
        shrunken_pz_resize(c, b, v, "B");
        d_alignment_prep::apply_profile(c, a, b, ca, cb, q, phi, role, s_rot, offset, true);
        // The inverse PREP image is the previous forward framed boundary.
        shrunken_pz_resize(c, a, previous, "A");
        shrunken_pz_resize(c, b, previous, "B");
    }
}

#[path = "d_alignment_iteration_selftest.rs"]
mod checks;
pub(crate) fn selftest() {
    checks::run();
}
