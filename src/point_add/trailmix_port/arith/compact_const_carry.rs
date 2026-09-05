//! Form carry XOR addend-control in the carry itself, restoring it after use.
use super::{cbit, xor_carries_ctrl_refs};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

pub(super) fn add(
    circ: &mut Circuit, ctrl: &QReg, a: &[&QReg], constant: &[u8], dirty: &[&QReg],
) {
    let n = a.len();
    assert!(n >= 2 && dirty.len() >= n - 1);
    let previous = circ.push_section("gidney_cadd");
    let mut ghosts = Vec::with_capacity(n - 1);
    let mut carry = circ.alloc_qreg("gcc_cy");
    for i in 0..n - 1 {
        let next = circ.alloc_qreg("gcc_carry");
        circ.cx(&carry, a[i]);
        if cbit(constant, i) { circ.cx(ctrl, &carry); }
        circ.ccx(a[i], &carry, &next);
        if cbit(constant, i) { circ.cx(ctrl, &carry); }
        circ.cx(&carry, &next);
        circ.cx(&next, dirty[i]);
        if cbit(constant, i) { circ.cx(ctrl, a[i]); }
        if i > 0 { ghosts.push(circ.hmr_ghost(&carry)); }
        circ.zero_and_free(carry);
        carry = next;
    }
    if cbit(constant, n - 1) { circ.cx(ctrl, a[n - 1]); }
    circ.cx(&carry, a[n - 1]);
    ghosts.push(circ.hmr_ghost(&carry));
    circ.zero_and_free(carry);
    for (ghost, &bit) in ghosts.iter_mut().zip(dirty) {
        circ.ghost_xor_z(ghost, bit);
    }
    for &bit in a { circ.x(bit); }
    xor_carries_ctrl_refs(circ, ctrl, a, constant, dirty);
    for &bit in a { circ.x(bit); }
    for (mut ghost, &bit) in ghosts.into_iter().zip(dirty) {
        circ.ghost_xor_z(&mut ghost, bit);
        circ.close_ghost(ghost);
    }
    circ.pop_section(&previous);
}
