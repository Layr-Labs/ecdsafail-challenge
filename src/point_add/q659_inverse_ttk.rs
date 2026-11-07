// Substitute for `inverse_virtual_digit` inside q659_length_pilot.rs. Uses
// the existing `cell`, `literal`, `Roles`, and `B` in that module. The most
// expensive multi-control writes in v2 are reduced to one shared mask plus
// an ancilla-free controlled TTK addition. The sign is a spectator.
fn inverse_compare_ttk_digit(b: &mut B, q: &[QubitId], t: &[QubitId], r: Roles,
                             first: usize, dirty: &[QubitId]) -> Vec<G> {
    assert!(first < 128 && q.len() == 128 && t.len() == 129 && !dirty.is_empty());
    b.begin();
    for &wire in t { b.x(wire); }
    for i in first..127 {
        let incoming = if i == first { r.work } else { q[i - 1] };
        cell(b, q[i], t[i], incoming, false);
    }
    let lower_carry = q[126];
    // Top carry = t127 OR lower_carry. Its action on either target is
    // A*gate*(1 XOR (!t127 AND !lower_carry)). The compare leaves all
    // low target data intact so its entire carry ladder can be reversed.
    let xor_top_carry = |b: &mut B, gate: QubitId, target: QubitId| {
        b.ccx(r.activity, gate, target);
        literal(b, &[(r.activity,false), (gate,false), (t[127],true), (lower_carry,true)],
                target, dirty);
    };
    b.cx(r.activity, r.flight);
    xor_top_carry(b, t[128], r.flight);
    xor_top_carry(b, r.flight, t[128]);
    for i in (first..127).rev() {
        let incoming = if i == first { r.work } else { q[i - 1] };
        cell(b, q[i], t[i], incoming, true);
    }
    // work has returned to zero, so a single compute/uncompute protects
    // all lower writes, even when the retained sign is arbitrary.
    b.ccx(r.activity, r.flight, r.work);
    if first == 127 {
        // Preserve the pinned digit's q126 dependency even outside the
        // one-bit data subrange on which that cell would be zero.
        literal(b, &[(r.work,false), (q[126],true)], t[127], dirty);
    } else {
        let sub = &q[first..127];
        let dst = &t[first..127];
        if sub.len() == 1 {
            literal(b, &[(r.work,false), (sub[0],false), (dst[0],false)], t[127], dirty);
            b.ccx(r.work, sub[0], dst[0]);
        } else {
            super::super::arith::ttk_add(b, sub, dst, Some(r.work), Some((t[127], dirty[0])));
        }
        b.cx(r.work, t[127]); // virtual leading one plus lower carry
    }
    b.ccx(r.activity, r.flight, r.work);
    for &wire in t { b.x(wire); }
    b.end()
}
