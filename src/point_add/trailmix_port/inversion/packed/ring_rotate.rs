//! Packed-prefix primitive `ring_rotate` (tools/spike/packed_design.md, section 2.1):
//! precondition-free cyclic rotation of a sub-ring of a register by a k-bit
//! quantum amount, built from Fredkins only (1 T each), no ancillae.
//!
//! `ring[w]`, w = 0..W, is the sub-ring `[L, T)` in ascending wire order
//! (`ring[0]` = wire L, `ring[W-1]` = wire T-1). Forward (`inverse = false`)
//! rotates UP: the bit on `ring[w]` moves to `ring[(w + amount) mod W]`, i.e.
//! reading the ring as an integer with bit w on `ring[w]` it is a cyclic left
//! rotation by `amount mod W`. `inverse = true` rotates DOWN by the same amount
//! and is the exact gate-for-gate mirror (reversed layers, reversed cycles,
//! reversed pairs; every Fredkin is self-inverse).
//!
//! Layer i (bit i of `amount`, LSB first, as `barrel_shift_inplace` reads its
//! shift) applies the permutation `w -> (w + 2^i) mod W` under `amount[i]`.
//! That permutation is a product of `g = gcd(2^i mod W, W)` disjoint cycles of
//! length `m = W / g`; cycle c visits `p_j = (c + j * r) mod W`, j = 0..m, and
//! is realised as the chain `cswap(p_{m-2}, p_{m-1}), cswap(p_{m-3}, p_{m-2}),
//! ..., cswap(p_0, p_1)`, which carries the value of `p_{m-1}` down to `p_0`
//! while every other value moves up one cycle step - the barrel shifter's
//! top-down pair order (`arith/qshift_sub.rs:34-38`) closed into a ring.
//! Nothing shifts off an end, so there is no zero-wire precondition and no
//! widening transient; wires outside the slice are untouched.
//!
//! Cost per layer `W - gcd(2^i mod W, W)` Fredkins = Toffolis: exactly the
//! design's `W - 1` whenever `2^i` is coprime to W (every layer of an odd ring,
//! in particular the 257-wire rings and every prime width), fewer on even
//! widths and zero for a layer whose `2^i` is a multiple of W (the design's
//! `k (W - 1)` is therefore an upper bound that this implementation meets or
//! beats). Depth-free of ancillae: no wire is allocated.
//!
//! Choices where the design is silent (documented here, checked by the
//! selftest): (1) the amount is taken modulo W - rotation by `amount >= W` is a
//! well-defined rotation by `amount mod W`, so the design's `amount < W`
//! precondition is not needed; (2) `amount` may have any number of bits (the
//! design uses k <= 8; a 9-bit amount would cost one more layer); (3) a ring of
//! width 0 or 1, or an empty `amount`, is a no-op (nothing emitted).
//!
//! Preconditions (the only ones): `amount` must be disjoint from `ring`, and the
//! ring wires must be pairwise distinct (a slice of one register; any order is
//! accepted and rotation is in slice order, so a slice handed over in
//! descending wire order rotates the other way in wire terms - the selftest
//! checks the two agree gate-for-gate in Toffoli count). The amount wires are
//! controls only and are never written. Ops are emitted under the profile
//! section `p.ring`.
//!
//! Selftest (`MIDQ_PACKED_SELFTEST=1`): `ring_rotate_selftest.rs`.

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "ring_rotate_selftest.rs"]
mod ring_rotate_selftest;

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// `2^i mod w` without overflow for any layer index.
pub(crate) fn layer_step(w: usize, i: usize) -> usize {
    if w == 0 {
        return 0;
    }
    let mut r = 1 % w;
    for _ in 0..i {
        r = (r * 2) % w;
    }
    r
}

/// The Fredkin pairs of one layer, in forward order: rotating a `w`-wire ring
/// up by `r` (taken mod `w`) as `w - gcd(r, w)` position swaps. Empty when the
/// rotation is the identity.
pub(crate) fn layer_pairs(w: usize, r: usize) -> Vec<(usize, usize)> {
    if w < 2 {
        return Vec::new();
    }
    let r = r % w;
    if r == 0 {
        return Vec::new();
    }
    let g = gcd(r, w);
    let m = w / g;
    let mut pairs = Vec::with_capacity(w - g);
    for c in 0..g {
        for j in (0..m - 1).rev() {
            pairs.push(((c + j * r) % w, (c + (j + 1) * r) % w));
        }
    }
    pairs
}

/// Toffoli count of one layer (`w - gcd(2^i mod w, w)`, 0 for an identity
/// layer); the whole rotation costs the sum over `i < amount.len()`.
pub(crate) fn layer_toffoli(w: usize, i: usize) -> usize {
    let r = layer_step(w, i);
    if w < 2 || r == 0 {
        0
    } else {
        w - gcd(r, w)
    }
}

/// Total Toffoli count of `ring_rotate` on a `w`-wire ring with a `k`-bit amount.
#[allow(dead_code)]
pub(crate) fn toffoli(w: usize, k: usize) -> usize {
    (0..k).map(|i| layer_toffoli(w, i)).sum()
}

/// Cyclic rotation of `ring` (ascending wire order) by the quantum `amount`
/// (LSB first): up when `!inverse`, down when `inverse`; see the module doc.
pub(crate) fn ring_rotate(c: &mut Circuit, ring: &[QReg], amount: &[QReg], inverse: bool) {
    let w = ring.len();
    if w < 2 || amount.is_empty() {
        return;
    }
    let prev = c.push_section("p.ring");
    let layers: Vec<usize> = if inverse {
        (0..amount.len()).rev().collect()
    } else {
        (0..amount.len()).collect()
    };
    for i in layers {
        let mut pairs = layer_pairs(w, layer_step(w, i));
        if inverse {
            pairs.reverse();
        }
        for (a, b) in pairs {
            c.cswap(&amount[i], &ring[a], &ring[b]);
        }
    }
    c.pop_section(&prev);
}

/// Selftest entry called by `packed::selftest_all`.
#[allow(dead_code)]
pub(crate) fn selftest() {
    ring_rotate_selftest::run();
}
