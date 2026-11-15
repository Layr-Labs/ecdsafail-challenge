//! FD pane: descending consume seeds with measured activation.
//!
//! A w-bit descending seed maps z = (j in z's top w lanes, rest |0>, flag 0) to (j * a mod p, flag 1) by 2^w - 1 steps:
//! step j moves the branch (top = j, flag 0) to (z = 0, flag 1) and then adds a to every flag-1 branch. The parent
//! activates with one 257-control test (flag ^= [flag ? z == 0 : z == j<<s]). Here the forward activation computes
//! g = [flag == 0 and top == j] (exact: every flag-0 branch has a zero low part) into the clean lane k, moves the
//! branch with CNOTs, and erases g by an X-basis measurement. The phase debt (-1)^(m_j [original top == j]) is paid
//! later wherever the consumed bits are explicit again (`pay_debts`). The inverse seed computes g from the after-state
//! with a low-ZW-lane zero test (other flag-1 branches hold (j' - j) a != 0; a zero low window has 2^-ZW weight per shot and step) and
//! uncomputes it with the cheap exact test.
use super::builder::{B, G};
use super::descending_seed::xor_eq;
use super::mask::mcx_dirty;
use crate::circuit::{BitId, QubitId};

/// Low lanes read by the inverse activation's zero test.
pub const ZW: usize = 40;

/// k ^= [flag == fval and top == j] (top = z's top w lanes, bit i of j on top[i]).
fn test_top(b: &mut B, z: &[QubitId], flag: QubitId, fval: bool, k: QubitId, j: usize, w: usize, dirty: &[QubitId]) {
    let top = &z[z.len() - w..];
    let mut ctl = vec![flag];
    ctl.extend_from_slice(top);
    if !fval { b.x(flag); }
    for i in 0..w { if j >> i & 1 == 0 { b.x(top[i]); } }
    mcx_dirty(b, &ctl, k, dirty);
    for i in 0..w { if j >> i & 1 == 0 { b.x(top[i]); } }
    if !fval { b.x(flag); }
}

/// CNOT the activation bit k into flag and into the top lanes where j has a one.
fn move_branch(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, j: usize, w: usize) {
    let top = &z[z.len() - w..];
    b.cx(k, flag);
    for i in 0..w { if j >> i & 1 == 1 { b.cx(k, top[i]); } }
}

/// Forward seed with measured activation. `add` adds a to z under `flag` (k |0> in and out). Returns the debt bits,
/// index j - 1. `dirty`: lanes outside z, flag, k, at least 254 of them.
pub fn seed_fwd(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId],
                add: &mut dyn FnMut(&mut B)) -> Vec<BitId> {
    assert!(w >= 1 && w <= 13 && dirty.len() >= 254);
    let bits = b.fresh_bits((1usize << w) - 1);
    for j in (1..(1usize << w)).rev() {
        test_top(b, z, flag, false, k, j, w, dirty);
        move_branch(b, z, flag, k, j, w);
        b.hmr_to(k, bits[j - 1]);
        add(b);
    }
    b.x(flag);
    xor_eq(b, z, [0; 5], flag, dirty);
    bits
}

/// Exact inverse of `seed_fwd`'s unitary part (no measurement, no debt): `add_rec` is the recorded add.
pub fn seed_inv(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId], add_rec: &[G]) {
    assert!(w >= 1 && w <= 13 && dirty.len() >= 254);
    xor_eq(b, z, [0; 5], flag, dirty);
    b.x(flag);
    for j in 1..(1usize << w) {
        b.play(add_rec, true);
        // k = [flag == 1 and z low window == 0]
        let mut ctl = vec![flag];
        ctl.extend_from_slice(&z[..ZW]);
        for &q in &z[..ZW] { b.x(q); }
        mcx_dirty(b, &ctl, k, dirty);
        for &q in &z[..ZW] { b.x(q); }
        move_branch(b, z, flag, k, j, w);
        test_top(b, z, flag, false, k, j, w, dirty);
    }
}

/// `seed_inv` with the zero-test width `zw` in place of ZW (r765b P3NAT_SEED: the six-bit inverse of a streamed seed
/// tests 42 low lanes over its 63 steps). Same gates as `seed_inv` when zw = ZW.
pub fn seed_inv_zw(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId], add_rec: &[G], zw: usize) {
    assert!(w >= 1 && w <= 13 && dirty.len() >= 254 && zw >= 2 && zw <= z.len() - w);
    xor_eq(b, z, [0; 5], flag, dirty);
    b.x(flag);
    for j in 1..(1usize << w) {
        b.play(add_rec, true);
        // k = [flag == 1 and z low window == 0]
        let mut ctl = vec![flag];
        ctl.extend_from_slice(&z[..zw]);
        for &q in &z[..zw] { b.x(q); }
        mcx_dirty(b, &ctl, k, dirty);
        for &q in &z[..zw] { b.x(q); }
        move_branch(b, z, flag, k, j, w);
        test_top(b, z, flag, false, k, j, w, dirty);
    }
}

/// Pay the phase debts of a measured seed: for every j with bits[j - 1] = 1, phase -1 on [top == j]. `top` holds the
/// consumed bits (bit i of j on top[i]); `k` is a clean lane; `dirty` >= w - 2 lanes outside top and k.
pub fn pay_debts(b: &mut B, top: &[QubitId], bits: &[BitId], k: QubitId, dirty: &[QubitId]) {
    let w = top.len();
    assert_eq!(bits.len(), (1usize << w) - 1);
    for j in 1..(1usize << w) {
        b.push_cond(bits[j - 1]);
        for i in 0..w { if j >> i & 1 == 0 { b.x(top[i]); } }
        mcx_dirty(b, top, k, dirty);
        b.z_if(k, bits[j - 1]);
        mcx_dirty(b, top, k, dirty);
        for i in 0..w { if j >> i & 1 == 0 { b.x(top[i]); } }
        b.pop_cond();
    }
}

/// `pay_debts` with a second clean lane `k2`: the high w - 5 consumed bits are decoded once per block of 32 patterns
/// into k (unconditional), and each pattern's phase is a 6-control test on (k, low 5 bits) into k2 under its bit.
pub fn pay_debts2(b: &mut B, top: &[QubitId], bits: &[BitId], k: QubitId, k2: QubitId, dirty: &[QubitId]) {
    let w = top.len();
    if w <= 6 { return pay_debts(b, top, bits, k, dirty); }
    assert_eq!(bits.len(), (1usize << w) - 1);
    let (lo, hi) = top.split_at(5);
    for h in 0..(1usize << (w - 5)) {
        let flip_hi = |b: &mut B| { for i in 0..w - 5 { if h >> i & 1 == 0 { b.x(hi[i]); } } };
        flip_hi(b);
        mcx_dirty(b, hi, k, dirty);
        flip_hi(b);
        let mut ctl = vec![k];
        ctl.extend_from_slice(lo);
        for l in 0..32usize {
            let j = (h << 5) | l;
            if j == 0 { continue; }
            b.push_cond(bits[j - 1]);
            for i in 0..5 { if l >> i & 1 == 0 { b.x(lo[i]); } }
            mcx_dirty(b, &ctl, k2, dirty);
            b.z_if(k2, bits[j - 1]);
            mcx_dirty(b, &ctl, k2, dirty);
            for i in 0..5 { if l >> i & 1 == 0 { b.x(lo[i]); } }
            b.pop_cond();
        }
        flip_hi(b);
        mcx_dirty(b, hi, k, dirty);
        flip_hi(b);
    }
}
