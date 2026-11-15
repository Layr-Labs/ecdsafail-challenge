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
    assert!(w >= 1 && w <= 24 && dirty.len() >= 254);
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
    assert!(w >= 1 && w <= 24 && dirty.len() >= 254);
    xor_eq(b, z, [0; 5], flag, dirty);
    b.x(flag);
    for j in 1..(1usize << w) {
        b.play(add_rec, true);
        // k = [flag == 1 and z low window == 0]
        let win: &[QubitId] = if hyb() { &z[z.len() - ZW.max(w)..] } else { &z[..ZW] };
        let mut ctl = vec![flag];
        ctl.extend_from_slice(win);
        for &q in win { b.x(q); }
        mcx_dirty(b, &ctl, k, dirty);
        for &q in win { b.x(q); }
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

// ---- adv2 (2026-11-13) HYBRID seed, COUNT-LEVEL experiment (register-level model: lanes/advisory/adv2/proto/toy2.py).
/// FD_HYB=1: step 1 = exact product of the tag with the low s lanes of a (tag stays), descending loop adds only a[s..].
pub fn hyb() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_HYB").map(|v| v.trim() == "1" || v.trim() == "2").unwrap_or(true))
}
/// FD_HYB=2: hybrid seed with the SCALED FOLD: during the loop the low HF lanes of z hold V = c^-1 * (true low bits) mod 2^HF,
/// so the fold "+c on overflow" is one controlled increment of V on HM lanes (drops a carry w.p. 2^-HM; the true carry out
/// of the field is lost w.p. c / 2^HF = 2^-40 per fold). cscale converts in place (exact, polynomial, twice per seed run).
pub fn hyb2() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_HYB").map(|v| v.trim() == "2").unwrap_or(true))
}
pub const HF: usize = 73;
pub const HM: usize = 40;
/// t <- c * t mod 2^n (inv: c^-1 * t) in place, c = 2^32 + 977 (odd): top-down t += t_i * (c - 1) << i. dirty: >= n lanes outside t.
pub fn cscale(b: &mut B, t: &[QubitId], dirty: &[QubitId], inv: bool) {
    b.begin();
    for i in (0..t.len()).rev() {
        if t.len() - i > 4 {
            super::modp_frogdrop::add_const_exact(b, &t[i..], Some(t[i]), super::modp_frogdrop::C - 1, dirty);
        }
    }
    let r = b.end();
    b.play(&r, inv);
}
/// after hyb_pre / before the loop (to = true: into V form) and after the loop (to = false: back to true form)
pub fn hyb_scale(b: &mut B, z: &[QubitId], dirty: &[QubitId], to: bool) {
    if hyb2() { cscale(b, &z[..HF], dirty, to); }
}
/// low lanes of a handled by the exact product: 256 - 2w - g with w + g = max(40, w)
pub fn hyb_s(w: usize) -> usize { 256 - w - ZW.max(w) }
/// z[0 .. s + w) += top * a[0..s) (exact integer; z's low part |0> in; top = z's top w lanes, untouched). d: borrowed.
pub fn hyb_pre(b: &mut B, z: &[QubitId], a: &[QubitId], w: usize, d: QubitId) {
    let s = hyb_s(w);
    let top = &z[z.len() - w..];
    for i in 0..w {
        super::arith::ttk_add(b, &a[..s], &z[i..i + s], Some(top[i]), Some((z[i + s], d)));
    }
}
