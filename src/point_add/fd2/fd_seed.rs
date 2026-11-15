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

// ---- Saatgutzuegle (lane saatgut, 2026-11-15): the hybrid seed with scaled fold (adv2, lanes/advisory q2-below757 section 1)
// ported into the P3NAT shell. Every function below is new; seed_fwd / seed_inv / seed_inv_zw above are untouched.
/// Source switch (the box builders wipe the environment): 2 = hybrid seed with the scaled fold (default), 1 = narrow add
/// with the parent's fold (count experiment only), 0 = the parent's seed at every site (reproduces the parent stream).
/// Override FD_HYB=0/1/2.
pub const HYB: u8 = 2;
pub fn hyb_mode() -> u8 {
    static P: std::sync::OnceLock<u8> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_HYB").ok().and_then(|v| v.trim().parse::<u8>().ok()).unwrap_or(HYB))
}
/// hybrid seed on: step 1 = exact product of the tag with the low s lanes of a (tag stays), the loop adds only a[s..].
pub fn hyb() -> bool { hyb_mode() >= 1 }
/// scaled fold on: during the loop the low HF lanes of z hold V = c^-1 * (true low bits) mod 2^HF, so the fold "+c on
/// overflow" is one controlled increment of V on HM lanes (drops a carry w.p. 2^-HM; the true carry out of the field is
/// lost w.p. c / 2^HF = 2^-41 per fold). cscale converts in place (exact, polynomial).
pub fn hyb2() -> bool { hyb_mode() == 2 }
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
/// to = true: true form -> V form (before a loop); to = false: back (after a loop). No-op without the scaled fold.
pub fn hyb_scale(b: &mut B, z: &[QubitId], dirty: &[QubitId], to: bool) {
    if hyb2() { cscale(b, &z[..HF], dirty, to); }
}
/// Low lanes of the multiplicand handled by the exact pre-product for a w-bit seed whose inverse tests the top
/// max(zw, w) lanes: s = 256 - w - max(zw, w), so the pre-product j * a[..s) lives in z[..s + w) below the window.
pub fn hyb_s_zw(w: usize, zw: usize) -> usize {
    let s = 256 - w - zw.max(w);
    assert!(s + w >= HF && s + super::modp_frogdrop::CMPT <= 256, "hybrid split s {s} at w {w} zw {zw}");
    s
}
/// The adv2 split (window ZW = 40).
pub fn hyb_s(w: usize) -> usize { hyb_s_zw(w, ZW) }
/// z[0 .. s + w) += top * a[0..s) (exact integer; z's low part |0> in; top = z's top w lanes, untouched). d: borrowed.
pub fn hyb_pre(b: &mut B, z: &[QubitId], a: &[QubitId], w: usize, s: usize, d: QubitId) {
    assert!(s + 2 * w <= z.len() && s <= a.len() && !z.contains(&d) && !a.contains(&d));
    let top = &z[z.len() - w..];
    for i in 0..w {
        super::arith::ttk_add(b, &a[..s], &z[i..i + s], Some(top[i]), Some((z[i + s], d)));
    }
}
/// Forward hybrid seed: hyb_pre, scale, the parent's descending loop with the caller's narrow add (`add` = ctrl_modadd_top
/// or ctrl_modadd255_top at split s), unscale. Same interface and debts as `seed_fwd`. `a` = the multiplicand (also the
/// scale's dirty lanes), `d` = a borrowed lane outside z and a.
pub fn seed_fwd_hyb(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId], a: &[QubitId], d: QubitId,
                    s: usize, add: &mut dyn FnMut(&mut B)) -> Vec<BitId> {
    hyb_pre(b, z, a, w, s, d);
    hyb_scale(b, z, a, true);
    let bits = seed_fwd(b, z, flag, k, w, dirty, add);
    hyb_scale(b, z, a, false);
    bits
}
/// Exact inverse of `seed_fwd_hyb`'s unitary part at width w and split s (`add_rec` = the narrow add at the same s).
/// Activation: k = [flag == 1 and z[s + w ..] == 0] (the top max(zw, w) lanes; a wrong flag-1 branch passes w.p. about
/// 2^-(256 - s - w) per step). Ends with the inverse pre-product, so z = j << (256 - w) on exit.
pub fn seed_inv_hyb(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId], add_rec: &[G],
                    a: &[QubitId], d: QubitId, s: usize) {
    // Saatgutzuegle 2 (A): w <= 14 (was 13). The inverse takes no classical bit ids; its widest MCX has 1 + max(zw, w)
    // controls against >= 254 dirty lanes; the window/split asserts below are the real constraints. 14 = the streamed
    // inverse at consume width 13.
    assert!(w >= 1 && w <= 14 && dirty.len() >= 254 && z.len() == 256);
    let lo = s + w;
    assert!(lo >= HF && 256 - lo >= w && 256 - lo >= 2);
    hyb_scale(b, z, a, true);
    xor_eq(b, z, [0; 5], flag, dirty);
    b.x(flag);
    for j in 1..(1usize << w) {
        b.play(add_rec, true);
        let win = &z[lo..];
        let mut ctl = vec![flag];
        ctl.extend_from_slice(win);
        for &q in win { b.x(q); }
        mcx_dirty(b, &ctl, k, dirty);
        for &q in win { b.x(q); }
        move_branch(b, z, flag, k, j, w);
        test_top(b, z, flag, false, k, j, w, dirty);
    }
    hyb_scale(b, z, a, false);
    b.begin();
    hyb_pre(b, z, a, w, s, d);
    let r1 = b.end();
    b.play(&r1, true);
}

// ---- Saatgutzuegle round 2 (lane saatgut2, 2026-11-15). Every switch off = the round-1 stream byte for byte.
fn s2_env(name: &str, default: bool) -> bool {
    std::env::var(name).map(|v| v.trim() != "0").unwrap_or(default)
}
/// Stichschnitt (F, forward seeds with the narrowest split): the four forward seeds run no inverse, so their split only
/// has to keep the pre-product j * a[..s) below the tag: s = 256 - 2w. The loop's ripple then covers the top 2w lanes
/// and the erase compare reads exactly those lanes (exact, see ctrl_modadd_top). Const + env FD_S2FSPLIT (0/1).
pub const S2_FSPLIT: bool = true; // round 2 default on; FD_S2FSPLIT=0 = round 1
pub fn s2_fsplit() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| s2_env("FD_S2FSPLIT", S2_FSPLIT))
}
/// The split of a forward-only use of the hybrid seed at width w (all four forward seeds): hyb_s(w) (round 1) or, with
/// Stichschnitt, 256 - 2w (pre-product below the tag, ripple at least as wide as the scaled region is far: s >= HF).
pub fn fwd_split(w: usize) -> usize {
    if !s2_fsplit() { return hyb_s(w); }
    let s = 256 - 2 * w;
    assert!(s >= HF && s + w >= HF && 2 * w >= 2, "forward split s {s} at w {w}");
    s
}
/// Schuldbueechli (D, debt book with a second clean lane): pay debts2 (P2a) and debts4 (in P3) with pay_debts2 and the
/// site's clean flag as k2, as round 1 already does for debts1 and debts5. Const + env FD_S2DEBT (0/1).
pub const S2_DEBT: bool = true; // round 2 default on; FD_S2DEBT=0 = round 1
pub fn s2_debt() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| s2_env("FD_S2DEBT", S2_DEBT))
}
/// Ueberlaufchlemmer (O, P1's narrow add in exact-overflow form): ctrl_modadd255_top writes k = ctl & carry & z255_old with
/// fd_shell's overflow ripple (on lanes [s, 256)) instead of ripple + first compare. Const + env FD_S2OVF (0/1).
pub const S2_OVF: bool = true; // round 2 default on; FD_S2OVF=0 = round 1
pub fn s2_ovf() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| s2_env("FD_S2OVF", S2_OVF)) && super::fd_shell::ovf_on()
}
/// Rueckwaertsmessli (E, inverse seed with measured erases): in the w-bit hybrid inverse (no streamed bit) the step's
/// subtract erases its overflow flag by X-measurement (`sub`, e.g. modp_frogdrop::ctrl_modsub_top_m) and the activation
/// bit k is erased by X-measurement after the branch move instead of the exact test_top. Debt of step j: phase -1 on the
/// moved branch = [top == j] at the end, the same pattern as the forward seed's debt j, so `merge_debts` folds it into the
/// forward debt bit (classical XOR) and one pay_debts / pay_debts2 pays both. Const + env FD_S2MINV (0/1); needs hyb2.
pub const S2_MINV: bool = true; // round 2 default on (acts only with Bitbhaltis); FD_S2MINV=0 = round 1
pub fn s2_minv() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| s2_env("FD_S2MINV", S2_MINV)) && hyb2()
}
/// `seed_inv_hyb` with Rueckwaertsmessli: same activation and branch moves; `sub` = the measured inverse of the narrow
/// add at split s; returns the inverse's debt bits (index j - 1). Merge them into the forward debts with `merge_debts`.
pub fn seed_inv_hyb_m(b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId],
                      sub: &mut dyn FnMut(&mut B), a: &[QubitId], d: QubitId, s: usize) -> Vec<BitId> {
    assert!(w >= 1 && w <= 14 && dirty.len() >= 254 && z.len() == 256 && hyb2());
    let lo = s + w;
    assert!(lo >= HF && 256 - lo >= w && 256 - lo >= 2);
    let bits = b.fresh_bits((1usize << w) - 1);
    hyb_scale(b, z, a, true);
    xor_eq(b, z, [0; 5], flag, dirty);
    b.x(flag);
    for j in 1..(1usize << w) {
        sub(b);
        let win = &z[lo..];
        let mut ctl = vec![flag];
        ctl.extend_from_slice(win);
        for &q in win { b.x(q); }
        mcx_dirty(b, &ctl, k, dirty);
        for &q in win { b.x(q); }
        move_branch(b, z, flag, k, j, w);
        b.hmr_to(k, bits[j - 1]);
    }
    hyb_scale(b, z, a, false);
    b.begin();
    hyb_pre(b, z, a, w, s, d);
    let r1 = b.end();
    b.play(&r1, true);
    bits
}
/// fwd[i] ^= inv[i] (classically conditioned BitInvert; sim.rs: target ^= condition).
pub fn merge_debts(b: &mut B, fwd: &[BitId], inv: &[BitId]) {
    use crate::circuit::{Op, OperationType};
    assert_eq!(fwd.len(), inv.len());
    for i in 0..fwd.len() {
        b.raw_op(Op { kind: OperationType::BitInvert, c_target: fwd[i], c_condition: inv[i], ..Op::empty() });
    }
}
