//! Lilypad-G (r6_tick): the Lilypad walk in G-coordinates G = 2g - f, C_G = 2c_g - c_f (C_F = c_f).
//! Same decisions, same Q words, same eraser as lilypad.rs; the tick is
//!   e ^= 1 ^ X.v[1] ^ Y.v[1] ^ rho                (e = g mod 2 of the Lilypad state; Clifford)
//!   sigma = e & [h >= 0]
//!   X.v += (-1)^(1+e+rho) Y.v ; Y.c += (-1)^(1+e+rho) X.c      (UNCONTROLLED signed adds: forced digit)
//!   halve (relabel), then in frame t+1: cswap(X, Y) on sigma (no negation; signs float), rho ^= sigma
//!   h ^= sigma, h += 1, cap, sigma ^= X.c[1]
//! Rings: X = (G | C_F), Y = (F | C_G); G, F odd; C_F, C_G even. Signs of the four fields float; only rho = swap
//! parity is tracked. The eraser reads c_g through an in-place window conversion Y.c <- X.c + (-1)^rho Y.c
//! (= 2 d c_g, d = sign of the stored C_F) and an offset view (bsig + 1).
use super::builder::{B, G, ONE};
use super::chunked::AddRole;
use super::frogstrip::{sec, SEC_INV};
use super::modp_ft::ctrl_add_pool;
use super::lilypad::{
    cap_logic, digit_add, eraser, fix_boundary, inc_unctl, inc_unctl_dirty, lsc, lsc_from, mclear, win_len,
    ParityCtl, PSched, PScr, PWalk, HB,
};
use crate::circuit::{BitId, QubitId};

pub const LILYPAD_G_SCHED: &str = include_str!("lilypad_g_sched.txt");
/// Exact representation change: both stored cofactors are always even, so
/// store U=C_F/2 and V=C_G/2 and remove their constant-zero low lanes.
pub const HALF_COFACTOR_G: bool = true;
const L2_CONVERSION_FREE_ERASER: bool = true;
const L5_PRE_SWAP_Q12_ERASER: bool = true;
pub(super) const PAGE3_R: usize = 3;

#[cfg(test)]
pub(super) fn test_page3_storage() -> bool {
    std::env::var_os("LILYPAD_PAGE3_STORAGE").is_some()
}

#[cfg(not(test))]
pub(super) fn test_page3_storage() -> bool {
    true
}

#[cfg(test)]
pub(super) fn test_stream_page3_sources() -> bool {
    std::env::var_os("LILYPAD_STREAM_PAGE3_SOURCES").is_some() || test_page3_storage()
}

#[cfg(not(test))]
pub(super) fn test_stream_page3_sources() -> bool {
    true
}

fn page3_source_anf() -> &'static Vec<Vec<usize>> {
    static MASKS: std::sync::OnceLock<Vec<Vec<usize>>> = std::sync::OnceLock::new();
    MASKS.get_or_init(|| {
        const NV: usize = 8;
        let mut rows = vec![];
        for bit in 0..3usize {
            let mut anf = vec![0u8; 1 << NV];
            for assignment in 0..1usize << NV {
                let g = 1 | (((assignment >> 0) & 3) << 1);
                let f = 1 | (((assignment >> 2) & 3) << 1);
                let u = (assignment >> 4) & 7;
                let rho = (assignment >> 7) & 1;
                let sign_p = if rho == 0 { 7 } else { 1 };
                let inv = (1usize..8).find(|z| (f * z) & 7 == 1).unwrap();
                let v = ((g * u + sign_p) * inv) & 7;
                anf[assignment] = ((v >> bit) & 1) as u8;
            }
            for k in 0..NV {
                for mask in 0..1usize << NV {
                    if mask & (1 << k) != 0 { anf[mask] ^= anf[mask ^ (1 << k)]; }
                }
            }
            rows.push(anf.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect());
        }
        rows
    })
}

fn page3_general_anf() -> &'static Vec<Vec<usize>> {
    static MASKS: std::sync::OnceLock<Vec<Vec<usize>>> = std::sync::OnceLock::new();
    MASKS.get_or_init(|| {
        const NV: usize = 9;
        let mut rows = vec![];
        for bit in 0..PAGE3_R {
            let mut anf = vec![0u8; 1 << NV];
            for assignment in 0..1usize << NV {
                let g = assignment & 7;
                let f = 1 | (((assignment >> 3) & 3) << 1);
                let u = (assignment >> 5) & 7;
                let rho = (assignment >> 8) & 1;
                let sign_p = if rho == 0 { 7 } else { 1 };
                let inv = (1usize..8).find(|z| (f * z) & 7 == 1).unwrap();
                let v = ((g * u + sign_p) * inv) & 7;
                anf[assignment] = ((v >> bit) & 1) as u8;
            }
            for k in 0..NV {
                for mask in 0..1usize << NV {
                    if mask & (1 << k) != 0 { anf[mask] ^= anf[mask ^ (1 << k)]; }
                }
            }
            rows.push(anf.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect());
        }
        rows
    })
}

pub(super) fn page3_sources_xor_direct_rho(
    b: &mut B,
    w: &PWalk,
    frame: usize,
    rho: &ParityCtl,
    out_v1: QubitId,
    out_v2: QubitId,
    dirty: &[QubitId],
) {
    assert!(dirty.len() >= 4);
    let vars = [
        w.af(frame, 1),
        w.af(frame, 2),
        w.bf(1),
        w.bf(2),
        w.asig(frame, 0),
        w.asig(frame, 1),
        w.asig(frame, 2),
    ];
    for (bit, target) in [(1usize, out_v1), (2usize, out_v2)] {
        for &mask in &page3_source_anf()[bit] {
            let base: Vec<(QubitId, bool)> = (0..vars.len())
                .filter(|k| mask & (1 << k) != 0)
                .map(|k| (vars[k], false))
                .collect();
            if mask & (1 << 7) == 0 {
                super::mask::mc_xor(b, &base, target, &[], dirty);
            } else {
                for &rq in &rho.qs {
                    let mut controls = base.clone();
                    controls.push((rq, false));
                    super::mask::mc_xor(b, &controls, target, &[], dirty);
                }
                if rho.flip {
                    super::mask::mc_xor(b, &base, target, &[], dirty);
                }
            }
        }
    }
}

fn page3_general_xor_direct_rho(
    b: &mut B,
    w: &PWalk,
    frame: usize,
    rho: &ParityCtl,
    out: &[QubitId],
    dirty: &[QubitId],
) {
    assert!(out.len() <= PAGE3_R && dirty.len() >= 5);
    let vars = [
        w.af(frame, 0),
        w.af(frame, 1),
        w.af(frame, 2),
        w.bf(1),
        w.bf(2),
        w.asig(frame, 0),
        w.asig(frame, 1),
        w.asig(frame, 2),
    ];
    for (bit, &target) in out.iter().enumerate() {
        for &mask in &page3_general_anf()[bit] {
            let base: Vec<(QubitId, bool)> = (0..vars.len())
                .filter(|k| mask & (1 << k) != 0)
                .map(|k| (vars[k], false))
                .collect();
            if mask & (1 << 8) == 0 {
                super::mask::mc_xor(b, &base, target, &[], dirty);
            } else {
                for &rq in &rho.qs {
                    let mut controls = base.clone();
                    controls.push((rq, false));
                    super::mask::mc_xor(b, &controls, target, &[], dirty);
                }
                if rho.flip {
                    super::mask::mc_xor(b, &base, target, &[], dirty);
                }
            }
        }
    }
}

pub(super) fn page3_storage_xor(b: &mut B, w: &PWalk, frame: usize, rho: &ParityCtl, dirty: &[QubitId]) {
    let out: Vec<QubitId> = (0..PAGE3_R).map(|s| w.bsig(s)).collect();
    page3_general_xor_direct_rho(b, w, frame, rho, &out, dirty);
}

/// In-place low-page codec
///
///     U -> V = (G U + (-1)^rho p) F^-1 mod 2^r.
///
/// `G`, `F`, and `U` are little-endian r-bit two's-complement views with G/F
/// odd.  The caller supplies a physical |1>, restored clean carry lanes, and
/// arbitrary restored dirty loans.  Recording this body and playing it in
/// reverse gives V -> U with the same sources.
pub(super) fn page_codec_u_to_v(
    b: &mut B,
    u: &[QubitId],
    g: &[QubitId],
    f: &[QubitId],
    rho: QubitId,
    one: QubitId,
    dirty: &[QubitId],
) {
    let r = u.len();
    assert!(r >= 3 && r <= 16);
    assert_eq!(g.len(), r);
    assert_eq!(f.len(), r);
    assert!(dirty.len() >= r.saturating_sub(2).max(4));

    // Multiply by the odd G.
    super::lilypad::finish_mul_no_tmp(b, &g[1..], u, one, dirty);

    // (-1)^rho p = p + rho*(-2p) modulo 2^r.
    let mask = (1u64 << r) - 1;
    let p = super::frogdrop_sched::p().as_limbs()[0] & mask;
    let add_constant = |b: &mut B, ctl: QubitId, k: u64| {
        for j in 0..r {
            if k & (1 << j) == 0 { continue; }
            let word = &u[j..];
            for i in (1..word.len()).rev() {
                let mut controls = vec![(ctl, false)];
                controls.extend(word[..i].iter().copied().map(|q| (q, false)));
                super::mask::mc_xor(b, &controls, word[i], &[], dirty);
            }
            b.cx(ctl, word[0]);
        }
    };
    add_constant(b, one, p);
    add_constant(b, rho, (!p.wrapping_mul(2)).wrapping_add(1) & mask);

    // Divide by odd F by reversing the exact in-place multiplier.
    b.begin();
    super::lilypad::finish_mul_no_tmp(b, &f[1..], u, one, dirty);
    let mul_f = b.end();
    b.play(&mul_f, true);
}

fn page3_replay(w: &PWalk, sc: &PScr) -> bool {
    test_page3_storage() && w.q.len() >= 5 && sc.sp.len() >= 4 && !sc.d.is_empty()
}

#[cfg(test)]
thread_local! {
    static TEST_L2: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
    static TEST_L5: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
}

#[cfg(test)]
pub(crate) fn test_l2_override(value: Option<bool>) {
    TEST_L2.with(|v| v.set(value.map_or(-1, i8::from)));
}

#[cfg(test)]
pub(crate) fn test_l5_override(value: Option<bool>) {
    TEST_L5.with(|v| v.set(value.map_or(-1, i8::from)));
}

fn l2_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L2.with(|v| match v.get() { 0 => false, 1 => true, _ => L2_CONVERSION_FREE_ERASER });
    }
    #[cfg(not(test))]
    {
        L2_CONVERSION_FREE_ERASER
    }
}

fn l5_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L5.with(|v| match v.get() { 0 => false, 1 => true, _ => L5_PRE_SWAP_Q12_ERASER });
    }
    #[cfg(not(test))]
    {
        L5_PRE_SWAP_Q12_ERASER
    }
}

fn dirty_hinc_enabled(w: &PWalk) -> bool {
    #[cfg(test)]
    {
        return w.q.len() >= 4 && std::env::var_os("LILYPAD_DIRTY_HINC").is_some();
    }
    #[cfg(not(test))]
    {
        l5_enabled() && w.q.len() >= 4
    }
}

pub(crate) fn inverse_tmp_len_g() -> usize {
    #[cfg(test)]
    if let Ok(v) = std::env::var("LILYPAD_INV_TMP") {
        return v.parse().expect("LILYPAD_INV_TMP");
    }
    if l5_enabled() { super::lilypad::G_INV_NT } else { super::lilypad::NT }
}

pub(crate) fn inverse_d_len_g() -> usize {
    1
}

pub(crate) fn rho_stable(w: &PWalk, completed_ticks: usize) -> ParityCtl {
    if neg("norho") {
        return ParityCtl { qs: vec![], flip: false };
    }
    let mut qs = vec![w.h[0]];
    if w.log.len() >= 8 {
        qs.extend([w.log[0], w.log[4]]);
    }
    ParityCtl { qs, flip: completed_ticks & 1 == 1 }
}

fn rho_pre_swap(w: &PWalk, t: usize, sigma: QubitId) -> ParityCtl {
    let mut rho = rho_stable(w, t);
    rho.qs.push(sigma);
    rho
}

pub fn sched_g() -> PSched {
    let mut sched = PSched::from_text(LILYPAD_G_SCHED);
    if HALF_COFACTOR_G {
        sched.w -= 1;
        for t in 1..=sched.s + 1 {
            sched.kc[t] -= 1;
        }
    }
    sched
}

#[cfg(test)]
thread_local! {
    static G_TEST_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn g_test_neg(mode: u8) {
    G_TEST_NEG.with(|m| m.set(mode));
}

/// Test-only negative controls. Production builds are source-pinned and have
/// no environment-controlled circuit selectors.
#[cfg(test)]
fn neg(k: &str) -> bool {
    let code = match k {
        "norho" => 1,
        "flipsign" => 2,
        "noconvrho" => 3,
        "nofix" => 4,
        "noz" => 5,
        "noadrho" => 6,
        _ => 0,
    };
    code != 0 && G_TEST_NEG.with(|m| m.get() == code)
}

#[cfg(not(test))]
fn neg(_k: &str) -> bool {
    false
}

/// target += (-1)^(XOR negs ^ inv) source (mod 2^len), uncontrolled; paired chunks when `pairing` is set.
#[allow(clippy::too_many_arguments)]
fn sadd(
    b: &mut B,
    src: &[QubitId],
    tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    pool: &[QubitId],
    pairing: Option<(usize, bool)>,
    t: usize,
    role: AddRole,
) {
    let flip = |b: &mut B| {
        for &q in tgt {
            for &n in negs {
                b.cx(n, q);
            }
            if inv {
                b.x(q);
            }
        }
    };
    flip(b);
    digit_add(b, src, tgt, ONE, pool, pairing, t, role);
    flip(b);
}

fn page_xor_sign(b: &mut B, target: &[QubitId], negs: &[QubitId], inv: bool) {
    for &q in target {
        for &n in negs { b.cx(n, q); }
        if inv { b.x(q); }
    }
}

fn page_sadd_unitary(b: &mut B, src: &[QubitId], tgt: &[QubitId], negs: &[QubitId], inv: bool) {
    page_xor_sign(b, tgt, negs, inv);
    super::arith::ttk_add(b, src, tgt, None, None);
    page_xor_sign(b, tgt, negs, inv);
}

fn page_low_add(
    b: &mut B,
    src: &[QubitId],
    tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    carry: QubitId,
    one: QubitId,
    dirty: QubitId,
) {
    page_xor_sign(b, tgt, negs, inv);
    super::arith::ttk_add(b, src, tgt, Some(one), Some((carry, dirty)));
    page_xor_sign(b, tgt, negs, inv);
}

fn page_clear_carry(
    b: &mut B,
    src: &[QubitId],
    final_tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    carry: QubitId,
    one: QubitId,
    dirty: QubitId,
) {
    page_xor_sign(b, final_tgt, negs, !inv);
    super::arith::ttk_carry(b, src, final_tgt, one, carry, dirty);
    page_xor_sign(b, final_tgt, negs, !inv);
}

fn page_high_add(
    b: &mut B,
    src: &[QubitId],
    tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    cin: QubitId,
    zero: QubitId,
    one: QubitId,
) {
    page_xor_sign(b, &[zero], negs, !inv);
    let mut a = vec![cin];
    a.extend(src);
    let mut t = vec![zero];
    t.extend(tgt);
    page_xor_sign(b, &t, negs, inv);
    super::arith::ttk_add(b, &a, &t, Some(one), None);
    page_xor_sign(b, &t, negs, inv);
    page_xor_sign(b, &[zero], negs, !inv);
    b.cx(cin, zero);
}

/// Initial state: X.v = 2x - p (x shifted up one lane by swaps, then the uncontrolled subtract of Y.v = p),
/// Y = (p | C_G = 2), X.c = 0. Recorded so the inverse walk can unplay it.
pub fn init_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr) {
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.bf(f));
        }
    }
    b.x(w.bsig(usize::from(!HALF_COFACTOR_G)));
    for f in (0..256).rev() {
        b.swap(w.af(1, f), w.af(1, f + 1));
    }
    let kv = sch.kv[1];
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(1, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    let mut pl = sc.pool.clone();
    pl.extend(&sc.tmp);
    // 2x - p = ~(~X + Y) with Y = p; X lanes above 257 are 0 (sign extension of 2x >= 0 -> of 2x - p by the add)
    sadd(b, &bv, &av, &[], true, &pl, None, 0, AddRole::Value);
    // sign-extend X.v to its region (lanes kv..c are |0> before; the circuit keeps them sign copies)
    for f in kv..sch.c[1] {
        b.cx(w.af(1, kv - 1), w.af(1, f));
    }
}

/// Step of tick t up to the halve: e computed into `e` (|0> forward; Q's lane in the regenerating walk), sigma, adds.
pub fn step_core_g(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    rho: &ParityCtl,
    e: QubitId,
    extra: &[QubitId],
    pairing: Option<(usize, bool)>,
) {
    let (c, kv, kc) = (sch.c[t], sch.kv[t], sch.kc[t]);
    let sg = sc.sg;
    let h5 = w.h[HB - 1];
    sec(b, "lilyg.ctl", |b| {
        b.cx(w.af(t, 1), e);
        b.cx(w.bf(1), e);
        b.x(e);
        rho.xor_into(b, e);
        b.x(h5);
        b.and_c(e, h5, sg);
        b.x(h5);
    });
    let page_inverse = page3_replay(w, sc);
    let mut pl = if page_inverse {
        lsc_from(b, w, t, c, kv, kc, 0, PAGE3_R)
    } else {
        lsc(b, w, t, c, kv, kc)
    };
    pl.extend(&sc.pool);
    pl.extend(&sc.tmp);
    pl.extend(extra);
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    let sinv = !neg("flipsign") ^ rho.flip;
    let mut negs = vec![e];
    negs.extend(&rho.qs);
    if test_page3_storage() {
        let ac_lo: Vec<QubitId> = (0..PAGE3_R).map(|s| w.asig(t, s)).collect();
        let (low_tgt, carry, zero, low_dirty) = if page_inverse {
            let low = sc.sp[..PAGE3_R].to_vec();
            page3_general_xor_direct_rho(b, w, t, rho, &low, &w.q[..5]);
            (low, sc.sp[PAGE3_R], sc.d[0], w.q[0])
        } else {
            assert!(sc.tmp.len() >= 3);
            ((0..PAGE3_R).map(|s| w.bsig(s)).collect(), sc.tmp[0], sc.tmp[1], sc.tmp[2])
        };
        page_low_add(b, &ac_lo, &low_tgt, &negs, sinv, carry, w.bf(0), low_dirty);
        page_sadd_unitary(b, &bv, &av, &negs, sinv);
        let ac_hi: Vec<QubitId> = (PAGE3_R..kc).map(|s| w.asig(t, s)).collect();
        let bc_hi: Vec<QubitId> = (PAGE3_R..kc).map(|s| w.bsig(s)).collect();
        page_high_add(b, &ac_hi, &bc_hi, &negs, sinv, carry, zero, w.bf(0));
        page_clear_carry(b, &ac_lo, &low_tgt, &negs, sinv, carry, w.bf(0), low_dirty);
        if page_inverse {
            page3_general_xor_direct_rho(b, w, t, rho, &low_tgt, &w.q[..5]);
        }
    } else {
        sec(b, "lilyg.addv", |b| sadd(b, &bv, &av, &negs, sinv, &pl, pairing, t, AddRole::Value));
        // In the half-cofactor representation every physical cofactor lane is
        // live; in the legacy representation sig0 is the constant-zero lane.
        let c0 = usize::from(!HALF_COFACTOR_G);
        let ac: Vec<QubitId> = (c0..kc).map(|s| w.asig(t, s)).collect();
        let bc: Vec<QubitId> = (c0..kc).map(|s| w.bsig(s)).collect();
        sec(b, "lilyg.addc", |b| sadd(b, &ac, &bc, &negs, sinv, &pl, pairing, t, AddRole::Cofactor));
    }
    if page_inverse {
        lsc_from(b, w, t, c, kv, kc, 0, PAGE3_R);
    } else {
        lsc(b, w, t, c, kv, kc);
    }
}

/// Halve of tick t (relabel + boundary fixes), the deferred-to-frame-t+1 cswap, rho/delta update, cap, sigma decode.
pub fn halve_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        }
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
    });
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let paged = page3_replay(w, sc);
    sec(b, "lilyg.swap", |b| {
        if paged {
            lsc_from(b, w, t + 1, c, kv, kc, 0, PAGE3_R);
            let rho_before = rho_stable(w, t - 1);
            page3_general_xor_direct_rho(b, w, t + 1, &rho_before, &sc.sp[..PAGE3_R], &w.q[..5]);
            for s in 0..PAGE3_R { b.cswap(sg, w.asig(t + 1, s), sc.sp[s]); }
        } else {
            lsc(b, w, t + 1, c, kv, kc);
        }
        for f in 1..kv {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        let c0 = if paged { PAGE3_R } else { usize::from(!HALF_COFACTOR_G) };
        for s in c0..kc {
            b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
        }
        if paged {
            let mut rho_after = rho_stable(w, t - 1);
            rho_after.qs.push(sg);
            page3_general_xor_direct_rho(b, w, t + 1, &rho_after, &sc.sp[..PAGE3_R], &w.q[..5]);
            lsc_from(b, w, t + 1, c, kv, kc, 0, PAGE3_R);
        } else {
            lsc(b, w, t + 1, c, kv, kc);
        }
    });
    sec(b, "lilyg.hv", |b| {
        for &x in &w.h {
            b.cx(sg, x);
        }
        if dirty_hinc_enabled(w) {
            inc_unctl_dirty(b, &w.h, &w.q[..4]);
        } else {
            let mut htmp = sc.tmp.clone();
            htmp.extend(&sc.sp);
            inc_unctl(b, &w.h, &htmp);
        }
    });
    if w.capq > 0 {
        sec(b, "lilyg.cap", |b| cap_logic(b, w, sc));
    }
    b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
}

/// L5 inverse-regeneration ordering. The h/cap update commutes ahead of the
/// role swap; the conversion-free 12-lane eraser runs while sigma and rho are
/// still in the pre-swap frame, then the role swap and rho toggle complete the
/// tick.
pub fn halve_g_pre_erase(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    external_dirty: &[QubitId],
) {
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        }
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
        for &x in &w.h {
            b.cx(sc.sg, x);
        }
        if dirty_hinc_enabled(w) {
            inc_unctl_dirty(b, &w.h, &w.q[..4]);
        } else {
            let mut htmp = sc.tmp.clone();
            htmp.extend(&sc.sp);
            inc_unctl(b, &w.h, &htmp);
        }
    });
    if w.capq > 0 {
        sec(b, "lilyg.cap", |b| cap_logic(b, w, sc));
    }
    let rho = rho_pre_swap(w, t, sc.sg);
    eraser(
        b,
        w,
        t,
        sch,
        sc,
        usize::from(!HALF_COFACTOR_G),
        t == sch.s,
        Some(&rho),
        true,
        HALF_COFACTOR_G,
        external_dirty,
    );
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let paged = page3_replay(w, sc);
    sec(b, "lilyg.swap", |b| {
        if paged {
            lsc_from(b, w, t + 1, c, kv, kc, 0, PAGE3_R);
            page3_general_xor_direct_rho(b, w, t + 1, &rho, &sc.sp[..PAGE3_R], &w.q[..5]);
            for s in 0..PAGE3_R { b.cswap(sg, w.asig(t + 1, s), sc.sp[s]); }
        } else {
            lsc(b, w, t + 1, c, kv, kc);
        }
        for f in 1..kv {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        let c0 = if paged { PAGE3_R } else { usize::from(!HALF_COFACTOR_G) };
        for s in c0..kc {
            b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
        }
        if paged {
            let rho_after = rho_stable(w, t);
            page3_general_xor_direct_rho(b, w, t + 1, &rho_after, &sc.sp[..PAGE3_R], &w.q[..5]);
            lsc_from(b, w, t + 1, c, kv, kc, 0, PAGE3_R);
        } else {
            lsc(b, w, t + 1, c, kv, kc);
        }
    });
    b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
}

/// Window conversion for the eraser (frame t+1): Y.c[0..L] <- X.c[0..L] + (-1)^rho Y.c[0..L] (mod 2^L), so that
/// Y.c sig k+1 = bit k of d*c_g. Recording (unplay to restore).
fn conv_len(b: &mut B, w: &PWalk, t: usize, l: usize, rho: &ParityCtl, pool: &[QubitId]) -> Vec<G> {
    let start = usize::from(!HALF_COFACTOR_G);
    let xs: Vec<QubitId> = (start..l).map(|k| w.asig(t + 1, k)).collect();
    let ys: Vec<QubitId> = (start..l).map(|k| w.bsig(k)).collect();
    b.begin();
    // rho = 1: Y <- X - Y = ~(Y + ~X)
    let nr = neg("noconvrho");
    for &q in &xs {
        if !nr { rho.xor_into(b, q); }
    }
    ctrl_add_pool(b, &xs, &ys, ONE, pool);
    for &q in &ys {
        if !nr { rho.xor_into(b, q); }
    }
    for &q in &xs {
        if !nr { rho.xor_into(b, q); }
    }
    b.end()
}

fn conv(b: &mut B, w: &PWalk, t: usize, sch: &PSched, rho: &ParityCtl, pool: &[QubitId]) -> Vec<G> {
    let qb = w.q.len();
    let l = (qb.max(win_len(qb)) + 3).min(sch.w - sch.c[t + 1]);
    conv_len(b, w, t, l, rho, pool)
}

/// Record the public-end bridge from Lilypad-G's stored coordinates to the
/// shell interface. It leaves only key=[F<0], C_F, h and the cap log live:
/// C_G is converted to signed 2p and cleared, G and rho are cleared by their
/// audited invariants, and F is reduced to its sign key.
pub fn endpoint_adapter_g(
    b: &mut B,
    w: &PWalk,
    sch: &PSched,
    sc: &PScr,
) -> Vec<G> {
    let t = sch.s + 1;
    let value_len = sch.c[t];
    let cofactor_len = sch.w - value_len;
    let mut pool = sc.pool.clone();
    pool.extend(&sc.tmp);
    pool.extend(&sc.sp);
    pool.extend(&sc.d);
    pool.push(sc.e);
    pool.push(sc.sg);
    let rho = if neg("noadrho") {
        ParityCtl { qs: vec![], flip: false }
    } else {
        rho_stable(w, sch.s)
    };
    let cv = conv_len(b, w, sch.s, cofactor_len, &rho, &pool);
    let sign_f = w.bf(1);
    let endpoint_constant = if HALF_COFACTOR_G {
        super::frogdrop_sched::p()
    } else {
        super::frogdrop_sched::p() << 1usize
    };
    let endpoint_negative = (!endpoint_constant).wrapping_add(super::frogdrop_sched::N::from(1u64));

    b.begin();
    b.play(&cv, false);
    for s in usize::from(!HALF_COFACTOR_G)..cofactor_len {
        let pos = endpoint_constant.bit(s);
        let neg = endpoint_negative.bit(s);
        if pos {
            b.x(w.bsig(s));
        }
        if pos != neg {
            b.cx(sign_f, w.bsig(s));
        }
    }
    // G = -(-1)^rho F at a successful endpoint.
    b.x(w.af(t, 0));
    for f in 1..value_len {
        b.x(w.af(t, f));
        rho.xor_into(b, w.af(t, f));
        b.cx(sign_f, w.af(t, f));
    }
    // F is +/-1: retain its sign in lane 1 as the shell key.
    b.x(w.bf(0));
    for f in 2..value_len {
        b.cx(sign_f, w.bf(f));
    }
    b.end()
}

pub struct GScr;

/// Forward walk: init, ticks 1..=S, e X-measured each tick. Returns the measurement bits (index t).
pub fn walk_forward_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>) -> Vec<BitId> {
    init_g(b, w, sch, sc);
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        let rho = rho_stable(w, t - 1);
        step_core_g(b, w, t, sch, sc, &rho, sc.e, &[], division.map(|d| (d, false)));
        halve_g(b, w, t, sch, sc);
        b.hmr_to(sc.e, m[t]);
    }
    m
}

/// Regenerating tick t as two recordings: (step core, halve + marker clear / converted eraser).
pub fn rec_regen_g(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    _g: &GScr,
    division: Option<usize>,
    external_dirty: &[QubitId],
) -> (Vec<G>, Vec<G>) {
    let qe = w.qfr(t)[w.q.len() - 1];
    let mut extra = vec![sc.e];
    extra.extend(&sc.d);
    extra.extend(&sc.sp);
    b.begin();
    let rho_before = rho_stable(w, t - 1);
    step_core_g(b, w, t, sch, sc, &rho_before, qe, &extra, division.map(|d| (d, true)));
    let p1 = b.end();
    b.begin();
    if t % 2 == 0 && l5_enabled() {
        halve_g_pre_erase(b, w, t, sch, sc, external_dirty);
        let p3 = b.end();
        return (p1, p3);
    }
    halve_g(b, w, t, sch, sc);
    if t % 2 == 1 {
        mclear(b, w, t, sc, HALF_COFACTOR_G, external_dirty);
    } else {
        let mut cp: Vec<QubitId> = sc.pool.clone();
        cp.extend(&sc.tmp);
        cp.extend(&sc.sp);
        cp.push(sc.e);
        if l2_enabled() {
            let rho = rho_stable(w, t);
            eraser(
                b,
                w,
                t,
                sch,
                sc,
                usize::from(!HALF_COFACTOR_G),
                t == sch.s,
                Some(&rho),
                false,
                HALF_COFACTOR_G,
                external_dirty,
            );
        } else {
            let rho = rho_stable(w, t);
            let cv = conv(b, w, t, sch, &rho, &cp);
            sec(b, "er.conv", |b| b.play(&cv, false));
            eraser(b, w, t, sch, sc, 1, t == sch.s, None, false, false, external_dirty);
            sec(b, "er.conv", |b| b.play(&cv, true));
        }
    }
    let p3 = b.end();
    (p1, p3)
}

/// Inverse of walk_forward_g (Q clean in w.q; clean again afterwards).
pub fn walk_inverse_g(
    b: &mut B,
    w: &PWalk,
    sch: &PSched,
    sc: &PScr,
    g: &GScr,
    m: &[BitId],
    division: Option<usize>,
    external_dirty: &[QubitId],
) {
    SEC_INV.with(|c| c.set(true));
    for t in (1..=sch.s).rev() {
        let (p1, p3) = rec_regen_g(b, w, t, sch, sc, g, division, external_dirty);
        b.play(&p3, true);
        if !neg("noz") {
            b.z_if(w.qfr(t)[w.q.len() - 1], m[t]);
        }
        b.play(&p1, true);
    }
    if page3_replay(w, sc) {
        let rho0 = rho_stable(w, 0);
        page3_storage_xor(b, w, 1, &rho0, external_dirty);
    }
    b.begin();
    init_g(b, w, sch, sc);
    let ir = b.end();
    b.play(&ir, true);
    SEC_INV.with(|c| c.set(false));
}
