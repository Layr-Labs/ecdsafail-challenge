//! 3-of-4 Euclid machine: reversible 2-adic primitives.
//!
//! The 3-of-4 hold keeps three of (r_{j-1}, r_j, t_{j-1}, t_j); the dropped one is recovered from the invariant
//! r_{j-1} t_j + r_j t_{j-1} = p by an in-place 2-adic map x -> (p - x a) / b. Its building block is the in-place
//! multiply x -> x * a mod 2^L for odd a: top-down, bit i of x (never touched by later adds) controls
//! x[i+1..L) += (a >> 1) << (i + 1). The inverse circuit divides by a.

use super::arith::{down_m, inc, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

/// Controlled add t += g * s (t, s same length n >= 1), carry out of the top lane added into `tl` (truncated
/// there: the tail is a plain increment, its carry out is dropped). `c0` |0>, `anc` >= tl.len() - 1 clean.
pub fn cadd_tail(b: &mut B, g: QubitId, t: &[QubitId], s: &[QubitId], tl: &[QubitId], c0: QubitId, h: QubitId,
                 anc: &[QubitId]) {
    cadd_tail_and(b, g, t, s, tl, c0, h, anc, &[])
}

/// cadd_tail whose top min(andc.len(), n) lanes keep their carries on the clean qubits `andc` (logical-AND carries:
/// 1 Toffoli to compute, uncomputed by measurement), so a top lane costs 2 Toffoli (carry + controlled sum bit)
/// instead of the in-place ripple's 3. Same function as cadd_tail; `andc` |0> on entry and exit.
pub fn cadd_tail_and(b: &mut B, g: QubitId, t: &[QubitId], s: &[QubitId], tl: &[QubitId], c0: QubitId, h: QubitId,
                     anc: &[QubitId], andc: &[QubitId]) {
    let n = t.len();
    assert!(n >= 1 && s.len() == n);
    let k = andc.len().min(n);
    let l0 = n - k;
    // low lanes [0, l0): in-place ripple, carry into lane l0 on its wire
    let up = up_m(b, &t[..l0], &s[..l0], c0, false);
    let dn = down_m(b, &t[..l0], &s[..l0], c0, Dm::Cond(g), false);
    let cw = |i: usize| -> QubitId {
        // wire holding the carry into lane i (i >= l0)
        if i == l0 {
            if l0 == 0 { c0 } else { s[l0 - 1] }
        } else {
            andc[i - 1 - l0]
        }
    };
    if l0 > 0 {
        b.play(&up, false);
    }
    // top lanes: c_{i+1} = c_i ^ ((t_i ^ c_i) & (s_i ^ c_i)) on andc[i - l0]
    for i in l0..n {
        let c = cw(i);
        b.cx(c, t[i]);
        b.cx(c, s[i]);
        b.and_c(t[i], s[i], andc[i - l0]);
        b.cx(c, andc[i - l0]);
    }
    if !tl.is_empty() {
        let cout = if k > 0 { andc[k - 1] } else { s[n - 1] }; // MAJ leaves c_{k+1} in s[k]
        b.and_c(g, cout, h);
        inc(b, h, tl, &anc[..tl.len() - 1]);
        b.and_u(g, cout, h);
    }
    for i in (l0..n).rev() {
        let c = cw(i);
        b.cx(c, andc[i - l0]);
        b.and_u(t[i], s[i], andc[i - l0]);
        b.cx(c, t[i]); // t_i restored
        // t_i ^= g & (s_i ^ c_i): s_i still holds s_i ^ c_i
        b.ccx(g, s[i], t[i]);
        b.cx(c, s[i]); // s_i restored
    }
    if l0 > 0 {
        b.play(&dn, false);
    }
}

/// x <- x * a mod 2^L, L = x.len(), a odd (only a[1..] is read; a[0] = 1 is implied). Carry tails truncated
/// `tail` lanes above each add's source span. Scratch: c0, h, anc (>= tail - 1), all |0> and returned |0>.
pub fn mul_odd(b: &mut B, x: &[QubitId], a: &[QubitId], tail: usize, c0: QubitId, h: QubitId, anc: &[QubitId]) {
    let l = x.len();
    let m = a.len().saturating_sub(1);
    if l < 2 || m == 0 {
        return;
    }
    for i in (0..l - 1).rev() {
        let lo = i + 1;
        let nm = m.min(l - lo);
        let nt = tail.min(l - lo - nm);
        cadd_tail(b, x[i], &x[lo..lo + nm], &a[1..1 + nm], &x[lo + nm..lo + nm + nt], c0, h, anc);
    }
}

/// Scratch for the masked multiply: ladder carry c0, mask f, cell temp t, tail source lanes (|0>), decoder prefixes
/// for the boundary (>= bv.len() - 1), the control-gate flag e with its own prefixes, the gated control g.
pub struct MulScr {
    pub c0: QubitId,
    pub f: QubitId,
    pub t: QubitId,
    pub zeros: Vec<QubitId>,
    pub pre: Vec<QubitId>,
    pub e: QubitId,
    pub epre: Vec<QubitId>,
    pub g: QubitId,
    pub dirty: Vec<QubitId>,
}

/// x[0..beta) <- x * a mod 2^beta per shot (lanes >= beta untouched), a odd (only a[1..] read), beta = value of
/// register `bv`, every shot's beta in [wlo, whi) (1 <= wlo, whi <= x.len()). Top-down: control lane i, gated by
/// e = [i < beta] (lanes at or above beta belong to another value), adds (a >> 1) << (i + 1) through a ladder whose
/// running mask is cut at lane beta (truncation mod 2^beta per shot).
pub fn mul_odd_masked(b: &mut B, x: &[QubitId], a: &[QubitId], tail: usize, bv: &[QubitId], wlo: usize, whi: usize,
                      sc: &MulScr) {
    use super::mask::{mc_xor, mdown, mup, Dec, Lad, Mscr, Src};
    let m = a.len().saturating_sub(1);
    assert!(whi <= x.len() && wlo >= 1 && wlo < whi && m >= 1);
    let ms = Mscr { f: sc.f, t: sc.t, gf: sc.t, chain: sc.pre.clone(), dirty: sc.dirty.clone() };
    let mut edec = Dec::new(bv, &sc.epre);
    for i in (0..whi - 1).rev() {
        // e = [i < beta]: flips to 1 at i = beta - 1
        if i + 1 >= wlo && i + 1 < whi {
            let c = edec.ctrls(b, i + 1);
            mc_xor(b, &c, sc.e, &[sc.t], &sc.dirty);
        }
        if i + 1 == wlo {
            edec.clear(b);
        }
        let lo = i + 1;
        let top = whi.min(lo + m + tail);
        let nm = m.min(top - lo);
        let nt = top - lo - nm;
        let t: Vec<QubitId> = x[lo..top].to_vec();
        let mut s: Vec<QubitId> = a[1..1 + nm].to_vec();
        s.extend(&sc.zeros[..nt]);
        let mut srcs = vec![];
        let wl = wlo.max(lo);
        if wl < top {
            srcs.push(Src { lo: wl - lo, hi: top - lo, v: bv.to_vec(), a: lo as isize, d: 1, pre: sc.pre.clone(),
                            late: false });
        }
        let ld = Lad { t: &t, s: &s, c0: sc.c0, srcs: &srcs, f0: true, cmpl: false, sc: &ms, keep_f: true };
        let ru = mup(b, &ld);
        let gated = i >= wlo; // below wlo every shot has e = 1
        if gated {
            b.and_c(x[i], sc.e, sc.g);
        }
        let rd = mdown(b, &ld, Some(if gated { sc.g } else { x[i] }));
        b.play(&ru, false);
        b.play(&rd, false);
        if gated {
            b.and_u(x[i], sc.e, sc.g);
        }
    }
    b.x(sc.e); // every shot flipped e exactly once
}

/// Controlled cyclic rotation of `v`, content moving UP by r (lane j -> lane j + r mod n).
pub fn crot_up(b: &mut B, c: QubitId, v: &[QubitId], r: usize) {
    let n = v.len();
    let r = r % n;
    if r == 0 {
        return;
    }
    let g = gcd(n, r);
    for s in 0..g {
        let len = n / g;
        // cycle s -> s + r -> ...: content at lane x moves to x + r; walk the cycle backwards with swaps
        let cyc: Vec<usize> = (0..len).map(|k| (s + k * r) % n).collect();
        for k in (1..len).rev() {
            b.cswap(c, v[cyc[k]], v[cyc[k - 1]]);
        }
    }
}
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Rotate `v` up by the value of register `amt` (bit k rotates by 2^k); `inverse` rotates down by it.
pub fn rot_by(b: &mut B, v: &[QubitId], amt: &[QubitId], inverse: bool) {
    b.begin();
    for (k, &c) in amt.iter().enumerate() {
        crot_up(b, c, v, 1 << k);
    }
    let r = b.end();
    b.play(&r, inverse);
}

/// rot_by with `amt` read as two's complement (top bit weighs -2^(len-1)).
pub fn rot_by_signed(b: &mut B, v: &[QubitId], amt: &[QubitId], inverse: bool) {
    let n = v.len();
    let k = amt.len() - 1;
    b.begin();
    for (i, &c) in amt[..k].iter().enumerate() {
        crot_up(b, c, v, 1 << i);
    }
    crot_up(b, amt[k], v, n - (1usize << k) % n);
    let r = b.end();
    b.play(&r, inverse);
}

/// Rotated-frame multiply: x' = x * a mod 2^(top - lsb) for the value occupying lanes [lsb, top) of `v`, a odd
/// (only a[1..] read, a outside `v`), `top` fixed, lsb per shot in [llo, top) given by e-flag decoding of register
/// `lsbv` (value = lsb). Lanes below lsb are untouched (controls there are gated off; adds only write lanes above
/// their control). Scratch: c0, h, anc (>= tail - 1), e, epre, g clean.
pub fn mul_odd_frame(b: &mut B, v: &[QubitId], top: usize, llo: usize, lsbv: &[QubitId], a: &[QubitId], tail: usize,
                     c0: QubitId, h: QubitId, anc: &[QubitId], e: QubitId, epre: &[QubitId], g: QubitId,
                     dirty: &[QubitId]) {
    mul_odd_frame_by(b, v, top, llo, lsbv, |x| x, a, tail, c0, h, anc, e, epre, g, dirty)
}

/// mul_odd_frame with the value's lsb given as lsb = inv(v): the decoder looks for v == val_of(lsb).
pub fn mul_odd_frame_by(b: &mut B, v: &[QubitId], top: usize, llo: usize, lsbv: &[QubitId],
                        val_of: impl Fn(usize) -> usize, a: &[QubitId], tail: usize, c0: QubitId, h: QubitId,
                        anc: &[QubitId], e: QubitId, epre: &[QubitId], g: QubitId, dirty: &[QubitId]) {
    mul_odd_frame_and(b, v, top, llo, lsbv, val_of, a, tail, c0, h, anc, e, epre, g, dirty, &[])
}

/// mul_odd_frame_by with logical-AND carries on the top `andc.len()` lanes of every add.
pub fn mul_odd_frame_and(b: &mut B, v: &[QubitId], top: usize, llo: usize, lsbv: &[QubitId],
                         val_of: impl Fn(usize) -> usize, a: &[QubitId], tail: usize, c0: QubitId, h: QubitId,
                         anc: &[QubitId], e: QubitId, epre: &[QubitId], g: QubitId, dirty: &[QubitId],
                         andc: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    let m = a.len().saturating_sub(1);
    assert!(top <= v.len() && llo < top && m >= 1);
    // e = [i >= lsb]: starts 1 at the top (every shot's value reaches lane top - 1), flips to 0 below lane lsb
    b.x(e);
    let mut edec = Dec::new(lsbv, epre);
    for i in (llo..top - 1).rev() {
        let lo = i + 1;
        let nm = m.min(top - lo);
        let nt = tail.min(top - lo - nm);
        // control lane i is in the value iff i >= lsb; e must be [i >= lsb] here: flip when passing lsb = i + 1
        // (a lsb whose decoder value does not fit the register belongs to no shot)
        if lo > llo && val_of(lo) < (1usize << lsbv.len()) {
            let c = edec.ctrls(b, val_of(lo));
            mc_xor(b, &c, e, &[g], dirty);
        }
        b.and_c(v[i], e, g);
        cadd_tail_and(b, g, &v[lo..lo + nm], &a[1..1 + nm], &v[lo + nm..lo + nm + nt], c0, h, anc, andc);
        b.and_u(v[i], e, g);
    }
    // flip e back for the shots with lsb = llo ... every shot: e = [llo >= lsb] = [lsb == llo]
    if val_of(llo) < (1usize << lsbv.len()) {
        let c = edec.ctrls(b, val_of(llo));
        mc_xor(b, &c, e, &[g], dirty);
    }
    edec.clear(b);
    // now e = 0 for every shot
}

/// Walk lanes l in [clo, chi) with f = [l < cut] live (cut = value of `cutv`, any cut <= chi; cuts below clo give
/// f = 0 throughout); per(b, l, f) runs per lane. f is |0> before and after. `pre` >= cutv.len() - 1 clean (decoder
/// prefixes / comparator chain), `tmp` clean.
pub fn walk_cut(b: &mut B, cutv: &[QubitId], clo: usize, chi: usize, f: QubitId, pre: &[QubitId], tmp: QubitId,
                dirty: &[QubitId], mut per: impl FnMut(&mut B, usize, QubitId)) {
    if clo >= chi {
        return;
    }
    use super::mask::{ge_const, mc_xor, Dec};
    ge_const(b, cutv, clo as isize + 1, f, pre); // f = [clo < cut]
    let mut dec = Dec::new(cutv, pre);
    for l in clo..chi {
        if l > clo {
            let c = dec.ctrls(b, l);
            mc_xor(b, &c, f, &[tmp], dirty); // f = [l < cut]: flips off at l == cut
        }
        per(b, l, f);
    }
    let c = dec.ctrls(b, chi);
    mc_xor(b, &c, f, &[tmp], dirty);
    dec.clear(b);
}

/// Region [0, cut) of `v` (cut per shot in [clo, chi]): shift its content up (`up`) or down by the value of `amt`.
/// Up needs the region's top 2^|amt| lanes zero; down needs its low lanes zero. Lanes >= cut untouched.
pub fn shift_region(b: &mut B, v: &[QubitId], cutv: &[QubitId], clo: usize, chi: usize, amt: &[QubitId], up: bool,
                    f: QubitId, pre: &[QubitId], tmp: QubitId, g: QubitId, dirty: &[QubitId]) {
    shift_regionf(b, v, &Cut::reg(cutv), clo, chi, amt, up, f, pre, tmp, g, dirty)
}

pub fn shift_regionf(b: &mut B, v: &[QubitId], cut: &Cut, clo: usize, chi: usize, amt: &[QubitId], up: bool,
                     f: QubitId, pre: &[QubitId], tmp: QubitId, g: QubitId, dirty: &[QubitId]) {
    let stages: Vec<usize> = if up { (0..amt.len()).rev().collect() } else { (0..amt.len()).collect() };
    for k in stages {
        let s = 1usize << k;
        let c = amt[k];
        if s >= chi {
            continue;
        }
        let mcswap = |b: &mut B, f: QubitId, hi: usize, lo: usize| {
            b.and_c(c, f, g);
            b.cswap(g, v[hi], v[lo]);
            b.and_u(c, f, g);
        };
        if up {
            // pairs (l, l - s), l descending from chi - 1 to s; active iff l < cut
            walk_cutf_desc(b, cut, clo.max(s), chi, f, pre, tmp, dirty, |b, l, f| mcswap(b, f, l, l - s));
            for l in (s..clo.max(s)).rev() {
                b.cswap(c, v[l], v[l - s]);
            }
        } else {
            // pairs (l + s, l), l ascending; active iff l + s < cut
            for hi in s..clo.max(s) {
                b.cswap(c, v[hi], v[hi - s]);
            }
            walk_cutf(b, cut, clo.max(s), chi, f, pre, tmp, dirty, |b, l, f| mcswap(b, f, l, l - s));
        }
    }
}

/// walk_cut in descending lane order (f = [l < cut] live at lane l; any cut <= chi).
pub fn walk_cut_desc(b: &mut B, cutv: &[QubitId], clo: usize, chi: usize, f: QubitId, pre: &[QubitId], tmp: QubitId,
                     dirty: &[QubitId], mut per: impl FnMut(&mut B, usize, QubitId)) {
    if clo >= chi {
        return;
    }
    use super::mask::{ge_const, mc_xor, Dec};
    let mut dec = Dec::new(cutv, pre);
    let c = dec.ctrls(b, chi);
    mc_xor(b, &c, f, &[tmp], dirty); // f = [chi - 1 < cut] = [cut == chi]
    for l in (clo..chi).rev() {
        if l + 1 < chi {
            let c = dec.ctrls(b, l + 1);
            mc_xor(b, &c, f, &[tmp], dirty); // f flips on at cut == l + 1
        }
        per(b, l, f);
    }
    dec.clear(b);
    ge_const(b, cutv, clo as isize + 1, f, pre); // f = [clo < cut] -> 0
}

/// Z <- p - Z mod 2^cut on the region [0, cut) of `v` (every shot's cut in [clo, chi], clo > 42 + tail): masked
/// complement, subtract 2^32 + 976 (p + 1 = 2^256 - 2^32 - 976) with borrow chains cut `tail` lanes above each
/// constant (a longer borrow needs that many zero lanes: ~2^-tail), and add 2^256 where cut > 256 (masked
/// increment of [256, cut)). `anc` >= tail + 12 clean, `one` clean.
pub fn p_minus(b: &mut B, v: &[QubitId], cutv: &[QubitId], clo: usize, chi: usize, tail: usize, anc: &[QubitId],
               one: QubitId, f: QubitId, pre: &[QubitId], tmp: QubitId, dirty: &[QubitId]) {
    p_minusf(b, v, &Cut::reg(cutv), clo, chi, tail, anc, one, f, pre, tmp, dirty)
}

pub fn p_minusf(b: &mut B, v: &[QubitId], cut: &Cut, clo: usize, chi: usize, tail: usize, anc: &[QubitId],
                one: QubitId, f: QubitId, pre: &[QubitId], tmp: QubitId, dirty: &[QubitId]) {
    // W = Z X <= p (the map's exact identity Z X + Z' Y = p), so lanes >= 256 of W and of p - W are 0: only the low
    // min(cut, 256) lanes change (complement, then - (2^32 + 976) = + (p + 1 - 2^256))
    assert!(clo > 42 + tail && chi <= v.len());
    let _ = anc;
    for l in 0..clo.min(256) {
        b.x(v[l]);
    }
    if chi <= 256 {
        walk_cutf(b, cut, clo, chi, f, pre, tmp, dirty, |b, l, f| b.cx(f, v[l]));
    } else {
        walk_cutf_capped(b, cut, clo, 256, f, pre, tmp, dirty, |b, l, f| b.cx(f, v[l]));
    }
    sub_const_dirty(b, &v[0..10 + tail], 976, one, dirty);
    sub_const_dirty(b, &v[32..33 + tail], 1, one, dirty);
}

/// x -= k (borrow out of the top dropped) by complement + dirty-ancilla increments; `c1` clean, `dirty` >= x.len()
/// borrowed qubits disjoint from x.
fn sub_const_dirty(b: &mut B, x: &[QubitId], k: u64, c1: QubitId, dirty: &[QubitId]) {
    for &q in x {
        b.x(q);
    }
    for i in 0..64 {
        if (k >> i) & 1 == 1 && i < x.len() {
            super::modp_frogdrop::inc_dirty(b, &x[i..], dirty, c1);
        }
    }
    for &q in x {
        b.x(q);
    }
}

/// x -= k on a short register (borrow out of the top dropped). `one` clean, `anc` >= x.len() - 1 clean.
fn sub_const_short(b: &mut B, x: &[QubitId], k: u64, one: QubitId, anc: &[QubitId]) {
    for &q in x {
        b.x(q);
    }
    b.x(one);
    for i in 0..64 {
        if (k >> i) & 1 == 1 && i < x.len() {
            let bits = &x[i..];
            super::arith::inc(b, one, bits, &anc[..bits.len().saturating_sub(1)]);
        }
    }
    b.x(one);
    for &q in x {
        b.x(q);
    }
}

/// ez ^= v2(x) for x != 0 with v2(x) < 2^ez.len() (and <= emax): scan lanes upward, ez steps k -> k + 1 while
/// x[k] = 0. `pre` >= ez.len() - 1 clean, `tmp` clean.
pub fn tz_probe(b: &mut B, x: &[QubitId], ez: &[QubitId], emax: usize, pre: &[QubitId], tmp: QubitId,
                dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    let mut dec = Dec::new(ez, pre);
    for k in 0..emax.min(x.len()) {
        // if ez == k and x[k] == 0: ez ^= k ^ (k + 1)
        let mut c = dec.ctrls(b, k);
        c.push((x[k], true));
        let d = k ^ (k + 1);
        // the decoder's held prefixes depend on ez's top bits; flip the low bits of ez that change, top-down so
        // the controls (which only read bits above the flipped ones... ) stay valid: flip via a temp
        mc_xor(b, &c, tmp, &[], dirty);
        dec.clear(b);
        for i in 0..ez.len() {
            if (d >> i) & 1 == 1 {
                b.cx(tmp, ez[i]);
            }
        }
        // tmp = [ez_old == k] & !x[k] = [ez_new == k + 1] & !x[k]
        let mut c2 = dec.ctrls(b, k + 1);
        c2.push((x[k], true));
        mc_xor(b, &c2, tmp, &[], dirty);
        dec.clear(b);
    }
}

/// Swap ring lane l with q[n - 1 - l] (n = ring.len()) for every lane l >= cut (and n - 1 - l < q.len()). Every
/// shot's cut in [clo, chi]; lanes >= chi swap unconditionally, lanes < clo never.
pub fn masked_swap(b: &mut B, ring: &[QubitId], q: &[QubitId], cutv: &[QubitId], clo: usize, chi: usize, f: QubitId,
                   pre: &[QubitId], tmp: QubitId, dirty: &[QubitId]) {
    let n = ring.len();
    let qlo = n.saturating_sub(q.len());
    for l in chi.max(qlo)..n {
        b.swap(ring[l], q[n - 1 - l]);
    }
    let lo = clo.max(qlo);
    if lo < chi {
        walk_cut(b, cutv,
                 lo, chi, f, pre, tmp, dirty, |b, l, f| {
            // swap iff l >= cut, i.e. f = 0
            b.x(f);
            b.cswap(f, ring[l], q[n - 1 - l]);
            b.x(f);
        });
    }
}

/// Scratch for the map.
#[derive(Clone)]
pub struct MapScr {
    /// clean qubits for logical-AND carries on the top lanes of the frame multiply's adds (may be empty)
    pub andc: Vec<QubitId>,
    pub c0: QubitId,
    pub h: QubitId,
    pub e: QubitId,
    pub g: QubitId,
    pub f: QubitId,
    pub tmp: QubitId,
    pub one: QubitId,
    /// carry-tail ancillas (>= tail + 12)
    pub anc: Vec<QubitId>,
    /// decoder prefixes (>= cut register bits - 1)
    pub pre: Vec<QubitId>,
    /// v2 register (5 bits) and its probe prefixes (>= 4)
    pub ez: Vec<QubitId>,
    pub epre: Vec<QubitId>,
    pub dirty: Vec<QubitId>,
}

/// Column-classical parameters of a map.
pub struct MapPar {
    /// every shot's cut in [clo, chi]
    pub clo: usize,
    pub chi: usize,
    /// multiplier/divisor envelope bits (Q lanes read)
    pub m: usize,
    pub tail: usize,
    /// largest v2 handled
    pub emax: usize,
}

/// One frame multiply (inverse = divide) of the ring's bottom region [0, cut) by Q's value (odd, lanes [0, m)):
/// rotate the ring down by cut so the region sits under the fixed top, multiply with gated controls, rotate back.
fn frame_mul(b: &mut B, ring: &[QubitId], q: &[QubitId], cut: &Cut, par: &MapPar, sc: &MapScr, inverse: bool) {
    let n = ring.len();
    b.begin();
    // rotate down by cut = a +- v: down by a is a relabel; down by v (or up by v when cut = a - v)
    rot_by(b, ring, &cut.v, !cut.neg);
    let a = cut.a.rem_euclid(n as isize) as usize;
    let fr: Vec<QubitId> = (0..n).map(|i| ring[(i + a) % n]).collect(); // frame lane i = lane i + a
    // region now [n - cut, n): lsb = n - cut; decoder value of v for a given lsb
    let (ca, neg) = (cut.a, cut.neg);
    let vof = move |lsb: usize| -> usize {
        let c = n as isize - lsb as isize; // cut
        let x = if neg { ca - c } else { c - ca };
        x.max(0) as usize
    };
    mul_odd_frame_and(b, &fr, n, n - par.chi, &cut.v, vof, &q[..par.m], par.tail, sc.c0, sc.h, &sc.anc, sc.e,
                      &sc.pre, sc.g, &sc.dirty, &sc.andc);
    rot_by(b, ring, &cut.v, cut.neg);
    let r = b.end();
    b.play(&r, inverse);
}

/// Map Z <- (p - Z X)/Y. Layout in: ring = [Z (LSB lane 0) | Y (LSB lane n-1, down)], Q = X; out: ring = [y | X],
/// Q = Y. cut = n - max(bl X, bl Y) per shot (value of `cutv`), X and Y coprime.
pub fn map(b: &mut B, ring: &[QubitId], q: &[QubitId], cutv: &[QubitId], par: &MapPar, sc: &MapScr) {
    map_upto(b, ring, q, &Cut::reg(cutv), par, sc, 99)
}

pub fn mapf(b: &mut B, ring: &[QubitId], q: &[QubitId], cut: &Cut, par: &MapPar, sc: &MapScr) {
    map_upto(b, ring, q, cut, par, sc, 99)
}

pub fn map_upto(b: &mut B, ring: &[QubitId], q: &[QubitId], cut: &Cut, par: &MapPar, sc: &MapScr, upto: usize) {
    let mut st = 0usize;
    let mut go = |_b: &B| { st += 1; st <= upto };
    let (clo, chi) = (par.clo, par.chi);
    b.begin();
    tz_probe(b, &q[..par.emax + 1], &sc.ez, par.emax, &sc.epre, sc.tmp, &sc.dirty);
    let prec = b.end();
    let mut on = false; // probe toggles between compute and its exact inverse
    let mut probe = |b: &mut B| { b.play(&prec, on); on = !on; };
    // multiply by X: X_odd in Q (rotate down by eX), Z * 2^eX (region shift), frame multiply, undo the rotation
    if !go(b) { return; } probe(b);
    if !go(b) { return; } rot_by(b, q, &sc.ez, true);
    if !go(b) { return; } shift_regionf(b, ring, cut, clo, chi, &sc.ez, true, sc.f, &sc.pre, sc.tmp, sc.g, &sc.dirty);
    if !go(b) { return; } frame_mul(b, ring, q, cut, par, sc, false);
    if !go(b) { return; } rot_by(b, q, &sc.ez, false);
    if !go(b) { return; } probe(b);
    if !go(b) { return; } p_minusf(b, ring, cut, clo, chi, par.tail, &sc.anc, sc.one, sc.f, &sc.pre, sc.tmp, &sc.dirty);
    if !go(b) { return; } masked_swapf(b, ring, q, cut, clo, chi, sc.f, &sc.pre, sc.tmp, &sc.dirty);
    if !go(b) { return; } probe(b);
    if !go(b) { return; } rot_by(b, q, &sc.ez, true);
    if !go(b) { return; } frame_mul(b, ring, q, cut, par, sc, true);
    if !go(b) { return; } shift_regionf(b, ring, cut, clo, chi, &sc.ez, false, sc.f, &sc.pre, sc.tmp, sc.g, &sc.dirty);
    if !go(b) { return; } rot_by(b, q, &sc.ez, false);
    if !go(b) { return; } probe(b);
}

/// Exact long division step D on the pair: X = ring top (bit m at lane n-1-m, region [cut, n)), Y = Q (LSB lane 0).
/// For k = qb.len()-1 .. 0: q_k ^= [X >= Y 2^k], X -= q_k Y 2^k. Needs X < Y 2^qb.len() and qb = 0 on entry.
/// The compare's borrow is read at the shot's region top (n - cut) through a decoder of `cutv`; ladders run
/// unmasked over the envelope (lanes past a shot's region are restored). `zeros` = s lanes past Q's top (clean).
/// Its exact inverse (play inverted) is D^-1: X += q Y with q erased, valid when X < Y on output.
pub fn dstep(b: &mut B, ring: &[QubitId], q: &[QubitId], cutv: &[QubitId], clo: usize, chi: usize, qb: &[QubitId],
             zeros: &[QubitId], c0: QubitId, tmp: QubitId, pre: &[QubitId], dirty: &[QubitId]) {
    use super::arith::{down_m, up_m, Dm};
    use super::mask::{mc_xor, Dec};
    let n = ring.len();
    let mtop = n - clo; // largest region size
    for k in (0..qb.len()).rev() {
        if k >= mtop {
            continue;
        }
        let len = mtop - k;
        let t: Vec<QubitId> = (k..mtop).map(|m| ring[n - 1 - m]).collect();
        let s: Vec<QubitId> = (k..mtop).map(|m| {
            let i = m - k;
            if i < q.len() { q[i] } else { zeros[i - q.len()] }
        }).collect();
        let up = up_m(b, &t, &s, c0, true);
        let dn = down_m(b, &t, &s, c0, Dm::Cond(qb[k]), true);
        b.play(&up, false);
        // borrow at region top p = n - cut: carry into lane p = s[p - 1 - k] (p in [n - chi, n - clo])
        b.x(qb[k]);
        let mut dec = Dec::new(cutv, pre);
        for p in (n - chi)..=(n - clo) {
            let mut c = dec.ctrls(b, n - p);
            if p >= k + 1 {
                c.push((s[p - 1 - k], false));
            } // p <= k: the region ends at or below bit k, Y 2^k > X: borrow = 1
            mc_xor(b, &c, qb[k], &[tmp], dirty);
        }
        dec.clear(b);
        let _ = len;
        b.play(&dn, false);
    }
}

/// Scratch / registers of the streaming quotient pipeline P.
#[derive(Clone)]
pub struct PScr {
    /// reciprocal remainder (K + 1 lanes)
    pub r: Vec<QubitId>,
    /// second-division remainder (KP + 1 lanes)
    pub rho: Vec<QubitId>,
    /// quotient q0 (QB lanes), bit k at q0[k]
    pub q0: Vec<QubitId>,
    pub f: QubitId,
    pub g: QubitId,
    pub c0: QubitId,
    /// a |0> lane (compare tops)
    pub zero: QubitId,
    /// a |1> lane (forces the reciprocal divisor odd); must be |1> on entry and exit
    pub one: QubitId,
    pub spre: Vec<QubitId>,
    pub tmp: QubitId,
    pub dirty: Vec<QubitId>,
}

/// t >= s compare-and-conditional-subtract: out ^= [t >= s]; t -= out * s (t has one more lane than s; s is padded
/// with `zero`). 3 Toffoli per lane.
fn cmp_csub(b: &mut B, t: &[QubitId], s: &[QubitId], zero: QubitId, c0: QubitId, out: QubitId) {
    use super::arith::{down_m, up_m, Dm};
    let mut sx = s.to_vec();
    while sx.len() < t.len() {
        sx.push(zero);
    }
    let up = up_m(b, t, &sx, c0, true);
    let dn = down_m(b, t, &sx, c0, Dm::Cond(out), true);
    b.play(&up, false);
    let ct = sx[t.len() - 1]; // carry out of ~t + s: [s > t]
    b.x(ct);
    b.cx(ct, out);
    b.x(ct);
    b.play(&dn, false);
}

/// P: streamed q0 = floor(F / Yh), rho = F mod Yh with F = floor((2^e - 1) / Zh), Zh = zh | 1 (zh[0] is replaced by
/// `one`), e = tot - start (start = value of `startv`, per shot). R holds the reciprocal remainder on exit.
/// Returns the final lane orders of (r, rho) (they are relabelled by the doubling shifts).
pub fn pipeline(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], tot: usize, qb: usize, ps: &PScr)
                -> (Vec<QubitId>, Vec<QubitId>) {
    pipeline_off(b, zh, yh, startv, 0, tot, qb, ps)
}

/// pipeline with start = value(startv) + soff (the decoder looks for value == i - soff mod 2^len).
pub fn pipeline_off(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], soff: i64, tot: usize, qb: usize,
                    ps: &PScr) -> (Vec<QubitId>, Vec<QubitId>) {
    use super::mask::{mc_xor, Dec};
    let mut r = ps.r.clone();
    let mut rho = ps.rho.clone();
    let mut zd: Vec<QubitId> = zh.to_vec();
    zd[0] = ps.one;
    let mut dec = Dec::new(startv, &ps.spre);
    for i in 0..tot {
        // gate g = [i >= start]: flips on at i == start
        let md = 1i64 << startv.len();
        let c = dec.ctrls(b, (i as i64 - soff).rem_euclid(md) as usize);
        mc_xor(b, &c, ps.g, &[ps.tmp], &ps.dirty);
        // R = 2R + g (top lane is 0: rotate the lane order, new lane 0 gets g)
        let top = r.pop().unwrap();
        r.insert(0, top);
        b.cx(ps.g, r[0]);
        // f = [R >= Zh]; R -= f Zh
        cmp_csub(b, &r, &zd, ps.zero, ps.c0, ps.f);
        // rho = 2 rho + f
        let top = rho.pop().unwrap();
        rho.insert(0, top);
        b.cx(ps.f, rho[0]);
        // f = parity(R) ^ g -> clear
        b.cx(r[0], ps.f);
        b.cx(ps.g, ps.f);
        if i + qb >= tot {
            let k = tot - 1 - i;
            cmp_csub(b, &rho, yh, ps.zero, ps.c0, ps.q0[k]);
        }
    }
    dec.clear(b);
    b.x(ps.g); // every shot's start < tot
    (r, rho)
}

/// out ^= bl(v restricted to lanes [0, lim)) where every shot's value lies in [0, 2^lim) and lanes >= lim are
/// ignored: scan lanes top-down, set out = l + 1 at the first set lane (while out == 0). `pre` >= out.len() - 1.
/// Its exact inverse (play inverted) erases.
pub fn msb_probe(b: &mut B, v: &[QubitId], lim: usize, out: &[QubitId], pre: &[QubitId], tmp: QubitId,
                 dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    for l in (0..lim).rev() {
        // tmp = [out == 0] & v[l]
        let mut dec = Dec::new(out, pre);
        let mut c = dec.ctrls(b, 0);
        c.push((v[l], false));
        mc_xor(b, &c, tmp, &[], dirty);
        dec.clear(b);
        let val = l + 1;
        for (i, &o) in out.iter().enumerate() {
            if (val >> i) & 1 == 1 {
                b.cx(tmp, o);
            }
        }
        // tmp = [out == l + 1] & v[l] now
        let mut dec = Dec::new(out, pre);
        let mut c = dec.ctrls(b, val);
        c.push((v[l], false));
        mc_xor(b, &c, tmp, &[], dirty);
        dec.clear(b);
    }
}

/// t += s (registers little-endian, s shorter or equal, t mod 2^t.len()), c0 clean. 2 Toffoli per lane.
pub fn reg_add_into(b: &mut B, t: &[QubitId], s: &[QubitId], zeros: &[QubitId], c0: QubitId) {
    use super::arith::{down_m, up_m, Dm};
    let mut sx = s.to_vec();
    let mut zi = 0;
    while sx.len() < t.len() {
        sx.push(zeros[zi]);
        zi += 1;
    }
    let up = up_m(b, t, &sx, c0, false);
    let dn = down_m(b, t, &sx, c0, Dm::Sum, false);
    b.play(&up, false);
    b.play(&dn, false);
}

/// t += k (classical) mod 2^t.len() via increments, one/anc clean.
pub fn reg_add_const(b: &mut B, t: &[QubitId], k: i64, one: QubitId, anc: &[QubitId]) {
    let n = t.len();
    let kk = (k.rem_euclid(1i64 << n)) as u64;
    b.x(one);
    for i in 0..n {
        if (kk >> i) & 1 == 1 {
            let bits = &t[i..];
            super::arith::inc(b, one, bits, &anc[..bits.len().saturating_sub(1)]);
        }
    }
    b.x(one);
}

/// Controlled exact add/sub of Q * 2^k into the ring-top value (bit m at ring lane n-1-m), ladder over target bits
/// [k, k + span): t += g * (q << k) (`sub` = false) or t -= g * (q << k). Lanes past a shot's value are restored
/// (exact arithmetic) unless the result goes negative (then the borrow runs up to the ladder top; undone by the
/// matching add). `zeros` = source lanes past Q's top.
pub fn ring_cadd(b: &mut B, ring: &[QubitId], q: &[QubitId], k: usize, span: usize, g: QubitId, sub: bool,
                 zeros: &[QubitId], c0: QubitId) {
    use super::arith::{down_m, up_m, Dm};
    let n = ring.len();
    let t: Vec<QubitId> = (k..k + span).map(|m| ring[n - 1 - m]).collect();
    let s: Vec<QubitId> = (0..span).map(|i| if i < q.len() { q[i] } else { zeros[i - q.len()] }).collect();
    let up = up_m(b, &t, &s, c0, sub);
    let dn = down_m(b, &t, &s, c0, Dm::Cond(g), sub);
    b.play(&up, false);
    b.play(&dn, false);
}

/// A per-shot cut given as an affine function of a register: cut = a + value(v) (neg = false) or a - value(v).
#[derive(Clone)]
pub struct Cut {
    pub v: Vec<QubitId>,
    pub a: isize,
    pub neg: bool,
}

impl Cut {
    pub fn reg(v: &[QubitId]) -> Cut {
        Cut { v: v.to_vec(), a: 0, neg: false }
    }
    /// register value at which cut == l (None if out of range)
    fn val_at(&self, l: isize) -> Option<usize> {
        let x = if self.neg { self.a - l } else { l - self.a };
        if x < 0 || x as usize >= (1usize << self.v.len()) { None } else { Some(x as usize) }
    }
    /// t ^= [cut >= k]
    fn ge(&self, b: &mut B, k: isize, t: QubitId, chain: &[QubitId]) {
        use super::mask::ge_const;
        if self.neg {
            // a - v >= k  <=>  v <= a - k  <=>  !(v >= a - k + 1)
            ge_const(b, &self.v, self.a - k + 1, t, chain);
            b.x(t);
        } else {
            ge_const(b, &self.v, k - self.a, t, chain);
        }
    }
}

/// walk_cut for an affine cut: f = [l < cut] at lane l (any cut <= chi; below clo f stays 0).
pub fn walk_cutf(b: &mut B, cut: &Cut, clo: usize, chi: usize, f: QubitId, pre: &[QubitId], tmp: QubitId,
                 dirty: &[QubitId], mut per: impl FnMut(&mut B, usize, QubitId)) {
    if clo >= chi {
        return;
    }
    use super::mask::{mc_xor, Dec};
    cut.ge(b, clo as isize + 1, f, pre); // f = [clo < cut]
    let mut dec = Dec::new(&cut.v, pre);
    for l in clo..chi {
        if l > clo {
            if let Some(v) = cut.val_at(l as isize) {
                let c = dec.ctrls(b, v);
                mc_xor(b, &c, f, &[tmp], dirty);
            }
        }
        per(b, l, f);
    }
    if let Some(v) = cut.val_at(chi as isize) {
        let c = dec.ctrls(b, v);
        mc_xor(b, &c, f, &[tmp], dirty);
    }
    dec.clear(b);
}

/// walk_cutf over lanes [clo, hi) where cuts may exceed hi (f = [cut >= hi] after the last lane is cleared by a
/// comparator instead of the cut == hi decode).
pub fn walk_cutf_capped(b: &mut B, cut: &Cut, clo: usize, hi: usize, f: QubitId, pre: &[QubitId], tmp: QubitId,
                        dirty: &[QubitId], mut per: impl FnMut(&mut B, usize, QubitId)) {
    if clo >= hi {
        return;
    }
    use super::mask::{mc_xor, Dec};
    cut.ge(b, clo as isize + 1, f, pre);
    let mut dec = Dec::new(&cut.v, pre);
    for l in clo..hi {
        if l > clo {
            if let Some(v) = cut.val_at(l as isize) {
                let c = dec.ctrls(b, v);
                mc_xor(b, &c, f, &[tmp], dirty);
            }
        }
        per(b, l, f);
    }
    dec.clear(b);
    cut.ge(b, hi as isize, f, pre);
}

/// descending variant of walk_cutf.
pub fn walk_cutf_desc(b: &mut B, cut: &Cut, clo: usize, chi: usize, f: QubitId, pre: &[QubitId], tmp: QubitId,
                      dirty: &[QubitId], mut per: impl FnMut(&mut B, usize, QubitId)) {
    if clo >= chi {
        return;
    }
    use super::mask::{mc_xor, Dec};
    let mut dec = Dec::new(&cut.v, pre);
    if let Some(v) = cut.val_at(chi as isize) {
        let c = dec.ctrls(b, v);
        mc_xor(b, &c, f, &[tmp], dirty);
    }
    for l in (clo..chi).rev() {
        if l + 1 < chi {
            if let Some(v) = cut.val_at(l as isize + 1) {
                let c = dec.ctrls(b, v);
                mc_xor(b, &c, f, &[tmp], dirty);
            }
        }
        per(b, l, f);
    }
    dec.clear(b);
    cut.ge(b, clo as isize + 1, f, pre);
}

/// masked_swap with an affine cut.
pub fn masked_swapf(b: &mut B, ring: &[QubitId], q: &[QubitId], cut: &Cut, clo: usize, chi: usize, f: QubitId,
                    pre: &[QubitId], tmp: QubitId, dirty: &[QubitId]) {
    let n = ring.len();
    let qlo = n.saturating_sub(q.len());
    for l in chi.max(qlo)..n {
        b.swap(ring[l], q[n - 1 - l]);
    }
    let lo = clo.max(qlo);
    if lo < chi {
        walk_cutf(b, cut, lo, chi, f, pre, tmp, dirty, |b, l, f| {
            b.x(f);
            b.cswap(f, ring[l], q[n - 1 - l]);
            b.x(f);
        });
    }
}

/// msb probe restricted per shot to lanes below `cut`: out ^= bl(v mod 2^cut) for values below the cut.
pub fn msb_probe_cut(b: &mut B, v: &[QubitId], cut: &Cut, clo: usize, chi: usize, out: &[QubitId], f: QubitId,
                     pre: &[QubitId], opre: &[QubitId], tmp: QubitId, tmp2: QubitId, dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    let probe_lane = |b: &mut B, l: usize, fl: Option<QubitId>| {
        let val = l + 1;
        for pass in 0..2 {
            let mut dec = Dec::new(out, opre);
            let mut c = dec.ctrls(b, if pass == 0 { 0 } else { val });
            c.push((v[l], false));
            if let Some(fq) = fl {
                c.push((fq, false));
            }
            mc_xor(b, &c, tmp, &[tmp2], dirty);
            dec.clear(b);
            if pass == 0 {
                for (i, &o) in out.iter().enumerate() {
                    if (val >> i) & 1 == 1 {
                        b.cx(tmp, o);
                    }
                }
            }
        }
    };
    // lanes >= clo are masked by the cut (descending), lanes below clo are inside every shot's range
    walk_cutf_desc(b, cut, clo, chi, f, pre, tmp2, dirty, |b, l, f| probe_lane(b, l, Some(f)));
    for l in (0..clo).rev() {
        probe_lane(b, l, None);
    }
}
