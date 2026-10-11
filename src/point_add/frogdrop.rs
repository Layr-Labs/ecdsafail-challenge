//! 3-of-4 Euclid machine: reversible 2-adic primitives.
//!
//! The 3-of-4 hold keeps three of (r_{j-1}, r_j, t_{j-1}, t_j); the dropped one is recovered from the invariant
//! r_{j-1} t_j + r_j t_{j-1} = p by an in-place 2-adic map x -> (p - x a) / b. Its building block is the in-place
//! multiply x -> x * a mod 2^L for odd a: top-down, bit i of x (never touched by later adds) controls
//! x[i+1..L) += (a >> 1) << (i + 1). The inverse circuit divides by a.

use super::arith::{down_m, inc, up_m, Dm};
use super::builder::{B,G};
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

/// Exact controlled carry-tail addition using arbitrary dirty passenger wires.
pub fn cadd_tail_and_dirty(b: &mut B, g: QubitId, t: &[QubitId], s: &[QubitId], tl: &[QubitId], c0: QubitId, h: QubitId,
                     dirty: &[QubitId], andc: &[QubitId]) {
    cadd_tail_and_mixed(b, g, t, s, tl, c0, h, &[], dirty, andc)
}

// Fully unitary conditional-clean controlled increment. Anc are globallyzero;
// lower controls are borrowed only while the retained summary implies theyare1.
pub fn conditional_inc_need(n:usize)->usize {
    if n<=1{return 0;}let(mut remaining,mut lower,mut depth)=(n-1,2usize,1usize);
    while remaining>lower+1 {remaining-=lower+1;lower=2*lower+1;depth+=1;}depth
}
pub fn conditional_inc_cost(n:usize)->usize {if n<=1{0}else{3*(n-1)-conditional_inc_need(n)}}
fn conditional_inc_upper(b:&mut B,summary:QubitId,lower:&[QubitId],remaining:&[QubitId],anc:&[QubitId]) {
    if remaining.is_empty(){return;}
    let size=remaining.len().min(lower.len()+1);let(head,rest)=remaining.split_at(size);
    for j in 1..size {let prev=if j==1{head[0]}else{lower[j-2]};b.x(lower[j-1]);b.ccx(prev,head[j],lower[j-1]);}
    if !rest.is_empty(){
        let last=if size==1{head[0]}else{lower[size-2]};let next=anc[0];b.ccx(summary,last,next);
        let mut known=lower.to_vec();known.extend_from_slice(head);
        conditional_inc_upper(b,next,&known,rest,&anc[1..]);b.ccx(summary,last,next);
    }
    for j in (1..size).rev(){let prev=if j==1{head[0]}else{lower[j-2]};
        b.ccx(prev,head[j],lower[j-1]);b.x(lower[j-1]);b.ccx(summary,prev,head[j]);}
    b.cx(summary,head[0]);
}
pub fn conditional_inc(b:&mut B,ctrl:QubitId,bits:&[QubitId],anc:&[QubitId]) {
    if bits.is_empty(){return;}if bits.len()==1{b.cx(ctrl,bits[0]);return;}
    let need=conditional_inc_need(bits.len());assert!(anc.len()>=need);
    let mut seen=std::collections::HashSet::new();assert!(seen.insert(ctrl.0));
    for &q in bits.iter().chain(&anc[..need]){assert!(seen.insert(q.0));}
    let summary=anc[0];b.ccx(ctrl,bits[0],summary);
    conditional_inc_upper(b,summary,&[ctrl,bits[0]],&bits[1..],&anc[1..need]);
    b.ccx(ctrl,bits[0],summary);b.cx(ctrl,bits[0]);
}

/// Controlled tail increment: clean low carry prefix, exact dirty high suffix.
/// The suffix restores its control before any measured prefix is uncomputed.
pub(crate) fn inc_mixed(b: &mut B, ctrl: QubitId, bits: &[QubitId], anc: &[QubitId], dirty: &[QubitId]) {
    if bits.is_empty() { return; }
    let old_k=anc.len().min(bits.len()-1);
    let old_suffix=bits.len()-old_k;
    let old_cost=old_k+if old_suffix==1{0}else{4*old_suffix};
    let mut best=None;
    for k in 0..=old_k {let suffix=bits.len()-k;let need=conditional_inc_need(suffix);
        if need<=anc.len()-k {let cost=k+conditional_inc_cost(suffix);
            if cost<old_cost&&best.is_none_or(|(paid,_)|cost<paid){best=Some((cost,k));}}}
    if let Some((_,k))=best {
        let mut prev=ctrl;for i in 0..k {b.and_c(prev,bits[i],anc[i]);prev=anc[i];}
        conditional_inc(b,prev,&bits[k..],&anc[k..]);
        for i in (0..k).rev(){let p=if i==0{ctrl}else{anc[i-1]};b.and_u(p,bits[i],anc[i]);b.cx(p,bits[i]);}
        return;
    }
    let k = old_k;
    let mut prev = ctrl;
    for i in 0..k {
        b.and_c(prev, bits[i], anc[i]);
        prev = anc[i];
    }
    if bits.len() - k == 1 {
        b.cx(prev, bits[k]);
    } else {
        let mut high = vec![prev];
        high.extend_from_slice(&bits[k..]);
        super::modp_frogdrop::inc_dirty_free(b, &high, dirty);
        b.x(prev);
    }
    for i in (0..k).rev() {
        let p = if i == 0 { ctrl } else { anc[i - 1] };
        b.and_u(p, bits[i], anc[i]);
        b.cx(p, bits[i]);
    }
}

/// Exact carry-tail addition using every available clean prefix, with an
/// arbitrary dirty passenger suffix only beyond that prefix.
pub fn cadd_tail_and_mixed(b: &mut B, g: QubitId, t: &[QubitId], s: &[QubitId], tl: &[QubitId], c0: QubitId, h: QubitId,
                     anc: &[QubitId], dirty: &[QubitId], andc: &[QubitId]) {
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
        inc_mixed(b, h, tl, anc, dirty);
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
        // Only nt-1 tail-prefix qubits are live in this add. The remainder
        // are clean carry loans; every loan is returned before the next add.
        let used_tail = nt.saturating_sub(1);
        let mut carry = andc.to_vec();
        carry.extend(&anc[used_tail..]);
        if nt == 0 { carry.push(h); } // no tail: its conjunction qubit is idle
        carry.truncate(nm);
        cadd_tail_and(b, g, &v[lo..lo + nm], &a[1..1 + nm], &v[lo + nm..lo + nm + nt], c0, h,
                      &anc[..used_tail], &carry);
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

/// Frame multiplication with exact dirty tail increments.
pub fn mul_odd_frame_and_dirty(b: &mut B, v: &[QubitId], top: usize, llo: usize, lsbv: &[QubitId],
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
        // Only nt-1 tail-prefix qubits are live in this add. The remainder
        // are clean carry loans; every loan is returned before the next add.
        let clean_tail = nt.saturating_sub(1) <= anc.len();
        let used_tail = nt.saturating_sub(1).min(anc.len());
        let mut carry = andc.to_vec();
        carry.extend(&anc[used_tail..]);
        if nt == 0 { carry.push(h); } // no tail: its conjunction qubit is idle
        carry.truncate(nm);
        if clean_tail {
            cadd_tail_and(b, g, &v[lo..lo + nm], &a[1..1 + nm], &v[lo + nm..lo + nm + nt], c0, h,
                          &anc[..used_tail], &carry);
        } else {
            cadd_tail_and_mixed(b, g, &v[lo..lo + nm], &a[1..1 + nm], &v[lo + nm..lo + nm + nt], c0, h,
                               &anc[..used_tail], dirty, &carry);
        }
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

/// Clean for the complete frame multiply: the region mask and probe temp have
/// been restored by the preceding shift; the constant-one qubit is idle;
/// tz_probe returns every probe prefix clean while keeping only ez as data.
/// Cut decoder prefixes, ez, and the running enable/control stay separate.
fn frame_carries(sc: &MapScr) -> Vec<QubitId> {
    let mut carry = sc.andc.clone();
    carry.extend([sc.f, sc.tmp, sc.one]);
    // tz-probe prefixes are clean here, but any shared cut prefix is live
    // in the frame's decoder and must never become a carry loan.
    carry.extend(sc.epre.iter().copied().filter(|q| !sc.pre.contains(q)));
    assert_eq!(carry.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), carry.len());
    carry
}

/// One frame multiply (inverse = divide) of the ring's bottom region [0, cut) by Q's value (odd, lanes [0, m)):
/// rotate the ring down by cut so the region sits under the fixed top, multiply with gated controls, rotate back.
fn frame_mul(b: &mut B, ring: &[QubitId], q: &[QubitId], cut: &Cut, par: &MapPar, sc: &MapScr, inverse: bool, fuse: bool) {
    let n = ring.len();
    // q is already rotated down by its exact trailing-zero count. The original
    // value fits par.m bits; its low zero bits wrap into the high zero suffix.
    // These source-external lanes are clean for the entire frame arithmetic.
    // Return every loan before undoing q's normalization or probing its value.
    let mut loaned = sc.clone();
    loaned.anc.extend_from_slice(&q[par.m..]);
    let sc = &loaned;
    b.begin();
    // rotate down by cut = a +- v: down by a is a relabel; down by v (or up by v when cut = a - v)
    let (vlo,vhi)=if cut.neg {((cut.a-par.chi as isize) as usize,(cut.a-par.clo as isize) as usize)}
                  else {((par.clo as isize-cut.a) as usize,(par.chi as isize-cut.a) as usize)};
    if fuse {
        assert!(cut.neg && cut.a==n as isize);
        assert!(vhi+par.emax < (1usize<<cut.v.len()));
        let pad=cut.v.len()-sc.ez.len();
        assert!(pad<=sc.anc.len());
        let mut ev=sc.ez.clone();ev.extend_from_slice(&sc.anc[..pad]);
        assert!(ev.iter().all(|w|!cut.v.contains(w)&&!ring.contains(w)));
        b.begin();super::arith::ttk_add(b,&ev,&cut.v,None,None);let add_e=b.end();
        b.play(&add_e,false);
        rot_by_range(b,ring,&cut.v,vlo,vhi+par.emax,false,&sc.dirty);
        shift_regionf(b,ring,&Cut::reg(&cut.v),vlo,vhi+par.emax,&sc.ez,false,sc.f,&sc.pre,sc.tmp,sc.g,&sc.dirty);
        b.play(&add_e,true);
    } else {rot_by_range(b,ring,&cut.v,vlo,vhi,!cut.neg,&sc.dirty);}
    let a = cut.a.rem_euclid(n as isize) as usize;
    let fr: Vec<QubitId> = (0..n).map(|i| ring[(i + a) % n]).collect(); // frame lane i = lane i + a
    // region now [n - cut, n): lsb = n - cut; decoder value of v for a given lsb
    let (ca, neg) = (cut.a, cut.neg);
    let vof = move |lsb: usize| -> usize {
        let c = n as isize - lsb as isize; // cut
        let x = if neg { ca - c } else { c - ca };
        x.max(0) as usize
    };
    
    mul_odd_frame_bounded(b, &fr, n, n-par.chi, n-par.clo, &cut.v, vof,
        &q[..par.m], par.tail, sc.c0, sc.h, &sc.anc, sc.e, &sc.pre, sc.g,
        &sc.dirty, &frame_carries(sc));
    
    rot_by_range(b,ring,&cut.v,vlo,vhi,cut.neg,&sc.dirty);
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
    let fuse=b.allow_booth && cut.neg && cut.a==ring.len() as isize;
    b.begin();
    // All map roles except the retained valuation output are globally zero
    // at each probe seam. Extension/source/header wires are never included.
    let mut tz_bank=super::priority_probe::map_bank(sc);
    tz_bank.retain(|q|!sc.ez.contains(q));
    assert!(!tz_bank.iter().any(|w|q.contains(w)||ring.contains(w)||cut.v.contains(w)||sc.dirty.contains(w)));
    super::priority_probe::trailing(b,q,par.emax,&sc.ez,&tz_bank);
    let prec = b.end();
    let mut on = false; // probe toggles between compute and its exact inverse
    let mut probe = |b: &mut B| { b.play(&prec, on); on = !on; };
    // multiply by X: X_odd in Q (rotate down by eX), Z * 2^eX (region shift), frame multiply, undo the rotation
    if !go(b) { return; }  probe(b); 
    if !go(b) { return; }  rot_by_source_support(b, q, &sc.ez, par.m, true); 
    if !go(b) { return; }  if !fuse {shift_regionf(b, ring, cut, clo, chi, &sc.ez, true, sc.f, &sc.pre, sc.tmp, sc.g, &sc.dirty);} 
    if !go(b) { return; }  frame_mul(b, ring, q, cut, par, sc, false, fuse); 
    if !go(b) { return; }  rot_by_source_support(b, q, &sc.ez, par.m, false); 
    if !go(b) { return; }  probe(b); 
    if !go(b) { return; }  p_minusf(b, ring, cut, clo, chi, par.tail, &sc.anc, sc.one, sc.f, &sc.pre, sc.tmp, &sc.dirty); 
    if !go(b) { return; }  masked_swapf(b, ring, q, cut, clo, chi, sc.f, &sc.pre, sc.tmp, &sc.dirty); 
    if !go(b) { return; }  probe(b); 
    if !go(b) { return; }  rot_by_source_support(b, q, &sc.ez, par.m, true); 
    if !go(b) { return; }  frame_mul(b, ring, q, cut, par, sc, true, fuse); 
    if !go(b) { return; }  if !fuse {shift_regionf(b, ring, cut, clo, chi, &sc.ez, false, sc.f, &sc.pre, sc.tmp, sc.g, &sc.dirty);} 
    if !go(b) { return; }  rot_by_source_support(b, q, &sc.ez, par.m, false); 
    if !go(b) { return; }  probe(b); 
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

/// Exact paid reciprocal warm-start and two physically funded overflow quotient lanes.
pub fn pipeline_overflow_off(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], soff: i64, tot: usize, qb: usize,
                    ps: &PScr) -> (Vec<QubitId>, Vec<QubitId>) {
    pipeline_overflow_carry_off(b,zh,yh,startv,soff,tot,qb,ps,&[])
}

/// Overflow pipeline with disjoint, clean carries leased for the complete P.
pub fn pipeline_overflow_carry_off(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], soff: i64, tot: usize, qb: usize, ps: &PScr, carries: &[QubitId]) -> (Vec<QubitId>, Vec<QubitId>) {
    pipeline_overflow_carry_off_prefix(b,zh,yh,startv,soff,tot,qb,ps,carries,0)
}
pub fn pipeline_overflow_carry_off_prefix(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], soff: i64, tot: usize, qb: usize,
                    ps: &PScr, carries: &[QubitId], skip: usize) -> (Vec<QubitId>, Vec<QubitId>) {
    assert_eq!(qb,ps.q0.len());
    use super::mask::{mc_xor, Dec};
    let mut r = ps.r.clone();
    let mut rho = ps.rho.clone();
    // The existing zero rho bank is idle until the first reciprocal iteration.
    // For 1<=d=-start<=K-1 seed R=2^d-1; all omitted quotient bits are zero.
    // Outside this safe warm-start interval the seed is the identity.
    let warm_max = zh.len()-1;
    assert!(skip <= warm_max && skip <= tot-qb);
    let chain = &ps.rho[..startv.len()-1];
    super::mask::ge_const(b,startv,(-soff-warm_max as i64) as isize,ps.g,chain);
    for i in 0..warm_max {
        b.cx(ps.g,r[i]);
        super::mask::ge_const(b,startv,(-soff-i as i64) as isize,r[i],chain);
    }
    super::mask::ge_const(b,startv,(-soff) as isize,ps.g,chain);
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
        if i >= skip { if carries.is_empty() {
            super::virtual_odd::cmp_csub_virtual_odd(b, &r, zh, ps.zero, ps.f);
        } else {
            let mut upper=zh[1..].to_vec();upper.push(ps.zero);
            b.x(r[0]);
            cmp_csub_carries(b,&r[1..],&upper,r[0],ps.f,carries);
            b.x(r[0]);b.cx(ps.f,r[0]);
        }
        }
        // rho = 2 rho + f
        let top = rho.pop().unwrap();
        rho.insert(0, top);
        b.cx(ps.f, rho[0]);
        // f = parity(R) ^ g -> clear
        b.cx(r[0], ps.f);
        b.cx(ps.g, ps.f);
        if i + qb >= tot {
            let k = tot - 1 - i;
            if carries.is_empty() { cmp_csub(b, &rho, yh, ps.zero, ps.c0, ps.q0[k]); }
            else {let mut sy=yh.to_vec();sy.push(ps.zero);cmp_csub_carries(b,&rho,&sy,ps.c0,ps.q0[k],carries);}
        }
    }
    dec.clear(b);
    b.x(ps.g); // every shot's start < tot
    (r, rho)
}

/// Compare/subtract with an arbitrary carry-in and measured top carries.
/// s,t have equal length; out XORs the complemented carry of ~t+s+c0,
/// then the selected subtraction is applied with exactly the original ladder
/// semantics. All clean carries are returned before their controls change.
pub fn cmp_csub_carries(b:&mut B,t:&[QubitId],s:&[QubitId],c0:QubitId,out:QubitId,andc:&[QubitId]) {
    let n=t.len();assert_eq!(n,s.len());assert!(n>0);
    let k=andc.len().min(n);let low=n-k;
    for &x in t {b.x(x);}
    let up=up_m(b,&t[..low],&s[..low],c0,false);
    let dn=down_m(b,&t[..low],&s[..low],c0,Dm::Cond(out),false);
    b.play(&up,false);
    let cw=|i:usize|if i==low {if low==0 {c0}else{s[low-1]}} else {andc[i-low-1]};
    for i in low..n {
        let c=cw(i);b.cx(c,t[i]);b.cx(c,s[i]);
        b.and_c(t[i],s[i],andc[i-low]);b.cx(c,andc[i-low]);
    }
    let cout=if k==0 {s[n-1]} else {andc[k-1]};
    b.x(out);b.cx(cout,out);
    for i in (low..n).rev() {
        let c=cw(i);b.cx(c,andc[i-low]);b.and_u(t[i],s[i],andc[i-low]);
        b.cx(c,t[i]);b.ccx(out,s[i],t[i]);b.cx(c,s[i]);
    }
    b.play(&dn,false);
    for &x in t {b.x(x);}
}

/// Exact dirty constant addition on a small register, signed nonadjacent digits.
fn add_const_dirty_exact(b:&mut B,v:&[QubitId],amount:usize,dirty:&[QubitId]) {
    let mut left=amount as isize;let mut bit=0usize;
    while left!=0 && bit<v.len() {
        if left&1!=0 {
            let digit=2-(left&3); // +1 or -1
            b.begin();super::modp_frogdrop::inc_dirty_free(b,&v[bit..],dirty);let inc=b.end();
            b.play(&inc,digit<0);left-=digit;
        }
        left>>=1;bit+=1;
    }
}
fn rot_const_up(b:&mut B,v:&[QubitId],r:usize) {
    let n=v.len();let r=r%n;if r==0{return;}
    let g=gcd(n,r);for s in 0..g {let cyc:Vec<_>=(0..n/g).map(|k|(s+k*r)%n).collect();
        for k in (1..cyc.len()).rev(){b.swap(v[cyc[k]],v[cyc[k-1]]);}}
}
/// Same rotation for every amount in the unchanged public interval [lo,hi].
/// The normalization is fully paid and returns amount and dirty passenger.
/// Outside that inherited envelope the same IR still has its exact inverse.
pub fn rot_by_range(b:&mut B,v:&[QubitId],amt:&[QubitId],lo:usize,hi:usize,inverse:bool,dirty:&[QubitId]) {
    assert!(lo<=hi && hi<(1usize<<amt.len()));
    let width=if hi==lo {0}else{(usize::BITS-(hi-lo).leading_zeros())as usize};
    // A full-width interval offers no control saving; retain the old circuit.
    if width==amt.len(){rot_by(b,v,amt,inverse);return;}
    let fixed=(lo>>width)<<width;
    if hi>>width==lo>>width {
        b.begin();rot_const_up(b,v,fixed);rot_by(b,v,&amt[..width],false);
        let r=b.end();b.play(&r,inverse);return;
    }
    b.begin();
    b.begin();add_const_dirty_exact(b,amt,lo,dirty);let shift=b.end();
    b.play(&shift,true);rot_const_up(b,v,lo);
    rot_by(b,v,&amt[..width],false);b.play(&shift,false);
    let r=b.end();b.play(&r,inverse);
}

/// MSB probe restricted to the unchanged public bit-length support.
pub fn msb_probe_range(b: &mut B, v: &[QubitId], lo: usize, lim: usize, out: &[QubitId], pre: &[QubitId], tmp: QubitId,
                 dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    assert!(lo<=lim && lim<=v.len());
    for l in (lo..lim).rev() {
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

/// Masked MSB probe restricted to the unchanged public bit-length support.
pub fn msb_probe_cut_range(b: &mut B, v: &[QubitId], cut: &Cut, clo: usize, chi: usize, bitlo: usize, bithi: usize, out: &[QubitId], f: QubitId,
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
    assert!(bitlo<bithi && bithi<=v.len());
    let low=clo.max(bitlo);let high=chi.min(bithi);
    if low<high {
        // The cap can fall below the real cut. Initialize from cut>=high,
        // not only cut==high, and erase the final cut>low predicate exactly.
        cut.ge(b,high as isize,f,pre);
        let mut dec=Dec::new(&cut.v,pre);
        for l in (low..high).rev() {
            if l+1<high {if let Some(v)=cut.val_at(l as isize+1) {
                let c=dec.ctrls(b,v);mc_xor(b,&c,f,&[tmp2],dirty);
            }}
            probe_lane(b,l,Some(f));
        }
        dec.clear(b);cut.ge(b,low as isize+1,f,pre);
    }
    for l in (bitlo..clo.min(bithi)).rev() {probe_lane(b,l,None);}
}

/// Odd frame multiplication with the same public [clo,chi] cut envelope.
/// Rows at or above lhi are always in the region: decoder, enable, and its
/// gated control remain zero and may serve as clean carries until lhi.
pub fn mul_odd_frame_bounded(b: &mut B, v: &[QubitId], top: usize, llo: usize, lhi: usize,
    lsbv: &[QubitId], val_of: impl Fn(usize)->usize, a: &[QubitId], tail: usize,
    c0: QubitId, h: QubitId, anc: &[QubitId], e: QubitId, epre: &[QubitId], g: QubitId,
    dirty: &[QubitId], andc: &[QubitId]) {
    use super::mask::{mc_xor,Dec};
    let m=a.len().saturating_sub(1);
    assert!(top<=v.len() && llo<=lhi && lhi<top && m>=1);
    let old_start=if b.allow_booth{booth_start(top,llo,lhi,m,tail,anc.len(),epre.len(),andc.len())}else{None};
    let signed_start=if b.allow_booth{signed_binary_start(top,llo,lhi,m,tail,anc.len(),epre.len(),andc.len(),old_start)}else{None};
    let batch_plan=if b.signed_batch_admitted(){super::signed_batch_frame::plan(top,llo,lhi,m,anc.len(),epre.len(),andc.len())}else{None};
    if let Some(p)=&batch_plan{assert_eq!(signed_start,Some(p.old),"original signed START compiler differs from pinned public geometry");}
    let signed_start=if let Some(p)=&batch_plan{Some(p.new)}else{signed_start};
    let start=if signed_start.is_some(){signed_start}else{old_start};
    let remaining=start.unwrap_or(top-1);
    let mut edec=Dec::new(lsbv,epre);let mut begun=false;
    if let Some(start)=signed_start{
        let mut fullbank=anc.to_vec();fullbank.extend(andc);fullbank.extend(epre);fullbank.extend([e,g,h]);
        let mut maskedbank=anc.to_vec();maskedbank.extend(andc);maskedbank.extend(epre);maskedbank.extend([g,h]);
        for i in (start+1..top).rev(){
            if let Some(p)=&batch_plan{if let Some((lo,hi,k,chunks))=p.batches.iter().find(|(lo,hi,_,_)|*lo<=i&&i<=*hi){
                if i==*hi{
                    // Original higher signed rows leave only e live; clear it
                    // before the independently typed batch decoder starts.
                    if begun{super::mask::ge_const(b,lsbv,val_of(i+1)as isize+1,e,epre);b.x(e);begun=false;}
                    assert!(anc.len()>=2);let mut bank=anc[2..].to_vec();bank.extend(andc);bank.extend(epre);bank.extend([g,h]);
                    let mut high=anc[2..].to_vec();high.extend(andc);
                    let offset=val_of(llo)as isize-llo as isize;assert!((*lo..=*hi).all(|j|val_of(j)as isize==offset+j as isize));
                    let shape=super::signed_batch::Shape{v:v[..top].to_vec(),source:a[1..].to_vec(),enables:vec![e;hi-lo+1],bank,high_bank:high,dirty:dirty.to_vec(),c0,h,nu:anc[0],sig:anc[1],lo:*lo,hi:*hi,k:*k,inverse:false,chunks:chunks.clone()};
                    b.signed_batch(super::signed_batch_frame::Recipe{shape,cut:lsbv.to_vec(),pre:epre.to_vec(),e,tmp:g,offset,lhi});
                }continue;
            }}
            if i>=lhi{signed_binary_digit(b,v,top,i,a,c0,h,g,&fullbank,dirty);}
            else{
                if !begun{b.x(e);begun=true;}
                if val_of(i+1)<(1usize<<lsbv.len()){let controls=edec.ctrls(b,val_of(i+1));mc_xor(b,&controls,e,&[g],dirty);edec.clear(b);}
                signed_binary_masked_digit(b,v,top,i,a,c0,h,e,g,&maskedbank,dirty);
            }
        }
        let boundary_tail=if batch_plan.is_some(){top-start-1-m}else{tail};
        if start>=lhi{signed_binary_boundary(b,v,top,start,a,boundary_tail,c0,h,anc,e,epre,g,dirty,andc);}
        else{
            if batch_plan.is_some(){
                // The last typed batch returned e to zero. Recreate the exact
                // boundary predicate before the unchanged unsigned recurrence.
                assert!(!begun);
                super::mask::ge_const(b,lsbv,val_of(start)as isize+1,e,epre);b.x(e);begun=true;
            }else{
                if !begun{b.x(e);begun=true;}
                if val_of(start+1)<(1usize<<lsbv.len()){let controls=edec.ctrls(b,val_of(start+1));mc_xor(b,&controls,e,&[g],dirty);edec.clear(b);}
            }
            b.and_c(e,v[start],g);b.x(g);
            let lo=start+1;let nm=(a.len()-1).min(top-lo);let nt=boundary_tail.min(top-lo-nm);let used=nt.saturating_sub(1).min(anc.len());
            let mut carry=andc.to_vec();carry.extend(&anc[used..]);carry.extend(epre);if nt==0{carry.push(h);}carry.truncate(nm);
            let mut bank=anc[..used].to_vec();bank.extend(&carry);
            b.begin();if !super::row_add::choose(b,g,&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&bank,dirty,used,carry.len()){
                cadd_tail_and_mixed(b,g,&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&anc[..used],dirty,&carry);}
            let r=b.end();b.play(&r,true);b.x(g);b.and_u(e,v[start],g);
        }
    }else if let Some(start)=start{
        let mut bank=anc.to_vec();bank.extend(andc);bank.extend(epre);
        assert_eq!(bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),bank.len());
        assert!(!bank.contains(&e)&&!bank.contains(&g)&&!bank.contains(&c0)&&!bank.contains(&h));
        for j in (start..top-1).step_by(2).rev(){booth_digit(b,v,top,j,a,c0,h,e,g,&bank,dirty);}
        booth_boundary_inverse(b,v,top,start,a,tail,c0,h,anc,e,epre,g,dirty,andc);
    }
    for i in (llo..remaining).rev() {
        let lo=i+1;let nm=m.min(top-lo);let nt=tail.min(top-lo-nm);
        let variable=i<lhi;
        if variable {
            if !begun {b.x(e);begun=true;}
            if lo>llo && val_of(lo)<(1usize<<lsbv.len()) {
                let c=edec.ctrls(b,val_of(lo));mc_xor(b,&c,e,&[g],dirty);
            }
            b.and_c(v[i],e,g);
        }
        let used_tail=nt.saturating_sub(1).min(anc.len());
        let mut carry=andc.to_vec();carry.extend(&anc[used_tail..]);
        if !variable {carry.extend(epre);carry.extend([e,g]);}
        if nt==0 {carry.push(h);}
        assert_eq!(carry.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),carry.len());
        carry.truncate(nm);
        let mut bank=anc[..used_tail].to_vec();bank.extend(&carry);
        if !super::row_add::choose(b,if variable{g}else{v[i]},&v[lo..lo+nm],&a[1..1+nm],
            &v[lo+nm..lo+nm+nt],c0,h,&bank,dirty,used_tail,carry.len()) {
            cadd_tail_and_mixed(b,if variable{g}else{v[i]},&v[lo..lo+nm],&a[1..1+nm],
                &v[lo+nm..lo+nm+nt],c0,h,&anc[..used_tail],dirty,&carry);
        }
        if variable {b.and_u(v[i],e,g);}
    }
    if begun {
        if val_of(llo)<(1usize<<lsbv.len()) {let c=edec.ctrls(b,val_of(llo));mc_xor(b,&c,e,&[g],dirty);}
        edec.clear(b);
    }
}

// Private exact-on-Y-domain count prototype. Public source width uses the
// existing column sy upper bound. The complete original target span is kept.
pub fn ring_cadd_loan(b:&mut B,ring:&[QubitId],q:&[QubitId],k:usize,span:usize,g:QubitId,sub:bool,
    zeros:&[QubitId],c0:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,dirty:&[QubitId]) {ring_cadd_loan_extra(b,ring,q,k,span,g,sub,zeros,c0,source_bound,loan_end,middle_zero,dirty,&[]);}
pub fn ring_cadd_loan_extra(b:&mut B,ring:&[QubitId],q:&[QubitId],k:usize,span:usize,g:QubitId,sub:bool,
    zeros:&[QubitId],c0:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,dirty:&[QubitId],extra:&[QubitId]) {
    let source_bound=source_bound.min(q.len());let nm=span.min(source_bound);
    if nm==0 {ring_cadd(b,ring,q,k,span,g,sub,zeros,c0);return;}
    let t:Vec<_>=(k..k+span).map(|i|ring[ring.len()-1-i]).collect();
    let h=zeros[0];assert!(source_bound<=loan_end && loan_end<=q.len());let mut bank=q[source_bound..loan_end].to_vec();bank.extend_from_slice(extra);bank.push(middle_zero);
    if nm==span {bank.push(h);}
    let nt=span-nm;let total_bank=bank.len()+usize::from(nt>0);
    let mut best=None;
    for chunk in 1..=nm {
        let blocks=nm.div_ceil(chunk);let flags=blocks-1+usize::from(nt>0);
        if flags+chunk.saturating_sub(1)>total_bank{continue;}
        let (u,c,_)=super::row_add::model(nm,nt,total_bank,chunk);let cost2=2*u+c;
        if cost2<6*span&&best.as_ref().is_none_or(|&(old,_)|cost2<old){best=Some((cost2,chunk));}
    }
    if let Some((_,chunk))=best {
        if nt>0{bank.push(h);}
        assert_eq!(bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),bank.len());
        assert!(!bank.contains(&g)&&!bank.contains(&c0));
        assert!(!t.iter().any(|q|bank.contains(q))&&!q[..nm].iter().any(|q|bank.contains(q)));
        if sub{for &q in &t{b.x(q);}}
        b.row_add(super::row_add::Row{signed_binary:false,mux:None,g,t:t[..nm].to_vec(),s:q[..nm].to_vec(),tail:t[nm..].to_vec(),c0,h,bank,dirty:dirty.to_vec(),chunk});
        if sub{for &q in &t{b.x(q);}}
    }else{ring_cadd(b,ring,q,k,span,g,sub,zeros,c0);}
}

// Exact unconditional +/- source through the full old ring target span.
// sign is retained; clean source suffix loans are returned before next row.
pub fn ring_signed_add(b:&mut B,ring:&[QubitId],q:&[QubitId],offset:usize,span:usize,sign:QubitId,
    zero:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,spare:QubitId,dirty:&[QubitId]) {ring_signed_add_extra(b,ring,q,offset,span,sign,zero,source_bound,loan_end,middle_zero,spare,dirty,&[]);}
pub fn ring_signed_add_extra(b:&mut B,ring:&[QubitId],q:&[QubitId],offset:usize,span:usize,sign:QubitId,
    zero:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,spare:QubitId,dirty:&[QubitId],extra:&[QubitId]) {
    let source_bound=source_bound.min(q.len());
    assert!(span>0&&offset+span<=ring.len()&&source_bound<=loan_end&&loan_end<=q.len());
    let t:Vec<_>=(offset..offset+span).map(|i|ring[ring.len()-1-i]).collect();let nm=span.min(source_bound);
    let mut bank=q[source_bound..loan_end].to_vec();bank.extend_from_slice(extra);bank.extend([middle_zero,zero,spare]);
    assert_eq!(bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),bank.len());
    assert!(!bank.contains(&sign)&&!t.iter().any(|q|bank.contains(q)));
    if nm>0 {
        let nt=span-nm;
        if let Some((cost2,chunk))=super::row_add::signed_best(nm,nt,bank.len()) {
            if cost2<=2*(2*span.saturating_sub(1)) {
                b.row_add(super::row_add::Row{signed_binary:true,mux:None,g:spare,
                    t:t[..nm].to_vec(),s:q[..nm].to_vec(),tail:t[nm..].to_vec(),c0:sign,h:zero,bank,dirty:dirty.to_vec(),chunk});
                return;
            }
        }
    }
    // Exact unitary full-word fallback; at most one source-padding zero is needed.
    assert!(span<=q.len()+1);let mut src=q[..span.min(q.len())].to_vec();if span>q.len(){src.push(zero);}
    for &x in &src{b.cx(sign,x);}nr_add(b,&t,&src,sign,&[]);for &x in &src{b.cx(sign,x);}
}

// Exact recoding of the retained, optionally quantum-masked quotient.
// Intended only outside a directly outer-controlled replay (allow_booth=true).
pub fn qadd_signed_recode(b:&mut B,ring:&[QubitId],q:&[QubitId],qb:&[QubitId],span:usize,
    act:Option<QubitId>,c0:QubitId,zero:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,
    spare:QubitId,dirty:&[QubitId]) {qadd_signed_recode_extra(b,ring,q,qb,span,act,c0,zero,source_bound,loan_end,middle_zero,spare,dirty,&[]);}
pub fn qadd_signed_recode_extra(b:&mut B,ring:&[QubitId],q:&[QubitId],qb:&[QubitId],span:usize,
    act:Option<QubitId>,c0:QubitId,zero:QubitId,source_bound:usize,loan_end:usize,middle_zero:QubitId,
    spare:QubitId,dirty:&[QubitId],extra:&[QubitId]) {
    assert!(b.allow_booth&&!qb.is_empty()&&qb.len()<=span);
    ring_signed_add_extra(b,ring,q,qb.len()-1,span-qb.len()+1,c0,zero,source_bound,loan_end,middle_zero,spare,dirty,extra);
    for i in (1..qb.len()).rev() {
        if let Some(a)=act{b.and_c(a,qb[i],c0);}else{b.cx(qb[i],c0);}
        b.x(c0);ring_signed_add_extra(b,ring,q,i-1,span-i+1,c0,zero,source_bound,loan_end,middle_zero,spare,dirty,extra);b.x(c0);
        if let Some(a)=act{b.and_u(a,qb[i],c0);}else{b.cx(qb[i],c0);}
    }
    if let Some(a)=act{b.and_c(a,qb[0],spare);}else{b.cx(qb[0],spare);}
    b.x(spare);ring_cadd_loan_extra(b,ring,q,0,span,spare,true,&[zero],c0,source_bound,loan_end,middle_zero,dirty,extra);b.x(spare);
    if let Some(a)=act{b.and_u(a,qb[0],spare);}else{b.cx(qb[0],spare);}
}

// Partial permutation implementing UP exactly on static public support.
// Close retained edge paths through their initially-zero terminal lanes.
fn crot_up_care(b:&mut B,c:QubitId,v:&[QubitId],r:usize,support:&std::collections::BTreeSet<usize>) {
    use std::collections::{BTreeMap,BTreeSet};
    let n=v.len();let r=r%n;if r==0{return;}
    let mut successor:BTreeMap<usize,usize>=support.iter().map(|&i|(i,(i+r)%n)).collect();
    let destinations:BTreeSet<usize>=successor.values().copied().collect();
    for &start in support.difference(&destinations) {
        let mut end=start;while support.contains(&end){end=successor[&end];}
        successor.insert(end,start);
    }
    let mut seen=BTreeSet::new();
    for &start in successor.keys() {
        if seen.contains(&start){continue;}
        let mut cycle=Vec::new();let mut i=start;
        while !seen.contains(&i){seen.insert(i);cycle.push(i);i=successor[&i];}
        assert_eq!(i,start);
        for k in (1..cycle.len()).rev(){b.cswap(c,v[cycle[k]],v[cycle[k-1]]);}
    }
}
fn rot_by_care(b:&mut B,v:&[QubitId],amt:&[QubitId],support:&mut std::collections::BTreeSet<usize>) {
    for (k,&c)in amt.iter().enumerate(){
        let r=(1usize<<k)%v.len();crot_up_care(b,c,v,r,support);
        let shifted:Vec<_>=support.iter().map(|&i|(i+r)%v.len()).collect();support.extend(shifted);
    }
}
// ONE recorded UP circuit is used in either direction. Initial UP support is
// the unchanged Y upper-height window at Q's top. The first DOWN is its inverse
// on low Y with amt=bl(Y); all intervening source uses restore Q before UP.
pub fn rot_by_range_care_y(b:&mut B,v:&[QubitId],amt:&[QubitId],lo:usize,hi:usize,inverse:bool,dirty:&[QubitId]) {
    assert!(lo<=hi&&hi<(1usize<<amt.len())&&hi<=v.len());
    let width=if hi==lo{0}else{(usize::BITS-(hi-lo).leading_zeros())as usize};
    let mut support:std::collections::BTreeSet<usize>=(v.len()-hi..v.len()).collect();
    b.begin();
    if width==amt.len(){rot_by_care(b,v,amt,&mut support);}
    else {
        let fixed=(lo>>width)<<width;
        if hi>>width==lo>>width {
            rot_const_up(b,v,fixed);
            support=support.iter().map(|&i|(i+fixed)%v.len()).collect();
            rot_by_care(b,v,&amt[..width],&mut support);
        }else {
            b.begin();add_const_dirty_exact(b,amt,lo,dirty);let shift=b.end();
            b.play(&shift,true);rot_const_up(b,v,lo);
            support=support.iter().map(|&i|(i+lo)%v.len()).collect();
            rot_by_care(b,v,&amt[..width],&mut support);b.play(&shift,false);
        }
    }
    let rec=b.end();b.play(&rec,inverse);
}

// P-only head/remainder query. A constant full-ring permutation followed by
// a public-range short-circle query selects exactly the original Zh+R window.
// All other ring data is restored by the recorded inverse after the P body.
pub fn p_rot_window(b:&mut B,v:&[QubitId],amt:&[QubitId],lo:usize,hi:usize,head:usize,zeros:usize,inverse:bool,dirty:&[QubitId]) {
    assert!(lo<=hi&&hi<=v.len());
    if head+zeros+hi-lo>v.len(){rot_by_range(b,v,amt,lo,hi,inverse,dirty);return;}
    assert!(head>0&&zeros>0);
    // Exact static price of the existing dirty NAF constant query. A plain
    // n-bit TTK add costs 2n-2; two passes make inc_dirty_free cost4n-4.
    let shift_cost=|base:usize|{
        let mut left=base as isize;let mut bit=0;let mut cost=0;
        while left!=0&&bit<amt.len(){
            if left&1!=0{let digit=2-(left&3);left-=digit;cost+=8*(amt.len()-bit-1);}
            left>>=1;bit+=1;
        }cost
    };
    let mut best=(usize::MAX,lo,0usize,0usize);
    // This is a public constant-lowering choice: no register is observed.
    for base in 0..=lo {
        let span=hi-base;let len=head+zeros+span;
        if len>v.len(){continue;}
        let width=if span==0{0}else{(usize::BITS-span.leading_zeros())as usize};
        assert!(width<=amt.len());
        let aligned=base%(1usize<<width)==0;
        let cost=(0..width).map(|i|len-gcd(len,(1usize<<i)%len)).sum::<usize>()
            +if aligned{0}else{shift_cost(base)};
        if cost<best.0 {best=(cost,base,width,len);}
    }
    let(_,base,width,len)=best;assert!(len>0);
    let mut window=v[v.len()-head..].to_vec();
    window.extend_from_slice(&v[..len-head]);
    b.begin();rot_const_up(b,v,(v.len()-base)%v.len());
    if width>0 {
        if base%(1usize<<width)==0 {rot_by(b,&window,&amt[..width],true);}
        else {
            b.begin();add_const_dirty_exact(b,amt,base,dirty);let shift=b.end();
            b.play(&shift,true);rot_by(b,&window,&amt[..width],true);b.play(&shift,false);
        }
    }
    let query=b.end();
    assert_eq!(best.0,query.iter().filter(|g|matches!(g,G::Ccx(..)|G::AndC(..))).count());
    b.play(&query,!inverse);
}

// Compare two exact public query schedules. The old recorded care permutation
// is retained whenever it is cheaper; the new query covers every body lane.
pub fn p_y_query(b:&mut B,v:&[QubitId],amt:&[QubitId],lo:usize,hi:usize,head:usize,zeros:usize,inverse:bool,dirty:&[QubitId]) {
    b.begin();rot_by_range_care_y(b,v,amt,lo,hi,true,dirty);let old=b.end();
    b.begin();p_rot_window(b,v,amt,lo,hi,head,zeros,true,dirty);let query=b.end();
    let cost=|r:&[G]|r.iter().filter(|g|matches!(g,G::Ccx(..)|G::AndC(..))).count();
    if cost(&query)<cost(&old){b.play(&query,!inverse);}else{b.play(&old,!inverse);}
}

// Private unqualified nonrestoring reciprocal prototype. Original P is retained.
fn nr_add(b:&mut B,t:&[QubitId],s:&[QubitId],cin:QubitId,bank:&[QubitId]) {
    let n=t.len();assert_eq!(n,s.len());assert!(n>0);
    let k=bank.len().min(n-1);let low=n-1-k;
    let up=up_m(b,&t[..low],&s[..low],cin,false);
    let dn=down_m(b,&t[..low],&s[..low],cin,Dm::Sum,false);
    b.play(&up,false);
    let prev=|i:usize|if i==low {if low==0{cin}else{s[low-1]}}else{bank[i-low-1]};
    for i in low..n {
        let c=prev(i);b.cx(c,t[i]);b.cx(c,s[i]);
        if i+1<n {b.and_c(t[i],s[i],bank[i-low]);b.cx(c,bank[i-low]);}
    }
    for i in (low..n).rev() {
        let c=prev(i);
        if i+1<n {b.cx(c,bank[i-low]);b.and_u(t[i],s[i],bank[i-low]);}
        b.cx(c,t[i]);b.cx(s[i],t[i]);b.cx(c,s[i]);
    }
    b.play(&dn,false);
}

pub fn pipeline_nonrestoring_old_rho(b:&mut B,zh:&[QubitId],yh:&[QubitId],startv:&[QubitId],soff:i64,tot:usize,qb:usize,ps:&PScr,carries:&[QubitId],skip:usize)->(Vec<QubitId>,Vec<QubitId>) {
    assert_eq!(qb,ps.q0.len());assert_eq!(ps.r.len(),zh.len()+1);
    let mut r=ps.r.clone();let mut rho=ps.rho.clone();
    let warm_max=zh.len()-1;let chain=&ps.rho[..startv.len()-1];
    super::mask::ge_const(b,startv,(-soff-warm_max as i64)as isize,ps.g,chain);
    for i in 0..warm_max {b.cx(ps.g,r[i]);super::mask::ge_const(b,startv,(-soff-i as i64)as isize,r[i],chain);}
    super::mask::ge_const(b,startv,(-soff)as isize,ps.g,chain);
    // Public proof must guarantee all omitted reciprocal bits are zero.
    assert!(skip<=zh.len()-1 && skip<=tot-qb);
    let mut du=zh[1..].to_vec();du.push(ps.zero);
    let mut dec=super::mask::Dec::new(startv,&ps.spre);
    for i in 0..tot {
        let md=1i64<<startv.len();let c=dec.ctrls(b,(i as i64-soff).rem_euclid(md)as usize);
        super::mask::mc_xor(b,&c,ps.g,&[ps.tmp],&ps.dirty);
        if i<skip {
            let top=r.pop().unwrap();r.insert(0,top);b.cx(ps.g,r[0]);
            let z=rho.pop().unwrap();rho.insert(0,z);
            continue;
        }
        if i==skip {
            for &s in &du {b.x(s);}nr_add(b,&r[1..],&du,r[0],carries);for &s in &du{b.x(s);}b.x(r[0]);
        }
        let top=r.pop().unwrap();r.insert(0,top);
        let previous_q=if i==skip {b.x(top);None}else{
            let z=rho.pop().unwrap();rho.insert(0,z);b.x(top);b.swap(top,z);Some(z)
        };
        b.cx(ps.g,r[0]);b.x(r[0]);
        if let Some(q)=previous_q {for &s in &du{b.cx(q,s);}}
        nr_add(b,&r[1..],&du,ps.g,carries);
        if let Some(q)=previous_q {for &s in &du{b.cx(q,s);}}
        if i>skip && i+qb>tot {
            let k=tot-i;
            if carries.is_empty(){cmp_csub(b,&rho,yh,ps.zero,ps.c0,ps.q0[k]);}
            else{let mut sy=yh.to_vec();sy.push(ps.zero);cmp_csub_carries(b,&rho,&sy,ps.c0,ps.q0[k],carries);}
        }
    }
    dec.clear(b);b.x(ps.g);
    let z=rho.pop().unwrap();rho.insert(0,z);b.cx(r[r.len()-1],z);b.x(z);
    // Normalize final signed remainder, while the last quotient bit is retained.
    b.x(z);b.and_c(z,r[0],ps.f);
    let up=up_m(b,&r[1..],&du,ps.f,false);let dn=down_m(b,&r[1..],&du,ps.f,Dm::Cond(z),false);
    b.play(&up,false);b.play(&dn,false);b.cx(z,r[0]);b.x(r[0]);b.and_u(z,r[0],ps.f);b.x(r[0]);b.x(z);
    if carries.is_empty(){cmp_csub(b,&rho,yh,ps.zero,ps.c0,ps.q0[0]);}
    else{let mut sy=yh.to_vec();sy.push(ps.zero);cmp_csub_carries(b,&rho,&sy,ps.c0,ps.q0[0],carries);}
    (r,rho)
}


// Exact addition with one virtual zero source top. Lower source/carry lanes
// are restored before their predicates change; no physical second zero pad.
fn finite_rho_add_virtual_top(b:&mut B,t:&[QubitId],s:&[QubitId],cin:QubitId,bank:&[QubitId]) {
    let n=t.len();assert_eq!(n,s.len()+1);assert!(n>1);
    let k=bank.len().min(n-1);let low=n-1-k;
    let up=up_m(b,&t[..low],&s[..low],cin,false);
    let dn=down_m(b,&t[..low],&s[..low],cin,Dm::Sum,false);
    b.play(&up,false);
    let prev=|i:usize|if i==low {if low==0{cin}else{s[low-1]}}else{bank[i-low-1]};
    for i in low..n-1 {
        let c=prev(i);b.cx(c,t[i]);b.cx(c,s[i]);
        b.and_c(t[i],s[i],bank[i-low]);b.cx(c,bank[i-low]);
    }
    b.cx(prev(n-1),t[n-1]);
    for i in (low..n-1).rev() {
        let c=prev(i);b.cx(c,bank[i-low]);b.and_u(t[i],s[i],bank[i-low]);
        b.cx(c,t[i]);b.cx(s[i],t[i]);b.cx(c,s[i]);
    }
    b.play(&dn,false);
}
// PRIVATE UNQUALIFIED exact finite-word rho draft. Entry low rho represents
// S=A-(1-previous)*Y; the current unwritten quotient is a globally clean0.
// Its temporary high lane combines the previous sign and the complemented
// virtual source-top, whose XOR is always1. After addition it becomes q.
fn finite_rho_signed_step(b:&mut B,rho:&[QubitId],yh:&[QubitId],previous:Option<QubitId>,out:QubitId,ps:&PScr,bank:&[QubitId]) {
    assert_eq!(rho.len(),yh.len()+1);
    let mut t=rho.to_vec();t.push(out);
    let mut sy=yh.to_vec();sy.push(ps.zero);
    for &q in bank {assert!(!t.contains(&q)&&!sy.contains(&q)&&q!=ps.c0);}
    b.x(out);
    if let Some(q)=previous {
        for &s in &sy {b.cx(q,s);}b.cx(q,ps.c0);
    } else {
        for &s in &sy {b.x(s);}b.x(ps.c0);
    }
    finite_rho_add_virtual_top(b,&t,&sy,ps.c0,bank);
    if let Some(q)=previous {
        b.cx(q,ps.c0);for &s in &sy {b.cx(q,s);}
    } else {
        b.x(ps.c0);for &s in &sy {b.x(s);}
    }
    b.x(out);
}
pub fn pipeline_nonrestoring_off_prefix(b:&mut B,zh:&[QubitId],yh:&[QubitId],startv:&[QubitId],soff:i64,tot:usize,qb:usize,ps:&PScr,carries:&[QubitId],skip:usize)->(Vec<QubitId>,Vec<QubitId>) {
    assert_eq!(qb,ps.q0.len());assert!(qb>0&&qb<=tot);assert_eq!(ps.r.len(),zh.len()+1);
    assert_eq!(ps.rho.len(),yh.len()+1);
    let mut r=ps.r.clone();let mut rho=ps.rho.clone();
    let first=tot-qb+1;
    let mut base_bank=carries.to_vec();
    // f/c0 are clean between old rho comparisons and outside final R repair.
    assert!(!base_bank.contains(&ps.f)&&!base_bank.contains(&ps.c0));
    base_bank.extend([ps.f,ps.c0]);
    let warm_max=zh.len()-1;let chain=&ps.rho[..startv.len()-1];
    super::mask::ge_const(b,startv,(-soff-warm_max as i64)as isize,ps.g,chain);
    for i in 0..warm_max {b.cx(ps.g,r[i]);super::mask::ge_const(b,startv,(-soff-i as i64)as isize,r[i],chain);}
    super::mask::ge_const(b,startv,(-soff)as isize,ps.g,chain);
    // Public proof must guarantee all omitted reciprocal bits are zero.
    assert!(skip<=zh.len()-1 && skip<=tot-qb);
    let mut du=zh[1..].to_vec();du.push(ps.zero);
    let mut dec=super::mask::Dec::new(startv,&ps.spre);
    for i in 0..tot {
        let md=1i64<<startv.len();let c=dec.ctrls(b,(i as i64-soff).rem_euclid(md)as usize);
        super::mask::mc_xor(b,&c,ps.g,&[ps.tmp],&ps.dirty);
        if i<skip {
            let top=r.pop().unwrap();r.insert(0,top);b.cx(ps.g,r[0]);
            let z=rho.pop().unwrap();rho.insert(0,z);
            continue;
        }
        let free=if i<first {qb}else{tot-i+1};
        let mut rbank=base_bank.clone();rbank.extend_from_slice(&ps.q0[..free]);
        let used=rbank.len().min(r.len()-2);let mut seen=std::collections::HashSet::new();
        for &q in &rbank[..used] {assert!(seen.insert(q.0));assert!(!r.contains(&q)&&!du.contains(&q)&&q!=ps.g);}
        if i==skip {
            for &s in &du {b.x(s);}nr_add(b,&r[1..],&du,r[0],&rbank);for &s in &du{b.x(s);}b.x(r[0]);
        }
        let top=r.pop().unwrap();r.insert(0,top);
        let previous_q=if i==skip {b.x(top);None}else{
            let z=rho.pop().unwrap();rho.insert(0,z);
            if i>first {b.x(z);b.cx(ps.q0[tot-i+1],z);}
            b.x(top);b.swap(top,z);Some(z)
        };
        b.cx(ps.g,r[0]);b.x(r[0]);
        if let Some(q)=previous_q {for &s in &du{b.cx(q,s);}}
        nr_add(b,&r[1..],&du,ps.g,&rbank);
        if let Some(q)=previous_q {for &s in &du{b.cx(q,s);}}
        if i>skip && i+qb>tot {
            let k=tot-i;
            let previous=if i==first {None}else{Some(ps.q0[k+1])};
            let mut rho_bank=carries.to_vec();rho_bank.push(ps.f);
            rho_bank.extend_from_slice(&ps.q0[..k]);
            finite_rho_signed_step(b,&rho,yh,previous,ps.q0[k],ps,&rho_bank);
        }
    }
    dec.clear(b);b.x(ps.g);
    let z=rho.pop().unwrap();rho.insert(0,z);
    if qb>1 {b.x(z);b.cx(ps.q0[1],z);}
    b.cx(r[r.len()-1],z);b.x(z);
    // Normalize final signed remainder, while the last quotient bit is retained.
    b.x(z);b.and_c(z,r[0],ps.f);
    let up=up_m(b,&r[1..],&du,ps.f,false);let dn=down_m(b,&r[1..],&du,ps.f,Dm::Cond(z),false);
    b.play(&up,false);b.play(&dn,false);b.cx(z,r[0]);b.x(r[0]);b.and_u(z,r[0],ps.f);b.x(r[0]);b.x(z);
    let mut rho_bank=carries.to_vec();rho_bank.push(ps.f);
    finite_rho_signed_step(b,&rho,yh,if qb==1{None}else{Some(ps.q0[1])},ps.q0[0],ps,&rho_bank);
    // Normalize every original rho lane, including its possibly nonzero top.
    let mut sy=yh.to_vec();sy.push(ps.zero);
    b.x(ps.q0[0]);
    let up=up_m(b,&rho,&sy,ps.c0,false);
    let dn=down_m(b,&rho,&sy,ps.c0,Dm::Cond(ps.q0[0]),false);
    b.play(&up,false);b.play(&dn,false);b.x(ps.q0[0]);
    (r,rho)
}

fn booth_old_cost2(top:usize,i:usize,m:usize,tail:usize,na:usize,np:usize,nc:usize)->usize{
    let n=m.min(top-i-1);let nt=tail.min(top-i-1-n);let used=nt.saturating_sub(1).min(na);
    let carry=n.min(nc+na-used+np+2+usize::from(nt==0));
    let bank=used+carry+usize::from(nt>0);
    let old=3*n-carry+if nt==0{0}else{let k=used.min(nt-1);k+if nt-k==1{0}else{4*(nt-k)}+1};
    let mut best=2*old;
    for chunk in 1..=n{let flags=n.div_ceil(chunk)-1+usize::from(nt>0);
        if flags+chunk-1>bank{continue;}
        let(u,c,_)=super::row_add::model(n,nt,bank,chunk);best=best.min(2*u+c);
    }best
}
fn signed_binary_start(top:usize,llo:usize,lhi:usize,m:usize,tail:usize,na:usize,np:usize,nc:usize,old_start:Option<usize>)->Option<usize>{
    let low=llo.max(top.saturating_sub(m+tail+1));
    let bank=na+np+nc;let signed_bank=bank+3;
    let old_saving=if let Some(start)=old_start{
        let base:usize=(start..top-1).map(|i|booth_old_cost2(top,i,m,tail,na,np,nc)).sum();
        let mut candidate=booth_old_cost2(top,start,m,tail,na,np,nc);
        for j in (start..top-1).step_by(2){let n=(m+1).min(top-j-1);let nt=top-j-1-n;
            candidate+=super::row_add::mux_best(n,nt,bank).unwrap().0;
        }base-candidate
    }else{0};
    let mut best=(old_saving,None);
    for start in low..top-1{
        let base:usize=(start..top-1).map(|i|booth_old_cost2(top,i,m,tail,na,np,nc)).sum();
        let mut candidate=booth_old_cost2(top,start,m,tail,na,np,nc);let mut valid=true;
        for i in start+1..top{let n=m.min(top-i);let nt=top-i-n;
            if let Some((cost,_))=super::row_add::signed_best(n,nt,if i<lhi{signed_bank-1}else{signed_bank}){candidate+=cost+if i<lhi{24}else{0};}else{valid=false;break;}
        }
        if valid&&base>candidate&&base-candidate>best.0{best=(base-candidate,Some(start));}
    }best.1
}
fn signed_binary_digit(b:&mut B,v:&[QubitId],top:usize,i:usize,a:&[QubitId],c0:QubitId,h:QubitId,
    g:QubitId,bank:&[QubitId],dirty:&[QubitId]){
    let n=(a.len()-1).min(top-i);let nt=top-i-n;
    let (_,chunk)=super::row_add::signed_best(n,nt,bank.len()).unwrap();
    b.x(c0);b.cx(v[i],c0);
    b.row_add(super::row_add::Row{signed_binary:true,mux:None,g,t:v[i..i+n].to_vec(),s:a[1..1+n].to_vec(),tail:v[i+n..top].to_vec(),c0,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});
    // Both +B and -B toggle this consumed target bit by exactly original B0.
    b.cx(v[i],c0);b.cx(a[1],c0);b.x(c0);
}
fn signed_binary_masked_digit(b:&mut B,v:&[QubitId],top:usize,i:usize,a:&[QubitId],c0:QubitId,h:QubitId,e:QubitId,g:QubitId,bank:&[QubitId],dirty:&[QubitId]){
 let n=(a.len()-1).min(top-i);let nt=top-i-n;let(_,chunk)=super::row_add::signed_best(n,nt,bank.len()).unwrap();
 b.and_c(e,v[i],c0);b.x(c0);
 b.row_add(super::row_add::Row{signed_binary:true,mux:None,g,t:v[i..i+n].to_vec(),s:a[1..1+n].to_vec(),tail:v[i+n..top].to_vec(),c0,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});
 b.x(c0);b.ccx(e,a[1],c0);b.and_u(e,v[i],c0);
}
fn signed_binary_boundary(b:&mut B,v:&[QubitId],top:usize,start:usize,a:&[QubitId],tail:usize,
    c0:QubitId,h:QubitId,anc:&[QubitId],e:QubitId,epre:&[QubitId],g:QubitId,dirty:&[QubitId],andc:&[QubitId]){
    // Paid -(1-b_start)*B*2^(start+1). The complete common top is retained.
    b.x(v[start]);
    let lo=start+1;let nm=(a.len()-1).min(top-lo);let nt=tail.min(top-lo-nm);let used=nt.saturating_sub(1).min(anc.len());
    let mut carry=andc.to_vec();carry.extend(&anc[used..]);carry.extend(epre);carry.extend([e,g]);if nt==0{carry.push(h);}carry.truncate(nm);
    let mut bank=anc[..used].to_vec();bank.extend(&carry);
    b.begin();
    if !super::row_add::choose(b,v[start],&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&bank,dirty,used,carry.len()){
        cadd_tail_and_mixed(b,v[start],&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&anc[..used],dirty,&carry);
    }
    let r=b.end();b.play(&r,true);
    b.x(v[start]);
}
fn booth_start(top:usize,llo:usize,lhi:usize,m:usize,tail:usize,na:usize,np:usize,nc:usize)->Option<usize>{
    let mut low=llo.max(lhi+1).max(top.saturating_sub(m+tail+1));low+=low&1;
    let bank=na+np+nc;let mut best=(0,None);
    for start in (low..top-1).step_by(2){
        let base:usize=(start..top-1).map(|i|booth_old_cost2(top,i,m,tail,na,np,nc)).sum();
        let mut candidate=booth_old_cost2(top,start,m,tail,na,np,nc);let mut valid=true;
        for j in (start..top-1).step_by(2){let n=(m+1).min(top-j-1);let nt=top-j-1-n;
            if let Some((cost,_))=super::row_add::mux_best(n,nt,bank){candidate+=cost;}else{valid=false;break;}
        }
        if valid&&base>candidate&&base-candidate>best.0{best=(base-candidate,Some(start));}
    }best.1
}
fn booth_digit(b:&mut B,v:&[QubitId],top:usize,j:usize,a:&[QubitId],c0:QubitId,h:QubitId,
    sigma:QubitId,u:QubitId,bank:&[QubitId],dirty:&[QubitId]){
    let m=a.len()-1;let low=v[j];let prev=v[j-1];let high=v[j+1];
    assert!(j>=1&&j+1<top&&j%2==0);
    // u=[digit!=0], sigma=[digit even], c0=original high/sign.
    b.x(sigma);b.cx(low,sigma);b.cx(prev,sigma);b.cx(high,c0);
    b.cx(high,u);b.cx(prev,u);
    b.cx(low,c0);b.x(sigma);b.ccx(c0,sigma,u);b.x(sigma);b.cx(low,c0);
    let n=(m+1).min(top-j-1);let nt=top-j-1-n;let(_,chunk)=super::row_add::mux_best(n,nt,bank.len()).unwrap();
    b.row_add(super::row_add::Row{signed_binary:false,mux:Some(super::row_add::MuxSource{sigma}),g:u,t:v[j+1..j+1+n].to_vec(),s:a[1..].to_vec(),tail:v[j+1+n..top].to_vec(),c0,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});
    // Saved sign is retained through every sum/carry/phase operation. Only
    // low and prev, which descending rows have not touched, clear selectors.
    b.cx(c0,u);b.cx(prev,u);b.cx(low,c0);b.x(sigma);b.and_u(c0,sigma,u);b.x(sigma);b.cx(low,c0);
    b.x(sigma);b.cx(low,sigma);b.cx(prev,sigma);
    // high_new XOR high_old = B0*(low XOR prev), including digit0/double.
    b.cx(high,c0);b.ccx(a[1],low,c0);b.ccx(a[1],prev,c0);
}
fn booth_boundary_inverse(b:&mut B,v:&[QubitId],top:usize,i:usize,a:&[QubitId],tail:usize,
    c0:QubitId,h:QubitId,anc:&[QubitId],e:QubitId,epre:&[QubitId],g:QubitId,dirty:&[QubitId],andc:&[QubitId]){
    let lo=i+1;let nm=(a.len()-1).min(top-lo);let nt=tail.min(top-lo-nm);let used=nt.saturating_sub(1).min(anc.len());
    let mut carry=andc.to_vec();carry.extend(&anc[used..]);carry.extend(epre);carry.extend([e,g]);if nt==0{carry.push(h);}carry.truncate(nm);
    let mut bank=anc[..used].to_vec();bank.extend(&carry);
    b.begin();
    if !super::row_add::choose(b,v[i-1],&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&bank,dirty,used,carry.len()){
        cadd_tail_and_mixed(b,v[i-1],&v[lo..lo+nm],&a[1..1+nm],&v[lo+nm..lo+nm+nt],c0,h,&anc[..used],dirty,&carry);
    }
    let r=b.end();b.play(&r,true);
}

// Recorded UP agrees with full rotation on the normalized low-source support.
// First DOWN is its inverse on the raw value, whose low amount bits are zero.
// Frame uses restore every Q lane, including upper clean loans, before UP.
pub(super) fn rot_by_source_support(b:&mut B,v:&[QubitId],amt:&[QubitId],m:usize,inverse:bool) {
    assert!(m<=v.len());let mut support:std::collections::BTreeSet<usize>=(0..m).collect();
    b.begin();rot_by_care(b,v,amt,&mut support);let rec=b.end();b.play(&rec,inverse);
}

pub(super)fn fusion_kernel_invoice(b:&mut B,ring:&[QubitId],q:&[QubitId],cut:&Cut,par:&MapPar,sc:&MapScr,inverse:bool){frame_mul(b,ring,q,cut,par,sc,inverse,true);}
