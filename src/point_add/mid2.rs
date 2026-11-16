//! sub700b column middle: the quotient estimate's state (R in the ring gap, rho in the pool) is live only inside
//! self-contained P blocks, never across the column's adds, corrections or payload steps.
//!
//! HR (Z = r_j, X = t_{j-1} in the ring top, Y = t_j in Q): a P block copies q0's bits (on HR stepping shots) beside
//! R in the rotated ring, subtracts bq = [rho < Xh] there (q = q0 - bq), uncomputes R and rho and moves q into the
//! fixed lanes F. Then the payload U += q |t_j|, and per bit k (ascending, X_old < Y): X += 2^k q_k Y and
//! q_k ^= [X >= 2^k Y] (the in-place multiply D^-1, which erases q exactly).
//! HT (Z = t_j, X = r_{j-1}, Y = r_j): q = floor(X / Y) by restoring division into F (X becomes r_{j+1}), the payload
//! U += q |t_j|, then a P block moves q beside R, adds bq' = [rho < Xh(R')] (q + bq' = q0 when the estimate is right)
//! and XORs q0's bits back out during the pipeline's inverse.
use super::builder::{B, G};
use super::frogdrop::{cmp_csub_carries, cmp_csub_carries_vz, inc_mixed, reg_add_into, rot_by_range_care, PScr};
use super::frogdrop_col::{ge_const_compact, mc_xor_dn, rec, ring_cadd2_loan, rotated, ColPar, ColScr, Fd};
use super::mask::{mc_xor, Dec};
use super::payload::{gate_le, gate_le_undo, pad, read_lane, ripple, wl, DigScr, PlCol, KE, L0P, NP};
use crate::circuit::QubitId;

/// the new middle replaces stages 3-7 (FD_OLDMID=1 restores the subset-storage middle)
pub fn enabled() -> bool {
    std::env::var("FD_OLDMID").is_err()
}

/// stored quotient bits (the predictor fails q0 >= 2^QB)
pub const QF: usize = KE;

/// least s = sz + sy of any shot at a P block (the start register holds s' = s - SMIN on SBITS lanes)
pub(crate) const SMIN: usize = 228;
pub(crate) const SBITS: usize = 5;

/// Fixed roles of the new middle on the column scratch.
pub(crate) struct Roles {
    /// stepping flag of the running phase during a block (HR: !ph & !sw, HT: ph & !done)
    pub act: QubitId,
    /// bq / bq' while a block holds rho
    pub bqt: QubitId,
    /// bq & act
    pub t2: QubitId,
    /// q between blocks (bit k at f[k])
    pub f: Vec<QubitId>,
    /// rho's top lane after the pipeline (zero), also the swap decoder's fourth prefix
    pub mz: QubitId,
    /// pipeline helpers
    pub pf: QubitId,
    pub pg: QubitId,
    pub pc0: QubitId,
    pub pzero: QubitId,
}

pub(crate) fn roles(sc: &ColScr, tot: usize, kp: usize) -> Roles {
    // (Scheme G on a short pool: no rho; mz is the first pool lane past the old stored-quotient pair)
    let mz = if sc.ps.rho.len() > kp { rotated(&sc.ps.rho, tot)[kp] } else { sc.rho_clean[sc.u2.len()] };
    assert!(sc.rho_clean.contains(&mz), "rho's zero top lane must be clean outside the P frame");
    // F: rho's lanes that are clean outside the P frame (scratch of the HR loop, the HT division and the moves)
    let f: Vec<QubitId> = sc.rho_clean.iter().copied().filter(|&x| x != mz).collect();
    assert!(f.len() >= 12 || super::midg::enabled(), "middle scratch F: {} lanes", f.len());
    // distinct lanes: act on the old stored-quotient lane, bq/t2 on bq and the second overflow lane
    let pool_extra: Vec<QubitId> = {
        let mut v: Vec<QubitId> = sc.ps.q0.clone();
        v.sort();
        v.dedup();
        v
    };
    assert!(pool_extra.len() >= 2, "two old stored-quotient lanes");
    let r = Roles { act: pool_extra[0], bqt: sc.bq, t2: pool_extra[1], f, mz, pf: sc.ps.f, pg: sc.ps.g,
                    pc0: sc.ps.c0, pzero: sc.ps.zero };
    let all = [r.act, r.bqt, r.t2, r.mz, r.pf, r.pg, r.pc0, r.pzero];
    for (i, a) in all.iter().enumerate() {
        for b2 in &all[i + 1..] { assert_ne!(a, b2, "middle roles overlap"); }
        assert!(!r.f.contains(a));
    }
    r
}

/// y <-> x on shots with AND(ctrls)
pub(crate) fn mc_swap(b: &mut B, ctrls: &[(QubitId, bool)], x: QubitId, y: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    b.cx(y, x);
    let mut c = ctrls.to_vec();
    c.push((x, false));
    mc_xor(b, &c, y, temps, dirty);
    b.cx(y, x);
}

/// c <-> lane(v) on shots with reg == v (v in [lo, hi]) and AND(extra)
#[allow(clippy::too_many_arguments)]
pub(crate) fn dec_swap(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, c: QubitId,
            extra: &[(QubitId, bool)], pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    let mut dec = Dec::new(reg, pre);
    for v in lo..=hi {
        if v >= 1usize << reg.len() { break; }
        if let Some(l) = lane(v) {
            let mut ct = dec.ctrls(b, v);
            ct.extend_from_slice(extra);
            mc_swap(b, &ct, l, c, temps, dirty);
        }
    }
    dec.clear(b);
}

/// In the P frame (ring down by sz; the start register `sv` holds s' = sz + sy - SMIN): reverse the
/// beside-R segment [K+1, n - s) on shots with AND(extra), i.e. lane K+1+k <-> lane n-1-s-k (the in-place quotient
/// lane, X-index sy + k, once the frame is undone).
#[allow(clippy::too_many_arguments)]
fn reflect_beside(b: &mut B, ring: &[QubitId], kk: usize, sv: &[QubitId], extra: &[(QubitId, bool)], pre: &[QubitId],
                  temps: &[QubitId], dirty: &[QubitId]) {
    let n = ring.len();
    assert_eq!(sv.len(), SBITS);
    let vals: Vec<(usize, usize)> = (0..1usize << SBITS).map(|v| (v, v + SMIN)).collect();
    let mut dec = Dec::new(sv, pre);
    for (v, s_true) in vals {
        let l = n as isize - kk as isize - 1 - s_true as isize;
        if l < 2 { continue; }
        let l = l as usize;
        let mut ct = dec.ctrls(b, v);
        ct.extend_from_slice(extra);
        for i in 0..l / 2 {
            mc_swap(b, &ct, ring[kk + 1 + i], ring[kk + l - i], temps, dirty);
        }
    }
    dec.clear(b);
}

/// t += s (positions k.. of the post region) on shots with c, writing only positions pos <= 258 - 2^sh (sy >> sh):
/// the post region [0, 258 - sy] and at most 2^sh - 1 positions above it (zero source and carry there). The write
/// mask g = c & [sy >> sh <= (258 - pos) >> sh] grows one decoded value at a time and ends as g = c.
#[allow(clippy::too_many_arguments)]
fn trans_masked(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, c: QubitId, sy: &[QubitId], sh: usize,
                sylo: usize, syhi: usize, g: QubitId, c0: QubitId, pre: &[QubitId], temps: &[QubitId],
                dirty: &[QubitId]) {
    let bits = &sy[sh..];
    let (alo, ahi) = (sylo >> sh, syhi >> sh);
    let mut dec = Dec::new(bits, pre);
    let mut next = alo;
    let mut mid = |_b: &mut B| {};
    let mut gate = |b: &mut B, i: Option<usize>| -> Option<QubitId> {
        let lim = match i { Some(i) => (258 - (k + i) as isize).div_euclid(1 << sh), None => isize::MAX };
        while next <= ahi && (next as isize) <= lim {
            let mut ct = dec.ctrls(b, next);
            ct.push((c, false));
            mc_xor(b, &ct, g, temps, dirty);
            next += 1;
        }
        match i {
            Some(_) => Some(g),
            None => {
                dec.clear(b);
                b.cx(c, g);
                None
            }
        }
    };
    ripple(b, t, s, c0, false, &mut mid, &mut gate);
}

/// HT restoring division with q in place (X = r_{j-1} in the ring top, Y = r_j in Q). Per bit k (descending,
/// X < 2^(k+1) Y): q_k = [X >> k >= Y], the carry read at the shot's relative position sy (X's lanes above it hold
/// q's upper bits); X -= 2^k q_k Y; the payload U += 2^k q_k |t_j| (|t_j| = Z in the ring bottom, write mask
/// `trans_masked` stops below the in-place bits); then q_k moves to X-index sy + k (zero on stepping shots once
/// X < 2^k Y). q's top bit waits on `c23` until bit 0's payload add has run (its lane is bit 0's top source lane).
#[allow(clippy::too_many_arguments)]
pub(crate) fn ht_div_inplace(b: &mut B, fd: &Fd, cp: &ColPar, act: QubitId, ds: &DigScr, c: QubitId, c23: QubitId,
                  bank: &[QubitId], temps: &[QubitId], chain: &[QubitId], pl: Option<&PlCol>, dirty: &[QubitId]) {
    let n = fd.ring.len();
    let nq = fd.q.len();
    let mt = (n - (cp.sz.0 + cp.h) + 1).min(nq.max(cp.xw) + 1);
    let (szlo, szhi) = (cp.sz.0.max(1), cp.sz.1.min(256));
    let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(L0P));
    let srange = (szlo + sylo, (szhi + syhi).min(257));
    let top = QF - 1;
    let lane_at = |k: usize| move |v: usize| {
        let i = n as isize - 1 - v as isize - k as isize;
        if i >= 0 { Some(fd.ring[i as usize]) } else { None }
    };
    let mut ran_top = false;
    for k in (0..QF).rev() {
        if k >= mt { continue; }
        let qk = if k == top { c23 } else { c };
        let mut hxe: Vec<QubitId> = vec![ds.sv];
        hxe.extend_from_slice(chain);
        if k == top { hxe.push(c); }
        let Some((fa, made)) = gate_le(b, ds, act, srange, 257 - k as isize, &hxe) else { continue };
        if k == top { ran_top = true; }
        // X >> k < 2 Y: positions 0..=sy decide the compare and take the whole subtraction
        let span = (syhi + 1).min(mt - k);
        let mut pads: Vec<QubitId> = ds.zeros.clone();
        pads.extend([ds.sv, ds.g]);
        let t: Vec<QubitId> = (k..k + span).map(|m| fd.ring[n - 1 - m]).collect();
        let src: Vec<QubitId> = fd.q.iter().chain(pads.iter()).copied().take(span).collect();
        assert_eq!(src.len(), span, "HT division pads");
        let rd = src.clone();
        let mut mid = |b: &mut B| {
            let lane = |v: usize| if v < rd.len() { Some(rd[v]) } else { None };
            read_lane(b, &fd.sy, sylo, syhi, &lane, true, &[(fa, false)], qk, bank, &ds.tmp, dirty);
        };
        let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| qk);
        ripple(b, &t, &src, ds.c0, true, &mut mid, &mut gate);
        if let Some(pl) = pl {
            let sh = (usize::BITS - 1 - (k + 1).leading_zeros()) as usize;
            let tt: Vec<QubitId> = (k..NP).map(|pos| wl(&pl.p, pos)).collect();
            let ss: Vec<QubitId> = fd.ring[..(NP - k).min(fd.ring.len())].to_vec();
            trans_masked(b, &tt, &ss, k, qk, &fd.sy, sh.min(4), sylo, syhi, ds.g, ds.c0, bank, temps, &pl.dirty);
        }
        // (lowq_cross repair) the in-place lane X-index sy + k is the quotient's only where the gate took bit k
        // (s <= 257 - k); past it the lane lies in the headroom or Z: swap under the gate, not act
        if k != top {
            dec_swap(b, &fd.sy, sylo, syhi, &lane_at(k), c, &[(fa, false)], bank, temps, dirty);
        }
        if made { gate_le_undo(b, ds, act, 257 - k as isize, &hxe); }
    }
    if ran_top {
        let mut hxe: Vec<QubitId> = vec![ds.sv];
        hxe.extend_from_slice(chain);
        hxe.push(c);
        if let Some((fa, made)) = gate_le(b, ds, act, srange, 257 - top as isize, &hxe) {
            dec_swap(b, &fd.sy, sylo, syhi, &lane_at(top), c23, &[(fa, false)], bank, temps, dirty);
            if made { gate_le_undo(b, ds, act, 257 - top as isize, &hxe); }
        }
    }
}

/// bqt ^= [rho < Xh] inside the P frame (ring down by sz; `s5` = s' = s - SMIN). The ring down by a = ~s' (31 - s')
/// puts X's top kp bits at fixed lanes: Xh bit j (X bit sy - kp + j) at ring[WL + kp - 1 - j], WL = n - SMIN - 31.
/// Below X's LSB those lanes hold Z's low bits, so for sy < kp the compare drops positions below d = kp - sy: its
/// carry lane into position d is swapped with the clean `z0` there (rho < X 2^d iff rho >> d < X).
#[allow(clippy::too_many_arguments)]
/// Where bcmp_in's carry restart (sy < kp) reads d = kp - sy.
pub(crate) enum Restart<'a> {
    Sy(&'a [QubitId]),
}

#[allow(clippy::too_many_arguments)]
fn bcmp_in(b: &mut B, ring: &[QubitId], s5: &[QubitId], rs: &Restart, sylo: usize, syhi: usize, rho_rot: &[QubitId],
           kp: usize, bqt: QubitId, c0: QubitId, pad: QubitId, z0: QubitId, pre: &[QubitId], temps: &[QubitId],
           dirty: &[QubitId]) {
    let n = ring.len();
    let wl = n - SMIN - 31;
    let dest: std::collections::BTreeSet<usize> = (wl..wl + kp).collect();
    let rot = rec(b, |b| {
        for &x in s5 { b.x(x); }
        rot_by_range_care(b, ring, s5, 0, 31, true, dirty, &dest);
        for &x in s5 { b.x(x); }
    });
    let mut s: Vec<QubitId> = (0..kp).map(|j| ring[wl + kp - 1 - j]).collect();
    s.push(pad);
    assert_eq!(rho_rot.len(), kp + 1);
    let up = rec(b, |b| {
        for &q in rho_rot { b.x(q); }
        let Restart::Sy(dsy) = rs;
        let mut dec = Dec::new(dsy, pre);
        for i in 0..=kp {
            let v = kp as isize - i as isize;
            if i >= 1 && v >= sylo.max(1) as isize && v <= syhi as isize {
                let mut ct = dec.ctrls(b, v as usize);
                ct.push((s[i - 1], false));
                // swap s[i-1] <-> z0 on [sy == v]
                b.cx(z0, s[i - 1]);
                mc_xor(b, &ct, z0, temps, dirty);
                b.cx(z0, s[i - 1]);
            }
            let x = if i == 0 { c0 } else { s[i - 1] };
            b.cx(s[i], rho_rot[i]);
            b.cx(s[i], x);
            b.ccx(x, rho_rot[i], s[i]);
        }
        dec.clear(b);
    });
    b.play(&rot, false);
    b.play(&up, false);
    b.cx(s[kp], bqt);
    b.play(&up, true);
    b.play(&rot, true);
}

pub(crate) fn ghash(r: &[G]) -> (usize, u64) {
    let mut h: u64 = 1469598103934665603;
    for g in r {
        let s = format!("{:?}", g);
        for c in s.bytes() { h ^= c as u64; h = h.wrapping_mul(1099511628211); }
    }
    (r.len(), h)
}

/// Scratch of the HT restoring division: q into F; s = sz + sy needs nine bits, so an eight-lane sz takes the (idle)
/// act lane on top.
pub(crate) fn ht_ds(fd: &Fd, sc: &ColScr, ro: &Roles) -> DigScr {
    let sa = if sc.sz.len() >= 9 { sc.sz.clone() } else { let mut v = sc.sz.clone(); v.push(ro.act); v };
    DigScr { e: ro.f.clone(), sa, sb: fd.sy.clone(), sv: ro.bqt, fa: ro.t2, g: ro.pg, c0: ro.pc0,
             tmp: vec![ro.pzero, ro.pf], pre1: vec![], pre2: vec![], zeros: vec![ro.mz], dirty: sc.dirty.clone(),
             smin: 0 }
}

/// Recorded pipeline (head + tail) in the P frame; with `copy`, quotient bit k (k < dest.len()) is also XORed into
/// dest[k] under `act` while the unstored tail lane holds it.
#[allow(clippy::too_many_arguments)]
fn pipeline_rec(b: &mut B, zh: &[QubitId], yh: &[QubitId], startv: &[QubitId], soff: i64, tot: usize, qb: usize,
                ps: &PScr, carries: &[QubitId], tq: QubitId, skip: usize, warm: bool,
                copy: Option<(QubitId, &[QubitId])>) -> Vec<G> {
    b.begin();
    let mut r = ps.r.clone();
    let mut rho = ps.rho.clone();
    let warm_max = zh.len() - 1;
    let chain = &ps.rho[..startv.len() - 1];
    if warm {
        super::mask::ge_const(b, startv, (-soff - warm_max as i64) as isize, ps.g, chain);
        for i in 0..warm_max {
            b.cx(ps.g, r[i]);
            super::mask::ge_const(b, startv, (-soff - i as i64) as isize, r[i], chain);
        }
        super::mask::ge_const(b, startv, (-soff) as isize, ps.g, chain);
    }
    let mut car: Vec<QubitId> = carries.to_vec();
    if !car.contains(&ps.c0) { car.push(ps.c0); }
    let mut dec = Dec::new(startv, &ps.spre);
    for i in 0..tot {
        let md = 1i64 << startv.len();
        let v = i as i64 - soff;
        // a short start register (s' = s - SMIN) holds the exact offset: only in-range steps toggle g
        if startv.len() > SBITS || (0..md).contains(&v) {
            let c = dec.ctrls(b, v.rem_euclid(md) as usize);
            let tt: Vec<QubitId> = if rho.contains(&ps.tmp) { vec![] } else { vec![ps.tmp] };
            mc_xor(b, &c, ps.g, &tt, &ps.dirty);
        }
        let top = r.pop().unwrap();
        r.insert(0, top);
        b.cx(ps.g, r[0]);
        pipeline_step(b, i, tot, qb, skip, zh, yh, ps, &car, tq, copy, &mut r, &mut rho);
    }
    dec.clear(b);
    b.x(ps.g); // every shot's start < tot
    b.end()
}

/// One pipeline step after the g toggle and R's rotation: R's compare-subtract (step >= skip), rho's shift and, in the
/// last qb steps, its compare-subtract with the quotient bit on `tq` (copied to dest under act).
#[allow(clippy::too_many_arguments)]
fn pipeline_step(b: &mut B, i: usize, tot: usize, qb: usize, skip: usize, zh: &[QubitId], yh: &[QubitId], ps: &PScr,
                 car: &[QubitId], tq: QubitId, copy: Option<(QubitId, &[QubitId])>, r: &mut [QubitId],
                 rho: &mut Vec<QubitId>) {
    // a virtual zero top lane when rho holds the zero lane
    let vz = rho.contains(&ps.zero);
    let ccs = |b: &mut B, t: &[QubitId], hi: &[QubitId], c: QubitId, out: QubitId| {
        if vz { cmp_csub_carries_vz(b, t, &hi[1..], c, out, car); }
        else { let mut upper = hi[1..].to_vec(); upper.push(ps.zero); cmp_csub_carries(b, t, &upper, c, out, car); }
    };
    if i >= skip {
        b.x(r[0]);
        ccs(b, &r[1..], zh, r[0], ps.f);
        b.x(r[0]);
        b.cx(ps.f, r[0]);
    }
    let top = rho.pop().unwrap();
    rho.insert(0, top);
    b.cx(ps.f, rho[0]);
    b.cx(r[0], ps.f);
    b.cx(ps.g, ps.f);
    if i + qb >= tot {
        let k = tot - 1 - i;
        b.x(rho[0]);
        ccs(b, &rho[1..], yh, rho[0], tq);
        b.x(rho[0]);
        b.cx(tq, rho[0]);
        if let Some((act, dest)) = copy {
            if k < dest.len() { b.ccx(tq, act, dest[k]); }
        }
        b.cx(rho[0], tq);
        b.cx(r[0], tq);
        b.cx(ps.g, tq);
    }
}

/// target ^= [k < L] gate parts for the beside-R lane k, L = n - (K+1) - s, s in the start register `sv` (s exact on
/// nine lanes, or s mod 256 on eight with every stepping shot's s in [128, 383]). Calls `body` with the extra literal
/// list(s) whose XOR is the flag; `tmp` holds a compare (clean).
fn with_lane_flag(b: &mut B, sv: &[QubitId], n: usize, kk: usize, k: usize, tmp: QubitId, temps: &[QubitId],
                  dirty: &[QubitId], body: &mut dyn FnMut(&mut B, &[(QubitId, bool)])) {
    let t = n as isize - kk as isize - 1 - k as isize; // k < L  <=>  s < t
    if sv.len() >= 9 {
        let g = rec(b, |b| ge_const_compact(b, sv, t, tmp, temps, dirty));
        b.play(&g, false);
        body(b, &[(tmp, true)]);
        b.play(&g, true);
        return;
    }
    assert_eq!(sv.len(), 8);
    let m7 = sv[7];
    if t <= 256 {
        // flag = m >= 128 & m < t
        let g = rec(b, |b| ge_const_compact(b, sv, t, tmp, temps, dirty));
        b.play(&g, false);
        body(b, &[(m7, false), (tmp, true)]);
        b.play(&g, true);
    } else {
        // flag = m >= 128 | m < t - 256 = 1 ^ (m < 128 & m >= t - 256)
        body(b, &[]);
        let g = rec(b, |b| ge_const_compact(b, sv, t - 256, tmp, temps, dirty));
        b.play(&g, false);
        body(b, &[(m7, true), (tmp, false)]);
        b.play(&g, true);
    }
}

/// The new middle (stages 3-7). `swap`: the stage-2 masked swap X <-> Y (four clean prefixes g, c0, cmpc, mz).
#[allow(clippy::too_many_arguments)]
pub(crate) fn middle(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: Option<&PlCol>, swap: &[G],
                     stage: &mut dyn FnMut(&mut B) -> bool) {
    let n = cp.n;
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    let nq = q.len();
    let ph = fd.ph;
    let (k, kp, qb, tot) = (cp.k, cp.kp, sc.ps.q0.len(), cp.tot);
    assert!(cp.h >= k + 2, "the new middle keeps q beside R: ring headroom K + 2");
    let dirty = sc.dirty.clone();
    let ro = roles(sc, tot, kp);
    let pclo = cp.sz.0 + cp.h;
    let mt = (n - pclo + 1).min(nq.max(cp.xw) + 1);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let loan_end = nq - if cp.dn { fd.cnt.len() } else { 0 };
    // ---- P frame (as the subset middle): ring down by sz, Q down by sy, sz += sy
    let soff = tot as i64 - 256 - k as i64 - kp as i64;
    let mut empty = nq.saturating_sub(cp.sy.1.min(nq)).min(nq - kp);
    if cp.dn { empty = empty.min(nq - fd.cnt.len() - 26); }
    let held = empty.min(sc.sz.len() - 1);
    let pcar = (empty - held).min(kp + 1);
    let (sylo, syhi) = (cp.sy.0.max(1).min(nq), cp.sy.1.min(nq));
    let mut ps = PScr { r: ring[0..k + 1].to_vec(), ..sc.ps.clone() };
    ps.dirty = dirty.clone();
    ps.spre = q[..held].to_vec();
    ps.tmp = ro.pzero;
    // rho: the column's clean lanes, then (short pools) lanes that are zero in the frame only
    let rho_mid = sc.ps.rho.clone();
    assert_eq!(rho_mid.len(), kp + 1, "rho for the P block");
    assert_eq!(rotated(&rho_mid, tot)[kp], ro.mz);
    ps.rho = rho_mid.clone();
    // R, the beside lanes and the in-place quotient lanes n - 1 - s - k (s >= SMIN) of the rotated frame
    let dest_r: std::collections::BTreeSet<usize> = (n - k..n).chain(0..(k + 1 + QF).max(n - SMIN + kp)).collect();
    let dest_q: std::collections::BTreeSet<usize> = (nq - kp..nq).chain(0..held + pcar).collect();
    // s' = sz + sy - SMIN on the low SBITS lanes of sz (every shot's s lies in [SMIN, SMIN + 31]); the rest is clean
    let s5: Vec<QubitId> = sc.sz[..SBITS].to_vec();
    let fz: Vec<QubitId> = sc.sz[SBITS..].to_vec();
    // the sw lane joins rho in the frame when the column's rho needs it
    let swe = cp.sw && sc.ps.rho.contains(&sc.sw);
    let rrot = rec(b, |b| {
        rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_r);
        rot_by_range_care(b, &q, &fd.sy, sylo, syhi, true, &dirty, &dest_q);
        reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0);
        let add = rec(b, |b| super::frogdrop::add_const_dirty_exact(b, &sc.sz, SMIN, &dirty));
        b.play(&add, true);
        if swe {
            // sw ^= !ph & [sy - s' >= SMIN - l0] (= its value: sz = s' + SMIN - sy), on rho's clean lanes
            let fl = &ro.f;
            let sub = rec(b, |b| {
                let neg: Vec<QubitId> = s5.to_vec();
                // sy -= s' (s' zero-extended)
                for &x in &fd.sy { b.x(x); }
                let mut sp = neg.clone();
                while sp.len() < fd.sy.len() { sp.push(fl[sp.len() - neg.len()]); }
                reg_add_into(b, &fd.sy, &sp, &fl[3..4], fl[4]);
                for &x in &fd.sy { b.x(x); }
            });
            b.play(&sub, false);
            // sy - s' lies in [-31, 128]: [SMIN - l0 <= v < 2^8 - 31] (negatives wrap to the top)
            let thr = SMIN as isize - cp.l0 as isize;
            let wrap = (1isize << fd.sy.len()) - 31;
            let cmp = rec(b, |b| {
                super::mask::ge_const(b, &fd.sy, thr, fl[5], &fl[6..14]);
                super::mask::ge_const(b, &fd.sy, wrap, fl[5], &fl[6..14]);
            });
            b.play(&cmp, false);
            b.x(ph);
            b.ccx(ph, fl[5], sc.sw);
            b.x(ph);
            b.play(&cmp, true);
            b.play(&sub, true);
        }
    });
    let start_min = SMIN as i64 + soff;
    assert!(start_min >= 0);
    let skip = (k - 1).min(tot - qb);
    let beside: Vec<QubitId> = (0..QF).map(|kk| ring[k + 1 + kk]).collect();
    let carries: Vec<QubitId> = q[held..held + pcar].to_vec();
    ps.spre.truncate(SBITS - 1);
    let yh: Vec<QubitId> = q[nq - kp..nq].to_vec();
    let fwd_copy = pipeline_rec(b, &ring[n - k..n], &yh, &s5, soff + SMIN as i64, tot, qb, &ps, &carries,
                                ro.pf, skip, false, Some((ro.act, &beside)));
    let fwd_plain = pipeline_rec(b, &ring[n - k..n], &yh, &s5, soff + SMIN as i64, tot, qb, &ps, &carries,
                                 ro.pf, skip, false, None);
    let rho_rot = rotated(&rho_mid, tot);
    let _ = swap;
    // bqt ^= [rho < Xh] in the frame (no stage-2 swap, no sy rotation of Q)
    let (bsylo, bsyhi) = (cp.sy.0.max(1), cp.sy.1.min((1usize << fd.sy.len()) - 1));
    let _ = &fz;
    let rs = Restart::Sy(&fd.sy);
    // with the zero lane in rho, the compare pads with g (free between pipeline passes)
    let vzm = rho_mid.contains(&ro.pzero);
    let (bpad, btemps): (QubitId, Vec<QubitId>) = if vzm { (ro.pg, vec![]) } else { (ro.pzero, vec![ro.pg]) };
    let bcmp = |b: &mut B| {
        bcmp_in(b, &ring, &s5, &rs, bsylo, bsyhi, &rho_rot, kp, ro.bqt, ro.pc0, bpad, ro.pf, &[], &btemps, &dirty);
    };

    // ---------------- HR
    let mk = super::frogdrop_col::mark;
    if cp.hr {
        let mut lits = vec![(ph, true)];
        if cp.sw { lits.push((sc.sw, true)); }
        mc_xor(b, &lits, ro.act, &[], &dirty);
        mk(b, 101);
        b.play(&rrot, false);
        mk(b, 102);
        b.play(&fwd_copy, false);
        mk(b, 103);
        mk(b, 104);
        bcmp(b);
        mk(b, 105);
        b.and_c(ro.bqt, ro.act, ro.pg);
        // q = q0 - bq on the beside-R lanes (complement, increment, complement)
        for &x in &beside { b.x(x); }
        inc_mixed(b, ro.pg, &beside, &[], &dirty);
        for &x in &beside { b.x(x); }
        b.and_u(ro.bqt, ro.act, ro.pg);
        mk(b, 106);
        bcmp(b);
        mk(b, 107);
        b.play(&fwd_plain, true);
        mk(b, 108);
        // q (beside R) to its in-place lanes (X-index sy + k after the frame): R and rho are clear, so F's lanes are
        // the decoder's prefixes
        reflect_beside(b, &ring, k, &s5, &[(ro.act, false)], &ro.f[..4], &ro.f[8..10], &dirty);
        b.play(&rrot, true);
        mc_xor(b, &lits, ro.act, &[], &dirty);
        mk(b, 109);
    }
    if !stage(b) { return; } // 3
    if cp.hr {
        // tt (column 1: X may equal Y = 1): run on X - 1 < Y
        let xl: Vec<QubitId> = (0..mt).map(|m| ring[n - 1 - m]).collect();
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, ro.pc0))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
        let c = ro.t2;
        let padl = ro.f[0];
        let bank: Vec<QubitId> = ro.f[1..8].to_vec();
        let temps: Vec<QubitId> = ro.f[8..10].to_vec();
        let wtop = 259 - (L0P + 1);
        let src = if pl.is_some() { pad(&fd.q, &[ro.f[10], ro.f[11]], wtop) } else { vec![] };
        // the HR stepping flag gates the bit moves and the erase compare (other shots hold X >= Y or data there)
        let mut lits = vec![(ph, true)];
        if cp.sw { lits.push((sc.sw, true)); }
        mc_xor(b, &lits, ro.act, &[], &dirty);
        for kk in 0..QF.min(mt) {
            // c <- q_k from X-index sy + k
            let lane = |v: usize| { let i = n as isize - 1 - v as isize - kk as isize; if i >= 0 { Some(ring[i as usize]) } else { None } };
            dec_swap(b, &fd.sy, sylo, syhi, &lane, c, &[(ro.act, false)], &bank, &temps, &dirty);
            if let Some(pl) = pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                super::payload::trans_one(b, &t, &src[..wtop - kk], kk, false, vec![(c, false)], None, ro.pg, ro.pc0, &[],
                                          &pl.dirty);
            }
            ring_cadd2_loan(b, &ring, &q, kk, mt - kk, c, false, &sc.zeros, ro.pc0, ro.bqt, &dirty, lsb, loan_end, ro.mz);
            // c ^= [X >= 2^kk Y]: carry out of the shot's top relative position sy (X < 2^(kk+1) Y)
            let span = (syhi + 1).min(n - kk);
            let t: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - kk - i]).collect();
            let mut s: Vec<QubitId> = q.iter().copied().take(span).collect();
            if s.len() < span { s.push(padl); }
            assert_eq!(s.len(), span);
            let rd = s.clone();
            let mut mid = |b: &mut B| {
                let lane = |v: usize| if v < rd.len() { Some(rd[v]) } else { None };
                read_lane(b, &fd.sy, sylo, syhi, &lane, true, &[(ro.act, false)], c, &bank, &temps, &dirty);
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            ripple(b, &t, &s, ro.pc0, true, &mut mid, &mut gate);
        }
        mc_xor(b, &lits, ro.act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
    }
    if !stage(b) { return; } // 4
    // ---------------- HT
    if cp.ht {
        // the HT stepping flag on the sw lane (sw = !ph & [sz <= l0] is recomputed afterwards), as the payload digit
        let actl = sc.sw;
        let ds = ht_ds(fd, sc, &ro);
        // (after the division F holds q: the compare's carries are the other clean roles)
        let swchain = vec![ro.bqt, ro.pg, ro.pc0, ro.pzero, ro.pf, ro.mz, ro.act];
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            super::mask::ge_const(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &swchain);
            mc_xor(b, &[(ds.fa, true), (ph, true)], sc.sw, &[], &dirty);
            super::mask::ge_const(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &swchain);
        };
        let set_act = |b: &mut B| {
            if cp.dn { mc_xor_dn(b, &[(ph, false)], actl, &ds.tmp, &dirty, fd, cp.l0, false); }
            else { mc_xor(b, &[(ph, false)], actl, &ds.tmp, &dirty); }
        };
        sw_toggle(b);
        set_act(b);
        // q in place (F idle): F[0] the bit control, F[1] q's top bit, decoder bank and temps, the rest chain lanes
        ht_div_inplace(b, fd, cp, actl, &ds, ro.f[0], ro.f[1], &ro.f[2..9], &ro.f[9..11], &ro.f[11..], pl, &dirty);
        set_act(b);
        sw_toggle(b);
    }
    if !stage(b) { return; } // 5
    if cp.ht {
        let set_act = |b: &mut B| {
            if cp.dn { mc_xor_dn(b, &[(ph, false)], ro.act, &[ro.bqt, ro.t2], &dirty, fd, cp.l0, false); }
            else { mc_xor(b, &[(ph, false)], ro.act, &[], &dirty); }
        };
        set_act(b);
        mk(b, 201);
        b.play(&rrot, false);
        // q from its in-place lanes (X-index sy + k) to the beside-R lanes
        reflect_beside(b, &ring, k, &s5, &[(ro.act, false)], &ro.f[..4], &ro.f[8..10], &dirty);
        mk(b, 202);
        b.play(&fwd_plain, false);
        mk(b, 203);
        mk(b, 204);
        bcmp(b);
        mk(b, 205);
        b.and_c(ro.bqt, ro.act, ro.pg);
        inc_mixed(b, ro.pg, &beside, &[], &dirty);
        b.and_u(ro.bqt, ro.act, ro.pg);
        mk(b, 206);
        bcmp(b);
        mk(b, 207);
        b.play(&fwd_copy, true);
        mk(b, 208);
        b.play(&rrot, true);
        set_act(b);
        mk(b, 209);
    }
    if !stage(b) { return; } // 6
    let _ = stage(b); // 7
}
