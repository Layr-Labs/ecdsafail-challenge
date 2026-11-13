//! q765-HRF: fused pure-HR column pairs (notes/q765/HRF_progress.md).
//!
//! q-box: the skipped quotient q_{j+1} = floor(r_j t_j / (p - r_j t_{j+1})) from W-bit heads.
//! Entry layout (column j after its stage 8): ring = [r_j (lane 0 up) | t_j (ring top, bit i at lane n-1-i)],
//! Q = t_{j+1}, sy = bl(t_j). With s = bl(r_j) - W and u = bl(t_{j+1}) - WT (u may be negative: exact shift up):
//! U = r_j >> s, T1 = t_{j+1} >> u, T0 = t_j >> u. Since bl(r_j) + bl(t_{j+1}) = 256 + d (d in {0,1}, d = parity),
//! p >> (s+u) = 2^(W+WT-d) - 1, so Dh = NOT(U T1) over W+WT-d bits. Products are truncated rows: row i adds
//! floor(U 2^i / 2^LT). The cache receives floor(Nh / Dh) (QC bits); every other lane is restored.
use super::builder::{B, G};
use super::frogdrop::*;
use crate::circuit::QubitId;

pub(crate) const W: usize = 52;
pub(crate) const WT: usize = 52;
pub(crate) const LT: usize = 45;
pub(crate) const QC: usize = 26;
/// product register width (lane 0 = product bit LT)
pub(crate) const RW: usize = W + WT - LT;

/// Public envelopes of column j: bl(r_j), bl(t_j), bl(t_{j+1}).
#[derive(Clone, Copy, Debug)]
pub(crate) struct QEnv {
    pub sz: (usize, usize),
    pub sy: (usize, usize),
    pub sx: (usize, usize),
}

/// Lanes of the q-box. `base` is clean on entry; `late` (ring gap and Q lanes, clean only after the two rotations)
/// is clean on entry too, but holds no role before the rotations.
pub(crate) struct QLanes {
    pub szr: Vec<QubitId>,
    pub dl: QubitId,
    pub c0: QubitId,
    pub h: QubitId,
    pub g: QubitId,
    pub gt: QubitId,
    pub dr: Vec<QubitId>,
    pub nr: Vec<QubitId>,
    pub bank: Vec<QubitId>,
}

fn rec(b: &mut B, f: impl FnOnce(&mut B)) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}

/// Lanes of the rotated ring that are zero for every shot after phase A: [0, 30).
pub(crate) fn ring_gap(ring: &[QubitId]) -> Vec<QubitId> { ring[..30].to_vec() }
/// Q lanes zero for every shot after `rot_q` (Q window q[..qw] rotated down by bl(t_{j+1})).
pub(crate) fn q_free(q: &[QubitId], qw: usize, env: &QEnv) -> Vec<QubitId> { q[..qw - env.sx.1].to_vec() }

/// Carve QLanes: phase-A roles (szr, dl, c0, h) from `base`; dr/nr and the rest from base[rest] ++ late.
pub(crate) fn carve(base: &[QubitId], late: &[QubitId]) -> QLanes {
    let mut all: Vec<QubitId> = base.to_vec();
    all.extend_from_slice(late);
    let szr = base[..9].to_vec();
    let (dl, c0, h, g, gt) = (base[9], base[10], base[11], base[12], base[13]);
    // dr/nr may reuse szr lanes (szr is erased before the products)
    let mut pool: Vec<QubitId> = base[..9].to_vec();
    pool.extend_from_slice(&base[14..]);
    pool.extend_from_slice(late);
    assert!(pool.len() >= 2 * RW, "HRF q-box: {} lanes for the two product registers", pool.len());
    let dr = pool[..RW].to_vec();
    let nr = pool[RW..2 * RW].to_vec();
    let bank = pool[2 * RW..].to_vec();
    QLanes { szr, dl, c0, h, g, gt, dr, nr, bank }
}

/// Phase A: probes, d, ring rotation (U at the top, T0 bit i at lane 31+WT-i after the d shift), szr erased by
/// sz = 256 + d - sx, Q window rotated down by sx (T1 at q[qw-WT..qw]). `sx` is |0> on entry and holds bl(t_{j+1}).
pub(crate) fn phase_a(b: &mut B, ring: &[QubitId], q: &[QubitId], qw: usize, sy: &[QubitId], sx: &[QubitId], env: &QEnv,
           l: &QLanes, probe_bank: &[QubitId], dirty: &[QubitId]) {
    let n = ring.len();
    let cut_y = Cut { v: sy.to_vec(), a: n as isize, neg: true };
    super::masked_priority_probe::emit(b, ring, &cut_y, n - env.sy.1, n - env.sy.0, env.sz.0.saturating_sub(1),
                                       env.sz.1, &l.szr, probe_bank, dirty);
    super::priority_probe::emit(b, &q[..qw], env.sx.0.saturating_sub(1), env.sx.1, sx, probe_bank);
    b.cx(l.szr[0], l.dl);
    b.cx(sx[0], l.dl);
    p_rot_window(b, ring, &l.szr, env.sz.0, env.sz.1, W, 32 + WT, true, dirty);
    // szr += sx (= 256 + d), then clear bit 8 and bit 0 (= d)
    let mut s9: Vec<QubitId> = sx.to_vec();
    s9.push(l.h);
    let add = rec(b, |b| {
        let up = super::arith::up_m(b, &l.szr, &s9, l.c0, false);
        let dn = super::arith::down_m(b, &l.szr, &s9, l.c0, super::arith::Dm::Sum, false);
        b.play(&up, false);
        b.play(&dn, false);
    });
    b.play(&add, false);
    b.x(l.szr[8]);
    b.cx(l.dl, l.szr[0]);
    // d: T0 bit i at lane 31 + WT - i - d -> shift the window up by d (segment [30, 31 + WT])
    for k in (31..=31 + WT).rev() {
        b.cswap(l.dl, ring[k], ring[k - 1]);
    }
    rot_by_range(b, &q[..qw], sx, env.sx.0, env.sx.1, true, dirty);
}

/// t += g * s with a one-lane tail (carry bound by the row order).
fn row_add(b: &mut B, g: QubitId, t: &[QubitId], s: &[QubitId], tl: &[QubitId], l: &QLanes, dirty: &[QubitId]) {
    cadd_tail_and_mixed(b, g, t, s, tl, l.c0, l.h, &[], dirty, &[]);
}

/// acc += sum_i ctl_i * floor(U 2^i / 2^LT), rows in increasing i (the running sum fits W - LT + i + 1 lanes).
fn product(b: &mut B, u: &[QubitId], acc: &[QubitId], ctl: &dyn Fn(&mut B, usize) -> Option<QubitId>,
           unctl: &dyn Fn(&mut B, usize), l: &QLanes, dirty: &[QubitId]) {
    for i in 0..WT {
        let (src, t0) = if i < LT { (&u[LT - i..], 0usize) } else { (&u[..], i - LT) };
        let len = src.len();
        if len == 0 { continue; }
        let t = &acc[t0..t0 + len];
        let tl: Vec<QubitId> = if t0 + len < RW { vec![acc[t0 + len]] } else { vec![] };
        if let Some(c) = ctl(b, i) {
            row_add(b, c, t, src, &tl, l, dirty);
        }
        unctl(b, i);
    }
}

/// Phase B: Nr = U T0 (rows masked while bl(t_{j+1}) < WT - i), Dr = NOT(U T1) (d-fixed), then the division.
pub(crate) fn phase_b(b: &mut B, ring: &[QubitId], q: &[QubitId], qw: usize, sx: &[QubitId], env: &QEnv, l: &QLanes,
           cache: &[QubitId], dirty: &[QubitId], upto: u8) -> (Vec<G>, Vec<G>) {
    let n = ring.len();
    let u: Vec<QubitId> = ring[n - W..].to_vec();
    let t1: Vec<QubitId> = q[qw - WT..qw].to_vec();
    let t0: Vec<QubitId> = (0..WT).map(|i| ring[31 + WT - i]).collect();
    // mask g_i = [sx >= WT - i]; g starts as [sx >= WT] and toggles on at i = WT - sx
    let masked = env.sx.0 < WT;
    let nprod = rec(b, |b| {
        if masked {
            let chain: Vec<QubitId> = l.dr[..sx.len()].to_vec(); // Dr is |0> during the N product
            super::mask::ge_const(b, sx, WT as isize, l.g, &chain);
        }
        let ctl = |b: &mut B, i: usize| -> Option<QubitId> {
            if !masked { return Some(t0[i]); }
            if i > 0 && WT - i >= env.sx.0 && WT - i <= env.sx.1 {
                let v = WT - i;
                let lits: Vec<(QubitId, bool)> = sx.iter().enumerate().map(|(k, &x)| (x, v >> k & 1 == 0)).collect();
                super::mask::mc_xor(b, &lits, l.g, &[], dirty);
            }
            b.and_c(t0[i], l.g, l.gt);
            Some(l.gt)
        };
        let unctl = |b: &mut B, i: usize| { if masked { b.and_u(t0[i], l.g, l.gt); } };
        product(b, &u, &l.nr, &ctl, &unctl, l, dirty);
        if masked { b.x(l.g); }
    });
    b.play(&nprod, false);
    if upto == 1 { return (vec![], nprod); }
    let dprod = rec(b, |b| {
        product(b, &u, &l.dr, &|_b, i| Some(t1[i]), &|_b, _i| {}, l, dirty);
        for &x in &l.dr { b.x(x); }
        b.cx(l.dl, l.dr[RW - 1]);
    });
    b.play(&dprod, false);
    if upto == 2 { return (dprod, nprod); }
    // division: for k = QC-1 .. 0: cache[k] = [Nr >> k >= Dr]; Nr[k..] -= Dr there. Zero extension = cache[..k].
    for k in (0..QC).rev() {
        let mut t: Vec<QubitId> = l.nr[k..].to_vec();
        t.extend_from_slice(&cache[..k]);
        cmp_csub(b, &t, &l.dr, l.h, l.c0, cache[k]);
    }
    (dprod, nprod)
}

/// The erase recipe of (Nr = remainder, Dr): Nr += q Dr, Nr -= U T0, Dr -= ... (exact inverse of the products).
fn erase_rec(b: &mut B, l: &QLanes, cache: &[QubitId], dprod: &[G], nprod: &[G], dirty: &[QubitId]) -> Vec<G> {
    rec(b, |b| {
        for k in 0..QC {
            cadd_tail_and_mixed(b, cache[k], &l.nr[k..], &l.dr[..RW - k], &[], l.c0, l.h, &[], dirty, &[]);
        }
        b.play(dprod, true); // Dr -> 0 first: the N product borrows Dr lanes as its ge chain
        b.play(nprod, true);
    })
}

/// The whole q-box (cache ^= q, cache |0> on entry). `sx` returns |0>. Outputs of the deferred erasure: Nr, Dr.
pub(crate) fn qbox(b: &mut B, ring: &[QubitId], q: &[QubitId], qw: usize, sy: &[QubitId], sx: &[QubitId],
                   env: &QEnv, l: &QLanes, cache: &[QubitId], probe_bank: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(cache.len(), QC);
    let a = rec(b, |b| phase_a(b, ring, q, qw, sy, sx, env, l, probe_bank, dirty));
    b.play(&a, false);
    b.pmark("qbox_b");
    let (dprod, nprod) = phase_b(b, ring, q, qw, sx, env, l, cache, dirty, 9);
    b.punmark("qbox_b");
    let e = erase_rec(b, l, cache, &dprod, &nprod, dirty);
    let mut outs = l.dr.clone();
    outs.extend_from_slice(&l.nr);
    if b.allow_booth { b.deferred_erasure(505, e, outs); } else { b.play(&e, false); }
    b.play(&a, true);
}

// ---------------------------------------------------------------------------------------------------------------
// Fused pair (j, j+1). Entry: column j start layout. Exit: column j+2 start layout (same sy/sx physical names).
// Layout: pool_v = pool (59) ++ Q[116..121) (every Q value of both columns < 2^116); cache = Q[121..138) ++
// pool_v[55..64); act = pool_v[54]; Q window q[..116].
// ---------------------------------------------------------------------------------------------------------------
use super::frogdrop_col::{ColPar, ColScr, Fd};

pub(crate) const QW: usize = 116;
pub(crate) const HDR: isize = 27; // bl(t_{j+2}) <= bl(t_{j+1}) + 26; gap above r_j >= 31

pub(crate) fn pair_ok(cp1: &ColPar, cp2: &ColPar) -> bool {
    let pure = |c: &ColPar| c.hr && !c.ht && !c.sw && !c.dn && !c.fin && !c.nomap;
    pure(cp1) && pure(cp2) && cp1.smax.1 + HDR as usize <= QW && cp2.smax.1 + 1 <= QW
        && 202usize.saturating_sub(cp1.smax.1) >= 2 * RW // q-box product registers (see carve)
        && 42 + (QW - cp1.smax.1) + 8 >= cp2.smax.1 // (d) box copy register
}

/// Swap inside the composite: exact cut n - sy (sy = bl(t_{j+2}) = the kernel cut; Z's region below is untouched).
fn swap_top_q_exact(b: &mut B, fd: &Fd, sy_env: (usize, usize), pool: &[QubitId], dirty: &[QubitId]) {
    let n = fd.ring.len();
    let cut = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    masked_swapf(b, &fd.ring, &fd.q[..QW], &cut, n - sy_env.1, n - sy_env.0, pool[0], &pool[1..9], pool[9], dirty);
}

/// Swap before the composite: cut n - 27 - sx (sx = bl(t_{j+1})), safe above r_j's >= 31-lane gap.
fn swap_top_q(b: &mut B, fd: &Fd, sx_env: (usize, usize), pool: &[QubitId], dirty: &[QubitId]) {
    let n = fd.ring.len();
    let cut = Cut { v: fd.sx.clone(), a: n as isize - HDR, neg: true };
    let (clo, chi) = (n - HDR as usize - sx_env.1, n - HDR as usize - sx_env.0);
    masked_swapf(b, &fd.ring, &fd.q[..QW], &cut, clo, chi, pool[0], &pool[1..9], pool[9], dirty);
}

/// ring top += sign * cache * Q (exact final value < 2^(span-1)); `sub` plays the subtraction (exact inverse).
fn digit(b: &mut B, fd: &Fd, cache: &[QubitId], span: usize, src_bound: usize, pool: &[QubitId], dirty: &[QubitId], sub: bool) {
    let r = rec(b, |b| qadd_signed_recode_extra(b, &fd.ring, &fd.q[..QW], cache, span, None, pool[0], pool[1],
                                                 src_bound, QW, pool[2], pool[3], dirty, &pool[4..54]));
    b.play(&r, sub);
}

fn kernel(b: &mut B, fd: &Fd, sck: &ColScr, held: &[QubitId], active: QubitId, cenv: (usize, usize), m: usize,
          tail: usize, inverse: bool) {
    let n = fd.ring.len();
    let q = &fd.q[..QW];
    let mut ms = sck.ms.clone();
    ms.andc.extend([sck.bq, sck.sw]);
    ms.anc.retain(|w| !held.contains(w) && *w != active);
    ms.andc.retain(|w| !held.contains(w) && *w != active);
    let mut bank = super::priority_probe::map_bank(&ms);
    bank.retain(|w| !ms.ez.contains(w));
    let cut = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let par = MapPar { clo: n - cenv.1, chi: n - cenv.0, m, tail, emax: 28 };
    super::priority_probe::trailing(b, q, 28, &ms.ez, &bank);
    rot_by_source_support(b, q, &ms.ez, m, true);
    fusion_kernel_invoice(b, &fd.ring, q, &cut, &par, &ms, inverse);
    rot_by_source_support(b, q, &ms.ez, m, false);
    super::priority_probe::trailing(b, q, 28, &ms.ez, &bank);
}

/// (d) erase box recipe: cache (= q = floor(t_{j+2}/t_{j+1})) -> 0 from the end state (ring top t_{j+2},
/// Q t_{j+1}, sy = bl(t_{j+2})). C = masked copy of the ring top; C -= q Q (= t_j); inverse restoring divmod
/// (C, q) -> (t_{j+2}, 0); uncopy C.
fn erase_q_rec(b: &mut B, fd: &Fd, cache: &[QubitId], m2: (usize, usize), m1: usize, cl: &[QubitId], work: &[QubitId],
               dirty: &[QubitId]) -> Vec<G> {
    let n = fd.ring.len();
    let span = m2.1;
    assert!(cl.len() >= span && work.len() >= 12);
    let c = &cl[..span];
    let (c0, h, f, tmp) = (work[0], work[1], work[2], work[3]);
    let pre = &work[4..12];
    let cut = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let copy = rec(b, |b| {
        for l in (n - m2.0)..n { b.cx(fd.ring[l], c[n - 1 - l]); }
        walk_cutf(b, &cut, n - m2.1, n - m2.0, f, pre, tmp, dirty, |b, l, f| {
            b.x(f); b.ccx(f, fd.ring[l], c[n - 1 - l]); b.x(f);
        });
    });
    let src = &fd.q[..m1];
    rec(b, |b| {
        b.play(&copy, false);
        // C -= q * Q : rows k (complement form of the add)
        let sub = rec(b, |b| {
            for k in 0..QC {
                if k >= span { break; }
                let len = (span - k).min(m1);
                let t = &c[k..k + len];
                let tl: Vec<QubitId> = c[k + len..span].to_vec();
                cadd_tail_and_mixed(b, cache[k], t, &src[..len], &tl, c0, h, &[], dirty, &[]);
            }
        });
        b.play(&sub, true);
        // D^-1: for k = 0..QC: C[k..] += cache[k] Q; cache[k] ^= [C >> k >= Q]
        for k in 0..QC {
            if k < span {
                let len = (span - k).min(m1);
                let tl: Vec<QubitId> = c[k + len..span].to_vec();
                cadd_tail_and_mixed(b, cache[k], &c[k..k + len], &src[..len], &tl, c0, h, &[], dirty, &[]);
            }
            cmp_ge_xor(b, &c[k.min(span)..], src, c0, tmp, cache[k], dirty);
        }
        b.play(&copy, true);
    })
}

/// out ^= [t >= s] (equal lengths), t and s restored.
fn cmp_only(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, out: QubitId) {
    let up = super::arith::up_m(b, t, s, c0, true);
    b.play(&up, false);
    let ct = s[t.len() - 1]; // [s > t]
    b.x(ct); b.cx(ct, out); b.x(ct);
    b.play(&up, true);
}

/// out ^= [t >= s] for unequal lengths: the longer operand's high lanes enter through a dirty-borrowed
/// zero test (no clean padding). `tmp` |0> in and out.
pub(crate) fn cmp_ge_xor(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, tmp: QubitId, out: QubitId, dirty: &[QubitId]) {
    use super::mask::mc_xor;
    let (lt, ls) = (t.len(), s.len());
    if lt == 0 { // t = 0 >= s  iff s == 0
        let lits: Vec<(QubitId, bool)> = s.iter().map(|&x| (x, true)).collect();
        mc_xor(b, &lits, out, &[], dirty);
        return;
    }
    if lt == ls { cmp_only(b, t, s, c0, out); return; }
    let l = lt.min(ls);
    let low = rec(b, |b| cmp_only(b, &t[..l], &s[..l], c0, tmp));
    b.play(&low, false); // tmp = [t_low >= s_low]
    if lt > ls {
        // t >= s  iff  t_high != 0 or tmp  =  NOT(t_high == 0 and !tmp)
        let mut lits: Vec<(QubitId, bool)> = t[l..].iter().map(|&x| (x, true)).collect();
        lits.push((tmp, true));
        b.x(out);
        mc_xor(b, &lits, out, &[], dirty);
    } else {
        // t >= s  iff  s_high == 0 and tmp
        let mut lits: Vec<(QubitId, bool)> = s[l..].iter().map(|&x| (x, true)).collect();
        lits.push((tmp, false));
        mc_xor(b, &lits, out, &[], dirty);
    }
    b.play(&low, true);
}

/// The fused pair, emitted (or recorded) in place of columns j and j+1.
pub(crate) fn pair(b: &mut B, fd: &mut Fd, cp1: &ColPar, cp2: &ColPar, pool_in: &[QubitId], dirty: &[QubitId]) {
    pair_upto(b, fd, cp1, cp2, pool_in, dirty, 99)
}
pub(crate) fn pair_upto(b: &mut B, fd: &mut Fd, cp1: &ColPar, cp2: &ColPar, pool_in: &[QubitId], dirty: &[QubitId], upto: u8) {
    assert!(pair_ok(cp1, cp2) && b.allow_booth && pool_in.len() == 59);
    let n = fd.ring.len();
    let mut pool_v = pool_in.to_vec();
    pool_v.extend_from_slice(&fd.q[QW..121]);
    let mut cache = fd.q[121..138].to_vec();
    cache.extend_from_slice(&pool_v[55..64]);
    let active = pool_v[54];
    let held = pool_v[55..64].to_vec();
    // 1. column j stages 1-8 (no map)
    let sc1 = ColScr::carve(pool_in, &fd.sx, dirty, super::pointadd_frogdrop::kp(), super::pointadd_frogdrop::QB,
                            super::pointadd_frogdrop::TAIL);
    b.pmark("hrf_col");
    super::frogdrop_col::column_upto(b, fd, cp1, &sc1, 7);
    b.punmark("hrf_col");
    // 2. q-box
    let env = QEnv { sz: cp1.sz, sy: cp1.sy, sx: cp1.smax };
    let mut base = pool_v[..54].to_vec();
    base.extend_from_slice(&fd.cnt);
    let mut late = ring_gap(&fd.ring);
    late.extend(q_free(&fd.q, QW, &env));
    let l = carve(&base, &late);
    let pb: Vec<QubitId> = base[14..].to_vec();
    b.pmark("hrf_qbox");
    qbox(b, &fd.ring, &fd.q, QW, &fd.sy, &fd.sx, &env, &l, &cache, &pb, dirty);
    b.punmark("hrf_qbox");
    b.pmark("hrf_glue");
    let probe_bank: Vec<QubitId> = pool_v[..54].to_vec();
    let (m1, m2) = (cp1.smax, cp2.smax); // bl(t_{j+1}), bl(t_{j+2}) envelopes
    if upto < 2 { return; }
    // 3. sx = bl(t_{j+1}); erase sy = bl(t_j) with t_j in Q
    super::priority_probe::emit(b, &fd.q[..QW], m1.0.saturating_sub(1), m1.1, &fd.sx, &probe_bank);
    swap_top_q(b, fd, m1, &pool_v, dirty);
    super::priority_probe::emit(b, &fd.q[..QW], cp1.sy.0.saturating_sub(1), cp1.sy.1, &fd.sy, &probe_bank);
    swap_top_q(b, fd, m1, &pool_v, dirty);
    if upto < 3 { return; }
    // 4. t-update: ring top t_j -> t_{j+2}
    b.punmark("hrf_glue");
    b.pmark("hrf_digit");
    digit(b, fd, &cache, m2.1 + 1, m1.1, &pool_v, dirty, false);
    b.punmark("hrf_digit");
    b.pmark("hrf_glue");
    if upto < 4 { return; }
    // 5. Q = t_{j+2}, ring top = t_{j+1}; sy = bl(t_{j+2})
    swap_top_q(b, fd, m1, &pool_v, dirty);
    super::priority_probe::emit(b, &fd.q[..QW], m2.0.saturating_sub(1), m2.1, &fd.sy, &probe_bank);
    b.punmark("hrf_glue");
    if upto < 5 { return; }
    // 6. composite: Z *= t_{j+2}; Z -= q p; echo; Z /= t_j; echo back
    b.x(active);
    let sck = ColScr::carve(&pool_v, &fd.sy, dirty, 30, 24, 40);
    b.pmark("hrf_kmul");
    kernel(b, fd, &sck, &held, active, m2, m2.1, cp2.tail, false);
    b.punmark("hrf_kmul");
    if upto < 6 { return; }
    b.pmark("hrf_qp");
    let corr = rec(b, |b| super::qp_naf_cut::correction(b, &fd.ring, &cache, &fd.sy, m2.1, active, &pool_v[..18]));
    b.play(&corr, true);
    b.punmark("hrf_qp");
    b.pmark("hrf_echo");
    swap_top_q_exact(b, fd, m2, &pool_v, dirty);
    digit(b, fd, &cache, m2.1 + 1, m1.1, &pool_v, dirty, true);
    swap_top_q_exact(b, fd, m2, &pool_v, dirty);
    b.punmark("hrf_echo");
    if upto < 7 { return; }
    b.pmark("hrf_kdiv");
    kernel(b, fd, &sck, &held, active, m2, cp1.sy.1, cp1.tail, true);
    b.punmark("hrf_kdiv");
    b.pmark("hrf_echo");
    swap_top_q_exact(b, fd, m2, &pool_v, dirty);
    digit(b, fd, &cache, m2.1 + 1, m1.1, &pool_v, dirty, false);
    b.punmark("hrf_echo");
    b.x(active);
    if upto < 8 { return; }
    // 7. erase the cache (deferred), then sx
    let mut cl: Vec<QubitId> = pool_v[12..54].to_vec();
    cl.extend_from_slice(&fd.q[m1.1..QW]);
    cl.extend_from_slice(&fd.cnt);
    cl.push(fd.ph); // pure HR: ph = 0 on every shot
    let e = erase_q_rec(b, fd, &cache, m2, m1.1, &cl, &pool_v[..12], dirty);
    if b.allow_booth { b.deferred_erasure(506, e, cache.clone()); } else { b.play(&e, false); }
    super::priority_probe::emit(b, &fd.q[..QW], m1.0.saturating_sub(1), m1.1, &fd.sx, &probe_bank);
    let _ = n;
}
