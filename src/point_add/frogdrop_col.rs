//! frogdrop lockstep columns (one Euclid step per column).
//!
//! Column-start layout: Q = X (CO/DV target), ring = [Z (LSB lane 0) | Y (LSB lane n-1, down)], sy = bl(Y).
//! Phase 1 (HR): Z = r_j, X = t_{j-1}, Y = t_j.  Column end: Z = r_{j+1}, Q = t_j, ring top = t_{j+1}.

use super::builder::{B, G};
use super::frogdrop::*;
use crate::circuit::QubitId;

/// Classical per-column parameters (envelopes over the shots of the column).
#[derive(Clone, Debug)]
pub struct ColPar {
    pub n: usize,
    pub nq: usize,
    /// ring headroom n - 257 (gap above Z, >= K + 1)
    pub h: usize,
    pub k: usize,
    pub kp: usize,
    pub qb: usize,
    pub tot: usize,
    /// bl(Z) range, bl(Y) range, max(bl X_new, bl Y) range
    pub sz: (usize, usize),
    pub sy: (usize, usize),
    pub smax: (usize, usize),
    /// pair-value envelope bits (Q lanes read by the map)
    pub m: usize,
    pub tail: usize,
    pub emax: usize,
    /// some shot steps in HR / steps in HT / may switch this column
    pub hr: bool,
    pub ht: bool,
    pub sw: bool,
    /// switch at the first HR state with bl(Z) <= l0
    pub l0: usize,
    /// lanes exchanged bottom <-> Q before / after the switching map
    pub swl: (usize, usize),
    /// some shot is done at column start / reaches r = 1 at column end
    pub dn: bool,
    pub fin: bool,
    /// final column: no map (the last HT middle with Y = 1 clears R)
    pub nomap: bool,
    /// T may equal t (column 1 = j 2 with q_1 = 1 on unreflected inputs): the HR sign read uses T - 1 - bq t
    pub tt: bool,
}

/// Persistent traversal registers.
pub struct Fd {
    pub ring: Vec<QubitId>,
    pub q: Vec<QubitId>,
    pub sy: Vec<QubitId>,
    /// spare size register (|0> between columns), swapped with sy each column
    pub sx: Vec<QubitId>,
    /// phase: 0 = HR (Z = r_j), 1 = HT (Z = t_j)
    pub ph: QubitId,
    /// 0 while stepping; 1 + idle columns once finished (Euclid reached r = 1); "done" = cnt != 0. Done shots
    /// alternate A0 = (t_{N-1}, R, 1) and B0 = (t_{N-2}, 1, R) by q = 0 maps.
    pub cnt: Vec<QubitId>,
}

/// Column scratch (all |0> between columns except `one` = |1>).
#[derive(Clone)]
pub struct ColScr {
    pub sz: Vec<QubitId>,
    pub cmpc: QubitId,
    pub bq: QubitId,
    /// switch flag (this column) and the gated-control temp
    pub sw: QubitId,
    pub g: QubitId,
    /// stepping flag !sw & !done (gates the q0 adds)
    pub act: QubitId,
    pub c0: QubitId,
    pub tmp: QubitId,
    pub tmp2: QubitId,
    pub f: QubitId,
    pub one: QubitId,
    pub pre: Vec<QubitId>,
    pub opre: Vec<QubitId>,
    pub anc: Vec<QubitId>,
    pub zeros: Vec<QubitId>,
    pub ps: PScr,
    pub ms: MapScr,
    pub dirty: Vec<QubitId>,
}

/// Size of the shared column scratch pool (plus the spare size register sx, which joins rho during P).
/// Column pool size for size registers of `sw` bits (the spare one is the first `sw` lanes of rho/q0).
pub fn pool_size(kp: usize, qb: usize, sw: usize) -> usize {
    18 + (kp + 1 + qb - sw)
}

impl ColScr {
    /// Carve the column scratch out of `pool` (all |0>) and the current spare size register `sx` (|0> outside the
    /// map stage). Roles overlap only where their live stages are disjoint:
    /// pool[0..9] sz, 9 sw, 10 bq (also the end's play_ctrl temp), 11 cmpc (also the P compares' zero lane, which
    /// is only needed while cmpc is idle), 12..16 PScr f g c0 one, 16..18 PScr spre, 18.. rho/q0 (with sx).
    /// PScr.tmp aliases cmpc/PScr.zero: decoder toggles complete before any compare starts.
    /// ColScr.tmp borrows rho only outside P lifetime; middle bcmp uses clean PScr.f.
    /// The six-prefix middle swap uses exact dirty three-control toggles and no clean temporary.
    /// Walk/probe transients reuse PScr misc (middle-safe) or the rho region (stages 1, 8, 9); MapScr reuses
    /// everything except sw, bq, cmpc and sx.
    pub fn carve(pool: &[QubitId], sx: &[QubitId], dirty: &[QubitId], kp: usize, qb: usize, tail: usize) -> ColScr {
        assert_eq!(pool.len(), pool_size(kp, qb, sx.len()));
        let p = |i: usize| pool[i];
        let mut rq: Vec<QubitId> = sx.to_vec();
        rq.extend(&pool[18..]);
        let rho = rq[..kp + 1].to_vec();
        let q0 = rq[kp + 1..kp + 1 + qb].to_vec();
        let spre = pool[16..18].to_vec();
        let ps = PScr { r: vec![], rho, q0, f: p(12), g: p(13), c0: p(14), zero: p(11), one: p(15), spre: spre.clone(),
                        tmp: p(11), dirty: dirty.to_vec() };
        let mut pre = spre.clone();
        pre.extend([p(13), p(14), p(15)]);
        // MapScr: pool[0..9] + pool[12..] (not sw/bq/cmpc, not sx)
        let mut mp: Vec<QubitId> = pool[0..9].to_vec();
        mp.extend(&pool[12..]);
        // Every column map uses the sx size register as its affine cut. Dec
        // holds at most sx.len()-1 prefixes and ge_const uses at most that many
        // carries. The formerly reserved eighth prefix was never accessed.
        let pre_end = 7 + sx.len().saturating_sub(1);
        let ez_end = pre_end + 5;
        let fixed = ez_end + 4;
        assert!(mp.len() >= fixed);
        // Exact dirty tail fallback supports every tail with fewer clean prefixes.
        let clean_tail = (tail - 1).min(mp.len() - fixed);
        let need = fixed + clean_tail;
        let ms = MapScr { c0: mp[0], h: mp[1], e: mp[2], g: mp[3], f: mp[4], tmp: mp[5], one: mp[6],
                          pre: mp[7..pre_end].to_vec(), ez: mp[pre_end..ez_end].to_vec(), epre: mp[ez_end..fixed].to_vec(),
                          anc: mp[fixed..fixed + clean_tail].to_vec(), dirty: dirty.to_vec(),
                          // Beyond the complete map layout: unused and clean for the map.
                          andc: mp[need..].to_vec() };
        ColScr { sz: pool[0..9].to_vec(), sw: p(9), bq: p(10), cmpc: p(11), act: p(12), g: p(13), c0: p(14),
                 tmp: p(20), tmp2: p(23), f: p(12), one: p(15), pre, opre: pool[24..32].to_vec(),
                 anc: pool[32..39].to_vec(), zeros: vec![p(15)], ps, ms, dirty: dirty.to_vec() }
    }
}

fn rec<F: FnOnce(&mut B)>(b: &mut B, f: F) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}

impl ColScr {
    /// a clean helper qubit for the constant adders (tmp2 is free whenever these run)
    fn one_tmp(&self) -> QubitId {
        self.tmp2
    }
}

/// Exact threshold using disjoint lexicographic terms. The terms of v < k have
/// highest differing bit i with k_i=1 and v_i=0. XOR of those disjoint terms,
/// complemented once, is [v >= k]. At most n-2 clean temporary qubits suffice.
fn ge_const_compact(b: &mut B, v: &[QubitId], k: isize, target: QubitId,
                    temp: &[QubitId], dirty: &[QubitId]) {
    use super::mask::mc_xor;
    if k <= 0 { b.x(target); return; }
    if k >= (1isize << v.len()) { return; }
    let kk = k as usize;
    b.x(target);
    for i in (0..v.len()).rev() {
        if (kk >> i) & 1 == 0 { continue; }
        let mut lits: Vec<_> = ((i+1)..v.len()).rev()
            .map(|j| (v[j], (kk >> j) & 1 == 0)).collect();
        lits.push((v[i], true));
        mc_xor(b, &lits, target, temp, dirty);
    }
}

/// The column cut is sz+h. Six clean prefixes for sz's nine bits suffice for
/// every equality toggle; the initial threshold is computed by the exact compact
/// comparator plus an exact dirty toggle. No rho/q0 lane is borrowed during these replays.
fn masked_swap_middle_compact(b: &mut B, ring: &[QubitId], q: &[QubitId], sz: &[QubitId], h: usize,
                              clo: usize, chi: usize, f: QubitId, pre: &[QubitId], dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    let n = ring.len();
    let qlo = n.saturating_sub(q.len());
    for l in chi.max(qlo)..n { b.swap(ring[l], q[n-1-l]); }
    let lo = clo.max(qlo);
    if lo >= chi { return; }
    ge_const_compact(b, sz, lo as isize + 1 - h as isize, f, pre, dirty);
    let mut dec = Dec::new(sz, pre);
    let at = |l: usize| l.checked_sub(h).filter(|&v| v < (1usize << sz.len()));
    for l in lo..chi {
        if l > lo {
            if let Some(v) = at(l) {
                let controls = dec.ctrls(b, v);
                assert!(controls.len() <= 3);
                mc_xor(b, &controls, f, &[], dirty);
            }
        }
        b.x(f); b.cswap(f, ring[l], q[n-1-l]); b.x(f);
    }
    if let Some(v) = at(chi) {
        let controls = dec.ctrls(b, v);
        assert!(controls.len() <= 3);
        mc_xor(b, &controls, f, &[], dirty);
    }
    dec.clear(b);
}

/// Unified column: every shot steps in its own phase (fd.ph = 0 HR, 1 HT) or, at its first HR state with
/// bl(Z) <= l0, switches HR -> HT without stepping (cp.sw columns): Q: t_{j-1} -> r_{j-1} by the column's own map
/// (bottom <-> Q exchanged around it), ring reversed (bottom t_j, top r_j).
/// Middle (X in the ring top, Y in Q): HR: bq = [rho < Xh]; T -= bq t; bq ^= sign (T < t); T += q0 t.
/// HT: R -= q0 r (complement trick: ~(~R + q0 r)); bq = sign; R += bq r; bq ^= [rho < Xh(R')].
pub fn column(b: &mut B, fd: &mut Fd, cp: &ColPar, sc: &ColScr) {
    column_upto(b, fd, cp, sc, 99)
}

pub fn column_upto(b: &mut B, fd: &mut Fd, cp: &ColPar, sc: &ColScr, upto: usize) {
    use super::mask::{mc_xor, Dec};
    let prof = std::env::var("FROGDROP_PROF").is_ok();
    let mut stn = 0usize;
    let mut last = b.tof;
    let mut prof_v: Vec<(usize, u64)> = vec![];
    macro_rules! stage { () => {
        stn += 1;
        if prof { prof_v.push((stn, b.tof - last)); last = b.tof; }
        if stn > upto { return; }
    } }
    let n = cp.n;
    let h = cp.h as isize;
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    let ph = fd.ph;
    let (k, kp, qb, tot) = (cp.k, cp.kp, cp.qb, cp.tot);
    let dirty = sc.dirty.clone();
    let cut_y = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let (pclo, pchi) = (cp.sz.0 + cp.h, cp.sz.1 + cp.h);
    // 1. sz = bl(Z) (probe below Y's MSB lane per shot)
    let mut probe_pre = sc.pre.clone();
    probe_pre.push(sc.bq); // bq is clean before P and after un-P
    probe_pre.push(sc.ps.q0[0]); // quotient is zero outside P lifetime, disjoint from probe temps
    let probe_z = rec(b, |b| {
        msb_probe_cut(b, &ring, &cut_y, n - cp.sy.1, n - cp.sy.0, &sc.sz, sc.f, &probe_pre, &sc.opre, sc.tmp, sc.tmp2,
                      &dirty)
    });
    b.play(&probe_z, false);
    // 1b. sw = HR & bl(Z) <= l0
    if cp.sw {
        let mut ch1 = sc.pre.clone();
        ch1.extend([sc.bq, sc.tmp, sc.tmp2]); // bq and rho are still zero before P
        let gsw = rec(b, |b| super::mask::ge_const(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch1));
        b.play(&gsw, false);
        mc_xor(b, &[(sc.cmpc, true), (ph, true)], sc.sw, &[], &dirty);
        b.play(&gsw, true);
    }
    stage!(); // 1
    // 2. Y into Q
    // Six prefixes leave three controls for the nine-bit cut. Exact dirty
    // multi-controlled toggles restore passenger wires and use no extra helper.
    let mut pre_sw = sc.pre.clone();
    pre_sw.push(sc.cmpc);
    let swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                   sc.f, &pre_sw, &dirty));
    assert_eq!(pre_sw.len(), sc.sz.len() - 3); // dirty three-control decoder: no temporary access
    b.play(&swap, false);
    stage!(); // 2
    // 3-4. window: Q down by sy puts Y's top kp bits (Yh = Y >> (sy - kp), or Y << (kp - sy) with zeros wrapped in
    // from Q's empty top) at Q's top kp lanes; ring down by sz puts Z's top k bits at the ring top; sz += sy gives
    // the pipeline start tot - e = sz + sy + (tot - 256 - k - kp)
    let soff = tot as i64 - 256 - k as i64 - kp as i64;
    let nq = q.len();
    let p_rec = rec(b, |b| {
        rot_by(b, &ring, &sc.sz, true);
        rot_by(b, &q, &fd.sy, true);
        reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0);
        let mut ps = PScr { r: ring[0..k + 1].to_vec(), ..sc.ps.clone() };
        ps.dirty = dirty.clone();
        b.x(ps.one);
        pipeline_off(b, &ring[n - k..n], &q[nq - kp..nq], &sc.sz, soff, tot, qb, &ps);
        b.x(ps.one);
        let rr = rec(b, |b| reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0));
        b.play(&rr, true);
        rot_by(b, &q, &fd.sy, false);
        rot_by(b, &ring, &sc.sz, false);
    });
    b.play(&p_rec, false);
    stage!(); // 3
    let rho = rotated(&sc.ps.rho, tot);
    // bq ^= AND(lits) & [rho < Xh], Xh = X >> syp (X in Q)
    let bcmp = |b: &mut B, lits: &[(QubitId, bool)]| {
        use super::arith::{down_m, up_m, Dm};
        rot_by(b, &q, &fd.sy, true);
        let mut s: Vec<QubitId> = q[nq - kp..nq].to_vec();
        s.push(sc.ps.zero);
        let up = up_m(b, &rho, &s, sc.c0, true);
        let dn = down_m(b, &rho, &s, sc.c0, Dm::Restore, true);
        b.play(&up, false);
        let mut c = vec![(s[kp], false)]; // carry of ~rho + Xh: [Xh > rho]
        c.extend_from_slice(lits);
        mc_xor(b, &c, sc.bq, &[sc.ps.f], &dirty);
        b.play(&dn, false);
        rot_by(b, &q, &fd.sy, false);
    };
    // ladder over the ring-top value's bits [0, mt): every pair value fits Q (< 2^nq), so bit nq is a sign bit
    let mt = (n - pclo + 1).min(nq + 1);
    let qbe = qb.min(mt); // q0 bits beyond the ladder are 0
    // bq ^= sign of the ring-top value: at the buffer lane cut - 1 = sz + h - 1, or at the ladder top n - mt for shots
    // whose region is wider than the ladder (sz + h - 1 < n - mt)
    let sign_into = |b: &mut B| {
        let lo = (pclo - 1).max(n - mt);
        if pclo - 1 < n - mt {
            let kk = (n - mt + 1) as isize - cp.h as isize; // sz >= kk: sign lane inside the ladder
            let mut chain = sc.ps.spre.clone();
            chain.extend([sc.ps.f, sc.ps.g, sc.ps.c0, sc.ps.one]);
            let gc = rec(b, |b| ge_const_compact(b, &sc.sz, kk, sc.cmpc, &chain, &dirty));
            b.play(&gc, false);
            mc_xor(b, &[(sc.cmpc, true), (ring[n - mt], false)], sc.bq, &[], &dirty);
            b.play(&gc, true);
        }
        let mut dec = Dec::new(&sc.sz, &sc.ps.spre);
        for l in lo..pchi {
            let v = l + 1 - cp.h;
            let mut c = dec.ctrls(b, v);
            c.push((ring[l], false));
            mc_xor(b, &c, sc.bq, &[sc.ps.tmp], &dirty);
        }
        dec.clear(b);
    };
    // 5. HR correction first: T -= bq t is negative iff bq (T < t), which erases bq
    if cp.hr {
        let mut lits = vec![(ph, true)];
        if cp.sw { lits.push((sc.sw, true)); }
        b.play(&swap, false);
        bcmp(b, &lits);
        b.play(&swap, false);
        ring_cadd(b, &ring, &q, 0, mt, sc.bq, true, &sc.zeros, sc.c0);
        if cp.tt {
            // T may equal t here (T >= 1): the sign of T - 1 - bq t is exactly bq
            let xl: Vec<QubitId> = (0..mt).map(|m| ring[n - 1 - m]).collect();
            let inc1 = rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, sc.ps.c0));
            b.play(&inc1, true);
            sign_into(b);
            b.play(&inc1, false);
        } else {
            sign_into(b);
        }
    }
    stage!(); // 4
    // 6. X +-= q0 Y (HT shots complemented around the adds), skipped for switching shots
    if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
    let mut actl = vec![];
    if cp.sw { actl.push((sc.sw, true)); }
    if cp.dn { actl.extend(fd.cnt.iter().map(|&x| (x, true))); } // not done: cnt == 0
    if !actl.is_empty() { mc_xor(b, &actl, sc.act, &[], &dirty); }
    for kk in 0..qbe {
        if !actl.is_empty() {
            b.and_c(sc.ps.q0[kk], sc.act, sc.g);
            ring_cadd(b, &ring, &q, kk, mt - kk, sc.g, false, &sc.zeros, sc.c0);
            b.and_u(sc.ps.q0[kk], sc.act, sc.g);
        } else {
            ring_cadd(b, &ring, &q, kk, mt - kk, sc.ps.q0[kk], false, &sc.zeros, sc.c0);
        }
    }
    if !actl.is_empty() { mc_xor(b, &actl, sc.act, &[], &dirty); }
    if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
    stage!(); // 5
    // 7. HT correction: bq = [R - q0 r < 0]; R += bq r; erase bq by [rho < Xh(R')]
    if cp.ht {
        sign_into(b);
        ring_cadd(b, &ring, &q, 0, mt, sc.bq, false, &sc.zeros, sc.c0);
        b.play(&swap, false);
        let mut l = vec![(ph, false)];
        if cp.dn { l.extend(fd.cnt.iter().map(|&x| (x, true))); }
        bcmp(b, &l);
        b.play(&swap, false);
    }
    stage!(); // 6
    // 8. un-P (Y in Q)
    b.play(&p_rec, true);
    stage!(); // 7
    // 9. X_new into Q (map layout); erase sz
    b.play(&swap, false);
    b.play(&probe_z, true);
    stage!(); // 8
    // 10. switching shots: bottom <-> Q (map target t_{j-1}, multiplier r_j)
    if cp.sw {
        for l in 0..cp.swl.0 { b.cswap(sc.sw, ring[l], q[l]); }
    }
    // 11-13. map stage
    if cp.nomap {
        stage!();
        return;
    }
    let ms_rec = map_stage(b, fd, cp, sc);
    b.play(&ms_rec, false);
    std::mem::swap(&mut fd.sy, &mut fd.sx);
    stage!(); // 9
    // 14. switching shots: bottom <-> Q (bottom t_j, Q r_{j-1}), ph = 1; erase sw = ph & bl(Q) > l0
    if cp.sw {
        for l in 0..cp.swl.1 { b.cswap(sc.sw, ring[l], q[l]); }
        b.cx(sc.sw, ph);
        b.cx(ph, sc.sw);
        let mut lits = vec![(ph, false)];
        lits.extend((cp.l0..cp.nq).map(|l| (q[l], true)));
        mc_xor(b, &lits, sc.sw, &[sc.tmp], &dirty);
    }
    // 15. idle counter: cnt += [cnt != 0]; then cnt = 1 for shots that just reached r = 1 (top = 1, ph = 1,
    // cnt == 0), erased via cnt == 1 (idle shots are >= 2 after their increment)
    let zl: Vec<(QubitId, bool)> = fd.cnt.iter().map(|&x| (x, true)).collect();
    if cp.dn {
        let anc: Vec<QubitId> = sc.anc[..fd.cnt.len() - 1].to_vec();
        mc_xor(b, &zl, sc.g, &[sc.tmp], &dirty);
        b.x(sc.g);
        super::arith::inc(b, sc.g, &fd.cnt, &anc);
        b.x(sc.g);
        mc_xor(b, &zl, sc.g, &[sc.tmp], &dirty);
    }
    if cp.fin {
        let mut sy1: Vec<(QubitId, bool)> = vec![(fd.sy[0], false)];
        sy1.extend(fd.sy[1..].iter().map(|&x| (x, true)));
        let mut l1 = vec![(ph, false)];
        l1.extend(sy1.iter().cloned());
        l1.extend(zl.iter().cloned());
        mc_xor(b, &l1, sc.g, &[sc.tmp], &dirty);
        b.cx(sc.g, fd.cnt[0]);
        let mut l2 = vec![(ph, false)];
        l2.extend(sy1.iter().cloned());
        l2.push((fd.cnt[0], false));
        l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
        mc_xor(b, &l2, sc.g, &[sc.tmp], &dirty);
    }
    stage!(); // 11
    if prof {
        let names = ["probe+sw", "swap", "P", "HR corr", "q0 adds", "HT corr", "un-P", "swap+unprobe", "map stage",
                     "sw+done"];
        let s: Vec<String> = prof_v.iter().map(|(i, t)| format!("{}={}", names[i - 1], t)).collect();
        eprintln!("  prof: {}", s.join(" "));
    }
}

/// Map stage (recorded): sx = bl(X); order; map with cut = n - max; unorder; erase sy by probing Q (= Y).
/// The caller relabels sy <-> sx afterwards (ring top then holds X, size sx).
fn map_stage(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr) -> Vec<G> {
    let ring = &fd.ring;
    let q = &fd.q;
    let n = cp.n;
    let dirty = sc.dirty.clone();
    rec(b, |b| {
        msb_probe(b, q, cp.nq, &fd.sx, &sc.opre, sc.tmp, &dirty);
        let order = rec(b, |b| {
            use super::arith::{down_m, up_m, Dm};
            let up = up_m(b, &fd.sx, &fd.sy, sc.c0, true);
            let dn = down_m(b, &fd.sx, &fd.sy, sc.c0, Dm::Restore, true);
            b.play(&up, false);
            b.cx(fd.sy[fd.sy.len() - 1], sc.cmpc); // carry of ~sx + sy (values < 2^width): [sy > sx]
            b.play(&dn, false);
            for i in 0..fd.sx.len() {
                b.cswap(sc.cmpc, fd.sx[i], fd.sy[i]);
            }
        });
        b.play(&order, false);
        let mcut = Cut { v: fd.sx.clone(), a: n as isize, neg: true };
        let mpar = MapPar { clo: n - cp.smax.1, chi: n - cp.smax.0, m: cp.m, tail: cp.tail, emax: cp.emax };
        let mut ms = sc.ms.clone();
        ms.dirty = dirty.clone();
        // Ordinary maps need at most 257 + emax <= n lanes by the product
        // invariant. Switch endpoints and pair values each fit nq lanes, so
        // 2*nq + emax - n extra lanes cover the complete retained v2 envelope.
        // Fund these transient lanes from tail prefixes. Dirty exact increments
        // replace only tails whose clean prefix no longer fits; loans remain
        // excluded from every map scratch and carry vector until returned.
        let extra = if cp.sw { (2 * cp.nq + cp.emax).saturating_sub(n) } else { 0 };
        assert!(ms.anc.len() >= extra);
        let extension = ms.anc.split_off(ms.anc.len() - extra);
        let mut extended = ring.to_vec();
        extended.extend_from_slice(&extension);
        let embed = rec(b, |b| {
            if extra == 0 { return; }
            for l in (mpar.chi..n).rev() { b.swap(extended[l], extended[l + extra]); }
            walk_cutf_desc(b, &mcut, mpar.clo, mpar.chi, ms.f, &ms.pre, ms.tmp, &dirty, |b, l, f| {
                b.x(f); b.cswap(f, extended[l], extended[l + extra]); b.x(f);
            });
        });
        b.play(&embed, false);
        let extcut = Cut { v: mcut.v.clone(), a: mcut.a + extra as isize, neg: mcut.neg };
        let extpar = MapPar { clo: mpar.clo + extra, chi: mpar.chi + extra,
                            m: mpar.m, tail: mpar.tail, emax: mpar.emax };
        mapf(b, &extended, q, &extcut, &extpar, &ms);
        b.play(&embed, true);
        b.play(&order, true);
        let probe_y = rec(b, |b| msb_probe(b, q, cp.nq, &fd.sy, &sc.opre, sc.tmp, &dirty));
        b.play(&probe_y, true);
    })
}

/// End of the traversal (every shot done): B0 shots (odd idle count, cnt[0] = 0) take one more q = 0 map ->
/// A0 = (t_{N-1}, R, 1) for all; then the last HT middle (Y = 1, q = R) clears R (Q = 0). `cp` = envelope of the
/// B0 shots for the map, `cpl` = the last-middle column (all shots A0, nomap).
pub fn traversal_end(b: &mut B, fd: &mut Fd, cp: Option<&ColPar>, cpl: &ColPar,
                     carve: &dyn Fn(&[QubitId]) -> ColScr) {
    if let Some(cp) = cp {
        // B0 <=> odd idle count <=> cnt (= 1 + idle) even
        let sc = carve(&fd.sx);
        let ms_rec = map_stage(b, fd, cp, &sc);
        b.x(fd.cnt[0]);
        b.play_ctrl(&ms_rec, fd.cnt[0], sc.bq);
        std::mem::swap(&mut fd.sy, &mut fd.sx);
        // shots that skipped the map keep their size in the (renamed) sx register: swap back
        b.x(fd.cnt[0]);
        for i in 0..fd.sy.len() {
            b.cswap(fd.cnt[0], fd.sy[i], fd.sx[i]);
        }
    }
    // carve after the rename: the spare register (part of the P scratch) changed
    let sc = carve(&fd.sx);
    column(b, fd, cpl, &sc);
}

/// the lane order a register has after `steps` doubling relabels (pop top, insert at 0)
fn rotated(v: &[QubitId], steps: usize) -> Vec<QubitId> {
    let mut r = v.to_vec();
    for _ in 0..steps {
        let top = r.pop().unwrap();
        r.insert(0, top);
    }
    r
}

#[cfg(test)]
mod pool65_tests {
    use super::*;
    use crate::circuit::{Op, OperationType as K, NO_BIT};
    fn symbolic(ops: &[Op], mut q: Vec<u64>) -> Vec<u64> {
        let mut measured = std::collections::BTreeMap::new();
        let mut phase = Vec::<u64>::new();
        let mut constant_phase = 0u64;
        for op in ops {
            let t = op.q_target.0 as usize;
            let a = op.q_control1.0 as usize;
            let c = op.q_control2.0 as usize;
            match op.kind {
                K::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
                K::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
                K::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
                K::Swap => q.swap(a, t),
                K::Hmr => {
                    measured.insert(op.c_target, phase.len());
                    phase.push(q[t]);
                    q[t] = 0;
                }
                K::CZ => {
                    if op.c_condition == NO_BIT { constant_phase ^= q[a] & q[t]; }
                    else { phase[measured[&op.c_condition]] ^= q[a] & q[t]; }
                }
                other => panic!("unexpected local operation {other:?}"),
            }
        }
        assert_eq!(constant_phase, 0);
        assert!(phase.iter().all(|&coefficient| coefficient == 0), "nonzero symbolic measurement phase");
        q
    }


    #[test]
    fn pool65_compact_threshold_all_values_and_phases() {
        let mut checks=0usize;
        for width in 1..=9 {
            let limit=1usize << width;
            for k in -1..=limit as isize + 1 {
                let mut b=B::new();
                let v=b.alloc_n(width);
                let t=b.alloc();
                let temp=b.alloc_n(width.saturating_sub(3));
                let dirty=b.alloc_n(8);
                b.begin();
                ge_const_compact(&mut b,&v,k,t,&temp,&dirty);
                let recipe=b.end();
                b.play(&recipe,false);
                let forward=std::mem::take(&mut b.ops);
                b.play(&recipe,true);
                let inverse=std::mem::take(&mut b.ops);
                for first in (0..limit).step_by(64) {
                    let mut initial=vec![0u64;b.width() as usize];
                    initial[t.0 as usize]=0xaaaaaaaaaaaaaaaa;
                    for (i,q) in dirty.iter().enumerate() {initial[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(i as u32);}
                    let mut mask=0u64;
                    for lane in 0..64 {
                        let value=(first+lane)%limit;
                        for (i,q) in v.iter().enumerate() {
                            if (value>>i)&1==1 {initial[q.0 as usize] |= 1u64<<lane;}
                        }
                        if value as isize>=k {mask |= 1u64<<lane;}
                    }
                    let mut expected=initial.clone();expected[t.0 as usize]^=mask;
                    let end=symbolic(&forward,initial.clone());
                    assert_eq!(end,expected,"width={width} threshold={k}");
                    assert_eq!(symbolic(&inverse,end),initial);
                    checks+=limit.min(64);
                }
            }
        }
        eprintln!("POOL65_COMPACT_THRESHOLD_ALL_PHASE_PASS checks={checks} widths=1..9 every_value_threshold=true inverse=true");
    }
}
