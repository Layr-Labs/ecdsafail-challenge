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

/// Column scratch (all |0> between columns); pool15/16 hold two quotient overflow bits during P.
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
    17 + (kp + 1 + qb - sw)
}

impl ColScr {
    /// Carve the column scratch out of `pool` (all |0>) and the current spare size register `sx` (|0> outside the
    /// map stage). Roles overlap only where their live stages are disjoint:
    /// pool[0..9] sz, 9 sw, 10 bq, 11 cmpc/P zero, 12..15 P f/g/c0,
    /// 15..17 two persistent quotient overflow bits, 17.. base rho/q0 (with sx).
    /// Virtual odd subtraction removes physical one; P holds no decoder prefix.
    /// PScr.tmp aliases cmpc/PScr.zero: decoder toggles complete before any compare starts.
    /// ColScr.tmp borrows rho only outside P lifetime; middle bcmp uses clean PScr.f.
    /// The four-prefix middle swap includes the exact zero top rho bit and uses dirty five-control toggles.
    /// Walk/probe transients reuse PScr misc (middle-safe) or the rho region (stages 1, 8, 9); MapScr reuses
    /// everything except sw, bq, cmpc and sx.
    pub fn carve(pool: &[QubitId], sx: &[QubitId], dirty: &[QubitId], kp: usize, qb: usize, tail: usize) -> ColScr {
        assert_eq!(pool.len(), pool_size(kp, qb, sx.len()));
        let p = |i: usize| pool[i];
        let mut rq: Vec<QubitId> = sx.to_vec();
        rq.extend(&pool[17..]);
        let rho = rq[..kp + 1].to_vec();
        let mut q0 = rq[kp + 1..kp + 1 + qb].to_vec();
        q0.extend([p(15),p(16)]); // two paid overflow lanes; base QB remains unchanged
        let spre = Vec::new();
        let ps = PScr { r: vec![], rho, q0, f: p(12), g: p(13), c0: p(14), zero: p(11), one: p(15), spre: spre.clone(),
                        tmp: p(11), dirty: dirty.to_vec() };
        let mut pre = vec![p(16)];
        pre.extend([p(13), p(14), p(15)]);
        // MapScr: pool[0..9] + pool[12..] (not sw/bq/cmpc, not sx)
        let mut mp: Vec<QubitId> = pool[0..9].to_vec();
        mp.extend(&pool[12..]);
        // Every column map uses the sx size register as its affine cut. Dec
        // holds at most sx.len()-1 prefixes and ge_const uses at most that many
        // carries. The formerly reserved eighth prefix was never accessed.
        let pre_end = 7 + sx.len().saturating_sub(1);
        let ez_end = pre_end + 5;
        // The tz-probe decoder and cut decoder have disjoint lifetimes. Share
        // one prefix; frame_carries explicitly excludes every cut-prefix alias.
        assert!(pre_end > 7);
        let fixed = ez_end + 3;
        let mut epre = vec![mp[pre_end - 1]];
        epre.extend_from_slice(&mp[ez_end..fixed]);
        assert!(mp.len() >= fixed);
        // Exact dirty tail fallback supports every tail with fewer clean prefixes.
        let clean_tail = (tail - 1).min(mp.len() - fixed);
        let need = fixed + clean_tail;
        let ms = MapScr { c0: mp[0], h: mp[1], e: mp[2], g: mp[3], f: mp[4], tmp: mp[5], one: mp[6],
                          pre: mp[7..pre_end].to_vec(), ez: mp[pre_end..ez_end].to_vec(), epre,
                          anc: mp[fixed..fixed + clean_tail].to_vec(), dirty: dirty.to_vec(),
                          // Beyond the complete map layout: unused and clean for the map.
                          andc: mp[need..].to_vec() };
        ColScr { sz: pool[0..9].to_vec(), sw: p(9), bq: p(10), cmpc: p(11), act: p(12), g: p(13), c0: p(14),
                 tmp: p(20), tmp2: p(23), f: p(12), one: p(15), pre, opre: pool[24..32].to_vec(),
                 anc: pool[32..39].to_vec(), zeros: vec![p(11)], ps, ms, dirty: dirty.to_vec() }
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

/// The column cut is sz+h. Four clean prefixes for sz's nine bits suffice for
/// every equality toggle; the initial threshold is computed by the exact compact
/// comparator plus an exact dirty toggle. Only rho's proved-zero top bit is borrowed; no quotient bit is borrowed.
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
                assert!(controls.len() <= 5);
                mc_xor(b, &controls, f, &[], dirty);
            }
        }
        b.x(f); b.cswap(f, ring[l], q[n-1-l]); b.x(f);
    }
    if let Some(v) = at(chi) {
        let controls = dec.ctrls(b, v);
        assert!(controls.len() <= 5);
        mc_xor(b, &controls, f, &[], dirty);
    }
    dec.clear(b);
}

/// Exact XOR oracle flag ^= [q0 >= 2], with arbitrary borrowed dirty wires
/// restored.  No clean temporary is borrowed: every high quotient lane is live.
/// In a column this helper is called only between the two middle swaps.
pub(super) fn hr_q_ge_two(b: &mut B, q0: &[QubitId], flag: QubitId, dirty: &[QubitId]) {
    assert!(!q0.is_empty());
    b.x(flag);
    let high_zero: Vec<_> = q0[1..].iter().map(|&q| (q, true)).collect();
    super::mask::mc_xor(b, &high_zero, flag, &[], dirty);
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
        if b.fusion_recording() { b.component_stage_mark(stn); }
        if stn > upto { return; }
    } }
    let n = cp.n;
    let h = cp.h as isize;
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    // Paid physical quotient extension on HR-only public shapes.  The
    // normalized Q window excludes the four held high quotient lanes through
    // the entire P -> correction -> un-P lifetime.  Global QB remains fixed.
    let public_mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(q.len() + 1);
    let head_extra = 6usize; // effective overflow K35 = physical q30 + retained five guard bits
    let lease_four = cp.hr && !cp.ht && cp.sy.1 <= q.len()-4-head_extra
        && cp.smax.1 <= q.len()-4-head_extra && public_mt <= q.len()-4-head_extra && cp.sz.0 >= cp.k+head_extra;
    let nqw = q.len() - if lease_four { 4+head_extra } else { 0 };
    let qw = &q[..nqw];
    let mut leased_sc = sc.clone();
    if lease_four { leased_sc.ps.q0.extend_from_slice(&q[q.len()-4..]); }
    let sc = &leased_sc;
    let ph = fd.ph;
    let (k, kp, qb, tot) = (cp.k + if lease_four { head_extra } else { 0 }, cp.kp, sc.ps.q0.len(), cp.tot);
    let dirty = sc.dirty.clone();
    // CNT is untouched until the finish/idle boundary. !dn licenses every
    // branch globally zero, including both switch domains and false controls.
    let middle_bank:Vec<_>=if !cp.dn {fd.cnt.clone()} else {Vec::new()};
    let cut_y = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let (pclo, pchi) = (cp.sz.0 + cp.h, cp.sz.1 + cp.h);
    // 1. sz = bl(Z) (probe below Y's MSB lane per shot)
    let mut probe_pre = sc.pre.clone();
    probe_pre.push(sc.bq); // bq is clean before P and after un-P
    probe_pre.extend_from_slice(&sc.ps.q0[..2]); // both quotient lanes are zero before P and after un-P
    let mut z_bank=sc.ps.rho.clone();z_bank.extend(&sc.ps.q0);z_bank.extend([sc.bq,sc.cmpc,sc.act,sc.g,sc.c0]);z_bank.extend(&fd.sx);z_bank.sort();z_bank.dedup();
    z_bank.retain(|w|!sc.sz.contains(w)&&*w!=sc.sw&&!ring.contains(w)&&!q.contains(w)&&!fd.sy.contains(w)&&!dirty.contains(w));
    let probe_z = rec(b, |b| {
        super::masked_priority_probe::emit(b,&ring,&cut_y,n-cp.sy.1,n-cp.sy.0,cp.sz.0.saturating_sub(1),cp.sz.1,&sc.sz,&z_bank,&dirty)
    });
    b.play(&probe_z, false);
    // 1b. sw = HR & bl(Z) <= l0
    if cp.sw {
        let mut ch1 = sc.pre.clone();
        ch1.extend([sc.bq, sc.tmp, sc.tmp2, sc.ps.q0[0]]); // bq and rho are still zero before P
        let gsw = rec(b, |b| super::mask::ge_const(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch1));
        b.play(&gsw, false);
        mc_xor(b, &[(sc.cmpc, true), (ph, true)], sc.sw, &[], &dirty);
        b.play(&gsw, true);
    }
    stage!(); // 1
    // 2. Y into Q
    // Four prefixes leave five controls for the nine-bit cut. Exact dirty
    // multi-controlled toggles restore passenger wires and use no extra helper.
    // Before P the whole rho bank is zero; afterward its top bit is zero
    // because rho<Yh<2^KP. Each use returns it before any rho compare.
    let middle_zero = rotated(&sc.ps.rho,tot)[kp];
    let pre_sw = vec![sc.g,sc.c0,sc.cmpc,middle_zero];
    let swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                   sc.f, &pre_sw, &dirty));
    assert_eq!(pre_sw.len(), sc.sz.len() - 5); // exact dirty five-control decoder
    let mut wide_pre_sw=pre_sw.clone();
    for &q in &sc.ps.rho {if !wide_pre_sw.contains(&q){wide_pre_sw.push(q);}}
    wide_pre_sw.truncate(sc.sz.len()-1);
    assert_eq!(wide_pre_sw.len(),sc.sz.len()-1);
    let wide_swap=rec(b,|b|masked_swap_middle_compact(b,&ring,&q,&sc.sz,cp.h,pclo,pchi,
        sc.f,&wide_pre_sw,&dirty));
    b.play(&wide_swap, false);
    stage!(); // 2
    // 3-4. window: Q down by sy puts Y's top kp bits (Yh = Y >> (sy - kp), or Y << (kp - sy) with zeros wrapped in
    // from Q's empty top) at Q's top kp lanes; ring down by sz puts Z's top k bits at the ring top; sz += sy gives
    // the pipeline start tot - e = sz + sy + (tot - 256 - k - kp)
    let soff = tot as i64 - 256 - k as i64 - kp as i64;
    let nq = q.len();
    let p_empty=nqw.saturating_sub(cp.sy.1.min(nqw)).min(nqw-kp);
    let p_held=p_empty.min(sc.sz.len()-1);
    // Reciprocal R needs at most K-1 carries, with f/c0 and at least one
    // unwritten q already appended. Signed rho needs KP+1, with f appended.
    let p_carry=(p_empty-p_held).min(k.saturating_sub(4).max(kp));
    let p_zeros=(p_held+p_carry).max(1);
    let mut p_prefix=Vec::new();let mut p_core=Vec::new();let mut p_outputs=Vec::new();
    let p_rec = rec(b, |b| {
        b.begin();
        p_rot_window(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, k, cp.k+1, true, &dirty);
        p_y_query(b, qw, &fd.sy, cp.sy.0.min(nqw), cp.sy.1.min(nqw), kp, p_zeros, true, &dirty);
        reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0);
        // Ring headroom funds the original K29+1 reciprocal remainder.
        // Six additional clean remainder lanes are fixed high Q lanes
        // excluded from both P and bcmp normalization for their lifetime.
        let extra_r = if lease_four { head_extra } else { 0 };
        let mut reciprocal_r = ring[0..cp.k + 1].to_vec();
        reciprocal_r.extend_from_slice(&q[nqw..nqw+extra_r]);
        assert_eq!(reciprocal_r.len(), k+1);
        let mut ps = PScr { r: reciprocal_r, ..sc.ps.clone() };
        ps.dirty = dirty.clone();
        // Y occupies q[nq-sy..nq] after its down rotation. Its public zero
        // prefix is outside Yh and is returned before the inverse rotation.
        let empty = nqw.saturating_sub(cp.sy.1.min(nqw)).min(nqw-kp);
        let held = empty.min(sc.sz.len()-1);
        ps.spre = qw[..held].to_vec();
        let start_min=cp.sz.0 as i64+cp.sy.0 as i64+soff;
        let dmax=if start_min<0 {((-start_min) as usize).min(k-1)}else{0};
        let skip=(k-1-dmax).min(tot-qb);
        eprintln!("PUBLIC_PREFIX K={k} QB={qb} start_min={start_min} dmax={dmax} skip={skip} sz0={} sy0={}",cp.sz.0,cp.sy.0);
        p_prefix=b.end();b.play(&p_prefix,false);
        p_outputs=ps.r.clone();p_outputs.extend(&ps.rho);p_outputs.extend(&ps.q0);
        b.begin();
        pipeline_nonrestoring_off_prefix(b, &ring[n - k..n], &qw[nqw - kp..nqw], &sc.sz, soff, tot, qb, &ps,
                                    &qw[held..held+p_carry], skip);
        p_core=b.end();b.play(&p_core,false);
        let rr = rec(b, |b| reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0));
        b.play(&rr, true);
        p_y_query(b, qw, &fd.sy, cp.sy.0.min(nqw), cp.sy.1.min(nqw), kp, p_zeros, false, &dirty);
        p_rot_window(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, k, cp.k+1, false, &dirty);
    });
    b.play(&p_rec, false);
    stage!(); // 3
    let rho = rotated(&sc.ps.rho, tot);
    // bq ^= AND(lits) & [rho < Xh], Xh = X >> syp (X in Q)
    let bcmp = |b: &mut B, lits: &[(QubitId, bool)], target: QubitId| {
        use super::arith::{down_m, up_m, Dm};
        p_rot_window(b, qw, &fd.sy, cp.sy.0.min(nqw), cp.sy.1.min(nqw), kp, 1, true, &dirty);
        let mut s: Vec<QubitId> = qw[nqw - kp..nqw].to_vec();
        s.push(sc.ps.zero);
        let up = up_m(b, &rho, &s, sc.c0, true);
        let dn = down_m(b, &rho, &s, sc.c0, Dm::Restore, true);
        b.play(&up, false);
        let mut c = vec![(s[kp], false)]; // carry of ~rho + Xh: [Xh > rho]
        c.extend_from_slice(lits);
        mc_xor(b, &c, target, &[sc.ps.f], &dirty);
        b.play(&dn, false);
        p_rot_window(b, qw, &fd.sy, cp.sy.0.min(nqw), cp.sy.1.min(nqw), kp, 1, false, &dirty);
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
            let mut chain = vec![middle_zero];
            chain.extend([sc.ps.f, sc.ps.g, sc.ps.c0]);
            let gc = rec(b, |b| ge_const_compact(b, &sc.sz, kk, sc.cmpc, &chain, &dirty));
            b.play(&gc, false);
            mc_xor(b, &[(sc.cmpc, true), (ring[n - mt], false)], sc.bq, &[], &dirty);
            b.play(&gc, true);
        }
        let sign_pre = [middle_zero];
        let mut dec = Dec::new(&sc.sz, &sign_pre);
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
        // On active HR determinant care p = R*t + Z*T with R > Z,
        // the exact correction [R < q0*Z] is false for stored q0 <= 1.
        // Retain the old rounded predicate only for q0 >= 2.  The flag
        // occupies g strictly between the middle swaps: g is a clean
        // decoder prefix of swap, and bcmp itself never borrows it.
        let q_ge_two = rec(b, |b| hr_q_ge_two(b, &sc.ps.q0, sc.g, &dirty));
        b.play(&q_ge_two, false);
        lits.push((sc.g, false));
        bcmp(b, &lits, sc.bq);
        b.play(&q_ge_two, true);
        b.play(&swap, false);
        ring_cadd_loan_extra(b, &ring, &q, 0, mt, sc.bq, true, &sc.zeros, sc.c0, cp.sy.1, nqw, middle_zero, &dirty,&middle_bank);
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
    if b.allow_booth && qbe>0 {
        qadd_signed_recode_extra(b,&ring,&q,&sc.ps.q0[..qbe],mt,
            if actl.is_empty(){None}else{Some(sc.act)},sc.c0,sc.zeros[0],cp.sy.1,nqw,middle_zero,sc.g,&dirty,&middle_bank);
    } else {
    for kk in 0..qbe {
        if !actl.is_empty() {
            b.and_c(sc.ps.q0[kk], sc.act, sc.g);
            ring_cadd_loan_extra(b, &ring, &q, kk, mt - kk, sc.g, false, &sc.zeros, sc.c0, cp.sy.1, nqw, middle_zero, &dirty,&middle_bank);
            b.and_u(sc.ps.q0[kk], sc.act, sc.g);
        } else {
            ring_cadd_loan_extra(b, &ring, &q, kk, mt - kk, sc.ps.q0[kk], false, &sc.zeros, sc.c0, cp.sy.1, nqw, middle_zero, &dirty,&middle_bank);
        }
    }
    }
    if !actl.is_empty() { mc_xor(b, &actl, sc.act, &[], &dirty); }
    if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
    stage!(); // 5
    // 7. HT correction: bq = [R - q0 r < 0]; R += bq r; erase bq by [rho < Xh(R')]
    if cp.ht {
        sign_into(b);
        ring_cadd_loan_extra(b, &ring, &q, 0, mt, sc.bq, false, &sc.zeros, sc.c0, cp.sy.1, nqw, middle_zero, &dirty,&middle_bank);
        const H: usize = 51;
        let can_lease = cp.sz.0 <= 257-H && cp.sy.0 <= nq-H;
        let predicate=rec(b,|b| {
        if !can_lease {
            b.play(&swap, false);
            let mut l = vec![(ph, false)];
            if cp.dn { l.extend(fd.cnt.iter().map(|&x| (x, true))); }
            bcmp(b, &l, sc.bq);
            b.play(&swap, false);
        } else {
            // Retain the old predicate on sw, which is zero on active HT.
            // HR switching branches retain their existing sw value unchanged.
            let old_pred = rec(b, |b| {
                b.play(&swap, false);
                let mut l = vec![(ph, false)];
                if cp.dn { l.extend(fd.cnt.iter().map(|&x| (x, true))); }
                bcmp(b, &l, sc.sw);
                b.play(&swap, false);
            });
            b.play(&old_pred, false);
            b.ccx(ph, sc.sw, sc.bq); // original rounded result is the fallback
            let w_add = rec(b, |b| {
                let mut active = vec![(ph, false)];
                if cp.dn { active.extend(fd.cnt.iter().map(|&x| (x, true))); }
                mc_xor(b, &active, sc.act, &[], &dirty);
                if b.allow_booth && qbe>0 {
                    qadd_signed_recode_extra(b,&ring,&q,&sc.ps.q0[..qbe],mt,Some(sc.act),sc.c0,sc.zeros[0],cp.sy.1,nqw,middle_zero,sc.g,&dirty,&middle_bank);
                }else{
                for kk in 0..qbe {
                    b.and_c(sc.ps.q0[kk], sc.act, sc.g);
                    ring_cadd_loan_extra(b, &ring, &q, kk, mt-kk, sc.g, false, &sc.zeros, sc.c0, cp.sy.1, nqw, middle_zero, &dirty,&middle_bank);
                    b.and_u(sc.ps.q0[kk], sc.act, sc.g);
                }
                }
                mc_xor(b, &active, sc.act, &[], &dirty);
            });
            b.play(&w_add, false);
            p_rot_window(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, H, 31+H, true, &dirty);
            let a: Vec<_> = ring[31..31+H].iter().rev().copied().collect();
            let mut target = ring[n-H..].to_vec();
            target.extend_from_slice(&q[nq-H..]);
            // w_add returns its complete Q source unchanged. The same
            // public suffix borrowed by its rows remains globally zero;
            // keep every target head lane and all P-held lanes excluded.
            assert!(!lease_four); // HT columns never lease HR quotient overflow
            let mut head_bank=vec![sc.g,middle_zero];head_bank.extend(&middle_bank);
            if cp.sy.1<nq-H {head_bank.extend_from_slice(&q[cp.sy.1..nq-H]);}
            for &w in &head_bank {assert!(!target.contains(&w)&&!a.contains(&w)&&!dirty.contains(&w));}
            let product = rec(b, |b| super::head_product_care::head_product(b, &target, &a,
                sc.c0, sc.f, &[sc.cmpc], &head_bank, &dirty));
            b.play(&product, false);
            // Bound errors by E=2^(H+1). Exclude the two E-sized bins
            // immediately adjacent to M=2^(2H-1), and preserve old behavior
            // there. All answers on the remaining domain are certified.
            let cmp_temp = [sc.cmpc, sc.g,middle_zero];
            ge_const_compact(b, &fd.sy, (nq-H+1) as isize, sc.f, &cmp_temp, &dirty);
            ge_const_compact(b, &sc.sz, (258-H) as isize, sc.c0, &cmp_temp, &dirty);
            let mut domain = vec![(ph,false),(sc.f,true),(sc.c0,true),(ring[30],true),(ring[31],false)];
            if cp.dn { domain.extend(fd.cnt.iter().map(|&x|(x,true))); }
            let msb = target[2*H-1];
            for (sign,old) in [(true,false),(false,true)] {
                let mut cond=domain.clone();
                cond.push((msb,!sign)); cond.push((sc.sw,!old));
                mc_xor(b,&cond,sc.bq,&cmp_temp,&dirty);
                let near_one = !sign;
                cond.extend(target[H+1..2*H-1].iter().map(|&x|(x,!near_one)));
                mc_xor(b,&cond,sc.bq,&cmp_temp,&dirty);
            }
            ge_const_compact(b, &sc.sz, (258-H) as isize, sc.c0, &cmp_temp, &dirty);
            ge_const_compact(b, &fd.sy, (nq-H+1) as isize, sc.f, &cmp_temp, &dirty);
            b.play(&product, true);
            p_rot_window(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, H, 31+H, false, &dirty);
            b.play(&w_add, true);
            b.play(&old_pred, true);
        }
        });
        if b.allow_booth {b.deferred_erasure(501,predicate,vec![sc.bq]);}else{b.play(&predicate,false);}
    }
    stage!(); // 6
    // 8. un-P (Y in Q)
    if b.allow_booth {
        b.play(&p_prefix,false);
        let core_inverse=rec(b,|b|b.play(&p_core,true));
        b.deferred_erasure(502,core_inverse,p_outputs);
        b.play(&p_prefix,true);
    }else{b.play(&p_rec,true);}
    stage!(); // 7
    // 9. X_new into Q (map layout); erase sz
    b.play(&wide_swap, false);
    if b.allow_booth && b.header_erasure_enabled {let erasure=rec(b,|b|b.play(&probe_z,true));b.deferred_erasure(503,erasure,sc.sz.clone());}else{b.play(&probe_z,true);}
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
    // At both bitlength seams every MapScr role is globally zero. The live
    // switch, quotient predicate, ordered-size comparator and both headers
    // are excluded by MapScr::carve. Aliased probe/cut prefixes occur once.
    let probe_bank=super::priority_probe::map_bank(&sc.ms);
    assert!(!probe_bank.iter().any(|q|fd.ring.contains(q)||fd.q.contains(q)||fd.sy.contains(q)||fd.sx.contains(q)||dirty.contains(q)||[sc.sw,sc.bq,sc.cmpc].contains(q)));
    rec(b, |b| {
        super::priority_probe::emit(b,q,0,cp.m,&fd.sx,&probe_bank);
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
        // Exact fixed3 normalized head, only original ordinary !SW&&!DN care.
        let head=if b.allow_booth && !cp.sw && !cp.dn {3usize} else {0};
        let norm=rec(b,|b|{
            if head==0{return;}
            let pad=&sc.ms.anc[..fd.sx.len()];
            assert!(pad.iter().all(|w|!fd.sx.contains(w)&&!fd.sy.contains(w)&&!ring.contains(w)&&!q.contains(w)));
            for (i,&w) in pad.iter().enumerate(){if head>>i&1!=0{b.x(w);}}
            super::arith::ttk_add(b,pad,&fd.sx,None,None);
            for (i,&w) in pad.iter().enumerate(){if head>>i&1!=0{b.x(w);}}
        });b.play(&norm,false);
        let mcut = Cut { v: fd.sx.clone(), a: n as isize, neg: true };
        let mpar = MapPar { clo: n - cp.smax.1 - head, chi: n - cp.smax.0 - head, m: cp.m, tail: cp.tail, emax: cp.emax };
        let mut ms = sc.ms.clone();
        ms.dirty = dirty.clone();
        // Ordinary maps need at most 257 + emax <= n lanes by the product
        // invariant. Switch endpoints and pair values each fit nq lanes, so
        // 2*nq + emax - n extra lanes cover the complete retained v2 envelope.
        // Fund these transient lanes from tail prefixes. Dirty exact increments
        // replace only tails whose clean prefix no longer fits; loans remain
        // excluded from every map scratch and carry vector until returned.
        let extra = if cp.sw { (2 * cp.nq + cp.emax).saturating_sub(n) } else { 0 };
        // bq has been erased by the middle correction and is not used by an
        // ordinary map. The end's controlled map has cp.sw=false and takes no
        // loan. With !dn every branch is still stepping: cnt is zero, and this
        // column's optional finish increment occurs only after the map returns.
        let mut extension = vec![];
        if extra > 0 {
            extension.push(sc.bq);
            if !cp.dn { extension.extend(fd.cnt.iter().copied().take(extra - 1)); }
        }
        let owed = extra - extension.len();
        assert!(ms.anc.len() >= owed);
        extension.extend(ms.anc.split_off(ms.anc.len() - owed));
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
        if b.allow_booth {
            if extra==0 {ms.andc.push(sc.bq);}
            if !cp.sw {ms.andc.push(sc.sw);}
            if !cp.dn {ms.andc.extend(fd.cnt.iter().copied().filter(|q|!extension.contains(q)));}
            assert_eq!(ms.andc.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),ms.andc.len());
            assert!(!ms.andc.iter().any(|q|extended.contains(q)));
        }
        mapf(b, &extended, q, &extcut, &extpar, &ms);
        b.play(&embed, true);
        b.play(&norm,true);
        b.play(&order, true);
        let probe_y = rec(b, |b| super::priority_probe::emit(b, q, cp.sy.0.saturating_sub(1), if cp.sy.1==0 {cp.m}else{cp.m.min(cp.sy.1)}, &fd.sy, &probe_bank));
        if b.allow_booth && b.header_erasure_enabled {let erasure=rec(b,|b|b.play(&probe_y,true));b.deferred_erasure(504,erasure,fd.sy.clone());}else{b.play(&probe_y,true);}
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
        let old_booth=b.allow_booth;b.allow_booth=false;
        let ms_rec = map_stage(b, fd, cp, &sc);
        b.allow_booth=old_booth;
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
mod pool64_tests {
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
    fn pool64_compact_threshold_all_values_and_phases() {
        let mut checks=0usize;
        for width in 1..=9 {
            let limit=1usize << width;
            for k in -1..=limit as isize + 1 {
                let mut b=B::new();
                let v=b.alloc_n(width);
                let t=b.alloc();
                let temp=b.alloc_n(width.saturating_sub(4));
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
        eprintln!("POOL64_COMPACT_THRESHOLD_ALL_PHASE_PASS checks={checks} widths=1..9 every_value_threshold=true inverse=true");
    }
}
