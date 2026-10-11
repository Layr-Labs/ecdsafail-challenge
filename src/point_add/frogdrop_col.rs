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
    /// payload: the previous column has HT stepping shots (their narrowing runs here), with that column's sy range
    pub pht: bool,
    pub psy: (usize, usize),
    /// largest ring-top (middle target) value bits; the previous column may switch (this one then holds first-HT
    /// shots in the switched layout: Q = Y = r_j, ring top = X = r_{j-1} > 2^l0)
    pub xw: usize,
    pub psw: bool,
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
    /// first-HT handling (clean outside P): size temp and the switched-layout flag
    pub u: Vec<QubitId>,
    pub u2: Vec<QubitId>,
    pub js: QubitId,
    /// subset-storage P (QSUB > 0): the quotient subsets in processing order (P stores qsets[0]) and the parity
    /// erase lane of unstored bits
    pub qsets: Vec<Vec<bool>>,
    pub tq: QubitId,
    pub ps: PScr,
    pub ms: MapScr,
    pub dirty: Vec<QubitId>,
}

/// Stored quotient bits per P subset (0: the whole 26-bit q0 is stored). With QSUB > 0 the 26 bits are split
/// top-down into subsets of QSUB; P stores one subset at a time and switches by replaying its quotient iterations.
pub const QSUB: usize = 2;

/// Stored quotient bits per subset (see QSUB).
pub fn qsub() -> usize {
    QSUB
}

/// Quotient subsets of a qb-bit q0, top-down chunks of QSUB (one full subset when QSUB == 0).
pub fn qsubsets(qb: usize) -> Vec<Vec<bool>> {
    let qs = qsub();
    if qs == 0 {
        return vec![vec![true; qb]];
    }
    let mut out = vec![];
    let mut hi = qb;
    while hi > 0 {
        let lo = hi.saturating_sub(qs);
        out.push((0..qb).map(|k| k >= lo && k < hi).collect());
        hi = lo;
    }
    out
}

/// Size of the shared column scratch pool (plus the spare size register sx, which joins rho during P).
/// Column pool size for size registers of `sw` bits (the spare one is the first `sw` lanes of rho/q0).
pub fn pool_size(kp: usize, qb: usize, sw: usize) -> usize {
    if qsub() > 0 {
        // rho and the stored subset beyond the two overflow lanes
        return 17 + (kp + 1 + qsub().max(2) - 2 - sw);
    }
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
        let mut q0 = if qsub() > 0 { vec![p(15); qb] } else { rq[kp + 1..kp + 1 + qb].to_vec() };
        q0.extend([p(15),p(16)]); // two paid overflow lanes; base QB remains unchanged
        let qsets = qsubsets(q0.len());
        let mut tq = p(16);
        if qsub() > 0 {
            let qs = qsub().max(2);
            // stored lanes: the bank above rho, then the two overflow lanes (each subset's top bits; q0[0..2] stay
            // off the probe prefixes)
            let mut st = rq[kp + 1..kp + 1 + qs - 2].to_vec();
            st.extend([p(15), p(16)]);
            // unstored bits go through P's f lane: clean at every quotient step (cleared by the parity of R)
            tq = p(12);
            let nb = q0.len();
            for set in &qsets {
                let mut r = 0;
                for kk in 0..nb {
                    if set[kk] { q0[kk] = st[r]; r += 1; }
                }
            }
        }
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
        // first-HT size temp and flag (stage 2, and the stage-14 probe): pool[39..48], or for smaller pools the rho
        // lanes outside the probe/swap helpers (tmp 20, tmp2 23, middle-zero rho lane 18) plus pool[39..]
        let (u, js) = if pool.len() >= 48 {
            (pool[39..47].to_vec(), p(47))
        } else {
            let mut c: Vec<QubitId> = [17usize, 19, 21, 22].iter().map(|&i| p(i)).collect();
            c.extend(&pool[39..]);
            // last resort: anc[6], anc[5], anc[4] (the probe/compare chains there use at most pre + anc[..4]) and
            // opre[7] (the probes into 8-lane outputs hold 7 prefixes)
            c.extend([p(38), p(37), p(36), p(31)]);
            assert!(c.len() >= 9, "pool too small for the first-HT temps");
            (c[..8].to_vec(), c[8])
        };
        ColScr { sz: pool[0..9].to_vec(), sw: p(9), bq: p(10), cmpc: p(11), act: p(12), g: p(13), c0: p(14),
                 tmp: p(20), tmp2: p(23), f: p(12), one: p(15), pre, opre: pool[24..32].to_vec(),
                 anc: pool[32..39].to_vec(), zeros: vec![p(11)], u, u2: sx.to_vec(), js, qsets, tq, ps, ms,
                 dirty: dirty.to_vec() }
    }
}


/// Done shots' Q value (R or 1) is below 2^RB (the quotient cap); the derived-done test checks Q[RA..ctop) == 0.
pub const RB: usize = 26;
pub const RA: usize = 64;

/// done (Euclid finished) is derived, not stored: done = ph & Q[RA..ctop) == 0 & cnt != 0 (a stepping HT value with
/// bits only in [0, RA) and [ctop, nq) is a ~2^-57 exception). The idle counter `cnt`
/// (Q's top lanes) is nonzero exactly on done shots, whose Q value (R or 1) is below 2^26; every other ph shot holds a
/// value below 2^l0 or, in its first HT column, a just-switched r_{j-1} with a set bit in [l0, ctop) (the rare
/// exception, no set bit there, is a predicted failure). Returns (ph & A, ph & A & B), A = Q[l0..ctop) == 0, B = cnt == 0.
fn dn_parts(fd: &Fd, _l0: usize) -> (Vec<(QubitId, bool)>, Vec<(QubitId, bool)>) {
    let ctop = fd.q.len() - fd.cnt.len();
    let mut a = vec![(fd.ph, false)];
    a.extend((RA..ctop).map(|l| (fd.q[l], true)));
    let mut ab = a.clone();
    ab.extend(fd.cnt.iter().map(|&x| (x, true)));
    (a, ab)
}

/// AND of two literal lists (duplicates merged); None when contradictory.
fn and_lits2(x: &[(QubitId, bool)], y: &[(QubitId, bool)]) -> Option<Vec<(QubitId, bool)>> {
    let mut out: Vec<(QubitId, bool)> = x.to_vec();
    for &(q, n) in y {
        match out.iter().find(|l| l.0 == q) {
            Some(&(_, m)) if m == n => {}
            Some(_) => return None,
            None => out.push((q, n)),
        }
    }
    Some(out)
}

/// target ^= AND(lits) & done (`done` true) or AND(lits) & !done, done derived as in `dn_parts`.
pub(crate) fn mc_xor_dn(b: &mut B, lits: &[(QubitId, bool)], target: QubitId, temps: &[QubitId], dirty: &[QubitId],
                        fd: &Fd, l0: usize, done: bool) {
    use super::mask::mc_xor;
    let (a, ab) = dn_parts(fd, l0);
    if !done {
        mc_xor(b, lits, target, temps, dirty);
    }
    if let Some(l) = and_lits2(lits, &a) { mc_xor(b, &l, target, temps, dirty); }
    if let Some(l) = and_lits2(lits, &ab) { mc_xor(b, &l, target, temps, dirty); }
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

/// masked_swap_middle_compact skipped on shots with `gate` = 1 (`tmp` clean).
fn masked_swap_gated(b: &mut B, ring: &[QubitId], q: &[QubitId], sz: &[QubitId], h: usize, clo: usize, chi: usize,
                     f: QubitId, pre: &[QubitId], dirty: &[QubitId], gate: QubitId, tmp: QubitId) {
    use super::mask::{mc_xor, Dec};
    let n = ring.len();
    let qlo = n.saturating_sub(q.len());
    b.x(gate);
    for l in chi.max(qlo)..n { b.cswap(gate, ring[l], q[n-1-l]); }
    b.x(gate);
    let lo = clo.max(qlo);
    if lo >= chi { return; }
    ge_const_compact(b, sz, lo as isize + 1 - h as isize, f, pre, dirty);
    let mut dec = Dec::new(sz, pre);
    let at = |l: usize| l.checked_sub(h).filter(|&v| v < (1usize << sz.len()));
    for l in lo..chi {
        if l > lo {
            if let Some(v) = at(l) {
                let controls = dec.ctrls(b, v);
                mc_xor(b, &controls, f, &[], dirty);
            }
        }
        b.x(f); b.x(gate);
        b.and_c(f, gate, tmp);
        b.cswap(tmp, ring[l], q[n-1-l]);
        b.and_u(f, gate, tmp);
        b.x(gate); b.x(f);
    }
    if let Some(v) = at(chi) {
        let controls = dec.ctrls(b, v);
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
    column_upto(b, fd, cp, sc, 99, None)
}

pub fn column_pl(b: &mut B, fd: &mut Fd, cp: &ColPar, sc: &ColScr, pl: Option<&super::payload::PlCol>) {
    column_upto(b, fd, cp, sc, 99, pl)
}

pub fn column_upto(b: &mut B, fd: &mut Fd, cp: &ColPar, sc: &ColScr, upto: usize,
                   pl: Option<&super::payload::PlCol>) {
    use super::mask::{mc_xor, Dec};
    let prof = std::env::var("FROGDROP_PROF").is_ok();
    let mut stn = 0usize;
    let mut last = if std::env::var("FROGDROP_PROF_OPS").is_ok() { b.ops.len() as u64 } else { b.tof };
    let mut prof_v: Vec<(usize, u64)> = vec![];
    macro_rules! stage { () => {
        stn += 1;
        if prof {
            let v = if std::env::var("FROGDROP_PROF_OPS").is_ok() { b.ops.len() as u64 } else { b.tof };
            prof_v.push((stn, v - last)); last = v;
        }
        if stn > upto { return; }
    } }
    let n = cp.n;
    let h = cp.h as isize;
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    let ph = fd.ph;
    let (k, kp, qb, tot) = (cp.k, cp.kp, sc.ps.q0.len(), cp.tot);
    let dirty = sc.dirty.clone();
    let cut_y = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let (pclo, pchi) = (cp.sz.0 + cp.h, cp.sz.1 + cp.h);
    // 1. sz = bl(Z) (probe below Y's MSB lane per shot)
    let mut probe_pre = sc.pre.clone();
    probe_pre.push(sc.bq); // bq is clean before P and after un-P
    // two distinct quotient lanes (zero before P and after un-P; subsets share lanes)
    let mut qz: Vec<QubitId> = vec![];
    for &x in &sc.ps.q0 { if !qz.contains(&x) && !probe_pre.contains(&x) { qz.push(x); } }
    // (few stored lanes: rho is zero here too; skip the probe's own helpers)
    for &x in &sc.ps.rho {
        if !qz.contains(&x) && !probe_pre.contains(&x) && !sc.opre.contains(&x) && x != sc.tmp && x != sc.tmp2 {
            qz.push(x);
        }
    }
    probe_pre.extend_from_slice(&qz[..2]);
    // bulengerk c4f95ef6: masked priority probe on lanes that are zero before P and after un-P
    let mut z_bank=sc.ps.rho.clone();z_bank.extend(&sc.ps.q0);z_bank.extend([sc.bq,sc.cmpc,sc.act,sc.g,sc.c0]);z_bank.extend(&fd.sx);
    z_bank.sort();z_bank.dedup();
    z_bank.retain(|w|!sc.sz.contains(w)&&*w!=sc.sw&&!ring.contains(w)&&!q.contains(w)&&!fd.sy.contains(w)&&!dirty.contains(w));
    // (small pools, e.g. 732: the old probe where the clean bank has no block layout)
    let zn = cp.sz.1 - cp.sz.0.saturating_sub(1);
    let masked_ok = super::masked_priority_probe::feasible(zn, cut_y.v.len(), z_bank.len());
    let probe_z = if std::env::var("FD_OLDPROBE").is_ok() || !masked_ok { rec(b, |b| {
        msb_probe_cut_range(b, &ring, &cut_y, n - cp.sy.1, n - cp.sy.0, cp.sz.0.saturating_sub(1), cp.sz.1,
                            &sc.sz, sc.f, &probe_pre, &sc.opre, sc.tmp, sc.tmp2, &dirty)
    }) } else { rec(b, |b| {
        super::masked_priority_probe::emit(b,&ring,&cut_y,n-cp.sy.1,n-cp.sy.0,cp.sz.0.saturating_sub(1),cp.sz.1,&sc.sz,&z_bank,&dirty)
    }) };
    b.play(&probe_z, false);
    // 1b. sw = HR & bl(Z) <= l0
    if cp.sw {
        let mut ch1 = sc.pre.clone();
        ch1.extend([sc.bq, sc.tmp, sc.tmp2, qz[0]]); // bq and the quotient/rho lanes are still zero before P
        let gsw = rec(b, |b| super::mask::ge_const(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch1));
        b.play(&gsw, false);
        mc_xor(b, &[(sc.cmpc, true), (ph, true)], sc.sw, &[], &dirty);
        b.play(&gsw, true);
    }
    if let Some(pl) = pl {
        super::payload::col_narrow_ht(b, fd, cp, sc, pl);
    }
    stage!(); // 1
    // 2. Y into Q
    // Four prefixes leave five controls for the nine-bit cut. Exact dirty
    // multi-controlled toggles restore passenger wires and use no extra helper.
    // Before P the whole rho bank is zero; afterward its top bit is zero
    // because rho<Yh<2^KP. Each use returns it before any rho compare.
    let middle_zero = rotated(&sc.ps.rho,tot)[kp];
    assert!(!sc.u.contains(&middle_zero) && sc.js != middle_zero);
    let pre_sw = vec![sc.g,sc.c0,sc.cmpc,middle_zero];
    let swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                   sc.f, &pre_sw, &dirty));
    assert_eq!(pre_sw.len(), sc.sz.len() - 5); // exact dirty five-control decoder
    // bulengerk: where the whole rho bank is |0> (before P, after un-P) the decoder takes wider clean prefixes
    let mut wide_pre_sw = pre_sw.clone();
    for &x in &sc.ps.rho { if !wide_pre_sw.contains(&x) { wide_pre_sw.push(x); } }
    wide_pre_sw.truncate(sc.sz.len() - 1);
    assert_eq!(wide_pre_sw.len(), sc.sz.len() - 1);
    let wide_swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                        sc.f, &wide_pre_sw, &dirty));
    if cp.psw {
        // first-HT shots arrive in the switched layout (Q = Y, top = X > 2^l0, sy = bl(X)): js = ph & sy > l0,
        // sy <-> U = bl(Q) on them (sy = bl(Y) for the column), and they skip this first swap
        let mut chain = sc.pre.clone();
        chain.extend_from_slice(&sc.anc);
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
        b.ccx(ph, sc.cmpc, sc.js);
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
        let pu = rec(b, |b| probe_gated(b, &q, 0, cp.l0.min(q.len()), &sc.u, &[(sc.js, false)], &sc.opre, sc.tmp,
                                        &[sc.tmp2], &dirty));
        b.play(&pu, false);
        for i in 0..fd.sy.len() { b.cswap(sc.js, fd.sy[i], sc.u[i]); }
        let first = rec(b, |b| masked_swap_gated(b, &ring, &q, &sc.sz, cp.h, pclo, pchi, sc.f, &pre_sw, &dirty,
                                                 sc.js, sc.bq));
        b.play(&first, false);
        // every shot now has X in the ring top: T = bl(top); U ^= js & T (= 0); js ^= ph & T > l0; T uncomputed
        let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
        let cutr = Cut { v: sc.sz.clone(), a: (n - cp.h) as isize, neg: true };
        let pt = rec(b, |b| msb_probe_cut_range(b, &rev, &cutr, n - cp.h - cp.sz.1, n - cp.h - cp.sz.0, 0,
                                                (cp.xw + 1).min(n), &sc.u2, sc.f, &chain, &sc.opre, sc.tmp, sc.tmp2,
                                                &dirty));
        b.play(&pt, false);
        for i in 0..fd.sy.len() { b.ccx(sc.js, sc.u2[i], sc.u[i]); }
        super::mask::ge_const(b, &sc.u2, cp.l0 as isize + 1, sc.cmpc, &chain);
        b.ccx(ph, sc.cmpc, sc.js);
        super::mask::ge_const(b, &sc.u2, cp.l0 as isize + 1, sc.cmpc, &chain);
        b.play(&pt, true);
    } else {
        b.play(&wide_swap, false);
    }
    if let Some(pl) = pl {
        super::payload::col_digit(b, fd, cp, sc, pl);
    }
    stage!(); // 2
    // 3-4. window: Q down by sy puts Y's top kp bits (Yh = Y >> (sy - kp), or Y << (kp - sy) with zeros wrapped in
    // from Q's empty top) at Q's top kp lanes; ring down by sz puts Z's top k bits at the ring top; sz += sy gives
    // the pipeline start tot - e = sz + sy + (tot - 256 - k - kp)
    let soff = tot as i64 - 256 - k as i64 - kp as i64;
    let nq = q.len();
    // loan bank for the ring adds: Q[lsb..loan_end) is |0> on every shot outside P (Y < 2^sy; done shots hold R < 2^26
    // in at most 28 low lanes and their counter in the top lanes)
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let loan_end = nq - if cp.dn { fd.cnt.len() } else { 0 };
    // Y occupies q[nq-sy..nq] after its down rotation. Its public zero
    // prefix is outside Yh and is returned before the inverse rotation.
    let mut empty = nq.saturating_sub(cp.sy.1.min(nq)).min(nq-kp);
    if cp.dn {
        // done shots' counter (Q's top lanes) rotates down by sy <= 26 here: keep these helpers below it
        empty = empty.min(nq - fd.cnt.len() - 26);
    }
    let held = empty.min(sc.sz.len()-1);
    let mut ps = PScr { r: ring[0..k + 1].to_vec(), ..sc.ps.clone() };
    ps.dirty = dirty.clone();
    ps.spre = q[..held].to_vec();
    // subset P: p_sets[i] = P storing qsets[i]; p_sw[i] switches the stored subset i -> i + 1
    let mut p_sets: Vec<Vec<super::builder::G>> = vec![];
    let mut p_sw: Vec<Vec<super::builder::G>> = vec![];
    // (rotation, head, last tail) of the subset P, for the deferred un-P erasure
    let mut p_parts: Option<(Vec<super::builder::G>, Vec<super::builder::G>, Vec<super::builder::G>)> = None;
    if qsub() > 0 {
        // care rotations: P reads only Zh (ring top k), R (ring[0..k+1]), Yh (Q top kp) and Q[0..empty)
        let care = std::env::var("FD_NOCARE").is_err();
        let dest_r: std::collections::BTreeSet<usize> = (n - k..n).chain(0..k + 1).collect();
        // P uses at most kp + 1 AND carries (the reciprocal bank adds its own): rotate only those clean lanes in
        let pcar = (empty - held).min(kp + 1);
        let dest_q: std::collections::BTreeSet<usize> = (nq - kp..nq).chain(0..held + pcar).collect();
        let rrot = rec(b, |b| {
            if care {
                rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_r);
                rot_by_range_care(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), true, &dirty, &dest_q);
            } else {
                rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty);
                rot_by_range(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), true, &dirty);
            }
            reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0);
        });
        // Every stepping shot has bl(r_j) + bl(t_j) >= 228: r_{j-1}|t_j| >= p/2 gives bl(r_{j-1}) + bl(t_j) >= 255 and
        // r_{j-1} < (q_j + 1) r_j with q_j < 2^26 gives bl(r_j) >= bl(r_{j-1}) - 27 (first-HT shots use r_{j-1}: larger).
        // Done shots' q0 is never used, and P stays reversible on them.
        let start_min = (cp.sz.0 + cp.sy.0).max(228) as i64 + soff;
        let dmax = if start_min < 0 { ((-start_min) as usize).min(k - 1) } else { 0 };
        let skip = if std::env::var("FD_NOSKIP").is_ok() { 0 } else { (k - 1 - dmax).min(tot - qb) };
        let (head, tails, swp, _, _) = super::frogdrop::pipeline_subset(b, &ring[n - k..n], &q[nq - kp..nq],
            &sc.sz, soff, tot, qb, &ps, &q[held..held + pcar], &sc.qsets, sc.tq, skip);
        for t in &tails {
            p_sets.push(rec(b, |b| { b.play(&rrot, false); b.play(&head, false); b.play(t, false);
                                     b.play(&rrot, true); }));
        }
        for (ta, tb) in &swp {
            p_sw.push(rec(b, |b| { b.play(&rrot, false); b.play(ta, true); b.play(tb, false);
                                   b.play(&rrot, true); }));
        }
        p_parts = Some((rrot.clone(), head.clone(), tails[tails.len() - 1].clone()));
    } else {
        p_sets.push(rec(b, |b| {
            rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty);
            rot_by_range(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), true, &dirty);
            reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0);
            pipeline_overflow_carry_off(b, &ring[n - k..n], &q[nq - kp..nq], &sc.sz, soff, tot, qb, &ps,
                                        &q[held..empty]);
            let rr = rec(b, |b| reg_add_into(b, &sc.sz, &fd.sy, &sc.zeros, sc.ps.c0));
            b.play(&rr, true);
            rot_by_range(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), false, &dirty);
            rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, false, &dirty);
        }));
    }
    let nsets = p_sets.len();
    b.play(&p_sets[0], false);
    if let Some(pl) = pl {
        super::payload::col_trans_hr_q0(b, fd, cp, sc, pl, &sc.qsets[0]);
    }
    stage!(); // 3
    let rho = rotated(&sc.ps.rho, tot);
    // bq ^= AND(lits) & [rho < Xh], Xh = X >> syp (X in Q)
    let bcmp = |b: &mut B, lits: &[(QubitId, bool)], target: QubitId| {
        use super::arith::{down_m, up_m, Dm};
        let dest_x: std::collections::BTreeSet<usize> = (nq - kp..nq).collect();
        let care = std::env::var("FD_NOCARE").is_err();
        if care { rot_by_range_care(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), true, &dirty, &dest_x); }
        else { rot_by_range(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), true, &dirty); }
        let mut s: Vec<QubitId> = q[nq - kp..nq].to_vec();
        s.push(sc.ps.zero);
        let up = up_m(b, &rho, &s, sc.c0, true);
        let dn = down_m(b, &rho, &s, sc.c0, Dm::Restore, true);
        b.play(&up, false);
        let mut c = vec![(s[kp], false)]; // carry of ~rho + Xh: [Xh > rho]
        c.extend_from_slice(lits);
        mc_xor(b, &c, target, &[sc.ps.f], &dirty);
        b.play(&dn, false);
        if care { rot_by_range_care(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), false, &dirty, &dest_x); }
        else { rot_by_range(b, &q, &fd.sy, cp.sy.0.min(nq), cp.sy.1.min(nq), false, &dirty); }
    };
    // ladder over the ring-top value's bits [0, mt): every pair value fits Q (< 2^nq), so bit nq is a sign bit
    let mt = (n - pclo + 1).min(nq.max(cp.xw) + 1);
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
        bcmp(b, &lits, sc.bq);
        b.play(&swap, false);
        ring_cadd2_loan(b, &ring, &q, 0, mt, sc.bq, true, &sc.zeros, sc.c0, sc.g, &dirty, lsb, loan_end, middle_zero);
        if let Some(pl) = pl {
            super::payload::col_trans_hr_bq(b, fd, cp, sc, pl);
        }
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
    // (subset mode undoes this complement at once: its +-Y adds run in the real frame)
    let mut actl = vec![];
    if cp.sw { actl.push((sc.sw, true)); }
    let set_act = |b: &mut B| {
        if cp.dn { mc_xor_dn(b, &actl, sc.act, &[], &dirty, fd, cp.l0, false); } // not done
        else if !actl.is_empty() { mc_xor(b, &actl, sc.act, &[], &dirty); }
    };
    let gated = cp.dn || !actl.is_empty();
    let adds = |b: &mut B, set: &[bool]| {
        for kk in 0..qbe {
            if !set[kk] { continue; }
            if gated {
                b.and_c(sc.ps.q0[kk], sc.act, sc.g);
                ring_cadd2_loan(b, &ring, &q, kk, mt - kk, sc.g, false, &sc.zeros, sc.c0, sc.bq, &dirty, lsb, loan_end, middle_zero);
                b.and_u(sc.ps.q0[kk], sc.act, sc.g);
            } else {
                ring_cadd2_loan(b, &ring, &q, kk, mt - kk, sc.ps.q0[kk], false, &sc.zeros, sc.c0, sc.bq, &dirty, lsb, loan_end, middle_zero);
            }
        }
    };
    if qsub() == 0 {
        set_act(b);
        adds(b, &sc.qsets[0]);
        set_act(b);
        if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
    } else {
        // subset P: the switch between subsets replays P, which reads R in the gap above Z, so every partial
        // ladder value must stay in [0, 2^region]: X += Y first (HR: T - bq t + t >= 0; HT: r_{j-1} + r_j - part
        // of q0 r_j >= r_{j+1} >= 0) and X -= Y after the last subset
        if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
        let act_on = |b: &mut B| if gated { set_act(b) } else { b.x(sc.act) };
        act_on(b);
        ring_cadd2_loan(b, &ring, &q, 0, mt, sc.act, false, &sc.zeros, sc.c0, sc.bq, &dirty, lsb, loan_end, middle_zero);
        act_on(b);
        for i in 0..nsets {
            if i > 0 {
                let sw0 = b.tof;
                b.play(&p_sw[i - 1], false);
                if std::env::var("FROGDROP_PROF2").is_ok() { eprintln!("swprof q0 {} i {}", b.tof - sw0, i); }
                if let Some(pl) = pl {
                    super::payload::col_trans_hr_q0(b, fd, cp, sc, pl, &sc.qsets[i]);
                }
            }
            if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
            set_act(b);
            adds(b, &sc.qsets[i]);
            set_act(b);
            if cp.ht { for l in (n - mt)..n { b.cx(ph, ring[l]); } }
        }
        act_on(b);
        ring_cadd2_loan(b, &ring, &q, 0, mt, sc.act, true, &sc.zeros, sc.c0, sc.bq, &dirty, lsb, loan_end, middle_zero);
        act_on(b);
    }
    stage!(); // 5
    // 7. HT correction: bq = [R - q0 r < 0]; R += bq r; erase bq by [rho < Xh(R')]
    if cp.ht {
        sign_into(b);
        ring_cadd2_loan(b, &ring, &q, 0, mt, sc.bq, false, &sc.zeros, sc.c0, sc.g, &dirty, lsb, loan_end, middle_zero);
        if let Some(pl) = pl {
            super::payload::col_trans_ht(b, fd, cp, sc, pl);
        }
        const H: usize = 51;
        let can_lease = cp.sz.0 <= 257-H && cp.sy.0 <= nq-H;
        // bulengerk b6907bb1: the whole bq erasure is one deferred box (forward walks measure bq; the mirrored
        // inverse walk recomputes it and cancels the phase)
        let predicate = rec(b, |b| {
        if !can_lease {
            b.play(&swap, false);
            // not-done active HT flag on g (free between the swaps; Q = X still shows done)
            if cp.dn { mc_xor_dn(b, &[(ph, false)], sc.g, &[], &dirty, fd, cp.l0, false); }
            let l = if cp.dn { vec![(sc.g, false)] } else { vec![(ph, false)] };
            bcmp(b, &l, sc.bq);
            if cp.dn { mc_xor_dn(b, &[(ph, false)], sc.g, &[], &dirty, fd, cp.l0, false); }
            b.play(&swap, false);
        } else {
            // Retain the old predicate on sw, which is zero on active HT.
            // HR switching branches retain their existing sw value unchanged.
            let old_pred = rec(b, |b| {
                b.play(&swap, false);
                if cp.dn { mc_xor_dn(b, &[(ph, false)], sc.g, &[], &dirty, fd, cp.l0, false); }
                let l = if cp.dn { vec![(sc.g, false)] } else { vec![(ph, false)] };
                bcmp(b, &l, sc.sw);
                if cp.dn { mc_xor_dn(b, &[(ph, false)], sc.g, &[], &dirty, fd, cp.l0, false); }
                b.play(&swap, false);
            });
            let ht0 = b.tof;
            b.play(&old_pred, false);
            b.ccx(ph, sc.sw, sc.bq); // original rounded result is the fallback
            let ht1 = b.tof;
            let w_add = rec(b, |b| {
                let active = vec![(ph, false)];
                let set = |b: &mut B| {
                    if cp.dn { mc_xor_dn(b, &active, sc.act, &[], &dirty, fd, cp.l0, false); }
                    else { mc_xor(b, &active, sc.act, &[], &dirty); }
                };
                // all of q0: the stored subset first, then switch back through the others (P state rewinds)
                for i in (0..nsets).rev() {
                    let sw0 = b.tof;
                    if i + 1 < nsets { b.play(&p_sw[i], true); }
                    if std::env::var("FROGDROP_PROF2").is_ok() && i + 1 < nsets { eprintln!("swprof w {} i {}", b.tof - sw0, i); }
                    set(b);
                    for kk in 0..qbe {
                        if !sc.qsets[i][kk] { continue; }
                        b.and_c(sc.ps.q0[kk], sc.act, sc.g);
                        ring_cadd2_loan(b, &ring, &q, kk, mt-kk, sc.g, false, &sc.zeros, sc.c0, middle_zero, &dirty, lsb, loan_end, middle_zero);
                        b.and_u(sc.ps.q0[kk], sc.act, sc.g);
                    }
                    set(b);
                }
            });
            b.play(&w_add, false);
            // the certificate reads ring[n-H..], ring[30..31+H] in the rotated frame
            let dest_h: std::collections::BTreeSet<usize> = (n - H..n).chain(30..31 + H).collect();
            let care_h = std::env::var("FD_NOCARE").is_err();
            if care_h { rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_h); }
            else { rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty); }
            let ht2 = b.tof;
            let a: Vec<_> = ring[31..31+H].iter().rev().copied().collect();
            let mut target = ring[n-H..].to_vec();
            target.extend_from_slice(&q[nq-H..]);
            // bulengerk bf1897f0: the public Q suffix the rows borrow is zero here too (from the loan bound lsb, which
            // keeps done shots' R; the counter lanes sit above nq - H)
            let mut head_bank=vec![sc.g,middle_zero];
            if std::env::var("FD_NOHEADBANK").is_err() && lsb<nq-H {head_bank.extend_from_slice(&q[lsb..nq-H]);}
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
            // done shots have bl(Z) >= 229 > 258 - H: c0 already excludes them
            let domain = vec![(ph,false),(sc.f,true),(sc.c0,true),(ring[30],true),(ring[31],false)];
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
            let ht3 = b.tof;
            if care_h { rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, false, &dirty, &dest_h); }
            else { rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, false, &dirty); }
            b.play(&w_add, true);
            b.play(&old_pred, true);
            if std::env::var("FROGDROP_PROF2").is_ok() { eprintln!("htprof old {} wadd {} prod {} undo {} nsets {} mt {}", ht1-ht0, ht2-ht1, ht3-ht2, b.tof-ht3, nsets, mt); }
        }
        });
        if b.allow_booth && std::env::var("FD_NODEFERASE").is_err() { b.deferred_erasure(501, predicate, vec![sc.bq]); }
        else { b.play(&predicate, false); }
    }
    stage!(); // 6
    // 8. un-P (Y in Q), from the last stored subset
    if let (true, Some((rrot, head, tail))) = (b.allow_booth && std::env::var("FD_NODEFERASE").is_err(), p_parts.as_ref()) {
        // bulengerk b6907bb1: un-P = rrot . (head . tail)^-1 . rrot^-1; the core's outputs (R, rho, q0, tq) are
        // computed from zero, so forward walks measure them and the mirrored inverse walk recomputes + Z-corrects
        b.play(rrot, false);
        let core_inverse = rec(b, |b| { b.play(tail, true); b.play(head, true); });
        let mut outs = ps.r.clone(); outs.extend(&ps.rho); outs.extend(&ps.q0); outs.push(sc.tq);
        outs.sort(); outs.dedup();
        b.deferred_erasure(502, core_inverse, outs);
        b.play(rrot, true);
    } else {
        b.play(&p_sets[nsets - 1], true);
    }
    stage!(); // 7
    // 9. X_new into Q (map layout); erase sz
    b.play(&wide_swap, false);
    if let Some(pl) = pl {
        super::payload::col_narrow_hr(b, fd, cp, sc, pl);
    }
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
    // 14. switching shots (after the map: bottom r_{j-1}, Q t_j, top r_j): ring reversal (bottom r_j, top r_{j-1}),
    // sy <- bl(top), bottom <-> Q: the switched layout (bottom t_j, Q = Y = r_j, ring top = X = r_{j-1} > 2^l0);
    // ph = 1; erase sw = ph & sy <= l0
    if cp.sw {
        for l in 0..n / 2 { b.cswap(sc.sw, ring[l], ring[n - 1 - l]); }
        let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
        let t = sc.u.clone();
        // switchers' bottom r_j < 2^l0: the reversed ring's first n - l0 lanes hold only gap and top
        let probe_t = rec(b, |b| probe_gated(b, &rev, 0, n - cp.l0, &t, &[(sc.sw, false)], &sc.opre, sc.tmp,
                                             &[sc.tmp2], &dirty));
        b.play(&probe_t, false);
        for i in 0..fd.sy.len() { b.cswap(sc.sw, fd.sy[i], t[i]); }
        for l in 0..cp.swl.1 { b.cswap(sc.sw, ring[l], q[l]); }
        let probe_q = rec(b, |b| probe_gated(b, &q, 0, cp.l0.min(nq), &t, &[(sc.sw, false)], &sc.opre, sc.tmp,
                                             &[sc.tmp2], &dirty));
        b.play(&probe_q, true);
        b.cx(sc.sw, ph);
        b.cx(ph, sc.sw);
        let mut chain = sc.pre.clone();
        chain.extend_from_slice(&sc.anc);
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
        mc_xor(b, &[(ph, false), (sc.cmpc, true)], sc.sw, &[], &dirty);
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
    }
    // 15. done shots: cnt += 1 (cnt in Q's top lanes, done derived); shots that just reached r = 1 (top = 1, ph = 1,
    // not done) get cnt = 1, the helper erased via done & cnt == 1 (older done shots are >= 2 after their increment)
    if cp.dn {
        let anc: Vec<QubitId> = sc.anc[..fd.cnt.len() - 1].to_vec();
        let d = sc.anc[fd.cnt.len() - 1];
        mc_xor_dn(b, &[], d, &[sc.tmp], &dirty, fd, cp.l0, true);
        super::arith::inc(b, d, &fd.cnt, &anc);
        mc_xor_dn(b, &[], d, &[sc.tmp], &dirty, fd, cp.l0, true);
    }
    if cp.fin {
        let mut sy1: Vec<(QubitId, bool)> = vec![(fd.sy[0], false)];
        sy1.extend(fd.sy[1..].iter().map(|&x| (x, true)));
        let mut l1 = vec![(ph, false)];
        l1.extend(sy1.iter().cloned());
        mc_xor_dn(b, &l1, sc.g, &[sc.tmp], &dirty, fd, cp.l0, false);
        b.cx(sc.g, fd.cnt[0]);
        let ctop = cp.nq - fd.cnt.len();
        let mut l2 = vec![(ph, false)];
        l2.extend(sy1.iter().cloned());
        l2.extend((cp.l0..ctop).map(|l| (q[l], true)));
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
        }
        let owed = extra - extension.len();
        assert!(ms.anc.len() >= owed);
        extension.extend(ms.anc.split_off(ms.anc.len() - owed));
        // done shots' counter sits in Q's top lanes: park it in clean tail lanes while the map reads Q, from
        // before the bl(X) probe (a probe bound m > nq - cnt would read the counter) until after the sy erase
        let nc = fd.cnt.len();
        // (the map frame also lends Q above its operand bound as clean carries)
        let park: Vec<QubitId> = if cp.dn { ms.anc.split_off(ms.anc.len() - nc) } else { vec![] };
        let pd = if cp.dn { ms.anc.pop() } else { None };
        if let Some(d) = pd { mc_xor_dn(b, &[], d, &[], &dirty, fd, cp.l0, true); }
        for (i, &x) in park.iter().enumerate() { b.cswap(pd.unwrap(), fd.cnt[i], x); }
        // bulengerk c4f95ef6: priority probes on the map's globally zero roles (after the extension, parked
        // counter and done flag are split off)
        let probe_bank=super::priority_probe::map_bank(&ms);
        assert!(!probe_bank.iter().any(|w|ring.contains(w)||q.contains(w)||fd.sy.contains(w)||fd.sx.contains(w)||dirty.contains(w)
            ||[sc.sw,sc.bq,sc.cmpc].contains(w)||extension.contains(w)||park.contains(w)||pd==Some(*w)));
        let oldp=std::env::var("FD_OLDPROBE").is_ok();
        let pok=|n:usize| n==0 || super::priority_probe::choose(n, probe_bank.len()).is_some();
        if oldp || !pok(cp.m) { msb_probe_range(b, q, 0, cp.m, &fd.sx, &sc.opre, sc.tmp, &dirty); }
        else { super::priority_probe::emit(b,q,0,cp.m,&fd.sx,&probe_bank); }
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
        // bulengerk bf1897f0: bq (when not lent to the extension) and sw (non-switch columns) are zero across the map;
        // not under the end's controlled replay (allow_booth=false), where sw is the control
        if b.allow_booth && std::env::var("FD_NOMAPANDC").is_err() {
            if extra==0 {ms.andc.push(sc.bq);}
            if !cp.sw {ms.andc.push(sc.sw);}
            assert_eq!(ms.andc.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),ms.andc.len());
            assert!(!ms.andc.iter().any(|w|extended.contains(w)||park.contains(w)||pd==Some(*w)));
        }
        mapf(b, &extended, q, &extcut, &extpar, &ms);
        b.play(&embed, true);
        b.play(&order, true);
        let ylim=if cp.sy.1==0 {cp.m}else{cp.m.min(cp.sy.1)};
        let probe_y = if oldp || !pok(ylim - cp.sy.0.saturating_sub(1)) { rec(b, |b| msb_probe_range(b, q, cp.sy.0.saturating_sub(1), ylim, &fd.sy, &sc.opre, sc.tmp, &dirty)) }
                      else { rec(b, |b| super::priority_probe::emit(b, q, cp.sy.0.saturating_sub(1), ylim, &fd.sy, &probe_bank)) };
        b.play(&probe_y, true);
        for (i, &x) in park.iter().enumerate() { b.cswap(pd.unwrap(), fd.cnt[i], x); }
        if let Some(d) = pd { mc_xor_dn(b, &[], d, &[], &dirty, fd, cp.l0, true); }
    })
}

/// End of the traversal (every shot done): B0 shots (odd idle count, cnt[0] = 0) take one more q = 0 map ->
/// A0 = (t_{N-1}, R, 1) for all; then the last HT middle (Y = 1, q = R) clears R (Q = 0). `cp` = envelope of the
/// B0 shots for the map, `cpl` = the last-middle column (all shots A0, nomap).
pub fn traversal_end(b: &mut B, fd: &mut Fd, cp: Option<&ColPar>, cpl: &ColPar,
                     carve: &dyn Fn(&[QubitId]) -> ColScr) {
    traversal_end_pl(b, fd, cp, cpl, carve, None)
}

pub fn traversal_end_pl(b: &mut B, fd: &mut Fd, cp: Option<&ColPar>, cpl: &ColPar,
                        carve: &dyn Fn(&[QubitId]) -> ColScr, pl: Option<&super::payload::PlCol>) {
    if let Some(cp) = cp {
        // B0 <=> odd idle count <=> cnt (= 1 + idle) even
        let sc = carve(&fd.sx);
        let old_booth=b.allow_booth;b.allow_booth=false;
        let ms_rec = map_stage(b, fd, cp, &sc);
        b.allow_booth=old_booth;
        // the map parks the counter (cnt[0] too): control on a copy of [cnt even] in the free sw lane
        b.cx(fd.cnt[0], sc.sw);
        b.x(sc.sw);
        b.play_ctrl(&ms_rec, sc.sw, sc.bq);
        b.x(sc.sw);
        b.cx(fd.cnt[0], sc.sw);
        std::mem::swap(&mut fd.sy, &mut fd.sx);
        // shots that skipped the map (cnt odd) keep their size in the (renamed) sx register: swap back
        for i in 0..fd.sy.len() {
            b.cswap(fd.cnt[0], fd.sy[i], fd.sx[i]);
        }
    }
    // every shot is A0 = (t_{N-1}, R, 1); R stays in Q (no last middle): the payload's last level uses q = R directly
    if let Some(pl) = pl {
        let sc = carve(&fd.sx);
        super::payload::pl_end(b, fd, cpl, &sc, pl);
    }
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

/// msb probe of v[lo..lim) into out (|0>) on shots where AND(extra) holds (others: out stays 0). Exact inverse by
/// playing it inverted.
pub(crate) fn probe_gated(b: &mut B, v: &[QubitId], lo: usize, lim: usize, out: &[QubitId], extra: &[(QubitId, bool)],
                          pre: &[QubitId], tmp: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    use super::mask::{mc_xor, Dec};
    assert!(lo <= lim && lim <= v.len());
    for l in (lo..lim).rev() {
        let val = l + 1;
        for pass in 0..2 {
            let mut dec = Dec::new(out, pre);
            let mut c = dec.ctrls(b, if pass == 0 { 0 } else { val });
            c.push((v[l], false));
            c.extend_from_slice(extra);
            mc_xor(b, &c, tmp, temps, dirty);
            dec.clear(b);
            if pass == 0 {
                for (i, &o) in out.iter().enumerate() {
                    if (val >> i) & 1 == 1 {
                        b.cx(tmp, o);
                    }
                }
            }
        }
    }
}

/// Exact controlled add/sub of Q * 2^k into the ring-top ladder like `ring_cadd`, for spans longer than Q plus the
/// zero lanes: the carry out of the sourced part is added into the remaining ladder lanes by a controlled increment
/// on borrowed lanes (`h` clean).
/// ring_cadd2 with bulengerk's loan-bank chunked row add (frogdrop::ring_cadd_loan): the source is Q[..sbound]
/// (Q[sbound..loan_end) is |0> on every shot and serves as the clean carry bank with `mz`). Falls back to ring_cadd2.
pub(crate) fn ring_cadd2_loan(b: &mut B, ring: &[QubitId], q: &[QubitId], k: usize, span: usize, g: QubitId, sub: bool,
                              zeros: &[QubitId], c0: QubitId, h: QubitId, dirty: &[QubitId], sbound: usize,
                              loan_end: usize, mz: QubitId) {
    // frogdrop::ring_cadd_loan, extended to spans beyond Q (the old path there is ring_cadd2's dirty tail)
    let sbound = sbound.min(q.len());
    let nm = span.min(sbound);
    if nm == 0 || sbound > loan_end {
        if std::env::var("FROGDROP_LOANDBG").is_ok() { eprintln!("loan skip span {span} sbound {sbound} loan_end {loan_end}"); }
        ring_cadd2(b, ring, q, k, span, g, sub, zeros, c0, h, dirty);
        return;
    }
    let n = ring.len();
    let t: Vec<QubitId> = (k..k + span).map(|i| ring[n - 1 - i]).collect();
    let hh = zeros[0];
    let mut bank = q[sbound..loan_end].to_vec();
    bank.push(mz);
    if nm == span { bank.push(hh); }
    let nt = span - nm;
    let total_bank = bank.len() + usize::from(nt > 0);
    let mut best: Option<(usize, usize)> = None;
    for chunk in 1..=nm {
        let blocks = nm.div_ceil(chunk);
        let flags = blocks - 1 + usize::from(nt > 0);
        if flags + chunk.saturating_sub(1) > total_bank { continue; }
        let (u, c, _) = super::row_add::model(nm, nt, total_bank, chunk);
        let cost2 = 2 * u + c;
        if cost2 < 6 * span && best.is_none_or(|(old, _)| cost2 < old) { best = Some((cost2, chunk)); }
    }
    if std::env::var("FROGDROP_LOANDBG").is_ok() { eprintln!("loan span {span} sbound {sbound} loan_end {loan_end} nm {nm} nt {nt} bank {total_bank} best {:?}", best); }
    let Some((_, chunk)) = best else {
        ring_cadd2(b, ring, q, k, span, g, sub, zeros, c0, h, dirty);
        return;
    };
    if nt > 0 { bank.push(hh); }
    assert_eq!(bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), bank.len());
    assert!(!bank.contains(&g) && !bank.contains(&c0));
    assert!(!t.iter().any(|x| bank.contains(x)) && !q[..nm].iter().any(|x| bank.contains(x)));
    if sub { for &x in &t { b.x(x); } }
    b.row_add(super::row_add::Row { signed_binary: false, mux: None, g, t: t[..nm].to_vec(), s: q[..nm].to_vec(),
                                    tail: t[nm..].to_vec(), c0, h: hh, bank, dirty: dirty.to_vec(), chunk });
    if sub { for &x in &t { b.x(x); } }
}

pub(crate) fn ring_cadd2(b: &mut B, ring: &[QubitId], q: &[QubitId], k: usize, span: usize, g: QubitId, sub: bool,
                         zeros: &[QubitId], c0: QubitId, h: QubitId, dirty: &[QubitId]) {
    let ls = q.len() + zeros.len();
    if span <= ls {
        ring_cadd(b, ring, q, k, span, g, sub, zeros, c0);
        return;
    }
    let n = ring.len();
    let t: Vec<QubitId> = (k..k + ls).map(|m| ring[n - 1 - m]).collect();
    let tl: Vec<QubitId> = (k + ls..k + span).map(|m| ring[n - 1 - m]).collect();
    let mut s: Vec<QubitId> = q.to_vec();
    s.extend_from_slice(zeros);
    if sub {
        for &x in t.iter().chain(tl.iter()) { b.x(x); }
    }
    super::frogdrop::cadd_tail_and_mixed(b, g, &t, &s, &tl, c0, h, &[], dirty, &[]);
    if sub {
        for &x in t.iter().chain(tl.iter()) { b.x(x); }
    }
}
