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
    /// ring headroom n - 257: >= K+2 for separate R/sign owners; K+1 requires the explicit zero alignment and donor.
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
    /// done shots' idle-counter bits that can be nonzero at the column start (cnt <= columns since the first
    /// column that may finish): the parkings move only these, the higher counter lanes are zero
    pub cntw: usize,
    /// agent_lowq_quot: the done counter's bound at this column's map (cnt <= cntmax; cntw = bl(cntmax))
    pub cntmax: usize,
    /// agent_lowq_quot: the traversal column (usize::MAX off the traversal)
    pub col: usize,
    /// the crossing form choice: some shot takes the delayed switch here (bl(r_j) >= dlr), some shot is in its
    /// no-step column after one (Q = r_j, top = r_{j+1}, bottom t_j: sz <= 127, sy <= l0, ph)
    pub dl: bool,
    pub dq: bool,
    pub dlr: usize,
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
    /// first-HT handling: the stage-14 size temp (sz lanes, clean after stage 9), the stage-2 top size (sx) and
    /// the switched-layout flag (clean outside P)
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
    /// rho's lanes that are clean outside the P frame (ps.rho may end in sz's top lanes, free only in the frame)
    pub rho_clean: Vec<QubitId>,
    /// SLIM: the four lanes (bq, cmpc, f, g; besides sz, sw and the idle size registers) that stages 1, 2's swaps,
    /// 9 and 14-15 draw their helpers from
    pub slim: Vec<QubitId>,
    /// Scheme G: the pool lanes past the 13-lane layout (sz, sw, bq, cmpc, f, g): the middle's crossing reserve only
    pub gx: Vec<QubitId>,
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

/// Lean map stage (see ColScr::carve_col): its pool lanes are four flags, the v2 register, the order bit (cmpc),
/// the switch-map extension (bq + 2) and the done counter's parking (cntw lanes, the first in the sw lane in a
/// switch column); LEAN_MAP_PARK lanes fund the extension and the parking.
pub const MAP_LEAN: bool = true;
/// Stages 1 (probes, HT narrowing, sw), 2 (the middle swap's and first-HT paths), 9 (swap, HR narrowing, sz erase) and
/// 14-15 (the switch tail) hold only sz, sw and ColScr::slim of the pool (plus sx where it is clean); short decoder
/// banks and comparator chains fall back to exact dirty-lane forms.
pub const SLIM: bool = true;
pub const LEAN_MAP_PARK: usize = 1;

/// Lanes of the sz register: bl(Z) <= 255 in every column but the first (r_2 < p / 2 and |t_j| <= p / 2); a column
/// whose envelope reaches 256 (column 0, which never switches) borrows the sw lane as its ninth bit.
pub const SZB: usize = 8;

/// Size of the shared column scratch pool (plus the spare size register sx, which joins rho during P).
/// Column pool size for size registers of `sw` bits (the spare one is the first `sw` lanes of rho/q0).
/// Column pool of the new middle (0: the full pool below); FD_POOL overrides it for experiments. The new middle
/// runs down to 27 lanes (rho tops up with sz's top lanes, the t2, sw and zero lanes inside the P frame).
pub const MID2_POOL: usize = 13;

pub fn pool_size(kp: usize, qb: usize, sw: usize) -> usize {
    if super::mid2::enabled() {
        if let Some(v) = std::env::var("FD_POOL").ok().and_then(|v| v.parse::<usize>().ok()) { return v; }
        if MID2_POOL > 0 { return MID2_POOL; }
    }
    if qsub() > 0 {
        // rho and the stored subset beyond the two overflow lanes
        return SZB + 8 + (kp + 1 + qsub().max(2) - 2 - sw);
    }
    SZB + 8 + (kp + 1 + qb - sw)
}

impl ColScr {
    /// carve_col for a column whose sz fits SZB lanes
    pub fn carve(pool: &[QubitId], sx: &[QubitId], dirty: &[QubitId], kp: usize, qb: usize, tail: usize) -> ColScr {
        ColScr::carve_col(pool, sx, dirty, kp, qb, tail, false)
    }

    /// Carve the column scratch out of `pool` (all |0>) and the current spare size register `sx` (|0> outside the
    /// map stage). Roles overlap only where their live stages are disjoint (o = SZB):
    /// pool[0..o] sz, o sw, o+1 bq, o+2 cmpc/P zero, o+3..o+6 P f/g/c0,
    /// o+6..o+8 two persistent quotient overflow bits, o+8.. base rho/q0 (with sx).
    /// `wide`: sz takes the sw lane as its ninth bit (a column without switching shots).
    /// Virtual odd subtraction removes physical one; P holds no decoder prefix.
    /// PScr.tmp aliases cmpc/PScr.zero: decoder toggles complete before any compare starts.
    /// ColScr.tmp borrows rho only outside P lifetime; middle bcmp uses clean PScr.f.
    /// The four-prefix middle swap includes the exact zero top rho bit and uses dirty five-control toggles.
    /// Walk/probe transients reuse PScr misc (middle-safe) or the rho region (stages 1, 8, 9); MapScr reuses
    /// everything except sw, bq, cmpc and sx.
    pub fn carve_col(pool: &[QubitId], sx: &[QubitId], dirty: &[QubitId], kp: usize, qb: usize, tail: usize,
                     wide: bool) -> ColScr {
        assert_eq!(pool.len(), pool_size(kp, qb, sx.len()));
        let o = SZB;
        // Scheme G + SLIM runs on pool[0..o + 5] (sz, sw, bq, cmpc, f, g); the P-only roles past it (P c0 / one, the
        // old stored-quotient pair, pre) alias sx: no stage of that build reads them
        let short = pool.len() < o + 8;
        assert!(!short || (super::midg::enabled() && SLIM && pool.len() >= o + 5), "pool too short: {}", pool.len());
        let p = |i: usize| if o - 9 + i < pool.len() { pool[o - 9 + i] } else { sx[o - 9 + i - pool.len()] };
        let mut rq: Vec<QubitId> = sx.to_vec();
        rq.extend(pool.get(o + 8..).unwrap_or(&[]));
        let rho_clean: Vec<QubitId> = rq[..rq.len().min(kp + 1)].to_vec();
        // the new middle tops rho up with sz's top lanes (zero in its P frame, where sz holds s - SMIN on its
        // low lanes) and the second overflow lane
        let mut rho = rho_clean.clone();
        // (Scheme G keeps no rho: the column's rho is just its clean lanes)
        if rho.len() < kp + 1 && !super::midg::enabled() {
            assert!(super::mid2::enabled(), "a short pool needs the new middle");
            let mut ext: Vec<QubitId> = pool[super::mid2::SBITS..o].to_vec();
            ext.push(p(16));
            // the sw lane: erased in the P frame (sw = !ph & [sz <= l0] = !ph & [sy >= s' + SMIN - l0])
            ext.push(p(9));
            // the P zero lane: the pipeline's compares then use a virtual zero top
            ext.push(p(11));
            for x in ext { if rho.len() < kp + 1 { rho.push(x); } }
        }
        assert!(rho.len() == kp + 1 || super::midg::enabled());
        let mut q0 = if qsub() > 0 { vec![p(15); qb] } else { rq[kp + 1..kp + 1 + qb].to_vec() };
        // No overflow bits: a model-clean shot has q0 < 2^QB at every level (predict's q0 cap; the 24-lane payload
        // digit relies on the same bound), so P computes QB quotient bits
        let qsets = qsubsets(q0.len());
        let mut tq = p(16);
        if qsub() > 0 {
            let qs = qsub().max(2);
            // stored lanes: the bank above rho, then the two overflow lanes (each subset's top bits; q0[0..2] stay
            // off the probe prefixes)
            let mut st = rq[(kp + 1).min(rq.len())..(kp + 1 + qs - 2).min(rq.len())].to_vec();
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
        // MapScr: pool[0..o] + pool[o+3..] (not sw/bq/cmpc, not sx)
        let mut mp: Vec<QubitId> = pool[0..o].to_vec();
        mp.extend(&pool[o + 3..]);
        MAPEXTRA.with(|m| mp.extend(m.borrow().iter()));
        // Every column map uses the sx size register as its affine cut. Dec
        // holds at most sx.len()-1 prefixes and ge_const uses at most that many
        // carries. The formerly reserved eighth prefix was never accessed.
        let pre_end = 7 + sx.len().saturating_sub(1);
        let ez_end = pre_end + 5;
        // The tz-probe decoder and cut decoder have disjoint lifetimes. Share
        // one prefix; frame_carries explicitly excludes every cut-prefix alias.
        assert!(pre_end > 7);
        let fixed = ez_end + 3;
        let mut epre = vec![];
        if !MAP_LEAN {
            epre.push(mp[pre_end - 1]);
            epre.extend_from_slice(&mp[ez_end..fixed]);
            assert!(mp.len() >= fixed);
        }
        // Exact dirty tail fallback supports every tail with fewer clean prefixes.
        let clean_tail = (tail - 1).min(mp.len().saturating_sub(fixed));
        let need = fixed + clean_tail;
        let ms = if MAP_LEAN {
            // Lean map: only the flags c0, e, g, f and the v2 register stay clean. h shares f (the frame multiply,
            // h's only user, leaves f idle) and tmp / one share e (clean wherever tmp / one are used); every
            // decoder, comparator chain and carry tail borrows the payload lanes dirty. anc holds only the extension
            // / counter-parking lanes (map_stage drops the rest).
            assert!(mp.len() >= 9 + LEAN_MAP_PARK);
            MapScr { c0: mp[0], h: mp[3], e: mp[1], g: mp[2], f: mp[3], tmp: mp[1], one: mp[1], pre: vec![],
                     ez: mp[4..9].to_vec(), epre: vec![], anc: mp[9..9 + LEAN_MAP_PARK].to_vec(),
                     dirty: dirty.to_vec(), andc: vec![] }
        } else {
            MapScr { c0: mp[0], h: mp[1], e: mp[2], g: mp[3], f: mp[4], tmp: mp[5], one: mp[6],
                     pre: mp[7..pre_end].to_vec(), ez: mp[pre_end..ez_end].to_vec(), epre,
                     anc: mp[fixed..fixed + clean_tail].to_vec(), dirty: dirty.to_vec(),
                     // Beyond the complete map layout: unused and clean for the map.
                     andc: mp[need..].to_vec() }
        };
        // Probe/compare helpers outside P live in the rho lanes above sx (pool[o+8..]): tmp h[3], tmp2 h[6], opre
        // h[7..15]; js is h[0] (never the middle-zero rho lane for KP 23..30); the other lanes extend the
        // compare / cut-decoder chains (`anc`). Stage 2 needs no size temp (bl(Q) is probed into the cleared sy);
        // the stage-14 probe temp and the stage-15 counter carries use sz, which is clean after stage 9.
        let h0: &[QubitId] = pool.get(o + 8..).unwrap_or(&[]);
        // short pools (Scheme G): the probe helpers past the pool alias sx (unused under SLIM where they collide)
        let hv: Vec<QubitId> = if h0.len() >= 9 { h0.to_vec() } else {
            assert!(super::midg::enabled() && SLIM, "pool too small for the probe helpers");
            h0.iter().copied().chain(sx.iter().copied()).collect()
        };
        let h = &hv[..];
        let js = h[0];
        let hi = h.len().min(15);
        let anc: Vec<QubitId> = if h0.len() >= 9 { h[1..3].iter().chain(&h[4..6]).chain(&h[hi..]).copied().collect() }
                                else { h0.iter().skip(1).copied().collect() };
        let mut sz = pool[0..o].to_vec();
        if wide { sz.push(p(9)); }
        ColScr { sz, sw: p(9), bq: p(10), cmpc: p(11), act: p(12), g: p(13), c0: p(14),
                 tmp: h[3], tmp2: h[6], f: p(12), one: p(15), pre, opre: h[7..hi].to_vec(),
                 anc, zeros: vec![p(11)], u: pool[0..sx.len()].to_vec(), u2: sx.to_vec(), js, qsets, tq, ps, ms,
                 dirty: dirty.to_vec(), rho_clean,
                 slim: vec![p(10), p(11), p(12), p(13)], gx: pool.get(o + 5..).unwrap_or(&[]).to_vec() }
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

pub(crate) fn rec<F: FnOnce(&mut B)>(b: &mut B, f: F) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}

/// Share the done predicate across all counter parking swaps. `flag` is a
/// clean map helper outside the parked counter, Q predicate, and park lanes;
/// the predicate's Q prefix is untouched during each call.
pub(crate) fn f1_lean_counter_swaps(b: &mut B, predicate: &[(QubitId, bool)], counter: &[QubitId],
                                    park: &[QubitId], flag: QubitId, dirty: &[QubitId], inverse: bool) {
    assert_eq!(counter.len(), park.len());
    assert!(!predicate.iter().any(|(q, _)| *q == flag));
    assert!(!counter.contains(&flag) && !park.contains(&flag) && !dirty.contains(&flag));
    if park.is_empty() { return; }
    super::mask::mc_xor(b, predicate, flag, &[], dirty);
    if inverse {
        for (i, &x) in park.iter().enumerate().rev() {
            b.ccx(flag, x, counter[i]);
            b.ccx(flag, counter[i], x);
        }
    } else {
        for (i, &x) in park.iter().enumerate() {
            b.ccx(flag, counter[i], x);
            b.ccx(flag, x, counter[i]);
        }
    }
    super::mask::mc_xor(b, predicate, flag, &[], dirty);
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
pub(crate) fn ge_const_compact(b: &mut B, v: &[QubitId], k: isize, target: QubitId,
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

/// t ^= [v >= k]: the carry-chain comparator when `chain` holds its carries, else the exact compact one (dirty)
pub(crate) fn ge_cd(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId], dirty: &[QubitId]) {
    if super::mask::ge_const_need(v.len(), k) <= chain.len() { super::mask::ge_const(b, v, k, t, chain); }
    else { ge_const_compact(b, v, k, t, chain, dirty); }
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
                assert!(controls.len() <= 5 || env_k("FD_LEAN_SX").is_some());
                mc_xor(b, &controls, f, &[], dirty);
            }
        }
        b.x(f); b.cswap(f, ring[l], q[n-1-l]); b.x(f);
    }
    if let Some(v) = at(chi) {
        let controls = dec.ctrls(b, v);
        assert!(controls.len() <= 5 || env_k("FD_LEAN_SX").is_some());
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

/// The in-place compare [sz > sy] (recorded and played; its inverse play restores both registers): ~sy + sz on bq's
/// carry, sz's top lane then holds the carry out.
fn sz_gt_sy(b: &mut B, fd: &Fd, sc: &ColScr) -> Vec<G> {
    assert!(SLIM && sc.sz.len() == fd.sy.len());
    let gt = super::arith::up_m(b, &fd.sy, &sc.sz, sc.bq, true);
    b.play(&gt, false);
    gt
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

thread_local! {
    /// FD_MARK census markers: (op index, stage) per column stage; the spare size register at each column start
    pub static MARKS: std::cell::RefCell<Vec<(usize, usize)>> = const { std::cell::RefCell::new(vec![]) };
    pub static COLSX: std::cell::RefCell<Vec<Vec<QubitId>>> = const { std::cell::RefCell::new(vec![]) };
    pub static COLINFO: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(vec![]) };
    /// test only (FD_MAPEXTRA): extra clean lanes appended to the map scratch, to test the other stages at short pools
    pub static MAPEXTRA: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(vec![]) };
    pub static D3_MAP_SEGMENTS: std::cell::RefCell<Vec<(usize, usize)>> = const { std::cell::RefCell::new(vec![]) };
    /// agent_lowq_quot: the controlled-map columns S and the column count (set by col_pars)
    pub static MAP_CTRL_S: std::cell::RefCell<(Vec<usize>, usize)> = const { std::cell::RefCell::new((vec![], 0)) };
    /// the last map_stage_ex left its ph-free flip to the caller
    pub static MAP_PH_OUT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// the last map_stage_ex is replayed under !(ph & sw') (QUOT_MAP_CTRL_SWPH): no done-flag lane
    pub static MAP_SWPH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// agent_lowq_quot QUOT_MAP_CTRL=lo-hi: in those map columns with done shots, done shots skip the map stage (it is
/// replayed controlled on !done) and keep their counter in Q's top lanes (no parking: the nc park lanes go to the
/// extension; the done flag and the control helper take two). A done shot then holds its form (A0 / B0) through
/// S: the end's B0 test counts only the maps it ran.
pub fn map_ctrl_range() -> Option<(usize, usize)> {
    let v = std::env::var("QUOT_MAP_CTRL").ok()?;
    let (a, b) = v.split_once('-')?;
    Some((a.parse().ok()?, b.parse().ok()?))
}
pub fn is_map_ctrl(cp: &ColPar) -> bool {
    map_ctrl_range().is_some_and(|(lo, hi)| cp.col >= lo && cp.col <= hi) && cp.dn && !cp.nomap && cp.sz != (0, 0)
}
/// skipped maps of a done shot with end counter v (it finished in column C - v): |S & [C - v + 1, C)|
pub fn map_ctrl_skipped(v: usize) -> usize {
    MAP_CTRL_S.with(|m| { let m = m.borrow(); m.0.iter().filter(|&&c| c + v >= m.1 + 1).count() })
}
/// skipped maps of a done shot whose last step column is f, by the end of column c: |S & (f, c]|
pub fn map_ctrl_skipped_by(f: usize, c: usize) -> usize {
    MAP_CTRL_S.with(|m| m.borrow().0.iter().filter(|&&x| x > f && x <= c).count())
}
pub(crate) fn d3_map_segment(b: &B, stage: usize) {
    if std::env::var_os("D3_TRACE_PHASE").is_some() {
        D3_MAP_SEGMENTS.with(|m| m.borrow_mut().push((b.recording_len(), stage)));
    }
}
pub fn mark(b: &B, st: usize) {
    if std::env::var("FD_MARK").is_ok() { MARKS.with(|m| m.borrow_mut().push((b.ops.len(), st))); }
}

/// FD_PSW_DELTA: the stage-2 first-HT path without the 8-lane top-size register u2. On a ph shot at a psw column
/// js (skip the first swap: a first-HT shot, top X = r_{j-1} with bl(X) > l0, or a delayed shot's no-step column,
/// sz <= 127) equals [sz <= 127] | [sz = 128] & X's bit l0 (bl(r_{j-1}) + bl(t_j) in {256, 257}: a first-HT shot
/// has sz <= 128, bl(X) = 129 at sz = 128; a regular HT shot has sz >= 128 and its ring top below 2^l0 both before
/// and after the swap; MEASURED 0 / 1.49M HT records). The top size is never held: sy (= bl(top) on js shots) is
/// erased by the inverse of a js-gated probe of the ring top, then refilled with bl(Q) as before. Lanes: sz, js
/// (s[3]), the swap's f (s[2]) and gate temp (s[0]), the probes' tmp / tmp2 (s[0], s[1]) and FD_S2_PRE prefixes
/// from sx (cut and out decoders share them in turn).
/// FD_LEAN_SX: how many sx lanes the stage-1 / 2 / 9 / 14 compare chains and decoder banks take (default: all
/// they took before); short chains fall back to the exact compact comparator, short banks to dirty toggles.
pub(crate) fn lean_sx(fd: &Fd, n: usize) -> Vec<QubitId> {
    let k = std::env::var("FD_LEAN_SX").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(n).min(n);
    fd.sx[..k].to_vec()
}
fn env_k(name: &str) -> Option<usize> { std::env::var(name).ok().and_then(|v| v.parse::<usize>().ok()) }
pub const PSW_DELTA: bool = false;
pub fn psw_delta() -> bool {
    std::env::var("FD_PSW_DELTA").map(|v| v == "1").unwrap_or(PSW_DELTA)
}
fn s2_pre() -> usize {
    std::env::var("FD_S2_PRE").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(7)
}
#[allow(clippy::too_many_arguments)]
fn psw_first_delta(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, ring: &[QubitId], q: &[QubitId], pclo: usize,
                   pchi: usize, dirty: &[QubitId]) {
    use super::mask::mc_xor;
    let s = &sc.slim;
    let n = cp.n;
    let ph = fd.ph;
    let js = s[3];
    assert!(SLIM && sc.f == s[2] && sc.bq == s[0]);
    let np = s2_pre().min(fd.sx.len()).min(sc.sz.len() - 1);
    let pre: Vec<QubitId> = fd.sx[..np].to_vec();
    let sz = &sc.sz;
    assert_eq!(sz.len(), SZB);
    let x_l0 = ring[n - 1 - cp.l0];
    // js ^= ph & ([sz <= 127] | [sz == 128] & X[l0])
    let js_toggle = |b: &mut B| {
        mc_xor(b, &[(ph, false), (sz[SZB - 1], true)], js, &[], dirty);
        let mut l: Vec<(QubitId, bool)> = vec![(ph, false), (sz[SZB - 1], false)];
        l.extend(sz[..SZB - 1].iter().map(|&x| (x, true)));
        l.push((x_l0, false));
        mc_xor(b, &l, js, &[], dirty);
    };
    js_toggle(b);
    let first = rec(b, |b| masked_swap_gated(b, ring, q, sz, cp.h, pclo, pchi, sc.f, &pre, dirty, js, sc.bq));
    b.play(&first, false);
    mark(b, 2013);
    // sy (= bl(top) on js shots) -> 0: the inverse of the js-gated top probe
    let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
    let cutr = Cut { v: sz.clone(), a: (n - cp.h) as isize, neg: true };
    let (k1, k2) = (np.div_ceil(2), np / 2);
    let (cpre, opre) = (pre[..k1].to_vec(), pre[k1..k1 + k2].to_vec());
    let pt = rec(b, |b| super::frogdrop::msb_probe_cut_range_x(b, &rev, &cutr, n - cp.h - cp.sz.1, n - cp.h - cp.sz.0, 0,
                                                               (cp.xw + 1).min(n), &fd.sy, sc.f, &cpre, &opre, s[0], s[1],
                                                               &[(js, false)], dirty));
    b.play(&pt, true);
    mark(b, 2014);
    // sy = bl(Q) on js shots
    let mut popre = vec![s[2]];
    popre.extend(&pre);
    let pu = rec(b, |b| probe_gated(b, q, 0, cp.l0.min(q.len()), &fd.sy, &[(js, false)], &popre, s[0], &[s[1]],
                                    dirty));
    b.play(&pu, false);
    mark(b, 2015);
    js_toggle(b);
    mark(b, 2016);
}

pub fn column_upto(b: &mut B, fd: &mut Fd, cp: &ColPar, sc: &ColScr, upto: usize,
                   pl: Option<&super::payload::PlCol>) {
    use super::mask::{mc_xor, Dec};
    if std::env::var("FD_MARK").is_ok() {
        COLSX.with(|m| m.borrow_mut().push(fd.sx.clone()));
        COLINFO.with(|m| m.borrow_mut().push(format!("{{\"sz\":[{},{}],\"sy\":[{},{}],\"hr\":{},\"ht\":{},\"sw\":{},\"dn\":{},\"xw\":{},\"m\":{}}}",
            cp.sz.0, cp.sz.1, cp.sy.0, cp.sy.1, cp.hr, cp.ht, cp.sw, cp.dn, cp.xw, cp.m)));
    }
    mark(b, 0);
    let prof = std::env::var("FROGDROP_PROF").is_ok();
    let mut stn = 0usize;
    const F1_MIDG_STAGES: [&str; 10] = ["column.probe_switch", "column.swap_digit", "column.midg_hr_search", "column.midg_hr_correction", "column.midg_ht_division", "column.midg_ht_correction", "column.midg_finish", "column.swap_unprobe", "column.map", "column.switch_done"];
    const F1_OLD_STAGES: [&str; 10] = ["column.probe_switch", "column.swap_digit", "column.P", "column.HR_correction", "column.q0_adds", "column.HT_correction", "column.unP", "column.swap_unprobe", "column.map", "column.switch_done"];
    let f1_stages = if super::mid2::enabled() { &F1_MIDG_STAGES } else { &F1_OLD_STAGES };
    let mut f1_last = b.tof;
    let mut last = if std::env::var("FROGDROP_PROF_OPS").is_ok() { b.ops.len() as u64 } else { b.tof };
    let mut prof_v: Vec<(usize, u64)> = vec![];
    macro_rules! stage { () => {
        stn += 1;
        mark(b, stn);
        super::f1_profile(f1_stages[stn - 1], f1_last, b.tof);
        f1_last = b.tof;
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
    // CONJECTURE pending independent native/whole replay. The compressed
    // layout lends R's known-zero logical top to the middle sign, and reserves
    // pool14 solely while a P tail switch needs the canonical R representation.
    assert!(cp.h >= k + 1);
    let reuse_r_zero = cp.h == k + 1;
    assert!(!reuse_r_zero || qsub() > 0, "Rzero/sign reuse requires subset-P c0 reservation");
    let dirty = sc.dirty.clone();
    let cut_y = Cut { v: fd.sy.clone(), a: n as isize, neg: true };
    let (pclo, pchi) = (cp.sz.0 + cp.h, cp.sz.1 + cp.h);
    // 1. sz = bl(Z) (probe below Y's MSB lane per shot)
    // SLIM: the bank is the slim lanes plus sx (clean at stage 1 and at the stage-9 erase); the fallback probe keeps
    // its cut-decoder prefixes in sx and its flag, temps and out-decoder prefixes in slim and sx (no other carve role
    // is read, so the slim stages run on pools that hold only sz, sw and the slim lanes)
    let mut qz: Vec<QubitId> = vec![];
    let (z_bank, probe_pre) = if SLIM {
        (sc.slim.iter().chain(&fd.sx).copied().collect::<Vec<QubitId>>(), fd.sx[..3].to_vec())
    } else {
        let mut probe_pre = sc.pre.clone();
        probe_pre.push(sc.bq); // bq is clean before P and after un-P
        // two distinct quotient lanes (zero before P and after un-P; subsets share lanes)
        for &x in &sc.ps.q0 { if !qz.contains(&x) && !probe_pre.contains(&x) { qz.push(x); } }
        // (few stored lanes: rho is zero here too; skip the probe's own helpers)
        for &x in &sc.rho_clean {
            if !qz.contains(&x) && !probe_pre.contains(&x) && !sc.opre.contains(&x) && x != sc.tmp && x != sc.tmp2 {
                qz.push(x);
            }
        }
        probe_pre.extend_from_slice(&qz[..2]);
        // bulengerk c4f95ef6: masked priority probe on lanes that are zero before P and after un-P
        let mut z_bank=sc.rho_clean.clone();z_bank.extend(&sc.ps.q0);z_bank.extend([sc.bq,sc.cmpc,sc.act,sc.g,sc.c0]);z_bank.extend(&fd.sx);
        z_bank.sort();z_bank.dedup();
        z_bank.retain(|w|!sc.sz.contains(w)&&*w!=sc.sw&&!ring.contains(w)&&!q.contains(w)&&!fd.sy.contains(w)&&!dirty.contains(w));
        // (small pools, e.g. 732: the old probe where the clean bank has no block layout)
        (z_bank, probe_pre)
    };
    let s = &sc.slim;
    let (pz_f, pz_tmp, pz_tmp2, pz_opre): (QubitId, QubitId, QubitId, Vec<QubitId>) =
        if SLIM { (s[2], s[0], s[1], vec![s[3]]) }
        else { (sc.f, sc.tmp, sc.tmp2, sc.opre.clone()) };
    let z_bank: Vec<QubitId> = match env_k("FD_ZBANK") { Some(k) => z_bank[..k.min(z_bank.len())].to_vec(), None => z_bank };
    let zn = cp.sz.1 - cp.sz.0.saturating_sub(1);
    let masked_ok = super::masked_priority_probe::feasible(zn, cut_y.v.len(), z_bank.len());
    let probe_z = if std::env::var("FD_OLDPROBE").is_ok() || !masked_ok { rec(b, |b| {
        msb_probe_cut_range(b, &ring, &cut_y, n - cp.sy.1, n - cp.sy.0, cp.sz.0.saturating_sub(1), cp.sz.1,
                            &sc.sz, pz_f, &probe_pre, &pz_opre, pz_tmp, pz_tmp2, &dirty)
    }) } else { rec(b, |b| {
        super::masked_priority_probe::emit(b,&ring,&cut_y,n-cp.sy.1,n-cp.sy.0,cp.sz.0.saturating_sub(1),cp.sz.1,&sc.sz,&z_bank,&dirty)
    }) };
    b.play(&probe_z, false);
    mark(b, 2001);
    if cp.dq {
        // a delayed shot leaves its crossing column with sw = 1 (bottom t_j, Q r_j, top r_{j+1}); at the next column
        // start no other ph shot has sy <= l0 and sz = bl(Z) <= 127 (bl(t_k) >= 128 once r_{k-1} <= 2^l0): sw ^= that
        let ch: Vec<QubitId> = lean_sx(fd, fd.sx.len() - 1);
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &ch, &dirty);
        mc_xor(b, &[(ph, false), (sc.cmpc, true), (sc.sz[SZB - 1], true)], sc.sw, &[sc.f], &dirty);
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &ch, &dirty);
    }
    mark(b, 2003);
    // 1a. payload HT narrowing (before 1b: it does not read sw, whose lane it borrows)
    if let Some(pl) = pl {
        super::payload::col_narrow_ht(b, fd, cp, sc, pl);
    }
    mark(b, 2002);
    // 1b. sw = HR & bl(Z) <= l0
    if cp.sw {
        let ch1 = if SLIM { lean_sx(fd, fd.sx.len() - 1) } else {
            let mut ch1 = sc.pre.clone();
            ch1.extend([sc.bq, sc.tmp, sc.tmp2, qz[0]]); // bq and the quotient/rho lanes are still zero before P
            ch1
        };
        let gsw = rec(b, |b| ge_cd(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch1, &dirty));
        b.play(&gsw, false);
        if cp.dl {
            // the crossing form choice: only shots with bl(r_j) <= bl(t_j) switch; the delayed ones step HR here
            let gt = sz_gt_sy(b, fd, sc);
            mc_xor(b, &[(sc.cmpc, true), (ph, true), (sc.sz[SZB - 1], true)], sc.sw, &[sc.f], &dirty);
            b.play(&gt, true);
        } else {
            mc_xor(b, &[(sc.cmpc, true), (ph, true)], sc.sw, &[], &dirty);
        }
        b.play(&gsw, true);
    }
    stage!(); // 1
    // 2. Y into Q
    // Four prefixes leave five controls for the nine-bit cut. Exact dirty
    // multi-controlled toggles restore passenger wires and use no extra helper.
    // Before P the whole rho bank is zero; afterward its top bit is zero
    // because rho<Yh<2^KP. Each use returns it before any rho compare.
    let middle_zero = if sc.ps.rho.len() > kp { rotated(&sc.ps.rho,tot)[kp] } else { fd.sx[fd.sx.len() - 1] };
    assert!(!sc.u.contains(&middle_zero) && sc.js != middle_zero);
    let pre_sw = vec![sc.g,sc.c0,sc.cmpc,middle_zero];
    let swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                   sc.f, &pre_sw, &dirty));
    assert!(pre_sw.len() + 5 >= sc.sz.len()); // exact dirty toggles of at most five controls
    // bulengerk: where the whole rho bank is |0> (before P, after un-P) the decoder takes wider clean prefixes
    let mut wide_pre_sw = pre_sw.clone();
    for &x in &sc.rho_clean { if !wide_pre_sw.contains(&x) { wide_pre_sw.push(x); } }
    if SLIM { wide_pre_sw = lean_sx(fd, sc.sz.len() - 1); }
    wide_pre_sw.truncate(sc.sz.len() - 1);
    assert!(wide_pre_sw.len() == sc.sz.len() - 1 || env_k("FD_LEAN_SX").is_some());
    let wide_swap = rec(b, |b| masked_swap_middle_compact(b, &ring, &q, &sc.sz, cp.h, pclo, pchi,
                                                        sc.f, &wide_pre_sw, &dirty));
    if cp.psw && psw_delta() {
        psw_first_delta(b, fd, cp, sc, &ring, &q, pclo, pchi, &dirty);
    } else if cp.psw {
        // first-HT shots arrive in the switched layout (Q = Y, top = X > 2^l0, sy = bl(X)): js = ph & sy > l0;
        // they skip this first swap, and their sy is cleared and refilled with bl(Q) (= bl(Y) for the column)
        let mut chain = sc.pre.clone();
        chain.extend_from_slice(&sc.anc);
        // SLIM: js = s[3] (g), cmpc = s[1], flag f = s[2], the first swap's gate temp bq = s[0]; the compare chain
        // and the first swap's prefixes in sx (clean until the T probe writes it); the T probe and the bl(Q) probe
        // take what is left (short decoders, dirty toggles), the last compare (sx is its operand) the exact compact
        let js = if SLIM { s[3] } else { sc.js };
        let (pre_first, pt_pre, pt_opre, pg_opre) = if SLIM {
            chain = fd.sx[..fd.sx.len() - 1].to_vec();
            (chain.clone(), vec![], vec![], vec![s[2]])
        } else { (pre_sw.clone(), chain.clone(), sc.opre.clone(), sc.opre.clone()) };
        let (pt_tmp, pt_tmp2) = if SLIM { (s[0], s[1]) } else { (sc.tmp, sc.tmp2) };
        let chain2: Vec<QubitId> = if SLIM { vec![s[0], s[2]] } else { chain.clone() };
        assert!(!SLIM || (sc.cmpc == s[1] && sc.f == s[2] && sc.bq == s[0]));
        assert!(!chain.contains(&js) && !chain2.iter().any(|x| *x == js || sc.u2.contains(x) || fd.sy.contains(x)));
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
        b.ccx(ph, sc.cmpc, js);
        // a delayed shot's no-step column (Q = Y = r_j, top = X = r_{j+1}): ph, sy <= l0, sz <= 127
        if cp.dq { mc_xor(b, &[(ph, false), (sc.cmpc, true), (sc.sz[SZB - 1], true)], js, &[], &dirty); }
        super::mask::ge_const(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain);
        mark(b, 2012);
        let first = rec(b, |b| masked_swap_gated(b, &ring, &q, &sc.sz, cp.h, pclo, pchi, sc.f, &pre_first, &dirty,
                                                 js, sc.bq));
        b.play(&first, false);
        mark(b, 2013);
        // every shot now has X in the ring top: T = bl(top); sy ^= js & T (= 0); sy = bl(Q) on js shots (Q still
        // holds Y there: they skipped the swap); js ^= ph & T > l0; T uncomputed
        let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
        let cutr = Cut { v: sc.sz.clone(), a: (n - cp.h) as isize, neg: true };
        let pt = rec(b, |b| msb_probe_cut_range(b, &rev, &cutr, n - cp.h - cp.sz.1, n - cp.h - cp.sz.0, 0,
                                                (cp.xw + 1).min(n), &sc.u2, sc.f, &pt_pre, &pt_opre, pt_tmp, pt_tmp2,
                                                &dirty));
        b.play(&pt, false);
        mark(b, 2014);
        for i in 0..fd.sy.len() { b.ccx(js, sc.u2[i], fd.sy[i]); }
        let pu = rec(b, |b| probe_gated(b, &q, 0, cp.l0.min(q.len()), &fd.sy, &[(js, false)], &pg_opre, pt_tmp,
                                        &[pt_tmp2], &dirty));
        b.play(&pu, false);
        mark(b, 2015);
        ge_cd(b, &sc.u2, cp.l0 as isize + 1, sc.cmpc, &chain2, &dirty);
        b.ccx(ph, sc.cmpc, js);
        if cp.dq { mc_xor(b, &[(ph, false), (sc.cmpc, true), (sc.sz[SZB - 1], true)], js, &[], &dirty); }
        ge_cd(b, &sc.u2, cp.l0 as isize + 1, sc.cmpc, &chain2, &dirty);
        mark(b, 2016);
        b.play(&pt, true);
    } else {
        b.play(&wide_swap, false);
    }
    mark(b, 2011);
    if let Some(pl) = pl {
        super::payload::col_digit(b, fd, cp, sc, pl);
    }
    stage!(); // 2
    let nq = q.len();
    if super::mid2::enabled() {
        let mut cont = true;
        let mid_fn = if super::midg::enabled() { super::midg::middle } else { super::mid2::middle };
        mid_fn(b, fd, cp, sc, pl, &swap, &mut |b: &mut B| {
            stn += 1;
            mark(b, stn);
            super::f1_profile(f1_stages[stn - 1], f1_last, b.tof);
            f1_last = b.tof;
            if prof {
                let v = if std::env::var("FROGDROP_PROF_OPS").is_ok() { b.ops.len() as u64 } else { b.tof };
                prof_v.push((stn, v - last)); last = v;
            }
            cont = stn <= upto;
            cont
        });
        if !cont { return; }
    } else {
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
    let mut r_alignment: Option<(QubitId, QubitId)> = None;
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
        // an 8-lane sz holds sz + sy (228..=257 on stepping shots) modulo 256: the start index is >= 0 and the
        // warm-up is constant; the start decoder distinguishes the tot iterations modulo 256
        let narrow = sc.sz.len() < 9;
        assert!(!narrow || (start_min >= 0 && tot <= 1usize << sc.sz.len() && 257 - 228 < 1usize << sc.sz.len()));
        let (head, tails, swp, rf, _) = super::frogdrop::pipeline_subset_with_reserved_c0(b,
            &ring[n - k..n], &q[nq - kp..nq], &sc.sz, soff, tot, qb, &ps,
            &q[held..held + pcar], &sc.qsets, sc.tq, skip, reuse_r_zero, !narrow);
        assert_eq!(rf.len(), k + 1);
        let align = if reuse_r_zero { Some((rf[k], ring[cp.h - 1])) } else { None };
        if let Some((a, z)) = align { assert_ne!(a, z); assert_ne!(sc.ps.c0, a); assert_ne!(sc.ps.c0, z); }
        r_alignment = align;
        for t in &tails {
            p_sets.push(rec(b, |b| {
                b.play(&rrot, false); b.play(&head, false); b.play(t, false);
                if let Some((a, z)) = align { b.swap(a, z); }
                b.play(&rrot, true);
            }));
        }
        for (ta, tb) in &swp {
            p_sw.push(rec(b, |b| {
                b.play(&rrot, false);
                // The buffer can be one during the +Y scaffold or W add.
                // Preserve that bit coherently before exposing Rzero to P.
                if let Some((a, z)) = align { b.swap(z, sc.ps.c0); b.swap(a, z); }
                b.play(ta, true); b.play(tb, false);
                if let Some((a, z)) = align { b.swap(a, z); b.swap(z, sc.ps.c0); }
                b.play(&rrot, true);
            }));
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
            // The buffer and W head track h independently of reciprocal precision.
            let dest_h: std::collections::BTreeSet<usize> = (n - H..n).chain(cp.h - 1..cp.h + H).collect();
            let care_h = std::env::var("FD_NOCARE").is_err();
            if care_h { rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_h); }
            else { rot_by_range(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty); }
            let ht2 = b.tof;
            let a: Vec<_> = ring[cp.h..cp.h+H].iter().rev().copied().collect();
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
            let domain = vec![(ph,false),(sc.f,true),(sc.c0,true),(ring[cp.h-1],true),(ring[cp.h],false)];
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
        // The corrected target fits its real region here, hence the shared
        // buffer is zero. Restore canonical R owners before tag502 measures
        // them; on the mirror, saved Z phases happen before the reversed S.
        if let Some((a, z)) = r_alignment { b.swap(a, z); }
        let core_inverse = rec(b, |b| { b.play(tail, true); b.play(head, true); });
        let mut outs = ps.r.clone(); outs.extend(&ps.rho); outs.extend(&ps.q0); outs.push(sc.tq);
        outs.sort(); outs.dedup();
        b.deferred_erasure(502, core_inverse, outs);
        b.play(rrot, true);
    } else {
        b.play(&p_sets[nsets - 1], true);
    }
    stage!(); // 7
    }
    // 9. X_new into Q (map layout); erase sz
    b.play(&wide_swap, false);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { mark(b, 800); }
    if cp.dl {
        // delayed shots (!ph & sz <= l0 & sz > sy): X_new = t_{j+1} (< 2^(n/2)) left its bits l0.. at ring lanes
        // n - 1 - l: move them to lanes l, above r_j, where stage 10's bottom <-> Q completes t_{j+1}; then sw marks
        // every crossing shot
        let dlf = |b: &mut B| {
            let ch: Vec<QubitId> = lean_sx(fd, fd.sx.len() - 1);
            ge_cd(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch, &dirty);
            let gt = sz_gt_sy(b, fd, sc);
            mc_xor(b, &[(ph, true), (sc.cmpc, true), (sc.sz[SZB - 1], false)], sc.g, &[sc.f], &dirty);
            b.play(&gt, true);
            ge_cd(b, &sc.sz, cp.l0 as isize + 1, sc.cmpc, &ch, &dirty);
        };
        dlf(b);
        for l in cp.l0..cp.xw.min(n / 2) { b.cswap(sc.g, ring[n - 1 - l], ring[l]); }
        b.cx(sc.g, sc.sw);
        dlf(b);
    }
    if let Some(pl) = pl {
        super::payload::col_narrow_hr(b, fd, cp, sc, pl);
    }
    if std::env::var_os("D3_TRACE_PHASE").is_some() { mark(b, 801); }
    if cp.dl {
        // delayed shots (!ph & sw & sz > sy): sz = bl(r_j) -> bl(ring[..n/2)) (r_j below t_{j+1}'s top bits), what the
        // probe's inverse erases
        let dlf = |b: &mut B| {
            let gt = sz_gt_sy(b, fd, sc);
            mc_xor(b, &[(ph, true), (sc.sw, false), (sc.sz[SZB - 1], false)], sc.g, &[sc.f], &dirty);
            b.play(&gt, true);
        };
        dlf(b);
        let pre: Vec<QubitId> = lean_sx(fd, fd.sx.len() - 1);
        let lo = cp.dlr.saturating_sub(1);
        let pr = rec(b, |b| probe_gated(b, &ring, lo, cp.l0, &sc.sz, &[(sc.g, false)], &pre, sc.cmpc, &[sc.f, sc.bq],
                                        &dirty));
        b.play(&pr, true);
        // (agent_lowq_quot: the swap above pairs lanes l and n - 1 - l, l < n / 2, so t_{j+1}'s bits up to n - 1 - l0
        // all reach their own lanes, the bits >= n / 2 through their partners and bit (n - 1) / 2 of an odd ring in
        // place; the probe reads them all: n / 2 alone missed bl(t_{j+1}) > n / 2, a delayed shot ~2.5e-5 per input
        // below ring 273)
        let pr = rec(b, |b| probe_gated(b, &ring, lo, cp.xw.min(n - cp.l0), &sc.sz, &[(sc.g, false)], &pre, sc.cmpc,
                                        &[sc.f, sc.bq], &dirty));
        b.play(&pr, false);
        dlf(b);
    }
    b.play(&probe_z, true);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { mark(b, 802); }
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
    let (ms_rec, ms_ctl) = map_stage_ex(b, fd, cp, sc);
    if let (Some((sw, _)), true) = (ms_ctl, MAP_SWPH.with(|c| c.get())) {
        // agent_lowq_quot: sw ^= D, then the record on !(ph & sw); done shots' sizes stay put (the rename below)
        let n = sc.dirty.len();
        let (w1, w2) = (sc.dirty[n - 2], sc.dirty[n - 1]);
        let dd: Vec<QubitId> = sc.dirty[..n - 2].to_vec();
        map_done_flag(b, fd, cp, sw, &dd);
        b.play_ctrl_nand2(&ms_rec, fd.ph, sw, w1, w2);
        for i in 0..fd.sx.len() { super::mid2::mc_swap(b, &[(fd.ph, false), (sw, false)], fd.sx[i], fd.sy[i], &[], &dd); }
        map_done_flag(b, fd, cp, sw, &dd);
    } else if let Some((d, h)) = ms_ctl {
        // agent_lowq_quot: done shots skip the map (every gate controlled, the AND pairs too: the record's lanes,
        // ph among them in a ph-free column, are not clean on them); their sizes stay put (sx <-> sy undoes the
        // rename below)
        mark(b, 8000);
        map_done_flag(b, fd, cp, d, &sc.dirty);
        mark(b, 8001);
        let ph_out = MAP_PH_OUT.with(|c| c.get());
        if ph_out { b.x(fd.ph); }
        b.x(d);
        if sc.dirty.last() == Some(&h) { b.play_ctrl_full_dirty(&ms_rec, d, h); } else { b.play_ctrl_full(&ms_rec, d, h); }
        b.x(d);
        if std::env::var_os("QUOT_CTRL_STATS").is_some() {
            let mut st = std::collections::BTreeMap::new();
            for g in &ms_rec { *st.entry(format!("{:?}", g).split('(').next().unwrap().to_string()).or_insert(0usize) += 1; }
            eprintln!("CTRLSTATS col {} {:?}", cp.col, st);
        }
        if ph_out { b.x(fd.ph); }
        mark(b, 8002);
        for i in 0..fd.sx.len() { b.cswap(d, fd.sx[i], fd.sy[i]); }
        mark(b, 8003);
        map_done_flag(b, fd, cp, d, &sc.dirty);
        mark(b, 8004);
    } else if std::env::var_os("D3_TRACE_PHASE").is_some() {
        let segs = D3_MAP_SEGMENTS.with(|m| std::mem::take(&mut *m.borrow_mut()));
        let mut at = 0;
        for (off, stage) in segs {
            if off >= at && off <= ms_rec.len() { b.play(&ms_rec[at..off], false); mark(b, stage); at = off; }
        }
        b.play(&ms_rec[at..], false);
    } else { b.play(&ms_rec, false); }
    std::mem::swap(&mut fd.sy, &mut fd.sx);
    stage!(); // 9
    // 14. switching shots (after the map: bottom r_{j-1}, Q t_j, top r_j): ring reversal (bottom r_j, top r_{j-1}),
    // sy <- bl(top), bottom <-> Q: the switched layout (bottom t_j, Q = Y = r_j, ring top = X = r_{j-1} > 2^l0);
    // ph = 1; erase sw = ph & sy <= l0
    if cp.sw && env_k("FD_SWT_DELTA") == Some(1) {
        // the switch tail without the size temp t: sy (= bl(r_j), the pre-reversal top below 2^l0) is erased on the
        // sw shots by the inverse of a gated top probe, the ring reversed, and sy refilled with bl(top) = bl(r_{j-1})
        let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
        let s = &sc.slim;
        let (t_opre, t_tmp, t_tmp2) = (lean_sx(fd, fd.sx.len() - 1), s[0], s[2]);
        let pr = rec(b, |b| probe_gated(b, &rev, 0, cp.l0, &fd.sy, &[(sc.sw, false)], &t_opre, t_tmp, &[t_tmp2],
                                        &dirty));
        b.play(&pr, true);
        for l in 0..n / 2 { b.cswap(sc.sw, ring[l], ring[n - 1 - l]); }
        let probe_t = rec(b, |b| probe_gated(b, &rev, 0, n - cp.l0, &fd.sy, &[(sc.sw, false)], &t_opre, t_tmp,
                                             &[t_tmp2], &dirty));
        b.play(&probe_t, false);
        for l in 0..cp.swl.1 { b.cswap(sc.sw, ring[l], q[l]); }
        b.cx(sc.sw, ph);
        b.cx(ph, sc.sw);
        assert_eq!(sc.cmpc, s[1]);
        let chain = lean_sx(fd, fd.sx.len());
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain, &dirty);
        mc_xor(b, &[(ph, false), (sc.cmpc, true)], sc.sw, &[], &dirty);
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain, &dirty);
    } else if cp.sw {
        for l in 0..n / 2 { b.cswap(sc.sw, ring[l], ring[n - 1 - l]); }
        let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
        let t = sc.u.clone();
        let s = &sc.slim;
        // SLIM: the spare size register (renamed after the map: the erased old sy) is clean here
        let (t_opre, t_tmp, t_tmp2) = if SLIM { (lean_sx(fd, fd.sx.len() - 1), s[0], s[2]) }
                                      else { (sc.opre.clone(), sc.tmp, sc.tmp2) };
        // switchers' bottom r_j < 2^l0: the reversed ring's first n - l0 lanes hold only gap and top
        let probe_t = rec(b, |b| probe_gated(b, &rev, 0, n - cp.l0, &t, &[(sc.sw, false)], &t_opre, t_tmp,
                                             &[t_tmp2], &dirty));
        b.play(&probe_t, false);
        for i in 0..fd.sy.len() { b.cswap(sc.sw, fd.sy[i], t[i]); }
        for l in 0..cp.swl.1 { b.cswap(sc.sw, ring[l], q[l]); }
        let probe_q = rec(b, |b| probe_gated(b, &q, 0, cp.l0.min(nq), &t, &[(sc.sw, false)], &t_opre, t_tmp,
                                             &[t_tmp2], &dirty));
        b.play(&probe_q, true);
        b.cx(sc.sw, ph);
        b.cx(ph, sc.sw);
        let mut chain = sc.pre.clone();
        chain.extend_from_slice(&sc.anc);
        if SLIM { assert_eq!(sc.cmpc, s[1]); chain = lean_sx(fd, fd.sx.len()); }
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain, &dirty);
        mc_xor(b, &[(ph, false), (sc.cmpc, true)], sc.sw, &[], &dirty);
        ge_cd(b, &fd.sy, cp.l0 as isize + 1, sc.cmpc, &chain, &dirty);
    }
    // 15. done shots: cnt += 1 (cnt in Q's top lanes, done derived); shots that just reached r = 1 (top = 1, ph = 1,
    // not done) get cnt = 1, the helper erased via done & cnt == 1 (older done shots are >= 2 after their increment)
    if cp.dn {
        // carries on the sz lanes (clean after stage 9; the stage-14 temp t is erased)
        let na = env_k("FD_CNT_ANC").unwrap_or(fd.cnt.len() - 1).min(fd.cnt.len() - 1);
        let anc: Vec<QubitId> = sc.u[..na].to_vec();
        let d = sc.u[fd.cnt.len() - 1];
        let t15 = if SLIM { sc.slim[0] } else { sc.tmp };
        mc_xor_dn(b, &[], d, &[t15], &dirty, fd, cp.l0, true);
        if na == fd.cnt.len() - 1 { super::arith::inc(b, d, &fd.cnt, &anc); }
        else { super::frogdrop::inc_mixed(b, d, &fd.cnt, &anc, &dirty); }
        mc_xor_dn(b, &[], d, &[t15], &dirty, fd, cp.l0, true);
    }
    if cp.fin {
        let mut sy1: Vec<(QubitId, bool)> = vec![(fd.sy[0], false)];
        sy1.extend(fd.sy[1..].iter().map(|&x| (x, true)));
        let mut l1 = vec![(ph, false)];
        l1.extend(sy1.iter().cloned());
        let tfin = if SLIM { sc.slim[0] } else { sc.tmp };
        mc_xor_dn(b, &l1, sc.g, &[tfin], &dirty, fd, cp.l0, false);
        b.cx(sc.g, fd.cnt[0]);
        let ctop = cp.nq - fd.cnt.len();
        let mut l2 = vec![(ph, false)];
        l2.extend(sy1.iter().cloned());
        l2.extend((cp.l0..ctop).map(|l| (q[l], true)));
        l2.push((fd.cnt[0], false));
        l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
        mc_xor(b, &l2, sc.g, &[tfin], &dirty);
    }
    stage!(); // 11
    if prof {
        let s: Vec<String> = prof_v.iter().map(|(i, t)| format!("{}={}", f1_stages[i - 1], t)).collect();
        eprintln!("  prof: {}", s.join(" "));
    }
}

/// Map stage (recorded): sx = bl(X); order; map with cut = n - max; unorder; erase sy by probing Q (= Y).
/// The caller relabels sy <-> sx afterwards (ring top then holds X, size sx).
pub(crate) fn map_stage(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr) -> Vec<G> {
    let (r, ctl) = map_stage_ex(b, fd, cp, sc);
    assert!(ctl.is_none(), "a controlled map column needs map_stage_ex");
    r
}

/// agent_lowq_quot QUOT_MAP_TZ=1: the map's 2^e room from the even operand's trailing zeros (frogdrop::mapf_tz)
pub(crate) fn map_tz() -> bool {
    static TZ: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *TZ.get_or_init(|| std::env::var("QUOT_MAP_TZ").map(|v| v == "1").unwrap_or(false))
}

/// map_stage, and for a controlled column (is_map_ctrl) the (done flag, control helper) lanes it leaves out
pub(crate) fn map_stage_ex(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr) -> (Vec<G>, Option<(QubitId, QubitId)>) {
    let ctrl = is_map_ctrl(cp);
    let mut ctl_out: Option<(QubitId, QubitId)> = None;
    let mut ph_out = false;
    // (a controlled replay takes no signed-binary rows)
    let old_booth = b.allow_booth;
    if ctrl { b.allow_booth = false; }
    let old_rows = b.no_rows;
    let ring = &fd.ring;
    let q = &fd.q;
    let n = cp.n;
    // a controlled map with a borrowed helper (QUOT_MAP_CTRL_DIRTY=1): the record leaves the last dirty lane alone
    let ctrl_dirty = ctrl && std::env::var("QUOT_MAP_CTRL_DIRTY").map(|v| v == "1").unwrap_or(false);
    // (QUOT_MAP_CTRL_SWPH=1, switch columns: done = ph & sw' with sw' = sw ^ D, since sw implies !ph and a done shot
    // has sw = 0; the record replays under !(ph & sw') with two borrowed helpers and no done-flag lane)
    let swph = ctrl_dirty && cp.sw && std::env::var("QUOT_MAP_CTRL_SWPH").map(|v| v == "1").unwrap_or(false);
    let nkeep = if swph { 2 } else if ctrl_dirty { 1 } else { 0 };
    let dirty: Vec<QubitId> = sc.dirty[..sc.dirty.len() - nkeep].to_vec();
    if ctrl_dirty { b.no_rows = true; }
    let r = rec(b, |b| {
        let mut ms = sc.ms.clone();
        ms.dirty = dirty.clone();
        // Ordinary maps need at most 257 + emax <= n lanes by the product
        // invariant. Switch endpoints and pair values each fit nq lanes, so
        // 2*nq + emax - n extra lanes cover the complete retained v2 envelope.
        // Fund these transient lanes from tail prefixes. Dirty exact increments
        // replace only tails whose clean prefix no longer fits; loans remain
        // excluded from every map scratch and carry vector until returned.
        // agent_lowq_quot QUOT_MAP_TZ=1: the frame room comes from the even operand's trailing zeros (mapf_tz), so the
        // extension covers only 257 - n (2 nq - n in a switch column) and one lane holds the flag t = [X even]
        let tz = map_tz();
        let extra = if cp.sw { (2 * cp.nq + if tz { 0 } else { cp.emax }).saturating_sub(n) }
                    else { (257 + if tz { 0 } else { cp.emax }).saturating_sub(n) };
        let mut tz_t: Option<QubitId> = None;
        // bq has been erased by the middle correction and is not used by an
        // ordinary map. The end's controlled map has cp.sw=false and takes no
        // loan. With !dn every branch is still stepping: cnt is zero, and this
        // column's optional finish increment occurs only after the map returns.
        let mut extension = vec![];
        // done shots' counter sits in Q's top lanes: park it in clean tail lanes while the map reads Q, from
        // before the bl(X) probe (a probe bound m > nq - cnt would read the counter) until after the sy erase
        // (its bits above cp.cntw are zero at this column)
        let nc = cp.cntw.min(fd.cnt.len());
        let ctop = q.len() - fd.cnt.len();
        // (the map frame also lends Q above its operand bound as clean carries)
        let mut park: Vec<QubitId> = vec![];
        let mut pd = None;
        // lean: a map that reads Q below ctop only leaves the counter in place (the frame then sees Q[..ctop]);
        // else each counter bit swaps with its parking lane under the done test A = ph & Q[RA..ctop) == 0 (a set
        // counter bit implies cnt != 0), no done flag held. A switch column parks bit 0 in the sw lane (done
        // shots never switch, sw = 0 there; the map does not touch sw).
        let lean_park = MAP_LEAN && cp.dn && cp.m > ctop && !ctrl;
        // agent_lowq_quot: park only the counter bits the map reads (Q[ctop..m)); the higher ones stay put and the
        // frame sees Q[..m] (no lent lanes above m). QUOT_MAP_FULLPARK=1: every cntw bit, the frame sees all of Q.
        let partial = lean_park && std::env::var_os("QUOT_MAP_FULLPARK").is_none();
        let nc = if partial { nc.min(cp.m - ctop) } else { nc };
        let qmap: &[QubitId] = if ctrl { q } else if MAP_LEAN && cp.dn && !lean_park { &q[..ctop] }
                               else if partial { &q[..cp.m.max(ctop + nc)] } else { q };
        // a parking column frees sy across the core: after the order sy holds min(bl X, bl Y), erased from Q (X) or
        // the ring top (Y, inside the region [n - max, n)) under cmpc and restored the same way afterwards; the
        // core's v2 register and flags c0, e, g then live in sy, the parked counter, the extension and f in the lean
        // lanes (`hl`: what stays clean outside the core)
        // agent_lowq_quot: a map whose ring lacks room (extension beyond bq and the lean anc lane) frees sy across
        // the core too, so the lean scratch lanes fund up to ten extension lanes (ring 270 at EMAX 23)
        // (the end B0 map, cp.sz == (0, 0), keeps the plain path: its Q holds only R < 2^26 and the counter, so
        // Q's idle lanes below the counter fund its extension, and pool g stays free for the controlled replay)
        let b0_map = cp.sz == (0, 0);
        let sy_free = lean_park || (!b0_map && extra > 1 + super::frogdrop_col::LEAN_MAP_PARK)
            || std::env::var_os("QUOT_SYFREE").is_some();
        // agent_lowq_quot: after the order sx = max(bl X, bl Y) is in [1, 128] on every shot of the envelope
        // (smax): held as max - 1 it fits sx[0..7], so sx[7] is |0> from the order to the unorder and serves as the
        // last extension lane (the probes' ring-top cut and the frame cut read the 7-bit offset form)
        let sxoff = sy_free && extra >= 2 && cp.smax.0 >= 1 && cp.smax.1 <= 128 && fd.sx.len() == 8
            && std::env::var_os("QUOT_MAP_NOSXOFF").is_none();
        let mut hl: Vec<QubitId> = vec![];
        // agent_lowq_quot: the order bit as an extension lane (`cmpc_l`: see the core below)
        let mut cmpc_free = false;
        // agent_lowq_quot QUOT_MAP_XCMPC=1: cmpc = [bl Y > bl X] = !X[max - 1] is re-derived from the data on each side
        // of the core (X in Q before it, in the ring top after it; sx holds max - 1), so cmpc is an extension lane in
        // every sy-free map (any column kind, done shots too)
        let mut xcmpc = false;
        // agent_lowq_quot F3: in a column with no HR and no switching shot every shot is HT or done, so ph = 1 on
        // every shot; flipped to 0 it is one more clean lane for the sy-free core (restored at the end)
        // (only when the plain sy-free budget, bq + the lean lanes + sw for parking - f, falls short)
        let syfree_budget = 1 + 9 + ms.anc.len() + usize::from(lean_park && nc > 0) - 1 + usize::from(sxoff);
        let ph_free = sy_free && !cp.hr && !cp.sw && (ctrl || extra + if lean_park { nc } else { 0 } > syfree_budget)
            && std::env::var_os("QUOT_NO_PHFREE").is_none();
        // (a controlled map flips ph outside its record, on every shot: the record's rows take ph as a clean lane, and
        // a row's carry ladder runs on control-0 shots too)
        if ph_free && !ctrl { b.x(fd.ph); }
        if ph_free && ctrl { ph_out = true; }
        if sy_free {
            let nc = if lean_park { nc } else { 0 };
            let mut free: Vec<QubitId> = vec![ms.c0, ms.e, ms.g, ms.f];
            free.extend(&ms.ez);
            free.extend(&ms.anc);
            if ph_free { free.insert(0, fd.ph); }
            // agent_lowq_quot: a column with HR shots only (no HT, switch, delayed or done shot) has ph = 0 on every
            // shot: one more clean lane, no flip (QUOT_MAP_PH0=1)
            let ph0_free = !ph_free && !cp.ht && !cp.sw && !cp.dl && !cp.dq && !cp.dn && !b0_map
                && std::env::var("QUOT_MAP_PH0").map(|v| v == "1").unwrap_or(false);
            if ph0_free { free.insert(0, fd.ph); }
            // a controlled map parks no counter: in a column with no switch, delayed or no-step shot sw is |0> on
            // every shot (QUOT_MAP_CTRL_SW=1: one more clean lane)
            if ctrl && !cp.sw && !cp.dl && !cp.dq && std::env::var("QUOT_MAP_CTRL_SW").map(|v| v == "1").unwrap_or(false) {
                free.push(sc.sw);
            }
            // a controlled map: its done flag and control helper (clean lean lanes) stay out of the record
            if swph {
                ctl_out = Some((sc.sw, sc.dirty[sc.dirty.len() - 1]));
            } else if ctrl && ctrl_dirty {
                free.retain(|&w| w != ms.c0);
                ctl_out = Some((ms.c0, sc.dirty[sc.dirty.len() - 1]));
            } else if ctrl {
                free.retain(|&w| w != ms.c0 && w != ms.e);
                ctl_out = Some((ms.c0, ms.e));
            }
            // bit 0 in the sw lane (switch columns: done shots never switch, sw = 0; else sw is clean), then bq when
            // no extension takes it
            if std::env::var_os("QUOT_MAPDBG").is_some() {
                let need = nc.saturating_sub(usize::from(nc > 0)) + extra.saturating_sub(1 + usize::from(sxoff)) + 1;
                eprintln!("MAPDBG col {} ctrl {} sw {} dn {} lean {} nc {} extra {} free {} ph_free {} hr {} ht {} need {} short {} m {} ctop {} cntmax {}",
                          cp.col, ctrl, cp.sw, cp.dn, lean_park, nc, extra, free.len(), ph_free, cp.hr, cp.ht, need,
                          need as isize - free.len() as isize, cp.m, ctop, cp.cntmax);
            }
            if nc > 0 { park.push(sc.sw); }
            if extra == 0 && park.len() < nc { park.push(sc.bq); }
            // agent_lowq_quot: when the pool falls short, cmpc is cleared across the core and serves as an extension
            // lane (QUOT_MAP_CMPC=1: wherever possible, =0: never); needs every counter bit parked (park[0] = sw holds
            // cnt[0], park[1..] the rest) and a pattern of park[1..] no done counter takes (all ones: cnt <= 2^nc - 3)
            let pops = nc - park.len() + if extra > 0 { extra - usize::from(sxoff) - 1 } else { 0 } + 1;
            let cmode = std::env::var("QUOT_MAP_CMPC").ok();
            // (before the controlled columns only: a done shot's form, hence cmpc, follows the maps it ran)
            let before_s = MAP_CTRL_S.with(|m| m.borrow().0.iter().all(|&c| cp.col < c));
            xcmpc = std::env::var("QUOT_MAP_XCMPC").map(|v| v == "1").unwrap_or(false) && !b0_map && sxoff
                && extra >= 2 + usize::from(sxoff);
            cmpc_free = !xcmpc && lean_park && nc >= 2 && nc == cp.cntw && cp.cntmax + 3 <= 1 << nc && !b0_map && before_s
                && extra >= 2 + usize::from(sxoff)
                && cmode.as_deref() != Some("0") && (free.len() < pops || cmode.as_deref() == Some("1"));
            // (QUOT_MAP_ALLOC=1, a budget probe: a short pool takes fresh lanes)
            let short_alloc = std::env::var_os("QUOT_MAP_ALLOC").is_some();
            let mut pop = |free: &mut Vec<QubitId>, b: &mut B| free.pop()
                .unwrap_or_else(|| { assert!(short_alloc, "map pool short"); b.alloc() });
            while park.len() < nc { park.push(pop(&mut free, b)); }
            if extra > 0 {
                extension.push(sc.bq);
                if cmpc_free || xcmpc { extension.push(sc.cmpc); }
                let from_pool = extra - usize::from(sxoff);
                while extension.len() < from_pool { extension.push(pop(&mut free, b)); }
                if sxoff { extension.push(fd.sx[7]); }
            }
            let fl = pop(&mut free, b);
            if tz { tz_t = Some(pop(&mut free, b)); }
            let sy = &fd.sy;
            ms = MapScr { c0: sy[5], h: fl, e: sy[6], g: sy[7], f: fl, tmp: sy[6], one: sy[6], pre: vec![],
                          ez: sy[0..5].to_vec(), epre: vec![], anc: vec![], dirty: dirty.clone(), andc: vec![] };
            hl = free;
            hl.push(fl);
        } else {
            if extra > 0 {
                extension.push(sc.bq);
                // The end B0 map needs two N277/EMAX22 extension lanes. Its Q
                // contains only R (< 2^26) and the counter in Q[121..];
                // Q[120] is a returned zero owner while this map reads
                // Q[0..28]. Keep pool g free for controlled replay.
                if cp.sz == (0, 0) && extra > 1 {
                    assert!(cp.dn && !cp.sw && cp.m <= 28 && ctop == 121);
                    // agent_lowq_quot: Q[28..121) is zero on every B0 shot; take as many as the ring lacks
                    let mut l = 120;
                    while extension.len() < extra { assert!(l >= 28); extension.push(q[l]); l -= 1; }
                }
            }
            let owed = extra - extension.len();
            assert!(ms.anc.len() >= owed);
            extension.extend(ms.anc.split_off(ms.anc.len() - owed));
            if lean_park {
                if cp.sw && nc > 0 { park.push(sc.sw); }
                let rest = nc - park.len();
                park.extend(ms.anc.split_off(ms.anc.len() - rest));
            } else if cp.dn && !MAP_LEAN {
                park = ms.anc.split_off(ms.anc.len() - nc);
                pd = ms.anc.pop();
            }
        }
        // (the end B0 map is replayed under play_ctrl with pool g, the lean anc lane, as its temp: t takes bq there,
        // clean with no extension and no booth loan in that map)
        if tz && tz_t.is_none() {
            tz_t = Some(if b0_map { assert!(!b.allow_booth); sc.bq } else { ms.anc.pop().expect("QUOT_MAP_TZ: a lane for t") });
        }
        // a lean map has no clean carry tail: the frame's dirty tail fallback covers it
        if MAP_LEAN { ms.anc.clear(); }
        let a_lits: Vec<(QubitId, bool)> = (if ph_free { None } else { Some((fd.ph, false)) }).into_iter()
            .chain((RA..ctop).map(|l| (q[l], true))).collect();
        if let Some(d) = pd { mc_xor_dn(b, &[], d, &[], &dirty, fd, cp.l0, true); }
        if lean_park { f1_lean_counter_swaps(b, &a_lits, &fd.cnt[..park.len()], &park, hl[0], &dirty, false); }
        else { for (i, &x) in park.iter().enumerate() { b.cswap(pd.unwrap(), fd.cnt[i], x); } }
        // bulengerk c4f95ef6: priority probes on the map's globally zero roles (after the extension, parked
        // counter and done flag are split off)
        let mut probe_bank = if sy_free { hl.clone() } else { super::priority_probe::map_bank(&ms) };
        // FD_MAP_PBANK: lane budget of the bl(X) / bl(Y) probes (bank and fallback prefixes)
        let pbk = env_k("FD_MAP_PBANK");
        if let Some(k) = pbk { probe_bank.truncate(k); }
        assert!(!probe_bank.iter().any(|w|ring.contains(w)||q.contains(w)||fd.sy.contains(w)||fd.sx.contains(w)||dirty.contains(w)
            ||[sc.sw,sc.bq,sc.cmpc].contains(w)||extension.contains(w)||park.contains(w)||pd==Some(*w)));
        assert!(!MAP_LEAN || !park.iter().any(|w| probe_bank.contains(w) || extension.contains(w)));
        let oldp=std::env::var("FD_OLDPROBE").is_ok();
        let pok=|n:usize| n==0 || super::priority_probe::choose(n, probe_bank.len()).is_some();
        // the fallback probes' prefixes and temp: the column's opre / tmp, or (lean) the map's own clean lanes
        let (ppre, ptmp): (Vec<QubitId>, QubitId) = if sy_free {
            (hl[1..].to_vec(), hl[0])
        } else if MAP_LEAN {
            ([ms.c0, ms.e, ms.g].iter().chain(&ms.ez).copied().collect(), ms.f)
        } else { (sc.opre.clone(), sc.tmp) };
        let ppre: Vec<QubitId> = match pbk { Some(k) => ppre[..k.saturating_sub(1).min(ppre.len())].to_vec(), None => ppre };
        if oldp || !pok(cp.m) { msb_probe_range(b, q, 0, cp.m, &fd.sx, &ppre, ptmp, &dirty); }
        else { super::priority_probe::emit(b,q,0,cp.m,&fd.sx,&probe_bank); }
        d3_map_segment(b, 901);
        let order = rec(b, |b| {
            use super::arith::{down_m, up_m, Dm};
            let oc0 = if sy_free { hl[0] } else if MAP_LEAN { ms.c0 } else { sc.c0 };
            let up = up_m(b, &fd.sx, &fd.sy, oc0, true);
            let dn = down_m(b, &fd.sx, &fd.sy, oc0, Dm::Restore, true);
            b.play(&up, false);
            b.cx(fd.sy[fd.sy.len() - 1], sc.cmpc); // carry of ~sx + sy (values < 2^width): [sy > sx]
            b.play(&dn, false);
            for i in 0..fd.sx.len() {
                b.cswap(sc.cmpc, fd.sx[i], fd.sy[i]);
            }
        });
        b.play(&order, false);
        let sxinc = if sxoff { rec(b, |b| super::modp_frogdrop::inc_dirty_free(b, &fd.sx, &dirty)) } else { vec![] };
        b.play(&sxinc, true);
        d3_map_segment(b, 902);
        // sy-free core: the erase / restore probes (helpers: hl and the extension lanes, clean outside the embed)
        let syp = if sy_free {
            let mut h = hl.clone();
            // (cmpc controls these probes)
            h.extend(extension.iter().filter(|&&w| w != sc.cmpc));
            // FD_MAP_SYBANK: lane budget of the sy erase / restore probes (three helpers plus prefixes)
            if let Some(k) = env_k("FD_MAP_SYBANK") { h.truncate(k.max(3)); }
            let (t1, t2, ff) = (h[0], h[1], h[2]);
            let rest = h[3..].to_vec();
            let k = rest.len() / 2;
            let (cpre, opre) = (rest[..k].to_vec(), rest[k..].to_vec());
            let opre_q: Vec<QubitId> = h[2..].to_vec();
            let mx = if sxoff { Cut { v: fd.sx[..7].to_vec(), a: 1, neg: false } }
                     else { Cut { v: fd.sx.clone(), a: 0, neg: false } };
            let rev: Vec<QubitId> = ring.iter().rev().copied().collect();
            // [cmpc == !neg]: from Q (bits [0, m)) / from the ring top inside the region (sx = max)
            let mut mk_q = |b: &mut B, neg: bool| rec(b, |b| probe_gated(b, q, 0, cp.m, &fd.sy, &[(sc.cmpc, neg)],
                                                                    &opre_q, t1, &[t2], &dirty));
            let pq1 = mk_q(b, false);
            let pq0 = mk_q(b, true);
            let mut mk_r = |b: &mut B, neg: bool| rec(b, |b| super::frogdrop::msb_probe_cut_range_x(b, &rev, &mx,
                cp.smax.0, cp.smax.1, 0, cp.smax.1, &fd.sy, ff, &cpre, &opre, t1, t2, &[(sc.cmpc, neg)], &dirty));
            let pr1 = mk_r(b, false);
            let pr0 = mk_r(b, true);
            Some((pq1, pq0, pr1, pr0))
        } else { None };
        if let Some((pq1, _, _, pr0)) = &syp {
            // cmpc = 1: sy = bl X (X in Q); cmpc = 0: sy = bl Y (Y in the ring top)
            b.play(pq1, true);
            b.play(pr0, true);
        }
        // agent_lowq_quot: cmpc |0> across the core. A done shot (cnt >= 1, every bit parked; Y and X alternate
        // each idle column) has cmpc = [cnt even] = !cnt[0]: cmpc ^= A & !park[0] & OR(park[1..]) clears it (an
        // A shot that is not done, Q < 2^RA, has the park lanes clean: the OR is 0). Every other shot has park[1..]
        // clean: cmpc goes there as all ones, a pattern no done counter takes (cnt <= 2^nc - 3), and the all-ones
        // test clears cmpc. (sw = park[0] is not read off the A shots: it may hold a switch / delayed flag.)
        let cfree = rec(b, |b| {
            if !cmpc_free { return; }
            let p1 = &park[1..];
            let d: Vec<QubitId> = dirty.iter().copied().filter(|&w| w != sc.cmpc && !park.contains(&w)
                && !a_lits.iter().any(|(x, _)| *x == w)).collect();
            let mut l1 = a_lits.clone();
            l1.push((park[0], true));
            super::mask::mc_xor(b, &l1, sc.cmpc, &[], &d);
            let mut l2 = l1.clone();
            l2.extend(p1.iter().map(|&x| (x, true)));
            super::mask::mc_xor(b, &l2, sc.cmpc, &[], &d);
            for &x in p1 { b.cx(sc.cmpc, x); }
            let l3: Vec<(QubitId, bool)> = p1.iter().map(|&x| (x, false)).collect();
            super::mask::mc_xor(b, &l3, sc.cmpc, &[], &d);
        });
        b.play(&cfree, false);
        // (QUOT_MAP_XCMPC) cmpc ^= !X[sx] read from Q: the extension lanes, clean until the embed, are the decoder's
        // prefixes
        let xread = |b: &mut B, post: bool| {
            if !xcmpc { return; }
            let pre: Vec<QubitId> = extension.iter().copied().filter(|&w| w != sc.cmpc).take(fd.sx.len() - 2).collect();
            let (lo, hi) = (cp.smax.0.max(1) - 1, cp.smax.1.min(128) - 1);
            let lane = |v: usize| if post { Some(ring[n - 1 - v]) } else { q.get(v).copied() };
            super::payload::read_lane(b, &fd.sx[..7], lo, hi, &lane, true, &[], sc.cmpc, &pre, &[], &dirty);
        };
        xread(b, false);
        d3_map_segment(b, 903);
        // FD_MAP_DFORM: across the embed and the core sy holds d = sx - sy = max - min = |bl X - bl Y| (bl(q) +- 1
        // < 2^5 on every model-clean shot), so its top three lanes are |0> and carry the core's c0, e (tmp, one)
        // and g: those three map lanes stay idle there
        let dform = !sy_free && env_k("FD_MAP_DFORM") == Some(1);
        let dconv = rec(b, |b| {
            if !dform { return; }
            for &x in &fd.sx { b.x(x); }
            super::frogdrop::reg_add_into(b, &fd.sy, &fd.sx, &[], ms.c0);
            for &x in &fd.sx { b.x(x); }
            for &x in &fd.sy { b.x(x); }
        });
        b.play(&dconv, false);
        let ms_full = ms.clone();
        if dform {
            let sy = &fd.sy;
            ms.c0 = sy[5];
            ms.e = sy[6];
            ms.tmp = sy[6];
            ms.one = sy[6];
            ms.g = sy[7];
        }
        let mcut = if sxoff { Cut { v: fd.sx[..7].to_vec(), a: n as isize - 1, neg: true } }
                   else { Cut { v: fd.sx.clone(), a: n as isize, neg: true } };
        // (a controlled map lends no Q lanes above m as clean carries: done shots keep their counter there)
        let mpar = MapPar { clo: n - cp.smax.1, chi: n - cp.smax.0, m: if ctrl { q.len() } else { cp.m }, tail: cp.tail,
                            emax: cp.emax };
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
        d3_map_segment(b, 904);
        let extcut = Cut { v: mcut.v.clone(), a: mcut.a + extra as isize, neg: mcut.neg };
        let extpar = MapPar { clo: mpar.clo + extra, chi: mpar.chi + extra,
                            m: mpar.m, tail: mpar.tail, emax: mpar.emax };
        // bq is zero after its middle-stage erasure; sw is zero in a
        // non-switch column. Lend either only when the extension/counter park
        // has not taken it, and return both at the frame boundary.
        if b.allow_booth && std::env::var("FD_NOMAPANDC").is_err() {
            if extra == 0 && !park.contains(&sc.bq) && !extension.contains(&sc.bq) { ms.andc.push(sc.bq); }
            if !cp.sw && !sc.sz.contains(&sc.sw) && !park.contains(&sc.sw) && !extension.contains(&sc.sw) {
                ms.andc.push(sc.sw);
            }
            assert_eq!(ms.andc.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),ms.andc.len());
            assert!(!ms.andc.iter().any(|w|extended.contains(w)||park.contains(w)||pd==Some(*w)));
        }
        let old_booth = b.allow_booth;
        if std::env::var_os("D3_NOMAPBOOTH").is_some() { b.allow_booth = false; }
        if let Some(t) = tz_t {
            assert_eq!(extra, 0, "QUOT_MAP_TZ: ring below 257 + its room");
            super::frogdrop::mapf_tz(b, &extended, qmap, &extcut, &extpar, &ms, t);
        } else {
            mapf(b, &extended, qmap, &extcut, &extpar, &ms);
        }
        b.allow_booth = old_booth;
        d3_map_segment(b, 905);
        b.play(&embed, true);
        b.play(&dconv, true);
        b.play(&cfree, true);
        // (QUOT_MAP_XCMPC) after the core X is in the ring top (bit i at lane n - 1 - i): cmpc ^= !X[sx] again
        xread(b, true);
        ms = ms_full;
        d3_map_segment(b, 906);
        if let Some((_, pq0, pr1, _)) = &syp {
            // after the core Q = Y and the ring top holds X: cmpc = 1: sy = bl X; cmpc = 0: sy = bl Y
            b.play(pr1, false);
            b.play(pq0, false);
        }
        d3_map_segment(b, 907);
        b.play(&sxinc, false);
        b.play(&order, true);
        d3_map_segment(b, 908);
        let ylim=if cp.sy.1==0 {cp.m}else{cp.m.min(cp.sy.1)};
        let probe_y = if oldp || !pok(ylim - cp.sy.0.saturating_sub(1)) { rec(b, |b| msb_probe_range(b, q, cp.sy.0.saturating_sub(1), ylim, &fd.sy, &ppre, ptmp, &dirty)) }
                      else { rec(b, |b| super::priority_probe::emit(b, q, cp.sy.0.saturating_sub(1), ylim, &fd.sy, &probe_bank)) };
        b.play(&probe_y, true);
        d3_map_segment(b, 909);
        if lean_park { f1_lean_counter_swaps(b, &a_lits, &fd.cnt[..park.len()], &park, hl[0], &dirty, true); }
        else { for (i, &x) in park.iter().enumerate() { b.cswap(pd.unwrap(), fd.cnt[i], x); } }
        if let Some(d) = pd { mc_xor_dn(b, &[], d, &[], &dirty, fd, cp.l0, true); }
        if ph_free && !ctrl { b.x(fd.ph); }
    });
    b.allow_booth = old_booth;
    b.no_rows = old_rows;
    assert!(!ctrl || ctl_out.is_some(), "a controlled map needs the sy-free lean path");
    MAP_PH_OUT.with(|c| c.set(ph_out));
    MAP_SWPH.with(|c| c.set(swph));
    (r, ctl_out)
}

/// agent_lowq_quot: done flag d ^= A & cnt != 0 (A = ph & Q[RA..ctop) == 0; a done shot has cnt >= 1, every shot
/// that is not done and passes A has Q < 2^RA, so its counter lanes are clean)
pub(crate) fn map_done_flag(b: &mut B, fd: &Fd, cp: &ColPar, d: QubitId, dirty: &[QubitId]) {
    let q = &fd.q;
    let ctop = q.len() - fd.cnt.len();
    let mut a: Vec<(QubitId, bool)> = vec![(fd.ph, false)];
    a.extend((RA..ctop).map(|l| (q[l], true)));
    super::mask::mc_xor(b, &a, d, &[], dirty);
    a.extend(fd.cnt[..cp.cntw.max(1)].iter().map(|&x| (x, true)));
    super::mask::mc_xor(b, &a, d, &[], dirty);
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
        // (agent_lowq_quot: a done shot skipped the controlled-map columns after it finished, so B0 = [cnt even] ^
        // [an odd count of those]: a toggle per counter value with an odd count)
        let dirty = sc.dirty.clone();
        let b0_flag = |b: &mut B| {
            b.cx(fd.cnt[0], sc.sw);
            b.x(sc.sw);
            for v in 1..(1usize << fd.cnt.len()) {
                if map_ctrl_skipped(v) % 2 == 1 {
                    let lits: Vec<(QubitId, bool)> = fd.cnt.iter().enumerate().map(|(i, &x)| (x, (v >> i) & 1 == 0))
                        .collect();
                    super::mask::mc_xor(b, &lits, sc.sw, &[], &dirty);
                }
            }
        };
        b0_flag(b);
        // B0's N277/EMAX22 ordinary map uses bq and Q[120] as extension lanes.
        // The returned pool g owner is the controlled replay helper here.
        b.play_ctrl(&ms_rec, sc.sw, sc.g);
        std::mem::swap(&mut fd.sy, &mut fd.sx);
        // shots that skipped the map (not B0) keep their size in the (renamed) sx register: swap back
        b.x(sc.sw);
        for i in 0..fd.sy.len() {
            b.cswap(sc.sw, fd.sy[i], fd.sx[i]);
        }
        b.x(sc.sw);
        b0_flag(b);
    }
    // every shot is A0 = (t_{N-1}, R, 1); R stays in Q (no last middle): the payload's last level uses q = R directly
    if let Some(pl) = pl {
        let sc = carve(&fd.sx);
        super::payload::pl_end(b, fd, cpl, &sc, pl);
    }
}

/// the lane order a register has after `steps` doubling relabels (pop top, insert at 0)
pub(crate) fn rotated(v: &[QubitId], steps: usize) -> Vec<QubitId> {
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
