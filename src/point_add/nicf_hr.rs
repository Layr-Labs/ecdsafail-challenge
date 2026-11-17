//! Floor-form NICF in HR (FD_FUSEHR=1, prefix FD_CF): a fused HR column also takes the next RCF step when its
//! quotient is 1, landing on level j + 2. Spec: golden-walk/pareto-drop/BUILD.md S1. Pieces (each gated by the
//! column's HR-active literals):
//!   decide   (stage 4, P alive, Q = Y): o ^= [rho + bq yd - (yd >> 1) - 1 >= Xh]  (= [2u > yd], u = rho - Xh + bq yd)
//!   fused add (stage 5 end): T += o Y
//!   map      : Z <- p - Z X (unfused) or Z X - p (fused) before the division (MAP_NEG hook in frogdrop::map_upto)
//!   qfix     (post-map, Q = t_k, top = T): Q <- T - Q where o
//!   erase    (post-map): o ^= golden(Q, top) (column 0: [Q >= 2]), 32-bit windows, conditional Fibonacci iteration
//! DEV lanes: FZ holds fresh qubits outside the pool (width grows); they are mapped onto pool lanes later.

use super::builder::{B, G};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// golden-erase window bits and iteration cap (the predictor's golden_iter must use the same)
pub fn gw() -> usize { super::frogdrop_sched::gw() }
pub fn gl() -> usize { super::frogdrop_sched::gl() }
const CB: usize = 5;
/// no dev bank any more: every lane of the fused column is a real lane (FIT.md F2)
pub const FZ_LANES: usize = 0;

thread_local! {
    pub static FZ: std::cell::RefCell<Vec<QubitId>> = std::cell::RefCell::new(vec![]);
    /// set around the map of a fused column: the fuse flag that negates the map's numerator
    pub static MAP_NEG: std::cell::Cell<Option<QubitId>> = std::cell::Cell::new(None);
}
pub fn fz() -> Vec<QubitId> { FZ.with(|x| x.borrow().clone()) }
thread_local! {
    /// fused-step parity of the current traversal (1/dx = (-1)^N t_{N-1} and N = columns + fused steps + ...): toggled by
    /// o in every fused column; after the forward traversal it holds cnt[0] ^ parity (the sign control)
    pub static FZP: std::cell::Cell<Option<QubitId>> = std::cell::Cell::new(None);
}
pub fn fzp() -> Option<QubitId> { FZP.with(|c| c.get()) }
pub fn map_neg() -> Option<QubitId> { MAP_NEG.with(|m| m.get()) }
pub fn set_map_neg(o: Option<QubitId>) { MAP_NEG.with(|m| m.set(o)) }

/// debug: NICF_SKIP=decide,add,map,qfix,erase disables pieces (the column is then wrong, but phase-clean pieces show)
pub fn skip(piece: &str) -> bool { std::env::var("NICF_SKIP").map_or(false, |v| v.split(',').any(|x| x == piece)) }

fn rec<F: FnOnce(&mut B)>(b: &mut B, f: F) -> Vec<G> { b.begin(); f(b); b.end() }

/// t -= a  as ~(~t + a) (a restored); `ctl` conditions the change
fn sub_ttk(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: Option<QubitId>) {
    for &x in t { b.x(x); }
    super::arith::ttk_add(b, a, t, ctl, None);
    for &x in t { b.x(x); }
}

/// Stage 4 (after bcmp and the swap back: Q = Y, ring top = X; P alive; bq valid).
/// `swap` = the column's masked middle swap (an involution), `rho` = P's rho lanes in the post-P frame,
/// `one` = a |1> lane, `gate` = HR-active literals (+ column-0 rule).
/// Payload e' decision inputs: (payload lanes p, sz register, sz range, ring, borrowed lanes for the p rotation)
pub struct Ef<'a> { pub ep: QubitId, pub p: &'a [QubitId], pub sz: &'a [QubitId], pub sz_rng: (usize, usize), pub ring: &'a [QubitId], pub pdirty: &'a [QubitId] }

/// t += a mod 2^n (a restored), k ^= carry_out(t + a): ttk_add's flag form without a control. 2n - 1 Toffoli.
fn add_flag(b: &mut B, a: &[QubitId], t: &[QubitId], k: QubitId) {
    let n = t.len();
    assert!(a.len() == n && n >= 2);
    for i in 1..n { b.cx(a[i], t[i]); }
    b.cx(a[n - 1], k);
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    b.ccx(t[n - 1], a[n - 1], k);
    for i in (1..n).rev() { b.cx(a[i], t[i]); b.ccx(t[i - 1], a[i - 1], a[i]); }
    for i in 1..n - 1 { b.cx(a[i], a[i + 1]); }
    b.cx(a[0], t[0]);
    for i in 1..n { b.cx(a[i], t[i]); }
}

/// One restoring-division step in place: r (nb lanes, LSB first, r <= div) <- 2 r - b div, b = [2 r >= div], for the
/// odd divisor div = 2 m + 1 (m: nb - 1 lanes). The top lane ends holding b and becomes the new LSB lane (relabel):
/// r_low <- r_low - m - 1 with the carry into the top lane (top = b), restored where b = 0. 5 (nb - 1) - 3 Toffoli.
fn ls_step(b: &mut B, r: &mut Vec<QubitId>, m: &[QubitId]) {
    let nb = r.len();
    assert_eq!(m.len(), nb - 1);
    let top = r[nb - 1];
    let low: Vec<QubitId> = r[..nb - 1].to_vec();
    for &x in m { b.x(x); }
    add_flag(b, m, &low, top);
    b.x(top);
    sub_ttk(b, m, &low, Some(top));
    b.x(top);
    for &x in m { b.x(x); }
    r.pop();
    r.insert(0, top);
}

/// Q = X (the column's middle-swapped frame): rho[0..kp] -= Xh (`undo`: += Xh), Xh = the top kp lanes of Q rotated by sy.
pub fn rho_xh(b: &mut B, q: &[QubitId], sy: &[QubitId], sy_rng: (usize, usize), kp: usize, rho: &[QubitId],
              dirty: &[QubitId], undo: bool) {
    use super::frogdrop::rot_by_range_care;
    if skip("decide") { return; }
    let nq = q.len();
    let dest: BTreeSet<usize> = (nq - kp..nq).collect();
    let (lo, hi) = (sy_rng.0.min(nq - 1), sy_rng.1.min(nq - 1));
    let r = rec(b, |b| {
        rot_by_range_care(b, q, sy, lo, hi, true, dirty, &dest);
        sub_ttk(b, &q[nq - kp..nq], &rho[..kp], None);
        rot_by_range_care(b, q, sy, lo, hi, false, dirty, &dest);
    });
    b.play(&r, undo);
}

/// lean e' window bits = lockstep steps (the predictor's ep_lean must use the same)
pub const LW: usize = 20;

/// Lean decision (FIT.md F1). u = rho - Xh + bq yd is formed in rho[0..kp] in place (mod 2^kp, exact: 0 <= u < yd);
/// one division step of u by yd = 2 Yh[1..] + 1 leaves o = [2u >= yd] in its LSB lane. Payload e' = [d/z >= u/yd]:
/// lockstep steps of u by yd and of dw (payload window, rotated by sz, in place) by zd = 2 Zw[1..] + 1 (ring window);
/// tracker c = index of the first differing quotient bit (transposition 0 <-> i, no flag lane); e' = that step's b2,
/// a tie reads 1. `scr`: 4 lanes clean between the swap plays (tracker c[0..4], c[0] also the |1> of the bq yd add);
/// c[4] is Q's lane 0 in the rotated frame (zero: bl(Y) <= nq - 1 in a fusing column). No other scratch.
pub fn decide(b: &mut B, q: &[QubitId], sy: &[QubitId], sy_rng: (usize, usize), kp: usize, rho: &[QubitId], bq: QubitId,
              o: QubitId, gate: &[(QubitId, bool)], dirty: &[QubitId], ef: Option<&Ef>, scr: &[QubitId]) {
    use super::frogdrop::rot_by_range_care;
    use super::mask::mc_xor;
    if skip("decide") { return; }
    let nq = q.len();
    let mut dest: BTreeSet<usize> = (nq - kp..nq).collect();
    dest.insert(0);
    let (lo, hi) = (sy_rng.0.min(nq - 1), sy_rng.1.min(nq - 1));
    assert!(scr.len() >= 4);
    let mut c: Vec<QubitId> = scr[..4].to_vec();
    c.push(q[0]);
    let top: Vec<QubitId> = q[nq - kp..nq].to_vec();
    let mut r1: Vec<QubitId> = rho[..kp].to_vec();
    let m1: Vec<QubitId> = top[1..].to_vec();
    let ep = ef.map(|e| e.ep);
    let (mut r2, mut m2): (Vec<QubitId>, Vec<QubitId>) = (vec![], vec![]);
    if let Some(e) = ef {
        let (np, nr) = (e.p.len(), e.ring.len());
        r2 = e.p[np - LW..np].to_vec();
        m2 = e.ring[nr - LW + 1..nr].to_vec();
    }
    // borrowed lanes of the tracker toggles: Q lanes outside the windows (no operand; the caller's `dirty` may hold the payload)
    let mdirty: Vec<QubitId> = q[1..nq - kp].iter().copied().take(10).collect();
    let pre = rec(b, |b| {
        // (rho -= Xh was done by the caller in its Q = X frame: rho_xh)
        // Q = Y: rho += bq yd, yd = [1, Yh[1..]]
        rot_by_range_care(b, q, sy, lo, hi, true, dirty, &dest);
        b.x(c[0]);
        let mut yd: Vec<QubitId> = vec![c[0]];
        yd.extend_from_slice(&m1);
        super::arith::ttk_add(b, &yd, &rho[..kp], Some(bq), None);
        b.x(c[0]);
        if let Some(e) = ef {
            let (np, nr) = (e.p.len(), e.ring.len());
            let dp: BTreeSet<usize> = (np - LW..np).collect();
            rot_by_range_care(b, e.p, e.sz, e.sz_rng.0, e.sz_rng.1.min(np - 1), true, e.pdirty, &dp);
            let dr: BTreeSet<usize> = (nr - LW..nr).collect();
            rot_by_range_care(b, e.ring, e.sz, e.sz_rng.0, e.sz_rng.1.min(nr - 1), true, dirty, &dr);
        }
    });
    b.play(&pre, false);
    let s1 = { let mut r = r1.clone(); let g = rec(b, |b| ls_step(b, &mut r, &m1)); r1 = r; g };
    b.play(&s1, false);
    let mut lits = vec![(r1[0], false)];
    lits.extend_from_slice(gate);
    mc_xor(b, &lits, o, &[], &mdirty);
    if let Some(ep) = ep {
        // steps 1..LW of stream 2, 2..LW of stream 1, tracker after each
        let emit = |b: &mut B, wr: bool, r1: &[QubitId], r2: &[QubitId]| {
            let (mut r1, mut r2) = (r1.to_vec(), r2.to_vec());
            for i in 1..=LW {
                if i > 1 { ls_step(b, &mut r1, &m1); }
                ls_step(b, &mut r2, &m2);
                let (b1, b2) = (r1[0], r2[0]);
                let k = i.trailing_zeros() as usize;
                b.cx(b1, b2);
                for j in 0..5 { if j != k && (i >> j) & 1 == 1 { b.cx(c[k], c[j]); } }
                let mut l: Vec<(QubitId, bool)> = vec![(b2, false)];
                l.extend((0..5).filter(|&j| j != k).map(|j| (c[j], true)));
                mc_xor(b, &l, c[k], &[], &mdirty);
                if wr {
                    let mut l: Vec<(QubitId, bool)> = vec![(c[k], false), (b1, true), (o, false)];
                    l.extend((0..5).filter(|&j| j != k).map(|j| (c[j], true)));
                    mc_xor(b, &l, ep, &[], &mdirty);
                }
                for j in 0..5 { if j != k && (i >> j) & 1 == 1 { b.cx(c[k], c[j]); } }
                b.cx(b1, b2);
            }
            if wr {
                let mut l: Vec<(QubitId, bool)> = vec![(o, false)];
                l.extend(c.iter().map(|&x| (x, true)));
                mc_xor(b, &l, ep, &[], &mdirty);
            }
        };
        emit(b, true, &r1, &r2);
        let un = rec(b, |b| emit(b, false, &r1, &r2));
        b.play(&un, true);
    }
    b.play(&s1, true);
    b.play(&pre, true);
}

/// Map hook (inside map_upto, right after p_minusf: region value L = p - W mod 2^min(cut, 256), W = Z X mod 2^cut):
/// where o, negate L mod 2^min(cut,256) (= W - p) and clear lane 256 on shots with cut > 256 (there W >= 2^256:
/// W - p = r_{j+2} t_j >= 2^33 in every fusing column). Increment carries cut `inc_len` lanes (v2(W - p) is small).
pub fn map_negate(b: &mut B, v: &[QubitId], cut: &super::frogdrop::Cut, clo: usize, chi: usize, o: QubitId,
                  f: QubitId, pre: &[QubitId], tmp: QubitId, one: QubitId, dirty: &[QubitId], inc_len: usize) {
    use super::frogdrop::{walk_cutf, walk_cutf_capped};
    if skip("map") { return; }
    for l in 0..clo.min(256) { b.cx(o, v[l]); }
    if chi <= 256 {
        walk_cutf(b, cut, clo, chi, f, pre, tmp, dirty, |b, l, f| b.ccx(f, o, v[l]));
    } else {
        walk_cutf_capped(b, cut, clo, 256, f, pre, tmp, dirty, |b, l, f| b.ccx(f, o, v[l]));
    }
    // + o: increment the register [o] ++ v[0..m] (o as bit 0), then flip o back
    let m = inc_len.min(clo.min(256));
    let mut x = vec![o];
    x.extend_from_slice(&v[..m]);
    let g: Vec<QubitId> = dirty.iter().copied().filter(|d| !x.contains(d) && *d != one).take(x.len()).collect();
    assert_eq!(g.len(), x.len(), "map_negate: not enough borrowed lanes");
    super::modp_frogdrop::inc_dirty(b, &x, &g, one);
    b.x(o);
    // lane 256 (W_hi = 1) cleared on fused shots whose region extends past 256
    if chi > 256 {
        cut.ge(b, 257, f, pre); // f = [cut >= 257]
        b.ccx(f, o, v[256]);
        cut.ge(b, 257, f, pre);
    }
}

/// Post-map: Q = t_k, ring top = T (bit i at ring[n-1-i], bl(T) = sy). Where o: Q <- T - Q = ~(Q + ~T) on the lanes
/// l < bl(T) only (masked ripple: the ring lanes past bl(T) hold the gap / Z and are never written from).
/// `bank`: 15 clean lanes; `dirty`: borrowed lanes outside Q and the ring top.
pub fn qfix(b: &mut B, ring: &[QubitId], q: &[QubitId], sy: &[QubitId], smax: (usize, usize), o: QubitId,
            bank: &[QubitId], dirty: &[QubitId]) {
    use super::frogdrop::Cut;
    if skip("qfix") { return; }
    let n = ring.len();
    let hi = smax.1.min(q.len());
    let lo = smax.0.min(hi);
    let t: Vec<QubitId> = q[..hi].to_vec();
    let s: Vec<QubitId> = (0..hi).map(|i| ring[n - 1 - i]).collect();
    let cut = Cut { v: sy.to_vec(), a: 0, neg: false };
    super::payload::reflect_masked(b, &t, &s, o, sy, smax.1, false, &cut, lo, bank[0], bank[1], bank[2], &bank[3..11],
                                   bank[11], &bank[3..15], dirty);
}

/// Post-fix erase, column 0: o ^= gate & [Q >= 2] (Q = t_1 = 1 unless fused); Q's live lanes are [0, m).
pub fn erase0(b: &mut B, q: &[QubitId], m: usize, gate: &[(QubitId, bool)], o: QubitId, tmp: &[QubitId], dirty: &[QubitId]) {
    if skip("erase") { return; }
    super::mask::mc_xor(b, gate, o, tmp, dirty);
    let mut lits: Vec<(QubitId, bool)> = gate.to_vec();
    lits.extend((1..m.min(q.len())).map(|i| (q[i], true)));
    super::mask::mc_xor(b, &lits, o, tmp, dirty); // gate & [Q < 2]
}

/// [S > T] carry ladder (t, s equal length; s holds the carry lanes), restored by `dn`. Returns (up, dn, carry lane).
fn cmp_gt(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId) -> (Vec<G>, Vec<G>, QubitId) {
    use super::arith::{down_m, up_m, Dm};
    let up = up_m(b, t, s, c0, true);
    let dn = down_m(b, t, s, c0, Dm::Restore, true);
    (up, dn, s[s.len() - 1])
}

/// Post-fix erase, later fusing columns: o ^= gate & golden(x, y), x = Q (t_{m-1}), y = ring top (t_m, bl = sy).
/// Windows: bits [sy - GW, sy) of both (zeros below bit 0). x in place (Q rotated down by sy), y copied into ty by
/// decoder reads of the ring top. Then up to GL steps (x, y) <- (y - x, x) while y/2 < x < y (counter cnt, one-hot
/// step condition), result = parity(cnt) ^ [2x > y]; everything but o is uncomputed.
#[allow(non_snake_case)]
pub fn erase_golden(b: &mut B, ring: &[QubitId], q: &[QubitId], sy: &[QubitId], sy_rng: (usize, usize),
                    gate: &[(QubitId, bool)], o: QubitId, bank: &[QubitId], dirty: &[QubitId]) {
    use super::frogdrop::rot_by_range_care;
    use super::mask::mc_xor;
    if skip("erase") { return; }
    let (GW, GL) = (gw(), gl());
    // bank (51): ty (GW) | cnt (CB) | cond, c1, c2, gc0 | z0, z1 | pre (7) | tmp (1)
    assert!(bank.len() >= GW + CB + 4 + 2 + 7 + 1, "golden erase bank: {} lanes", bank.len());
    struct Gl { o: QubitId, ty: Vec<QubitId>, cnt: Vec<QubitId>, cond: QubitId, c1: QubitId, c2: QubitId, gc0: QubitId,
                z: [QubitId; 2], pre: Vec<QubitId>, tmp: Vec<QubitId> }
    let g0 = GW + CB;
    let l = Gl { o, ty: bank[..GW].to_vec(), cnt: bank[GW..g0].to_vec(), cond: bank[g0], c1: bank[g0 + 1], c2: bank[g0 + 2],
                 gc0: bank[g0 + 3], z: [bank[g0 + 4], bank[g0 + 5]], pre: bank[g0 + 6..g0 + 13].to_vec(),
                 tmp: bank[g0 + 13..].to_vec() };
    let (n, nq) = (ring.len(), q.len());
    let (lo, hi) = (sy_rng.0.min(nq), sy_rng.1.min(nq));
    let dest: BTreeSet<usize> = (nq - GW..nq).collect();
    let body = rec(b, |b| {
        rot_by_range_care(b, q, sy, lo, hi, true, dirty, &dest);
        // ty[i] = bit (sy - GW + i) of the ring top
        for i in 0..GW {
            super::payload::read_lane(b, sy, lo, hi, &|v: usize| {
                if v + i >= GW { let bit = v + i - GW; if bit < n { Some(ring[n - 1 - bit]) } else { None } } else { None }
            }, false, &[], l.ty[i], &l.pre, &l.tmp, dirty);
        }
        let x: Vec<QubitId> = q[nq - GW..nq].to_vec();
        let y = l.ty.clone();
        // padded views: x2 = 2x (GW + 1 lanes: cz, x...), yp = y ++ [c2-free zero]: use z lanes as pads
        let mut x2: Vec<QubitId> = vec![l.z[0]];
        x2.extend_from_slice(&x);
        let mut yp: Vec<QubitId> = y.clone();
        yp.push(l.z[1]);
        for i in 0..GL {
            // c1 = [x < y]  ([S > T] with T = x, S = y)
            let (u1, d1, k1) = cmp_gt(b, &x, &y, l.gc0);
            b.play(&u1, false); b.cx(k1, l.c1); b.play(&d1, false);
            // cond ^= [cnt == i] & c1 & [2x > y]  ([S > T] with T = yp, S = x2)
            let (u2, d2, k2) = cmp_gt(b, &yp, &x2, l.gc0);
            b.play(&u2, false);
            let mut lits: Vec<(QubitId, bool)> = (0..CB).map(|k| (l.cnt[k], (i >> k) & 1 == 0)).collect();
            lits.push((l.c1, false));
            lits.push((k2, false));
            mc_xor(b, &lits, l.cond, &l.tmp, dirty);
            b.play(&d2, false);
            // uncompute c1 (x, y unchanged so far)
            b.play(&u1, false); b.cx(k1, l.c1); b.play(&d1, false);
            // step where cond: x <- y - x = ~(x + ~y); y <- y - x_new
            for &t in &y { b.x(t); }
            super::arith::ttk_add(b, &y, &x, Some(l.cond), None);
            for &t in &y { b.x(t); }
            for &t in &x { b.cx(l.cond, t); }
            sub_ttk(b, &x, &y, Some(l.cond));
            // cnt: i -> i + 1 where cond (flip the differing bits), then cond ^= [cnt == i + 1]
            for k in 0..CB { if ((i ^ (i + 1)) >> k) & 1 == 1 { b.cx(l.cond, l.cnt[k]); } }
            let lits: Vec<(QubitId, bool)> = (0..CB).map(|k| (l.cnt[k], ((i + 1) >> k) & 1 == 0)).collect();
            mc_xor(b, &lits, l.cond, &l.tmp, dirty);
        }
        // c2 = [2x > y] on the final pair
        let (u2, d2, k2) = cmp_gt(b, &yp, &x2, l.gc0);
        b.play(&u2, false); b.cx(k2, l.c2); b.play(&d2, false);
    });
    b.play(&body, false);
    let mut g1: Vec<(QubitId, bool)> = gate.to_vec();
    g1.push((l.cnt[0], false));
    mc_xor(b, &g1, l.o, &l.tmp, dirty);
    let mut g2: Vec<(QubitId, bool)> = gate.to_vec();
    g2.push((l.c2, false));
    mc_xor(b, &g2, l.o, &l.tmp, dirty);
    b.play(&body, true);
}
