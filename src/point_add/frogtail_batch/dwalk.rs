//! lowq-rho (2026-11-04), one-tape-bit walk wired into the Lilypad shell. Not for submission as is.
//! Forced-digit tick on rails plus integer cofactors. Every digit is read and erased from cofactor low lanes by CX;
//! deep/flat is one tape wire per tick; the shift letter comes from low lanes (S6 barrel, source: round 61/62 rail word).
//! End state: rails +-1, U1 = s0 p + s0 s1 U0 cleared by one row, U0 << D with D = E_INIT - sum(shift letters), then the
//! shell's reduce. 1/dx = (-1)^key U0 2^(D) 2^-H0, H0 = R (M + 1) + E_INIT, key = s0 ^ refl.
use super::builder::{B, ONE};
use super::modp_ft::{add_sext, ctrl_add_pool, ctrl_neg, sub_sext, Ms};
use super::rail_s6::rail_s6_barrel_g;
use crate::circuit::{BitId, QubitId as Q};

pub const ON: bool = true;
pub const M: usize = 3;
pub const R: usize = 110;
pub const CAPV: usize = 6;
pub const LW: usize = 36;
pub const MG: usize = 0;
pub const GOV: usize = 30;
pub const GS: usize = 5;
/// D = E_INIT - E on DB lanes; D is the integer shift of U0 before the reduce.
pub const E_INIT: usize = 180;
pub const DB: usize = 7;
/// lanes of U0 << D
pub const W_SH: usize = 384;
/// paired carry debts on rows of ticks below this (phase garbage above it is unresolved)
pub const PAIR_T: usize = 10000;
/// lanes at the top of a row that can be sign copies on a shot
pub const SIGN_TOP: usize = 100000;
/// last ticks use fewer digit rows: cofactors grow less on idle ticks. Digit count only falls, so the source cofactor keeps at least m + 1 low zeros.
pub const TA: usize = 99;
pub const T1: usize = 103;
pub const M2: usize = 1;
pub const RFLOOR: usize = 7;
pub const T2: usize = 106;
#[inline] pub const fn mt(t: usize) -> usize { if t < TA { M } else if t < T1 { 2 } else if t < T2 { M2 } else { 0 } }
pub const K0: usize = TA * (M + 1) + (T1 - TA) * 3 + (T2 - T1) * (M2 + 1) + (R - T2);
/// The tape bit only serves the next tick's decode, and only when its digit count equals this tick's.
#[inline] pub const fn tape_drop(t: usize) -> bool { t + 1 >= R || mt(t + 1) != mt(t) }
/// split walk (late drop): 0 = off. Clear U_d before tick T0, sub-walk on rails with own cofactors, Final by division.
pub const T0: usize = 0;
/// REDC steps on beta. x0 = (R - T0)(M + 1) - RS >= 0 public part of the shift of U_k.
pub const RS: usize = 88;
/// |Z| < 2^I0, Z lanes I0 + 1
pub const I0: usize = 258;
pub const DB2: usize = 7;
/// run the sub-walk back before the products: junk = rails at T0, no sub tape
pub const UNSUB: bool = true;
pub const H0: usize = K0 + E_INIT - if T0 > 0 { RS } else { 0 };
const TAB: &str = include_str!("dwalk_tab.txt");

pub fn tab() -> Vec<[usize; 5]> {
    TAB.lines().map(|l| { let v: Vec<usize> = l.split_whitespace().map(|x| x.parse().unwrap()).collect(); [v[0], v[1], v[2], v[3], v[4]] }).collect()
}
#[cfg(test)]
thread_local! { pub(crate) static MARKS: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) }; }
#[cfg(test)]
thread_local! { pub(crate) static IMARKS: std::cell::RefCell<Vec<(usize, &'static str, usize)>> = const { std::cell::RefCell::new(Vec::new()) }; }
#[allow(unused_variables)]
fn imark(b: &B, t: usize, name: &'static str) {
    #[cfg(test)]
    IMARKS.with(|m| m.borrow_mut().push((t, name, b.ops.len())));
}
/// lane moves of one tick's fit, for the exact mirror
type Log = Vec<(usize, Q, bool)>;
pub struct DwEnd {
    tape: Vec<Q>,
    dc: Vec<Q>,
    refl: Q,
    s0: Q,
    s1: Q,
    r0low: Vec<Q>,
    r1low: Vec<Q>,
    u0: Vec<Q>,
    u1: Vec<Q>,
    ext: Vec<Q>,
    logs: Vec<Log>,
    div: usize,
    wc_end: usize,
    sp: Option<Sp>,
    nsm: Option<(Vec<BitId>, Vec<Vec<BitId>>)>,
}
/// split-walk leftovers
pub struct Sp {
    sr: Q,
    zw: Q,
    dc2: Vec<Q>,
    clr: ClearRec,
    uk_ids: Vec<Q>,
    u_slots: [Vec<Q>; 2],
    b0: Vec<Q>,
    rho: Vec<Q>,
    rho_hi: Vec<Q>,
    nn_zero: Vec<Q>,
    nn_ext: Vec<Q>,
    win_low: Vec<Q>,
    z_lanes: Vec<Q>,
    m0: Vec<BitId>,
    ms: Vec<Vec<BitId>>,
    rails: Option<[Vec<Q>; 2]>,
    rails_t0: [Vec<Q>; 2],
}
pub struct ClearRec { y: Vec<Q>, zz: Q }
pub fn key_of(e: &DwEnd) -> Q { if let Some(sp) = &e.sp { sp.sr } else { e.s0 } }
pub fn inv_of(e: &DwEnd) -> Vec<Q> { e.u0.clone() }

fn cap() -> u64 { super::pointadd_lilypad::peak() }

fn fit(b: &mut B, l: &mut [Vec<Q>; 4], idx: usize, w: usize, log: &mut Log) {
    let v = &mut l[idx];
    while v.len() < w { let q = b.alloc(); let top = *v.last().unwrap(); b.cx(top, q); v.push(q); log.push((idx, q, true)); }
    while v.len() > w { let q = v.pop().unwrap(); let top = *v.last().unwrap(); b.cx(top, q); b.free(q); log.push((idx, q, false)); }
}
fn unfit(b: &mut B, l: &mut [Vec<Q>; 4], log: &Log) {
    for &(idx, q, grew) in log.iter().rev() {
        let v = &mut l[idx];
        if grew { let x = v.pop().unwrap(); assert_eq!(x, q); let top = *v.last().unwrap(); b.cx(top, q); b.free(q); }
        else { b.acquire(q); let top = *v.last().unwrap(); b.cx(top, q); v.push(q); }
    }
}
/// As unfit, but lanes may come back on any wire (the shrunk lane's old wire can be busy).
fn unfit_any(b: &mut B, l: &mut [Vec<Q>; 4], log: &Log) {
    for &(idx, _q, grew) in log.iter().rev() {
        let v = &mut l[idx];
        if grew { let x = v.pop().unwrap(); let top = *v.last().unwrap(); b.cx(top, x); b.free(x); }
        else { let q = b.alloc(); let top = *v.last().unwrap(); b.cx(top, q); v.push(q); }
    }
}
/// Move lanes onto the listed wires by swaps (0 T).
fn remap(b: &mut B, a: &mut Vec<Q>, target: &[Q]) {
    assert_eq!(a.len(), target.len());
    for i in 0..a.len() {
        if a[i] == target[i] { continue; }
        if let Some(k) = a.iter().position(|&q| q == target[i]) {
            b.swap(a[i], a[k]);
            a.swap(i, k);
        } else {
            b.acquire(target[i]);
            b.swap(a[i], target[i]);
            b.free(a[i]);
            a[i] = target[i];
        }
    }
}
/// tgt += (-1)^neg src mod 2^len (inv: the exact inverse), pool = every clean lane up to cap, paired carry debts between traversals
fn row(b: &mut B, src: &[Q], tgt: &[Q], neg: Q, inv: bool, key: Option<(usize, usize)>) {
    use super::chunked::{self, AddRole, Pair, PairKey};
    let n = tgt.len();
    let room = cap().saturating_sub(b.live) as usize;
    let pool = b.alloc_n(room.min(n));
    if inv { b.begin(); }
    for &q in tgt { b.cx(neg, q); }
    let mut done = n == 1;
    if n == 1 { b.cx(src[0], tgt[0]); }
    if !done {
        if let Some((division, tick)) = key {
            let k = PairKey { division, tick, role: AddRole::Value };
            if !inv || b.has_chunk_debts(k) {
                let pair = if inv { Pair::Inverse(k) } else { Pair::Forward(k) };
                if chunked::try_add_paired_cin(b, &src[..n], tgt, ONE, None, None, &pool, Some(pair)) { done = true; }
                else { assert!(!inv, "paired inverse must expose every carry position"); }
            }
        }
    }
    if !done { ctrl_add_pool(b, &src[..n], tgt, ONE, &pool); }
    for &q in tgt { b.cx(neg, q); }
    if inv {
        let r = b.end();
        if key.is_some() { super::chunked::DW_SAFE.with(|c| c.set(n.saturating_sub(SIGN_TOP).max(1))); }
        b.play(&r, true);
        super::chunked::DW_SAFE.with(|c| c.set(0));
    }
    b.free_n(&pool);
}
/// k ^= letter of l: low lanes of 2^e odd, e in 0..=CAPV-1. Temps return by measurement.
fn letter(b: &mut B, l: &[Q], k: &[Q; 3], temps: &[Q]) {
    let nz = CAPV - 2;
    let extra = nz.saturating_sub(temps.len());
    let more = b.alloc_n(extra);
    let z: Vec<Q> = temps.iter().copied().chain(more.iter().copied()).take(nz).collect();
    for &q in &l[..nz + 1] { b.x(q); }
    b.and_c(l[0], l[1], z[0]);
    for i in 1..nz { b.and_c(z[i - 1], l[i + 1], z[i]); }
    // l[0] (flipped) = e >= 1, z[i] = e >= i + 2
    b.cx(l[0], k[0]);
    for i in 0..nz { b.cx(z[i], k[0]); }
    b.cx(z[0], k[1]); b.cx(z[2], k[1]);
    b.cx(z[2], k[2]);
    for i in (1..nz).rev() { b.and_u(z[i - 1], l[i + 1], z[i]); }
    b.and_u(l[0], l[1], z[0]);
    for &q in &l[..nz + 1] { b.x(q); }
    b.free_n(&more);
}
/// dc += (sub ? -e : e), e = k1 + 2 k2 + 4 k3 (mod 2^DB). DB - 1 ANDs on temps.
fn counter(b: &mut B, dc: &[Q], k: &[Q; 3], sub: bool, temps: &[Q]) {
    let n = dc.len();
    let extra = (n - 1).saturating_sub(temps.len());
    let more = b.alloc_n(extra);
    let t: Vec<Q> = temps.iter().copied().chain(more.iter().copied()).take(n - 1).collect();
    if sub { for &q in dc { b.x(q); } }
    b.and_c(k[0], dc[0], t[0]);
    for i in 1..3 {
        b.cx(t[i - 1], k[i]); b.cx(t[i - 1], dc[i]);
        b.and_c(k[i], dc[i], t[i]);
        b.cx(t[i - 1], t[i]);
    }
    for i in 3..n - 1 { b.and_c(dc[i], t[i - 1], t[i]); }
    b.cx(t[n - 2], dc[n - 1]);
    for i in (3..n - 1).rev() { b.and_u(dc[i], t[i - 1], t[i]); b.cx(t[i - 1], dc[i]); }
    for i in (1..3).rev() {
        b.cx(t[i - 1], t[i]);
        b.and_u(k[i], dc[i], t[i]);
        b.cx(t[i - 1], k[i]);
        b.cx(k[i], dc[i]);
    }
    b.and_u(k[0], dc[0], t[0]);
    b.cx(k[0], dc[0]);
    if sub { for &q in dc { b.x(q); } }
    b.free_n(&more);
}
/// Compare without carry temps: carries live on a's lanes (Cuccaro MAJ), one clean wire cw as carry in. 2 CCX per lane against 1 AND per lane.
fn lt_chain_ip(b: &mut B, a: &[Q], c: &[Q], cw: Q) -> Q {
    let mut prev = cw;
    for i in 0..a.len() {
        b.x(a[i]);
        b.cx(a[i], c[i]); b.cx(a[i], prev);
        b.ccx(prev, c[i], a[i]);
        prev = a[i];
    }
    prev
}
fn lt_undo_ip(b: &mut B, a: &[Q], c: &[Q], cw: Q) {
    for i in (0..a.len()).rev() {
        let prev = if i == 0 { cw } else { a[i - 1] };
        b.ccx(prev, c[i], a[i]);
        b.cx(a[i], prev); b.cx(a[i], c[i]);
        b.x(a[i]);
    }
}
fn lt_chain(b: &mut B, a: &[Q], c: &[Q], t: &[Q]) {
    for i in 0..a.len() {
        b.x(a[i]);
        if i > 0 { b.cx(t[i - 1], a[i]); b.cx(t[i - 1], c[i]); }
        b.and_c(a[i], c[i], t[i]);
        if i > 0 { b.cx(t[i - 1], t[i]); }
    }
}
fn lt_undo(b: &mut B, a: &[Q], c: &[Q], t: &[Q]) {
    for i in (0..a.len()).rev() {
        if i > 0 { b.cx(t[i - 1], t[i]); }
        b.and_u(a[i], c[i], t[i]);
        if i > 0 { b.cx(t[i - 1], c[i]); b.cx(t[i - 1], a[i]); }
        b.x(a[i]);
    }
}
fn capped(b: &mut B, tt: &[Q], bb: &[Q], n: Q, out: Q) {
    for i in 2..=CAPV { b.cx(bb[i], tt[i]); b.cx(n, tt[i]); }
    let cz = b.alloc_n(CAPV - 2);
    b.and_c(tt[2], tt[3], cz[0]);
    for i in 4..=CAPV { b.and_c(cz[i - 4], tt[i], cz[i - 3]); }
    b.cx(*cz.last().unwrap(), out);
    for i in (4..=CAPV).rev() { b.and_u(cz[i - 4], tt[i], cz[i - 3]); }
    b.and_u(tt[2], tt[3], cz[0]);
    b.free_n(&cz);
    for i in 2..=CAPV { b.cx(bb[i], tt[i]); b.cx(n, tt[i]); }
}
/// out ^= [rails ahead of the schedule]: the GS lanes above cut on both rails are sign copies.
fn ahead(b: &mut B, tt: &[Q], bb: &[Q], cut: usize, lim: usize, out: Q) {
    let w = tt.len().min(bb.len());
    let (sx, sb) = (tt[w - 1], bb[w - 1]);
    if lim <= cut { b.x(out); return; }
    let mut lits = vec![];
    for i in cut..lim { b.cx(sx, tt[i]); b.x(tt[i]); lits.push(tt[i]); b.cx(sb, bb[i]); b.x(bb[i]); lits.push(bb[i]); }
    let z = b.alloc_n(lits.len() - 1);
    b.and_c(lits[0], lits[1], z[0]);
    for i in 2..lits.len() { b.and_c(z[i - 2], lits[i], z[i - 1]); }
    b.cx(*z.last().unwrap(), out);
    for i in (2..lits.len()).rev() { b.and_u(z[i - 2], lits[i], z[i - 1]); }
    b.and_u(lits[0], lits[1], z[0]);
    b.free_n(&z);
    for i in cut..lim { b.x(tt[i]); b.cx(sx, tt[i]); b.x(bb[i]); b.cx(sb, bb[i]); }
}
/// f ^= flat rule, given X in tt, B in bb, n = [sd = -1]. Same function both directions; every temp returns.
fn flat_rule(b: &mut B, tt: &[Q], bb: &[Q], n: Q, f: Q, anchor: usize) {
    let w = tt.len().min(bb.len());
    let (sx, sb) = (tt[w - 1], bb[w - 1]);
    let cd = b.alloc();
    capped(b, tt, bb, n, cd);
    let ah = b.alloc();
    let cut = anchor.saturating_sub(GOV).max(2);
    let lim = (cut + GS).min(w - 1);
    ahead(b, tt, bb, cut, lim, ah);
    let e = b.alloc();
    b.cx(sx, e); b.cx(sb, e); b.cx(n, e); b.x(e);
    let h = anchor.saturating_sub(LW).min(w.saturating_sub(3));
    let top = (h + LW).min(w - 1);
    let ta: Vec<Q> = (h..top).map(|i| tt[i]).collect();
    let tb: Vec<Q> = (h..top).map(|i| bb[i]).collect();
    for &q in &ta { b.cx(sx, q); }
    for &q in &tb { b.cx(sb, q); }
    let ll = ta.len();
    let z0 = b.alloc(); let z1 = b.alloc();
    let mut a1 = ta.clone(); a1.push(z0);
    let mut c1 = vec![z1]; c1.extend(&tb);
    // Width budget decides per tick: temps (one AND a lane) when the peak allows, else carries on the rail lanes (2 CCX a lane). Same function.
    let need = (ll as u64 + 1) + 5;
    let ip = cap().saturating_sub(b.live) < need;
    let cw = if ip { Some(b.alloc()) } else { None };
    let u1 = b.alloc();
    let t1 = if ip { vec![] } else { b.alloc_n(ll + 1) };
    if let Some(w) = cw {
        let o = lt_chain_ip(b, &a1, &c1, w);
        b.cx(o, u1);
        lt_undo_ip(b, &a1, &c1, w);
    } else {
        lt_chain(b, &a1, &c1, &t1);
        b.cx(t1[ll], u1);
        lt_undo(b, &a1, &c1, &t1);
    }
    b.free_n(&t1);
    let t2 = if ip { vec![] } else { b.alloc_n(ll + 1) };
    // pads z0, z1 are clean again here
    let mut a2 = tb.clone(); a2.push(z0);
    let mut c2 = vec![z1]; c2.extend(&ta);
    let o2c = if let Some(w) = cw { lt_chain_ip(b, &a2, &c2, w) } else { lt_chain(b, &a2, &c2, &t2); t2[ll] };
    let g1 = b.alloc(); let g2 = b.alloc();
    b.and_c(u1, o2c, g1);
    b.and_c(g1, e, g2);
    // f ^= cd or ah or g2 = not (not cd and not ah and not g2)
    let o1 = b.alloc(); let o2 = b.alloc();
    b.x(cd); b.x(ah); b.x(g2);
    b.and_c(cd, ah, o1);
    b.and_c(o1, g2, o2);
    b.cx(o2, f); b.x(f);
    b.and_u(o1, g2, o2);
    b.and_u(cd, ah, o1);
    b.x(cd); b.x(ah); b.x(g2);
    b.free(o1); b.free(o2);
    b.and_u(g1, e, g2);
    b.and_u(u1, o2c, g1);
    b.free(g1); b.free(g2);
    if let Some(w) = cw { lt_undo_ip(b, &a2, &c2, w); } else { lt_undo(b, &a2, &c2, &t2); }
    b.free_n(&t2);
    if let Some(w) = cw {
        let o = lt_chain_ip(b, &a1, &c1, w);
        b.cx(o, u1);
        lt_undo_ip(b, &a1, &c1, w);
        b.free(w);
    } else {
        let t1 = b.alloc_n(ll + 1);
        lt_chain(b, &a1, &c1, &t1);
        b.cx(t1[ll], u1);
        lt_undo(b, &a1, &c1, &t1);
        b.free_n(&t1);
    }
    b.free(u1);
    b.free(z0); b.free(z1);
    for &q in &ta { b.cx(sx, q); }
    for &q in &tb { b.cx(sb, q); }
    b.cx(sx, e); b.cx(sb, e); b.cx(n, e); b.x(e);
    b.free(e);
    ahead(b, tt, bb, cut, lim, ah);
    b.free(ah);
    capped(b, tt, bb, n, cd);
    b.free(cd);
}
fn half(b: &mut B, t: &mut Vec<Q>) { let z = t.remove(0); let top = *t.last().unwrap(); b.cx(top, z); t.push(z); }
fn unhalf(b: &mut B, t: &mut Vec<Q>) { let z = t.pop().unwrap(); let top = *t.last().unwrap(); b.cx(top, z); t.insert(0, z); }
fn shift_up(b: &mut B, u: &mut Vec<Q>, s: usize) { for _ in 0..s { let q = u.pop().unwrap(); let top = *u.last().unwrap(); b.cx(top, q); u.insert(0, q); } }
fn shift_dn(b: &mut B, u: &mut Vec<Q>, s: usize) { for _ in 0..s { let q = u.remove(0); let top = *u.last().unwrap(); b.cx(top, q); u.push(q); } }
fn pk(div: usize, t: usize, i: usize) -> Option<(usize, usize)> {
    let _ = i; let on = t < PAIR_T;
    if on { Some((div, t * 32 + i)) } else { None }
}

fn tick_fwd(b: &mut B, l: &mut [Vec<Q>; 4], tape: &mut Vec<Q>, dc: &[Q], t: usize, q: [usize; 5], div: usize) -> Log {
    let [wr, _r1, wu, wv, anchor] = q;
    let wr = (wr + MG).max(RFLOOR);
    let m = mt(t);
    let wc = wu.max(wv) + MG;
    let a = t & 1;
    let (ir_t, ir_b, iu_t, iu_b) = (a, 1 - a, 2 + a, 3 - a);
    let mut log = vec![];
    fit(b, l, ir_t, wr, &mut log); fit(b, l, ir_b, wr, &mut log); fit(b, l, iu_t, wc, &mut log); fit(b, l, iu_b, wc, &mut log);
    let mut tt = std::mem::take(&mut l[ir_t]);
    let bb = std::mem::take(&mut l[ir_b]);
    let ut = std::mem::take(&mut l[iu_t]);
    let mut ub = std::mem::take(&mut l[iu_b]);
    let d = b.alloc_n(m);
    let mut n = b.alloc();
    let k = b.alloc_n(3);
    let kk = [k[0], k[1], k[2]];
    let f = b.alloc();
    for i in 0..m {
        b.cx(tt[1], d[i]); b.cx(bb[1], d[i]);
        row(b, &bb, &tt, d[i], false, pk(div, t, i));
        half(b, &mut tt);
    }
    b.cx(tt[1], n); b.cx(bb[1], n); b.x(n);
    flat_rule(b, &tt, &bb, n, f, anchor);
    if tape_drop(t) {
        // the final sign holds the bit; the raw sign clears from the lanes
        b.cx(n, f);
        b.x(n); b.cx(bb[1], n); b.cx(tt[1], n);
        b.free(n);
        n = f;
    } else {
        b.cx(f, n);
    }
    row(b, &bb, &tt, n, false, pk(div, t, 8));
    half(b, &mut tt);
    letter(b, &tt[..CAPV], &kk, &[]);
    rail_s6_barrel_g(b, kk, &tt, None, false, false);
    row(b, &ub[..wc - m], &ut[m..], n, false, pk(div, t, 16));
    b.cx(ut[m + 1], n); b.cx(ub[1], n);
    if t > 0 && t != T0 && mt(t - 1) == m { let fp = *tape.last().unwrap(); b.cx(fp, n); }
    for i in (0..m).rev() {
        row(b, &ub[..wc - i], &ut[i..], d[i], false, pk(div, t, 17 + i));
        b.cx(ut[i + 1], d[i]); b.cx(ub[1], d[i]); b.x(d[i]);
    }
    rail_s6_barrel_g(b, kk, &ub, None, true, false);
    shift_up(b, &mut ub, m + 1);
    let mut tmp = d.clone(); tmp.push(n);
    counter(b, dc, &kk, !(T0 > 0 && t >= T0), &tmp);
    letter(b, &ub[m + 1..m + 1 + CAPV], &kk, &tmp);
    b.free_n(&k); b.free(n); b.free_n(&d);
    if !tape_drop(t) { tape.push(f); }
    l[ir_t] = tt; l[ir_b] = bb; l[iu_t] = ut; l[iu_b] = ub;
    log
}
fn tick_inv(b: &mut B, l: &mut [Vec<Q>; 4], tape: &mut Vec<Q>, dc: &[Q], t: usize, q: [usize; 5], div: usize, log: &Log) {
    tick_inv_x(b, l, tape, dc, t, q, div, log, true)
}
#[allow(clippy::too_many_arguments)]
fn tick_inv_x(b: &mut B, l: &mut [Vec<Q>; 4], tape: &mut Vec<Q>, dc: &[Q], t: usize, q: [usize; 5], div: usize, log: &Log, exact: bool) {
    let [wr, _r1, wu, wv, anchor] = q;
    let wr = (wr + MG).max(RFLOOR);
    let m = mt(t);
    let wc = wu.max(wv) + MG;
    let a = t & 1;
    let (ir_t, ir_b, iu_t, iu_b) = (a, 1 - a, 2 + a, 3 - a);
    let mut tt = std::mem::take(&mut l[ir_t]);
    let bb = std::mem::take(&mut l[ir_b]);
    let ut = std::mem::take(&mut l[iu_t]);
    let mut ub = std::mem::take(&mut l[iu_b]);
    assert_eq!((tt.len(), bb.len(), ut.len(), ub.len()), (wr, wr, wc, wc));
    let f = if tape_drop(t) { None } else { Some(tape.pop().unwrap()) };
    let d = b.alloc_n(m);
    let n = b.alloc();
    let k = b.alloc_n(3);
    let kk = [k[0], k[1], k[2]];
    let mut tmp = d.clone(); tmp.push(n);
    letter(b, &ub[m + 1..m + 1 + CAPV], &kk, &tmp);
    imark(b, t, "letter ub");
    counter(b, dc, &kk, T0 > 0 && t >= T0, &tmp);
    imark(b, t, "counter");
    shift_dn(b, &mut ub, m + 1);
    rail_s6_barrel_g(b, kk, &ub, None, false, false);
    imark(b, t, "barrel ub");
    for i in 0..m {
        b.x(d[i]); b.cx(ub[1], d[i]); b.cx(ut[i + 1], d[i]);
        row(b, &ub[..wc - i], &ut[i..], d[i], true, pk(div, t, 17 + i));
        imark(b, t, "cof row");
    }
    if t > 0 && t != T0 && mt(t - 1) == m { let fp = *tape.last().unwrap(); b.cx(fp, n); }
    b.cx(ub[1], n); b.cx(ut[m + 1], n);
    row(b, &ub[..wc - m], &ut[m..], n, true, pk(div, t, 16));
    imark(b, t, "cof top");
    rail_s6_barrel_g(b, kk, &tt, None, true, false);
    imark(b, t, "barrel tt");
    letter(b, &tt[..CAPV], &kk, &[]);
    unhalf(b, &mut tt);
    imark(b, t, "letter tt");
    row(b, &bb, &tt, n, true, pk(div, t, 8));
    imark(b, t, "rail top");
    if let Some(f) = f {
        b.cx(f, n);
        flat_rule(b, &tt, &bb, n, f, anchor);
        b.free(f);
        imark(b, t, "flat rule");
        b.x(n); b.cx(bb[1], n); b.cx(tt[1], n);
    } else {
        // n holds raw + rule: raw from the lanes, the rule erases the rest
        let nr = b.alloc();
        b.cx(tt[1], nr); b.cx(bb[1], nr); b.x(nr);
        b.cx(nr, n);
        flat_rule(b, &tt, &bb, nr, n, anchor);
        b.x(nr); b.cx(bb[1], nr); b.cx(tt[1], nr);
        b.free(nr);
        imark(b, t, "flat rule");
    }
    for i in (0..m).rev() {
        unhalf(b, &mut tt);
        row(b, &bb, &tt, d[i], true, pk(div, t, i));
        b.cx(bb[1], d[i]); b.cx(tt[1], d[i]);
        imark(b, t, "rail row");
    }
    b.free_n(&k); b.free(n); b.free_n(&d);
    l[ir_t] = tt; l[ir_b] = bb; l[iu_t] = ut; l[iu_b] = ub;
    if exact { unfit(b, l, log); } else { unfit_any(b, l, log); }
}
/// U <- U 2^(2^i) if ctl, sign copies on the top lanes; low lanes zero when shifted.
fn shift_layer(b: &mut B, u: &[Q], ctl: Q, k: usize, inv: bool) {
    let w = u.len();
    let g = |b: &mut B| {
        let s = u[w - 1];
        let g = b.alloc();
        b.and_c(ctl, s, g);
        for j in 0..k { b.cx(g, u[j]); }
        b.and_u(ctl, s, g);
        b.free(g);
    };
    if inv {
        g(b);
        for j in k..w { b.cswap(ctl, u[j], u[j - k]); }
    } else {
        for j in (k..w).rev() { b.cswap(ctl, u[j], u[j - k]); }
        g(b);
    }
}
fn sign_pattern(b: &mut B, u: &[Q], s: Q) {
    let p = super::frogdrop_sched::p();
    let np = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64));
    for (i, &q) in u.iter().enumerate() {
        let (pos, neg) = if i < 256 { (p.bit(i), np.bit(i)) } else { (false, true) };
        if pos { b.x(q); }
        if pos != neg { b.cx(s, q); }
    }
}
fn rail_clear(b: &mut B, r: &[Q]) {
    let top = *r.last().unwrap();
    b.x(r[0]);
    for &q in &r[1..r.len() - 1] { b.cx(top, q); }
}
/// tgt += (-1)^neg src on tgt.len() lanes, src filled upward with wire fill (zero wire or src's sign lane). Repeated source lanes are fine in chunk_ripple.
fn rowx(b: &mut B, src: &[Q], fill: Q, tgt: &[Q], neg: Q, inv: bool) {
    let n = tgt.len();
    let mut a: Vec<Q> = src[..src.len().min(n)].to_vec();
    while a.len() < n { a.push(fill); }
    let room = cap().saturating_sub(b.live) as usize;
    let pool = b.alloc_n(room.min(n.saturating_sub(1)));
    if inv { b.begin(); }
    for &q in tgt { b.cx(neg, q); }
    super::chunked::chunk_ripple(b, &a, tgt, &pool);
    for &q in tgt { b.cx(neg, q); }
    if inv { let r = b.end(); b.play(&r, true); }
    b.free_n(&pool);
}
/// lanes <- (-1)^c lanes, c outside lanes, zw a zero wire
fn cneg(b: &mut B, lanes: &[Q], c: Q, zw: Q, inv: bool) {
    let mut a = vec![c];
    while a.len() < lanes.len() { a.push(zw); }
    let room = cap().saturating_sub(b.live) as usize;
    let pool = b.alloc_n(room.min(lanes.len().saturating_sub(1)));
    if inv { b.begin(); }
    for &q in lanes { b.cx(c, q); }
    super::chunked::chunk_ripple(b, &a, lanes, &pool);
    if inv { let r = b.end(); b.play(&r, true); }
    b.free_n(&pool);
}
/// z <- rho z mod 2^w in place given z = odd lanes ud (lane 0 known 1). Returns the product lanes and the spare lane.
fn mul_rho(b: &mut B, ud: &[Q], rho: &[Q], zw: Q) -> (Vec<Q>, Q) {
    let w = ud.len();
    let mut y = vec![ud[0]];
    let mut zz = b.alloc();
    for i in (0..w - 1).rev() {
        y.insert(0, zz);
        let d = ud[i + 1];
        rowx(b, rho, zw, &y, d, true);
        b.cx(rho[1], d); b.cx(y[1], d);
        zz = d;
    }
    (y, zz)
}
/// Exact mirror of mul_rho.
fn div_rho(b: &mut B, y0: Vec<Q>, zz0: Q, rho: &[Q], zw: Q) -> Vec<Q> {
    let w = y0.len();
    let mut y = y0;
    let mut zz = zz0;
    let mut ud = vec![Q(0); w];
    for i in 0..w - 1 {
        let d = zz;
        b.cx(y[1], d); b.cx(rho[1], d);
        rowx(b, rho, zw, &y, d, false);
        zz = y.remove(0);
        ud[i + 1] = d;
    }
    ud[0] = y[0];
    b.free(zz);
    ud
}
/// z -= X_d U_k mod 2^w, rows by the signed digits of odd X_d.
fn sub_prod(b: &mut B, z: &[Q], rd: &[Q], uk: &[Q], sr: Q, inv: bool) {
    let l = rd.len().min(z.len());
    let w = z.len();
    let top = rd.len() - 1;
    let idx: Vec<usize> = if inv { (0..l).rev().collect() } else { (0..l).collect() };
    for &i in &idx {
        let n = w - i;
        let src = &uk[..n.min(uk.len())];
        let fill = uk[uk.len() - 1];
        let c = if i < top { rd[i + 1] } else { rd[top] };
        b.cx(sr, c);
        if i == top { b.x(c); }
        rowx(b, src, fill, &z[i..], c, inv);
        if i == top { b.x(c); }
        b.cx(sr, c);
    }
}
/// z = (-1)^s (neg ? -p : p) on all lanes -> 0, or the reverse.
fn const_pm_p(b: &mut B, z: &[Q], neg: bool, s: Q) {
    let p = super::frogdrop_sched::p();
    let np = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64));
    for (i, &q) in z.iter().enumerate() {
        let (vp, vn) = if i < 256 { (p.bit(i), np.bit(i)) } else { (false, true) };
        let (v0, v1) = if neg { (vn, vp) } else { (vp, vn) };
        if v0 { b.x(q); }
        if v0 != v1 { b.cx(s, q); }
    }
}
/// tick-boundary Clear: U_d gone, sr = sign of X_k.
fn clear_fwd(b: &mut B, l: &mut [Vec<Q>; 4], a: usize, zw: Q) -> (Q, ClearRec, Vec<Q>) {
    let (rk, rd) = (l[a].clone(), l[1 - a].clone());
    let (uk, ud) = (l[2 + a].clone(), l[3 - a].clone());
    let sr = b.alloc();
    b.cx(rk[rk.len() - 1], sr);
    cneg(b, &rk, sr, zw, false);
    let (y, zz) = mul_rho(b, &ud, &rk, zw);
    sub_prod(b, &y, &rd, &uk, sr, false);
    const_pm_p(b, &y, a == 1, sr);
    b.free_n(&y);
    b.free(zz);
    cneg(b, &rk, sr, zw, true);
    (sr, ClearRec { y, zz }, ud)
}
fn clear_inv(b: &mut B, l: &mut [Vec<Q>; 4], a: usize, zw: Q, sr: Q, c: &ClearRec, ud_ids: &[Q]) {
    let (rk, rd) = (l[a].clone(), l[1 - a].clone());
    let uk = l[2 + a].clone();
    cneg(b, &rk, sr, zw, false);
    for &q in &c.y { b.acquire(q); }
    b.acquire(c.zz);
    const_pm_p(b, &c.y, a == 1, sr);
    sub_prod(b, &c.y, &rd, &uk, sr, true);
    let ud = div_rho(b, c.y.clone(), c.zz, &rk, zw);
    assert_eq!(&ud[..], ud_ids);
    cneg(b, &rk, sr, zw, true);
    b.cx(rk[rk.len() - 1], sr);
    b.free(sr);
    l[3 - a] = ud;
}
/// One sweep of REDC on j: j <- (j -+ rho)/2 forced odd, digits kept on wires.
/// Deterministic lanes of j after each REDC step: |j'| <= (|j| + rho)/2, |rho| < 2^(lr-1).
fn redc_lanes(jl: usize, lr: usize) -> Vec<usize> {
    let mut bd: u128 = 0;
    let top = jl.saturating_sub(1).min(120);
    bd |= 1u128 << top;
    let r: u128 = 1u128 << (lr - 1).min(120);
    let mut v = vec![];
    for _ in 0..RS {
        bd = (bd + r) / 2 + 1;
        let need = (128 - bd.leading_zeros() as usize) + 1;
        v.push(need.max(lr + 1).min(jl));
    }
    v
}
fn redc_fwd(b: &mut B, j: &mut Vec<Q>, rho: &[Q], zw: Q) -> Vec<Q> {
    let mut ds = vec![];
    let lanes = redc_lanes(j.len(), rho.len());
    for k in 0..RS {
        let d = b.alloc();
        b.cx(j[1], d); b.cx(rho[1], d);
        rowx(b, rho, zw, &j[..], d, false);
        half(b, j);
        ds.push(d);
        while j.len() > lanes[k] { let q = j.pop().unwrap(); let top = *j.last().unwrap(); b.cx(top, q); b.free(q); }
    }
    ds
}
fn redc_inv(b: &mut B, j: &mut Vec<Q>, rho: &[Q], zw: Q, ds: &[Q], jl: usize) {
    let lanes = redc_lanes(jl, rho.len());
    for k in (0..RS).rev() {
        let want = if k == 0 { jl } else { lanes[k - 1] };
        while j.len() < want { let q = b.alloc(); let top = *j.last().unwrap(); b.cx(top, q); j.push(q); }
        let d = ds[k];
        unhalf(b, j);
        rowx(b, rho, zw, &j[..], d, true);
        b.cx(rho[1], d); b.cx(j[1], d);
        b.free(d);
    }
}
/// tq <- hh m, m = (c - 1)/16 = 2^28 + 2^6 - 3, or the reverse.
fn tq_m(b: &mut B, hh: &[Q], tq: &[Q], zw: Q, one: Q, inv: bool) {
    let i = hh.len();
    let n = tq.len();
    let ln = if i + 6 <= 28 { i + 6 } else { n };
    let mut ops: Vec<(usize, bool)> = vec![(6, false), (1, true), (0, true)];
    if inv { ops.reverse(); }
    if !inv { for r in 0..i { b.cx(hh[r], tq[28 + r]); } }
    for (sh, ng) in ops {
        if sh >= ln { continue; }
        rowx(b, hh, zw, &tq[sh..ln], if ng { one } else { zw }, inv);
    }
    if inv { for r in 0..i { b.cx(hh[r], tq[28 + r]); } }
}
/// v <- v 2^i mod 2^256 - c if ctl: rotate, add H (c - 1) on lanes 4.., X-measure the addend. H stays recoverable: low i lanes = H c mod 2^i.
fn mod_shift_fwd(b: &mut B, v: &[Q], ctl: Q, i: usize, zw: Q) -> Vec<BitId> {
    for j in (i..256).rev() { b.cswap(ctl, v[j], v[j - i]); }
    let hh = b.alloc_n(i);
    for r in 0..i { b.and_c(ctl, v[r], hh[r]); }
    let n = i + 29;
    let tq = b.alloc_n(n);
    let one = b.alloc(); b.x(one);
    tq_m(b, &hh, &tq, zw, one, false);
    b.x(one); b.free(one);
    for r in 0..i { b.and_u(ctl, v[r], hh[r]); }
    b.free_n(&hh);
    rowx(b, &tq, zw, &v[4..], zw, false);
    let m = b.fresh_bits(n);
    for k in 0..n { b.hmr_to(tq[k], m[k]); }
    b.free_n(&tq);
    m
}
fn inv_c_naf(i: usize) -> Vec<(usize, bool)> {
    let c: u128 = (1u128 << 32) + 977;
    let md: u128 = if i >= 64 { (1u128 << 64) - 1 } else { (1u128 << i) - 1 };
    let mut x: u128 = 1;
    for _ in 0..8 { x = x.wrapping_mul(2u128.wrapping_sub(c.wrapping_mul(x))) & md; }
    assert_eq!(c.wrapping_mul(x) & md, 1);
    let mut out = vec![];
    let mut v = x;
    let mut s = 0;
    while v != 0 && s < i {
        if v & 1 == 1 {
            let d = v & 3;
            if d == 3 { out.push((s, true)); v += 1; } else { out.push((s, false)); v -= 1; }
        }
        v >>= 1;
        s += 1;
    }
    out
}
fn mod_shift_undo(b: &mut B, v: &[Q], ctl: Q, i: usize, zw: Q, m: &[BitId]) {
    let hh = b.alloc_n(i);
    let one = b.alloc(); b.x(one);
    if i <= 4 {
        for r in 0..i { b.and_c(ctl, v[r], hh[r]); }
    } else {
        let y = b.alloc_n(i);
        for r in 0..i { b.and_c(ctl, v[r], y[r]); }
        for (s, ng) in inv_c_naf(i) {
            if s < i { rowx(b, &y, zw, &hh[s..], if ng { one } else { zw }, false); }
        }
        for r in 0..i { b.and_u(ctl, v[r], y[r]); }
        b.free_n(&y);
    }
    let n = i + 29;
    let tq = b.alloc_n(n);
    tq_m(b, &hh, &tq, zw, one, false);
    for k in 0..n { b.z_if(tq[k], m[k]); }
    rowx(b, &tq, zw, &v[4..], zw, true);
    tq_m(b, &hh, &tq, zw, one, true);
    b.free_n(&tq);
    b.x(one); b.free(one);
    for r in 0..i { b.and_u(ctl, v[r], hh[r]); }
    b.free_n(&hh);
    for j in i..256 { b.cswap(ctl, v[j], v[j - i]); }
}
/// N += (-1)^t j p on all lanes of nn
fn add_jp(b: &mut B, nn: &[Q], j: &[Q], t: Q, inv: bool) {
    let terms: [(usize, bool); 6] = [(0, true), (4, false), (5, false), (10, true), (32, true), (256, false)];
    let fill = j[j.len() - 1];
    let order: Vec<usize> = if inv { (0..6).rev().collect() } else { (0..6).collect() };
    for &k in &order {
        let (sh, ng) = terms[k];
        if ng { b.x(t); }
        rowx(b, j, fill, &nn[sh..], t, inv);
        if ng { b.x(t); }
    }
}
pub fn forward(b: &mut B, x: &[Q]) -> DwEnd {
    if T0 > 0 { return forward_split(b, x); }
    let tb = tab();
    let refl = b.alloc();
    b.cx(x[0], refl); b.x(refl);
    { let ms = Ms::alloc_room(b, cap()); ctrl_neg(b, &ms, x, Some(refl)); ms.release(b); }
    let div = b.new_division();
    let p = super::frogdrop_sched::p();
    let r0 = b.alloc_n(258);
    for i in 0..256 { if p.bit(i) { b.x(r0[i]); } }
    let mut r1 = x.to_vec(); r1.extend(b.alloc_n(2));
    let u0 = b.alloc_n(4);
    let u1 = b.alloc_n(4);
    b.x(u1[0]);
    let dc = b.alloc_n(DB);
    for i in 0..DB { if (E_INIT >> i) & 1 == 1 { b.x(dc[i]); } }
    let mut l = [r0, r1, u0, u1];
    let mut tape = vec![];
    let mut logs = vec![];
    for t in 0..R {
        logs.push(tick_fwd(b, &mut l, &mut tape, &dc, t, tb[t], div));
        #[cfg(test)]
        MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    }
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(usize::MAX));
    // end: rails +-1, signs on the top lanes
    let [r0, r1, u0, u1] = l;
    let (s0, s1) = (*r0.last().unwrap(), *r1.last().unwrap());
    rail_clear(b, &r0); rail_clear(b, &r1);
    let (r0low, r1low) = (r0[..r0.len() - 1].to_vec(), r1[..r1.len() - 1].to_vec());
    b.free_n(&r0low); b.free_n(&r1low);
    let wc_end = u0.len();
    // U1 - s0 s1 U0 = s0 p
    let nq = b.alloc();
    b.cx(s0, nq); b.cx(s1, nq); b.x(nq);
    row(b, &u0, &u1, nq, false, None);
    b.x(nq); b.cx(s1, nq); b.cx(s0, nq);
    b.free(nq);
    sign_pattern(b, &u1, s0);
    b.free_n(&u1);
    b.cx(refl, s0);
    // D' in place mod p: hi holds only U0's top lanes, no D lanes
    let m0 = reduce_fwd(b, &u0);
    let lo = u0[..256].to_vec();
    let zw = b.alloc();
    let mut ms = vec![];
    for i in 0..DB { ms.push(mod_shift_fwd(b, &lo, dc[i], 1 << i, zw)); }
    b.free(zw);
    DwEnd { tape, dc, refl, s0, s1, r0low, r1low, u0: lo, u1, ext: u0, logs, div, wc_end, sp: None, nsm: Some((m0, ms)) }
}
#[allow(unused_variables)]
fn stage(b: &B, name: &str) {
    #[cfg(test)]
    eprintln!("SPLITSTAGE {name:12} tof {} cond {} live {} peak {} ops {}", b.tof, b.tof_cond, b.live, b.peak, b.ops.len());
}
/// dc -= dc2 mod 2^DB (or the reverse)
fn dc_sub(b: &mut B, dc: &[Q], dc2: &[Q], inv: bool) {
    for &q in dc { b.x(q); }
    let mut a2 = dc2.to_vec(); a2.truncate(DB);
    let room = cap().saturating_sub(b.live) as usize;
    let pool = b.alloc_n(room.min(DB - 1));
    if inv { b.begin(); }
    super::chunked::chunk_ripple(b, &a2, dc, &pool);
    if inv { let r = b.end(); b.play(&r, true); }
    b.free_n(&pool);
    for &q in dc { b.x(q); }
}
/// b1 <- b1 -+ b0 = (-1)^s0 sigma X_k, then |X_k|. Rails are +-1 with signs s0, s1; sr = sign X_k.
fn final_adapter(b: &mut B, b0: &[Q], b1: &[Q], s0: Q, s1: Q, sr: Q, a: usize, zw: Q, inv: bool) {
    let nq = b.alloc();
    let c = b.alloc();
    if !inv {
        b.cx(s0, nq); b.cx(s1, nq); b.x(nq);
        row(b, b0, b1, nq, false, None);
        b.x(nq); b.cx(s1, nq); b.cx(s0, nq);
        b.cx(s0, c); b.cx(sr, c); if a == 1 { b.x(c); }
        cneg(b, b1, c, zw, false);
        if a == 1 { b.x(c); } b.cx(sr, c); b.cx(s0, c);
    } else {
        b.cx(s0, c); b.cx(sr, c); if a == 1 { b.x(c); }
        cneg(b, b1, c, zw, true);
        if a == 1 { b.x(c); } b.cx(sr, c); b.cx(s0, c);
        b.cx(s0, nq); b.cx(s1, nq); b.x(nq);
        row(b, b0, b1, nq, true, None);
        b.x(nq); b.cx(s1, nq); b.cx(s0, nq);
    }
    b.free(nq); b.free(c);
}
fn forward_split(b: &mut B, x: &[Q]) -> DwEnd {
    stage(b, "start");
    let tb = tab();
    let refl = b.alloc();
    b.cx(x[0], refl); b.x(refl);
    { let ms = Ms::alloc_room(b, cap()); ctrl_neg(b, &ms, x, Some(refl)); ms.release(b); }
    let div = b.new_division();
    let p = super::frogdrop_sched::p();
    let r0 = b.alloc_n(258);
    for i in 0..256 { if p.bit(i) { b.x(r0[i]); } }
    let mut r1 = x.to_vec(); r1.extend(b.alloc_n(2));
    let u0 = b.alloc_n(4);
    let u1 = b.alloc_n(4);
    b.x(u1[0]);
    let dc = b.alloc_n(DB);
    for i in 0..DB { if (E_INIT >> i) & 1 == 1 { b.x(dc[i]); } }
    let mut l = [r0, r1, u0, u1];
    let mut tape = vec![];
    let mut logs = vec![];
    for t in 0..T0 { logs.push(tick_fwd(b, &mut l, &mut tape, &dc, t, tb[t], div)); }
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    // Clear: kept slot a (T role of tick T0, even), dropped slot 1 - a (odd). R0 U1 - R1 U0 = p.
    stage(b, "phase1");
    let a = T0 & 1;
    let zw = b.alloc();
    let (sr, clr, ud_ids) = clear_fwd(b, &mut l, a, zw);
    stage(b, "clear");
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    let rails_t0 = [l[0].clone(), l[1].clone()];
    let uk = std::mem::take(&mut l[2 + a]);
    let mut u_slots = [vec![], vec![]];
    u_slots[a] = uk.clone();
    u_slots[1 - a] = ud_ids;
    let dc2 = b.alloc_n(DB2);
    // sub cofactors from (0, 1): 1 on the B role of tick T0
    let bk = b.alloc_n(4);
    let bd = b.alloc_n(4);
    b.x(bd[0]);
    l[2 + a] = bk; l[3 - a] = bd;
    for t in T0..R { logs.push(tick_fwd(b, &mut l, &mut tape, &dc2, t, tb[t], div)); }
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    stage(b, "subwalk");
    // end of sub-walk: rails +-1
    let [r0, r1, b0, b1] = l;
    let (s0, s1) = (*r0.last().unwrap(), *r1.last().unwrap());
    rail_clear(b, &r0); rail_clear(b, &r1);
    let (r0low, r1low) = (r0[..r0.len() - 1].to_vec(), r1[..r1.len() - 1].to_vec());
    b.free_n(&r0low); b.free_n(&r1low);
    let wc_end = b0.len();
    // b1 <- (-1)^s0 s X_k, then |X_k|
    final_adapter(b, &b0, &b1, s0, s1, sr, a, zw, false);
    let lr = tb[T0.saturating_sub(1)][0];
    let rho = b1[..lr].to_vec();
    let rho_hi = b1[lr..].to_vec();
    b.free_n(&rho_hi);
    // REDC, shift of U_k, N, division
    stage(b, "adapter");
    let mut j = b0.clone();
    let ds = redc_fwd(b, &mut j, &rho, zw);
    stage(b, "redc");
    let x0 = (R - T0) * (M + 1) - RS;
    let wn = I0 + lr + 1;
    let nn_zero = b.alloc_n(x0);
    let mut nn = nn_zero.clone();
    nn.extend(&uk);
    let mut nn_ext = vec![];
    while nn.len() < wn { let q = b.alloc(); let top = *nn.last().unwrap(); b.cx(top, q); nn.push(q); nn_ext.push(q); }
    for i in 0..DB2 { shift_layer(b, &nn, dc2[i], 1 << i, false); }
    let tw = b.alloc();
    b.cx(s0, tw); if a == 1 { b.x(tw); }
    add_jp(b, &nn, &j, tw, false);
    if a == 1 { b.x(tw); } b.cx(s0, tw);
    b.free(tw);
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    stage(b, "N");
    // non-restoring division, window lanes i-1 .. i+lr, old sign lane stays as the digit
    for i in (1..=I0).rev() {
        let sgn = nn[i + lr];
        let win = &nn[i - 1..i + lr];
        b.x(sgn);
        rowx(b, &rho, zw, win, sgn, false);
        b.x(sgn);
    }
    // R_0 = -rho t, t on lane lr
    let t = nn[lr];
    b.cx(t, nn[0]);
    for k in 1..lr {
        b.x(rho[k]);
        b.and_u(t, rho[k], nn[k]);
        b.x(rho[k]);
    }
    let win_low = nn[..lr].to_vec();
    b.free_n(&win_low);
    // Z lanes: not t, not s_0 .. not s_(I0-2), s_(I0-1)
    let mut z: Vec<Q> = nn[lr..].to_vec();
    assert_eq!(z.len(), I0 + 1);
    for k in 0..I0 { b.x(z[k]); }
    stage(b, "division");
    redc_inv(b, &mut j, &rho, zw, &ds, b0.len());
    let b0 = j.clone();
    stage(b, "unredc");
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    // D' = D0 - E1
    dc_sub(b, &dc, &dc2, false);
    let z_lanes = z.clone();
    let m0 = reduce_fwd(b, &z);
    let lo = z[..256].to_vec();
    let mut ms = vec![];
    for i in 0..DB { ms.push(mod_shift_fwd(b, &lo, dc[i], 1 << i, zw)); }
    stage(b, "shift");
    let mut rails = None;
    if UNSUB {
        dc_sub(b, &dc, &dc2, true);
        let mut b1v = rho.clone();
        b1v.extend(b.alloc_n(rho_hi.len()));
        final_adapter(b, &b0, &b1v, s0, s1, sr, a, zw, true);
        let mut r0 = b.alloc_n(r0low.len()); r0.push(s0);
        let mut r1 = b.alloc_n(r1low.len()); r1.push(s1);
        rail_clear(b, &r0); rail_clear(b, &r1);
        let mut l = [r0, r1, b0.clone(), b1v];
        for t in (T0..R).rev() { tick_inv_x(b, &mut l, &mut tape, &dc2, t, tb[t], div, &logs[t], false); }
        logs.truncate(T0);
        let (bk, bd) = (std::mem::take(&mut l[2 + a]), std::mem::take(&mut l[3 - a]));
        b.x(bd[0]);
        b.free_n(&bk); b.free_n(&bd);
        b.free_n(&dc2);
        let [r0, r1, _, _] = l;
        rails = Some([r0, r1]);
        stage(b, "unsub");
    }
    b.cx(refl, sr);
    let sp = Sp { sr, zw, dc2, clr, uk_ids: uk, u_slots, b0, rho, rho_hi, nn_zero, nn_ext, win_low, z_lanes, m0, ms, rails, rails_t0 };
    DwEnd { tape, dc, refl, s0, s1, r0low, r1low, u0: lo, u1: b1, ext: vec![], logs, div, wc_end, sp: Some(sp), nsm: None }
}
fn inverse_split(b: &mut B, e: DwEnd, x: &[Q]) {
    stage(b, "inv start");
    let tb = tab();
    let DwEnd { mut tape, dc, refl, mut s0, mut s1, mut r0low, mut r1low, u0: lo, u1: mut b1, mut logs, div, wc_end, sp, .. } = e;
    let Sp { sr, zw, mut dc2, clr, uk_ids, u_slots, mut b0, mut rho, mut rho_hi, nn_zero, nn_ext, win_low, z_lanes, m0, ms, rails, rails_t0, .. } = sp.unwrap();
    let a = T0 & 1;
    let lr = tb[T0.saturating_sub(1)][0];
    b.cx(refl, sr);
    if let Some([r0, r1]) = rails {
        // sub-walk again
        dc2 = b.alloc_n(DB2);
        let bk = b.alloc_n(4);
        let bd = b.alloc_n(4);
        b.x(bd[0]);
        let mut l = [r0, r1, vec![], vec![]];
        l[2 + a] = bk; l[3 - a] = bd;
        for t in T0..R { logs.push(tick_fwd(b, &mut l, &mut tape, &dc2, t, tb[t], div)); }
        let [r0, r1, nb0, nb1] = l;
        s0 = *r0.last().unwrap(); s1 = *r1.last().unwrap();
        rail_clear(b, &r0); rail_clear(b, &r1);
        r0low = r0[..r0.len() - 1].to_vec(); r1low = r1[..r1.len() - 1].to_vec();
        b.free_n(&r0low); b.free_n(&r1low);
        b0 = nb0; b1 = nb1;
        final_adapter(b, &b0, &b1, s0, s1, sr, a, zw, false);
        rho = b1[..lr].to_vec();
        rho_hi = b1[lr..].to_vec();
        b.free_n(&rho_hi);
        dc_sub(b, &dc, &dc2, false);
        stage(b, "resub");
    }
    for i in (0..DB).rev() { mod_shift_undo(b, &lo, dc[i], 1 << i, zw, &ms[i]); }
    let z = z_lanes;
    reduce_undo(b, &z, &m0);
    dc_sub(b, &dc, &dc2, true);
    // REDC again, rebuild the division window, undo division
    let mut j = b0.clone();
    let ds = redc_fwd(b, &mut j, &rho, zw);
    for k in 0..I0 { b.x(z[k]); }
    let mut nn = b.alloc_n(win_low.len());
    nn.extend(&z);
    let t = nn[lr];
    for k in (1..lr).rev() {
        b.x(rho[k]);
        b.and_c(t, rho[k], nn[k]);
        b.x(rho[k]);
    }
    b.cx(t, nn[0]);
    for i in 1..=I0 {
        let sgn = nn[i + lr];
        let win = &nn[i - 1..i + lr];
        b.x(sgn);
        rowx(b, &rho, zw, win, sgn, true);
        b.x(sgn);
    }
    let tw = b.alloc();
    b.cx(s0, tw); if a == 1 { b.x(tw); }
    add_jp(b, &nn, &j, tw, true);
    if a == 1 { b.x(tw); } b.cx(s0, tw);
    b.free(tw);
    for i in (0..DB2).rev() { shift_layer(b, &nn, dc2[i], 1 << i, true); }
    for _ in 0..nn_ext.len() { let q = nn.pop().unwrap(); let top = *nn.last().unwrap(); b.cx(top, q); b.free(q); }
    b.free_n(&nn[..nn_zero.len()]);
    let mut uk_cur: Vec<Q> = nn[nn_zero.len()..].to_vec();
    assert_eq!(uk_cur.len(), uk_ids.len());
    redc_inv(b, &mut j, &rho, zw, &ds, b0.len());
    let b0 = j.clone();
    let mut b1v = rho.clone();
    b1v.extend(b.alloc_n(rho_hi.len()));
    final_adapter(b, &b0, &b1v, s0, s1, sr, a, zw, true);
    let mut r0 = b.alloc_n(r0low.len()); r0.push(s0);
    let mut r1 = b.alloc_n(r1low.len()); r1.push(s1);
    rail_clear(b, &r0); rail_clear(b, &r1);
    let _ = wc_end;
    let mut l = [r0, r1, b0, b1v];
    stage(b, "inv final");
    for t in (T0..R).rev() { tick_inv_x(b, &mut l, &mut tape, &dc2, t, tb[t], div, &logs[t], false); }
    stage(b, "inv subwalk");
    // sub cofactors back to (0, 1)
    let (bk, bd) = (std::mem::take(&mut l[2 + a]), std::mem::take(&mut l[3 - a]));
    b.x(bd[0]);
    b.free_n(&bk); b.free_n(&bd);
    b.free_n(&dc2);
    {
        // all three lists may hold each other's old wires, so one joint permutation
        let (ra, rb) = (std::mem::take(&mut l[0]), std::mem::take(&mut l[1]));
        let (n0, n1) = (ra.len(), rb.len());
        let mut cur = ra; cur.extend(&rb); cur.extend(&uk_cur);
        let mut tgt = rails_t0[0].clone(); tgt.extend(&rails_t0[1]); tgt.extend(&uk_ids);
        remap(b, &mut cur, &tgt);
        l[0] = cur[..n0].to_vec(); l[1] = cur[n0..n0 + n1].to_vec();
        uk_cur = cur[n0 + n1..].to_vec();
    }
    l[2 + a] = uk_cur;
    clear_inv(b, &mut l, a, zw, sr, &clr, &u_slots[1 - a]);
    b.free(zw);
    stage(b, "inv clear");
    for t in (0..T0).rev() { tick_inv(b, &mut l, &mut tape, &dc, t, tb[t], div, &logs[t]); }
    let [r0, r1, u0, u1] = l;
    for i in 0..DB { if (E_INIT >> i) & 1 == 1 { b.x(dc[i]); } }
    b.free_n(&dc);
    let p = super::frogdrop_sched::p();
    b.x(u1[0]);
    b.free_n(&u0); b.free_n(&u1);
    assert_eq!(&r1[..256], x);
    b.free_n(&r1[256..]);
    for i in 0..256 { if p.bit(i) { b.x(r0[i]); } }
    b.free_n(&r0);
    b.close_division(div);
    { let ms = Ms::alloc_room(b, cap()); ctrl_neg(b, &ms, x, Some(refl)); ms.release(b); }
    b.x(refl); b.cx(x[0], refl);
    b.free(refl);
}
pub fn inverse(b: &mut B, e: DwEnd, x: &[Q]) {
    if T0 > 0 { return inverse_split(b, e, x); }
    let tb = tab();
    let DwEnd { mut tape, dc, refl, s0, s1, r0low, r1low, u0: lo, u1, ext, logs, div, wc_end, nsm, .. } = e;
    let (m0, ms) = nsm.unwrap();
    let zw = b.alloc();
    for i in (0..DB).rev() { mod_shift_undo(b, &lo, dc[i], 1 << i, zw, &ms[i]); imark(b, 900 + i, "unshift"); }
    b.free(zw);
    let u0 = ext;
    reduce_undo(b, &u0, &m0);
    assert_eq!(u0.len(), wc_end);
    b.cx(refl, s0);
    for &q in &u1 { b.acquire(q); }
    sign_pattern(b, &u1, s0);
    imark(b, 910, "pattern");
    let nq = b.alloc();
    b.cx(s0, nq); b.cx(s1, nq); b.x(nq);
    row(b, &u0, &u1, nq, true, None);
    imark(b, 911, "row u1");
    b.x(nq); b.cx(s1, nq); b.cx(s0, nq);
    b.free(nq);
    for &q in r0low.iter().chain(&r1low) { b.acquire(q); }
    let mut r0 = r0low.clone(); r0.push(s0);
    let mut r1 = r1low.clone(); r1.push(s1);
    rail_clear(b, &r0); rail_clear(b, &r1);
    let mut l = [r0, r1, u0, u1];
    imark(b, 999, "adapter");
    for t in (0..R).rev() { tick_inv(b, &mut l, &mut tape, &dc, t, tb[t], div, &logs[t]); imark(b, t, "unfit"); }
    let [r0, r1, u0, u1] = l;
    for i in 0..DB { if (E_INIT >> i) & 1 == 1 { b.x(dc[i]); } }
    b.free_n(&dc);
    let p = super::frogdrop_sched::p();
    b.x(u1[0]);
    b.free_n(&u0); b.free_n(&u1);
    assert_eq!(&r1[..256], x);
    b.free_n(&r1[256..]);
    for i in 0..256 { if p.bit(i) { b.x(r0[i]); } }
    b.free_n(&r0);
    b.close_division(div);
    { let ms = Ms::alloc_room(b, cap()); ctrl_neg(b, &ms, x, Some(refl)); ms.release(b); }
    b.x(refl); b.cx(x[0], refl);
    b.free(refl);
}
/// tq <- sext(hi) c mod 2^|tq|, c = 2^32 + 2^10 - 2^5 - 2^4 + 1
fn tq_build(b: &mut B, hi: &[Q], tq: &[Q], pool: &[Q]) {
    let h = hi.len();
    let w = h + 10;
    for j in 0..w { b.cx(hi[j.min(h - 1)], tq[j]); }
    add_sext(b, hi, &tq[10..w], pool);
    sub_sext(b, hi, &tq[5..w], pool);
    sub_sext(b, hi, &tq[4..w], pool);
    for j in w..tq.len() { b.cx(tq[w - 1], tq[j]); }
    add_sext(b, hi, &tq[32..], pool);
}
pub fn reduce_fwd(b: &mut B, inv: &[Q]) -> Vec<BitId> {
    if inv.len() <= 256 { return vec![]; }
    let (lo, hi) = (&inv[..256], &inv[256..]);
    let n = hi.len() + 34;
    let tq = b.alloc_n(n);
    let ms = Ms::alloc_room(b, cap());
    b.begin();
    tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    super::pointadd_lilypad::reduce_tq_add(b, lo, &tq, &ms.r, false);
    let m = b.fresh_bits(n);
    for i in 0..n { b.hmr_to(tq[i], m[i]); }
    ms.release(b);
    b.free_n(&tq);
    m
}
pub fn reduce_undo(b: &mut B, inv: &[Q], m: &[BitId]) {
    if inv.len() <= 256 { return; }
    let (lo, hi) = (&inv[..256], &inv[256..]);
    let n = hi.len() + 34;
    assert_eq!(m.len(), n);
    let tq = b.alloc_n(n);
    let ms = Ms::alloc_room(b, cap());
    b.begin();
    tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    for i in 0..n { b.z_if(tq[i], m[i]); }
    super::pointadd_lilypad::reduce_tq_add(b, lo, &tq, &ms.r, true);
    b.play(&r, true);
    ms.release(b);
    b.free_n(&tq);
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    /// Whole point add in the simulator: phase and value at each shell checkpoint.
    #[test]
    fn dwalk_shell_phase() {
        super::super::pointadd_lilypad::test_peak(std::env::var("DW_CAP").ok().and_then(|v| v.parse().ok()));
        let mut b = B::new();
        let (xq, yq) = super::super::pointadd_lilypad::point_add(&mut b);
        let cks: Vec<(String, usize)> = super::super::pointadd_lilypad::CKS.with(|c| c.borrow().clone());
        let ops = std::mem::take(&mut b.ops);
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let curve = super::super::tests_lilypad::lilypad_curve();
        let mut st = std::env::var("DW_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0xABCDu64);
        let mut rnd = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; st };
        let mut cases = vec![];
        while cases.len() < 64 {
            let k1 = ruint::aliases::U256::from_limbs([rnd(), rnd(), rnd(), rnd() >> 8]);
            let k2 = ruint::aliases::U256::from_limbs([rnd(), rnd(), rnd(), rnd() >> 8]);
            let t = curve.mul(curve.gx, curve.gy, k1);
            let o = curve.mul(curve.gx, curve.gy, k2);
            if t.0 == o.0 { continue; }
            let e = curve.add(t.0, t.1, o.0, o.1);
            cases.push((t, o, e));
        }
        let mut h = sha3::Shake256::default();
        h.update(b"dwalk-shell");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
        for (k, (t, o, _)) in cases.iter().enumerate() {
            s.set_register(&regs[0], t.0, k);
            s.set_register(&regs[1], t.1, k);
            s.set_register(&regs[2], o.0, k);
            s.set_register(&regs[3], o.1, k);
        }
        let mut from = 0;
        for (name, to) in cks.iter() {
            s.apply_iter(ops[from..*to].iter());
            eprintln!("SHELLPHASE {name:28} phase {:016x} pop {}", s.phase, s.phase.count_ones());
            from = *to;
        }
        s.apply_iter(ops[from..].iter());
        let mut wrong = 0; let mut wrongmask = 0u64;
        for (k, (_, _, e)) in cases.iter().enumerate() {
            if s.get_register(&regs[0], k) != e.0 || s.get_register(&regs[1], k) != e.1 { wrong += 1; wrongmask |= 1 << k; }
        }
        let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
        let mut dirty = 0;
        for q in 0..nq { if !data.contains(&q) && s.qubits[q as usize] != 0 { dirty += 1; } }
        eprintln!("SHELLPHASE end phase {:016x} pop {} wrong {wrong} mask {wrongmask:016x} dirty {dirty} ops {} T {}", s.phase, s.phase.count_ones(), ops.len(), s.stats.toffoli_gates / 64);
    }
    /// Forward walk alone, pairing off: phase after each tick. The first nonzero tick holds the wrong uncompute.
    #[test]
    fn dwalk_phase_ticks() {
        super::super::pointadd_lilypad::test_peak(Some(std::env::var("DW_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(1400)));
        let mut b = B::new();
        let x = b.alloc_n(256);
        let _y = b.alloc_n(256);
        let e = forward(&mut b, &x);
        let nf = b.ops.len();
        let inv0 = inv_of(&e);
        let m = reduce_fwd(&mut b, &inv0);
        let nr = b.ops.len();
        reduce_undo(&mut b, &inv0, &m);
        let nu = b.ops.len();
        inverse(&mut b, e, &x);
        let ni = b.ops.len();
        let mut marks: Vec<usize> = MARKS.with(|m| m.borrow().clone());
        marks.pop();
        marks.push(nf); marks.push(nr); marks.push(nu); marks.push(ni);
        let (aq, nbits, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"phase-ticks");
        let mut xr = h.finalize_xof();
        let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nbits as usize).max(1), &mut xr);
        let pp = super::super::frogdrop_sched::p();
        let mut st = 0x1234_5678_9ABC_DEFu64;
        let mut rnd = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; st };
        for k in 0..64 {
            let mut v = super::super::frogdrop_sched::N::ZERO;
            for w in 0..4 { v |= super::super::frogdrop_sched::N::from(rnd()) << (64 * w); }
            let m = (super::super::frogdrop_sched::N::from(1u64) << 256) - super::super::frogdrop_sched::N::from(1u64);
            v &= m;
            if v >= pp { v -= pp; }
            super::super::tests_strip::put(&mut s.qubits, &x, k, v);
        }
        let mut from = 0usize; let mut prev = 0u64;
        marks.pop();
        for (t, &to) in marks.iter().enumerate() {
            let to = to.min(b.ops.len());
            s.apply_iter(b.ops[from..to].iter());
            if s.phase != prev { eprintln!("TICKPHASE tick {t} ops {from}..{to} phase {:x} changed {:x} popcount {}", s.phase, s.phase ^ prev, (s.phase ^ prev).count_ones()); prev = s.phase; }
            from = to;
        }
        let im: Vec<(usize, &'static str, usize)> = IMARKS.with(|m| m.borrow().clone());
        for &(t, name, to) in &im {
            s.apply_iter(b.ops[from..to].iter());
            if s.phase != prev {
                eprintln!("INVPHASE tick {t} after {name}: changed {:x} pop {} (ops {from}..{to})", s.phase ^ prev, (s.phase ^ prev).count_ones());
                prev = s.phase;
            }
            from = to;
        }
        s.apply_iter(b.ops[from..ni].iter());
        from = ni;
        eprintln!("INVPHASE last phase {:x}", s.phase);
        eprintln!("TICKPHASE end phase {:x} marks {} stages forward {nf} reduce {nr} undo {nu} inverse {ni}", s.phase, marks.len());
        let mut dirty = 0;
        for q in 0..(aq as usize).max(b.width() as usize) { if !x.iter().any(|z| z.0 as usize == q) && s.qubits[q] != 0 { dirty += 1; } }
        eprintln!("TICKPHASE dirty lanes {dirty}");
        // binary search inside the first bad tick
        if prev != 0 {
            let first = marks.iter().position(|_| true).unwrap();
            let _ = first;
        }
    }
    /// Forward row then exact inverse on random words: shrinks the paired-row phase garbage to a (width, room, seed).
    #[test]
    fn dwalk_pair_witness() {
        let ws: Vec<usize> = std::env::var("PW_W").unwrap_or("300,330,360".into()).split(',').map(|x| x.parse().unwrap()).collect();
        let rooms: Vec<usize> = std::env::var("PW_R").unwrap_or("2,4,8,12,16,20,24,30,40,60,80,120,200".into()).split(',').map(|x| x.parse().unwrap()).collect();
        let trials: usize = std::env::var("PW_T").ok().and_then(|v| v.parse().ok()).unwrap_or(400);
        for &n in &ws { for &room in &rooms {
            let mut b = B::new();
            let src = b.alloc_n(n);
            let tgt = b.alloc_n(n);
            let neg = b.alloc();
            super::super::pointadd_lilypad::test_peak(Some(b.live + room as u64));
            let div = b.new_division();
            let key = if std::env::var_os("PW_NOPAIR").is_some() { None } else { Some((div, 1)) };
            row(&mut b, &src, &tgt, neg, false, key);
            let nf = b.ops.len();
            let tf = b.tof;
            row(&mut b, &src, &tgt, neg, true, key);
            b.close_division(div);
            let (aq, nbits, _, _) = analyze_ops(b.ops.iter());
            let mut bad_phase = 0u64; let mut bad_val = 0u64; let mut first = None;
            for tr in 0..trials {
                let mut h = sha3::Shake256::default();
                h.update(format!("pw{n}/{room}/{tr}").as_bytes());
                let mut xr = h.finalize_xof();
                let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nbits as usize).max(1), &mut xr);
                let mut st = 0x9E3779B97F4A7C15u64 ^ ((n as u64) << 40) ^ ((room as u64) << 20) ^ tr as u64;
                let mut rnd = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; st };
                let mut src0 = vec![]; let mut tgt0 = vec![];
                for &q in src.iter().chain(&tgt) { s.qubits[q.0 as usize] = rnd(); }
                // bias to long carry runs on half the trials
                if tr % 2 == 1 { for i in 0..n { let m = rnd() & rnd(); s.qubits[tgt[i].0 as usize] = (s.qubits[src[i].0 as usize] ^ !m) | 0; } }
                s.qubits[neg.0 as usize] = rnd();
                // PW_P: run the adapter's case. src = short signed word, tgt = +-p - (-1)^neg src, so the forward row lands on +-p.
                if std::env::var_os("PW_P").is_some() {
                    use super::super::frogdrop_sched::N;
                    let pp = super::super::frogdrop_sched::p();
                    let ng = s.qubits[neg.0 as usize];
                    let bits_src: usize = 330.min(n - 2);
                    let mask_n: N = if n >= 384 { !N::ZERO } else { (N::from(1u64) << n) - N::from(1u64) };
                    let mut vals_s = vec![N::ZERO; 64];
                    let mut vals_t = vec![N::ZERO; 64];
                    for k in 0..64 {
                        let mut v = N::ZERO;
                        for w in 0..6 { v |= N::from(rnd()) << (64 * w); }
                        let v = v & ((N::from(1u64) << bits_src) - N::from(1u64));
                        let neg_s = rnd() & 1 == 1;
                        let sv = if neg_s { (!v).wrapping_add(N::from(1u64)) & mask_n } else { v };
                        vals_s[k] = sv;
                        let pos_p = rnd() & 1 == 0;
                        let tp = if pos_p { pp } else { ((!pp).wrapping_add(N::from(1u64))) & mask_n };
                        let ngb = (ng >> k) & 1 == 1;
                        // forward: tgt' = tgt + (-1)^neg src = tp
                        vals_t[k] = if ngb { tp.wrapping_add(sv) & mask_n } else { tp.wrapping_sub(sv) & mask_n };
                    }
                    for k in 0..64 {
                        super::super::tests_strip::put(&mut s.qubits, &src, k, vals_s[k]);
                        super::super::tests_strip::put(&mut s.qubits, &tgt, k, vals_t[k]);
                    }
                }
                for &q in &src { src0.push(s.qubits[q.0 as usize]); }
                for &q in &tgt { tgt0.push(s.qubits[q.0 as usize]); }
                s.apply_iter(b.ops.iter());
                if s.phase != 0 { bad_phase += s.phase.count_ones() as u64; if first.is_none() { first = Some((tr, s.phase)); } }
                let mut v = 0u64;
                for (i, &q) in src.iter().enumerate() { v |= s.qubits[q.0 as usize] ^ src0[i]; }
                for (i, &q) in tgt.iter().enumerate() { v |= s.qubits[q.0 as usize] ^ tgt0[i]; }
                bad_val += v.count_ones() as u64;
            }
            eprintln!("PW n {n} room {room}: T fwd {tf} inv {} shots {} phase_bad {bad_phase} value_bad {bad_val} first {first:?}", b.tof - tf, trials*64);
            let _ = nf;
        } }
    }
}
