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
pub const RFZ: usize = 5;
#[inline] pub const fn rfl(t: usize) -> usize { if mt(t) == 0 { RFZ } else { RFLOOR } }
/// lanes of an idle rail during cofactor rows
pub const RMIN: usize = 3;
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
    trim: Option<TrimRec>,
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
/// Common-multiple trim: at tick t0 write (U_0, U_1) = lam (R_0, R_1) + (e_0, e_1). The tick acts on e as it acted on U, and lam only shifts.
/// Rails are normalized first, so rows run at fixed lanes and U never grows; lam digits stay in the lanes the rows free.
#[derive(Clone, Copy)]
pub struct TrimP { pub t0: usize, pub h: usize, pub aw: usize, pub we: usize, pub wh: usize }
pub const TRIM0: Option<TrimP> = Some(TrimP { t0: 78, h: 45, aw: 77, we: 219, wh: 90 });
const TRIM_LAYERS: [usize; 5] = [16, 8, 4, 2, 1];
const TRIM_CW: usize = 7;
const TRIM_UMAX: usize = 31;
fn trim_p() -> Option<TrimP> {
    TRIM0
}
pub struct TrimRec { lam: Vec<Q>, c: Vec<Q>, c0: Option<Q> }

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
    // lanes above the top are sign copies: same value as the top lane, so the test stops there
    let top = CAPV.min(tt.len().min(bb.len()) - 1);
    for i in 2..=top { b.cx(bb[i], tt[i]); b.cx(n, tt[i]); }
    let cz = b.alloc_n(top - 2);
    b.and_c(tt[2], tt[3], cz[0]);
    for i in 4..=top { b.and_c(cz[i - 4], tt[i], cz[i - 3]); }
    b.cx(*cz.last().unwrap(), out);
    for i in (4..=top).rev() { b.and_u(cz[i - 4], tt[i], cz[i - 3]); }
    b.and_u(tt[2], tt[3], cz[0]);
    b.free_n(&cz);
    for i in 2..=top { b.cx(bb[i], tt[i]); b.cx(n, tt[i]); }
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
    // ahead first: its 2 GS - 1 temps do not overlap the compare's
    let ah = b.alloc();
    let cut = anchor.saturating_sub(GOV).max(2);
    let lim = (cut + GS).min(w - 1);
    ahead(b, tt, bb, cut, lim, ah);
    let cd = b.alloc();
    capped(b, tt, bb, n, cd);
    let h = anchor.saturating_sub(LW).min(w.saturating_sub(3));
    let top = (h + LW).min(w - 1);
    let ta: Vec<Q> = (h..top).map(|i| tt[i]).collect();
    let tb: Vec<Q> = (h..top).map(|i| bb[i]).collect();
    for &q in &ta { b.cx(sx, q); }
    for &q in &tb { b.cx(sb, q); }
    let ll = ta.len();
    // X < 2B and B < 2X on lanes shifted by one: the lowest lane has no carry out, so it is skipped; one pad on top, reused
    let z0 = b.alloc();
    let mut a1: Vec<Q> = ta[1..].to_vec(); a1.push(z0);
    let c1: Vec<Q> = tb.clone();
    // Width budget decides per tick: temps (one AND a lane) when the peak allows, else carries on the rail lanes (2 CCX a lane). Same function.
    let need = ll as u64 + 5;
    let ip = cap().saturating_sub(b.live) < need;
    let cw = if ip { Some(b.alloc()) } else { None };
    let u1 = b.alloc();
    let t1 = if ip { vec![] } else { b.alloc_n(ll) };
    if let Some(w) = cw {
        let o = lt_chain_ip(b, &a1, &c1, w);
        b.cx(o, u1);
        lt_undo_ip(b, &a1, &c1, w);
    } else {
        lt_chain(b, &a1, &c1, &t1);
        b.cx(t1[ll - 1], u1);
        lt_undo(b, &a1, &c1, &t1);
    }
    b.free_n(&t1);
    let t2 = if ip { vec![] } else { b.alloc_n(ll) };
    let mut a2: Vec<Q> = tb[1..].to_vec(); a2.push(z0);
    let c2: Vec<Q> = ta.clone();
    let o2c = if let Some(w) = cw { lt_chain_ip(b, &a2, &c2, w) } else { lt_chain(b, &a2, &c2, &t2); t2[ll - 1] };
    let g1 = b.alloc(); let g2 = b.alloc();
    b.and_c(u1, o2c, g1);
    // e = sx ^ sb ^ n ^ 1 sits on n for the AND
    b.cx(sx, n); b.cx(sb, n); b.x(n);
    b.and_c(g1, n, g2);
    b.x(n); b.cx(sb, n); b.cx(sx, n);
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
    b.cx(sx, n); b.cx(sb, n); b.x(n);
    b.and_u(g1, n, g2);
    b.x(n); b.cx(sb, n); b.cx(sx, n);
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
        let t1 = b.alloc_n(ll);
        lt_chain(b, &a1, &c1, &t1);
        b.cx(t1[ll - 1], u1);
        lt_undo(b, &a1, &c1, &t1);
        b.free_n(&t1);
    }
    b.free(u1);
    b.free(z0);
    for &q in &ta { b.cx(sx, q); }
    for &q in &tb { b.cx(sb, q); }
    capped(b, tt, bb, n, cd);
    b.free(cd);
    ahead(b, tt, bb, cut, lim, ah);
    b.free(ah);
}
fn half(b: &mut B, t: &mut Vec<Q>) { let z = t.remove(0); let top = *t.last().unwrap(); b.cx(top, z); t.push(z); }
fn unhalf(b: &mut B, t: &mut Vec<Q>) { let z = t.pop().unwrap(); let top = *t.last().unwrap(); b.cx(top, z); t.insert(0, z); }
fn shift_up(b: &mut B, u: &mut Vec<Q>, s: usize) { for _ in 0..s { let q = u.pop().unwrap(); let top = *u.last().unwrap(); b.cx(top, q); u.insert(0, q); } }
fn shift_dn(b: &mut B, u: &mut Vec<Q>, s: usize) { for _ in 0..s { let q = u.remove(0); let top = *u.last().unwrap(); b.cx(top, q); u.push(q); } }
fn pk(div: usize, t: usize, i: usize) -> Option<(usize, usize)> {
    let _ = i; let on = t < PAIR_T;
    if on { Some((div, t * 32 + i)) } else { None }
}

fn resize(b: &mut B, v: &mut Vec<Q>, w: usize) {
    while v.len() < w { let q = b.alloc(); let top = *v.last().unwrap(); b.cx(top, q); v.push(q); }
    while v.len() > w { let q = v.pop().unwrap(); let top = *v.last().unwrap(); b.cx(top, q); b.free(q); }
}
/// Lanes at the start of tick t: rails, T-role cofactor (known low zeros not held), B-role cofactor, and the zero count.
fn lanes_before(tb: &[[usize; 5]], t: usize) -> (usize, usize, usize, usize) {
    let (r, ut, ub, z) = lanes_plain(tb, t);
    if let Some(p) = trim_p() { if p.t0 == t { return (p.aw, p.we - z, p.we, z); } }
    (r, ut, ub, z)
}
fn lanes_plain(tb: &[[usize; 5]], t: usize) -> (usize, usize, usize, usize) {
    if t == 0 { return (258, 4, 4, 0); }
    let [_, r, u, v, _] = tb[t - 1];
    let z = mt(t - 1) + 1;
    (r.max(RMIN), v - z, u, z)
}
#[allow(unused_variables)]
fn tr(b: &B, t: usize, name: &str) {
    #[cfg(test)]
    if std::env::var_os("DW_TRACE").is_some() { eprintln!("TR t={t} {name} live {} peak {}", b.live, b.peak); }
}
fn tick_fwd(b: &mut B, l: &mut [Vec<Q>; 4], tape: &mut Vec<Q>, dc: &[Q], t: usize, tb: &[[usize; 5]], div: usize) {
    let [ra, rc, wu, wv, anchor] = tb[t];
    let (ra, rc) = (ra.max(rfl(t)), rc.max(RMIN));
    let m = mt(t);
    let z = lanes_before(tb, t).3;
    let a = t & 1;
    let (ir_t, ir_b, iu_t, iu_b) = (a, 1 - a, 2 + a, 3 - a);
    let mut tt = std::mem::take(&mut l[ir_t]);
    let mut bb = std::mem::take(&mut l[ir_b]);
    let mut ut = std::mem::take(&mut l[iu_t]);
    let mut ub = std::mem::take(&mut l[iu_b]);
    resize(b, &mut tt, ra); resize(b, &mut bb, ra);
    let d = b.alloc_n(m);
    let mut n = b.alloc();
    let f = b.alloc();
    for i in 0..m {
        b.cx(tt[1], d[i]); b.cx(bb[1], d[i]);
        row(b, &bb, &tt, d[i], false, pk(div, t, i));
        half(b, &mut tt);
    }
    b.cx(tt[1], n); b.cx(bb[1], n); b.x(n);
    tr(b, t, "rail rows");
    flat_rule(b, &tt, &bb, n, f, anchor);
    tr(b, t, "flat");
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
    let k = b.alloc_n(3);
    let kk = [k[0], k[1], k[2]];
    letter(b, &tt[..CAPV - 1], &kk, &[]);
    rail_s6_barrel_g(b, kk, &tt, None, false, false);
    tr(b, t, "top+barrel");
    // rails idle from here: only their tail lanes stay
    resize(b, &mut tt, rc); resize(b, &mut bb, rc);
    // shrink before the zero lanes come back, so a tick that narrows does not spike
    if ut.len() + z > wu { let w0 = wu - z; resize(b, &mut ut, w0); }
    if ub.len() > wu { resize(b, &mut ub, wu); }
    let mut lowz = b.alloc_n(z);
    lowz.extend(&ut);
    ut = lowz;
    resize(b, &mut ut, wu); resize(b, &mut ub, wu);
    row(b, &ub[..wu - m], &ut[m..], n, false, pk(div, t, 16));
    b.cx(ut[m + 1], n); b.cx(ub[1], n);
    if t > 0 && mt(t - 1) == m { let fp = *tape.last().unwrap(); b.cx(fp, n); }
    for i in (0..m).rev() {
        row(b, &ub[..wu - i], &ut[i..], d[i], false, pk(div, t, 17 + i));
        b.cx(ut[i + 1], d[i]); b.cx(ub[1], d[i]); b.x(d[i]);
    }
    tr(b, t, "cof rows");
    b.free(n); b.free_n(&d);
    resize(b, &mut ub, wv);
    rail_s6_barrel_g(b, kk, &ub, None, true, false);
    tr(b, t, "barrel ub");
    shift_up(b, &mut ub, m + 1);
    counter(b, dc, &kk, true, &[]);
    letter(b, &ub[m + 1..m + 1 + CAPV], &kk, &[]);
    tr(b, t, "end");
    b.free_n(&k);
    let zl: Vec<Q> = ub.drain(..m + 1).collect();
    b.free_n(&zl);
    if !tape_drop(t) { tape.push(f); }
    l[ir_t] = tt; l[ir_b] = bb; l[iu_t] = ut; l[iu_b] = ub;
}
fn tick_inv(b: &mut B, l: &mut [Vec<Q>; 4], tape: &mut Vec<Q>, dc: &[Q], t: usize, tb: &[[usize; 5]], div: usize) {
    let [ra, rc, wu, wv, anchor] = tb[t];
    let (ra, rc) = (ra.max(rfl(t)), rc.max(RMIN));
    let m = mt(t);
    let (pr, put, pub_, z) = lanes_before(tb, t);
    let a = t & 1;
    let (ir_t, ir_b, iu_t, iu_b) = (a, 1 - a, 2 + a, 3 - a);
    let mut tt = std::mem::take(&mut l[ir_t]);
    let mut bb = std::mem::take(&mut l[ir_b]);
    let mut ut = std::mem::take(&mut l[iu_t]);
    let mut ub = std::mem::take(&mut l[iu_b]);
    assert_eq!((tt.len(), bb.len(), ut.len(), ub.len()), (rc, rc, wu, wv - (m + 1)));
    let f = if tape_drop(t) { None } else { Some(tape.pop().unwrap()) };
    let k = b.alloc_n(3);
    let kk = [k[0], k[1], k[2]];
    let mut lowz = b.alloc_n(m + 1);
    lowz.extend(&ub);
    ub = lowz;
    letter(b, &ub[m + 1..m + 1 + CAPV], &kk, &[]);
    imark(b, t, "letter ub");
    counter(b, dc, &kk, false, &[]);
    imark(b, t, "counter");
    shift_dn(b, &mut ub, m + 1);
    rail_s6_barrel_g(b, kk, &ub, None, false, false);
    imark(b, t, "barrel ub");
    resize(b, &mut ub, wu);
    let d = b.alloc_n(m);
    let n = b.alloc();
    for i in 0..m {
        b.x(d[i]); b.cx(ub[1], d[i]); b.cx(ut[i + 1], d[i]);
        row(b, &ub[..wu - i], &ut[i..], d[i], true, pk(div, t, 17 + i));
        imark(b, t, "cof row");
    }
    if t > 0 && mt(t - 1) == m { let fp = *tape.last().unwrap(); b.cx(fp, n); }
    b.cx(ub[1], n); b.cx(ut[m + 1], n);
    row(b, &ub[..wu - m], &ut[m..], n, true, pk(div, t, 16));
    imark(b, t, "cof top");
    let zl: Vec<Q> = ut.drain(..z).collect();
    b.free_n(&zl);
    resize(b, &mut ut, put); resize(b, &mut ub, pub_);
    resize(b, &mut tt, ra); resize(b, &mut bb, ra);
    rail_s6_barrel_g(b, kk, &tt, None, true, false);
    imark(b, t, "barrel tt");
    letter(b, &tt[..CAPV - 1], &kk, &[]);
    b.free_n(&k);
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
    b.free(n); b.free_n(&d);
    resize(b, &mut tt, pr); resize(b, &mut bb, pr);
    l[ir_t] = tt; l[ir_b] = bb; l[iu_t] = ut; l[iu_b] = ub;
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
/// out ^= |a| < |c| (ones' complement magnitudes, sign lane last)
fn rail_lt(b: &mut B, a: &[Q], c: &[Q], out: Q) {
    let n = a.len() - 1;
    let (sa, sc) = (a[n], c[n]);
    for i in 0..n { b.cx(sa, a[i]); b.cx(sc, c[i]); }
    let w = b.alloc();
    let o = lt_chain_ip(b, &a[..n], &c[..n], w);
    b.cx(o, out);
    lt_undo_ip(b, &a[..n], &c[..n], w);
    b.free(w);
    for i in 0..n { b.cx(sa, a[i]); b.cx(sc, c[i]); }
}
/// out ^= the k lanes under the sign lane of d all equal the sign
fn top_is_sign(b: &mut B, d: &[Q], k: usize, out: Q) {
    let n = d.len() - 1;
    let s = d[n];
    let lanes = d[n - k..n].to_vec();
    for &q in &lanes { b.cx(s, q); b.x(q); }
    if k == 1 { b.cx(lanes[0], out); } else {
        let tmp = b.alloc_n(k - 1);
        b.and_c(lanes[0], lanes[1], tmp[0]);
        for i in 2..k { b.and_c(tmp[i - 2], lanes[i], tmp[i - 1]); }
        b.cx(tmp[k - 2], out);
        for i in (2..k).rev() { b.and_u(tmp[i - 2], lanes[i], tmp[i - 1]); }
        b.and_u(lanes[0], lanes[1], tmp[0]);
        b.free_n(&tmp);
    }
    for &q in &lanes { b.x(q); b.cx(s, q); }
}
/// out ^= both arrays, without their top lane, can shift up by k
fn both_top(b: &mut B, d: &[Q], a: &[Q], k: usize, out: Q) {
    let t1 = b.alloc(); let t2 = b.alloc();
    top_is_sign(b, &d[..d.len() - 1], k, t1);
    top_is_sign(b, &a[..a.len() - 1], k, t2);
    b.ccx(t1, t2, out);
    top_is_sign(b, &a[..a.len() - 1], k, t2);
    top_is_sign(b, &d[..d.len() - 1], k, t1);
    b.free(t1); b.free(t2);
}
fn cswap_lanes(b: &mut B, sel: Q, l: &[Vec<Q>; 4], zo2: usize, zo3: usize, lo: usize, hi: usize, aw: usize) {
    for i in 0..aw { b.cswap(sel, l[0][i], l[1][i]); }
    for i in lo..hi { b.cswap(sel, l[2][i - zo2], l[3][i - zo3]); }
}
/// (array width, top row, bottom row, array low lane, implicit zeros on cofactors 2 and 3)
fn trim_geom(tb: &[[usize; 5]], p: TrimP) -> (usize, usize, usize, usize, usize, usize) {
    let t = p.t0;
    let [_, _, u, v, _] = tb[t - 1];
    let z = mt(t - 1) + 1;
    let iu_t = 2 + (t & 1);
    let (zo2, zo3) = (if iu_t == 2 { z } else { 0 }, if iu_t == 3 { z } else { 0 });
    let w = u.max(v) + 1;
    let top = w - p.aw - 1;
    let s_ = top + 1 - p.h;
    (w, top, s_, s_ - TRIM_UMAX, zo2, zo3)
}
fn rails_norm(b: &mut B, l: &[Vec<Q>; 4], nb: &[Q]) {
    for (j, &k) in TRIM_LAYERS.iter().enumerate() {
        top_is_sign(b, &l[1], k, nb[j]);
        shift_layer(b, &l[1], nb[j], k, false);
        shift_layer(b, &l[0], nb[j], k, false);
    }
}
fn rails_unnorm(b: &mut B, l: &[Vec<Q>; 4], nb: &[Q]) {
    for (j, &k) in TRIM_LAYERS.iter().enumerate().rev() {
        shift_layer(b, &l[0], nb[j], k, true);
        shift_layer(b, &l[1], nb[j], k, true);
        top_is_sign(b, &l[1], k, nb[j]);
    }
}
/// binary low lane first from the layers, largest first
fn bin(nb: &[Q]) -> Vec<Q> { nb.iter().rev().copied().collect() }
fn trim_fwd(b: &mut B, l: &mut [Vec<Q>; 4], dc: &[Q], tb: &[[usize; 5]], p: TrimP) -> TrimRec {
    let (w, top, s_, lw, zo2, zo3) = trim_geom(tb, p);
    let (aw, we) = (p.aw, p.we);
    for j in 0..2 { let mut x = std::mem::take(&mut l[j]); resize(b, &mut x, aw); l[j] = x; }
    { let mut x = std::mem::take(&mut l[2]); resize(b, &mut x, w - zo2); l[2] = x; }
    { let mut x = std::mem::take(&mut l[3]); resize(b, &mut x, w - zo3); l[3] = x; }
    let sel = b.alloc();
    { let (a0, a1) = (l[0].clone(), l[1].clone()); rail_lt(b, &a1, &a0, sel); }
    cswap_lanes(b, sel, l, zo2, zo3, lw, w, aw);
    let nd = b.alloc_n(TRIM_LAYERS.len());
    rails_norm(b, l, &nd);
    let nu = b.alloc_n(TRIM_LAYERS.len());
    for (j, &k) in TRIM_LAYERS.iter().enumerate() {
        let (ad, aa) = (l[3][lw - zo3..].to_vec(), l[2][lw - zo2..].to_vec());
        both_top(b, &ad, &aa, k, nu[j]);
        shift_layer(b, &ad, nu[j], k, false);
        shift_layer(b, &aa, nu[j], k, false);
    }
    let (rd, ra) = (l[1].clone(), l[0].clone());
    let (sd, sa) = (rd[aw - 1], ra[aw - 1]);
    for i in (s_..=top).rev() {
        let dl = l[3][i + aw - zo3];
        b.cx(sd, dl); b.x(dl);
        let tgt: Vec<Q> = l[3][i - zo3..i + aw - zo3].to_vec();
        row(b, &rd, &tgt, dl, false, None);
        let tgt2: Vec<Q> = l[2][i - zo2..].to_vec();
        rowx(b, &ra, sa, &tgt2, dl, false);
    }
    let lam = l[3].split_off(s_ + aw - zo3);
    for (j, &k) in TRIM_LAYERS.iter().enumerate().rev() {
        shift_layer(b, &l[3][lw - zo3..].to_vec(), nu[j], k, true);
        shift_layer(b, &l[2][lw - zo2..].to_vec(), nu[j], k, true);
    }
    // C = dc + n_D + (31 - n_U): the position of lam_f is fixed plus C - dc at the end. n_D is read again from the rails.
    let mut c = bin(&nu);
    for &q in &c { b.x(q); }
    c.extend(b.alloc_n(TRIM_CW - TRIM_LAYERS.len()));
    let zw = b.alloc();
    let pool = b.alloc_n(TRIM_CW - 1);
    let mut src = bin(&nd);
    while src.len() < TRIM_CW { src.push(zw); }
    super::chunked::chunk_ripple(b, &src, &c, &pool);
    super::chunked::chunk_ripple(b, &dc[..TRIM_CW], &c, &pool);
    b.free_n(&pool);
    b.free(zw);
    rails_unnorm(b, l, &nd);
    b.free_n(&nd);
    { let mut x = std::mem::take(&mut l[3]); resize(b, &mut x, we - zo3); l[3] = x; }
    { let mut x = std::mem::take(&mut l[2]); resize(b, &mut x, we - zo2); l[2] = x; }
    cswap_lanes(b, sel, l, zo2, zo3, lw, we, aw);
    { let (a0, a1) = (l[0].clone(), l[1].clone()); rail_lt(b, &a1, &a0, sel); }
    b.free(sel);
    TrimRec { lam, c, c0: None }
}
fn trim_inv(b: &mut B, l: &mut [Vec<Q>; 4], dc: &[Q], tb: &[[usize; 5]], p: TrimP, rec: TrimRec) {
    let (w, top, s_, lw, zo2, zo3) = trim_geom(tb, p);
    let (aw, we) = (p.aw, p.we);
    let TrimRec { lam, mut c, .. } = rec;
    let sel = b.alloc();
    { let (a0, a1) = (l[0].clone(), l[1].clone()); rail_lt(b, &a1, &a0, sel); }
    cswap_lanes(b, sel, l, zo2, zo3, lw, we, aw);
    { let mut x = std::mem::take(&mut l[3]); resize(b, &mut x, s_ + aw - zo3); l[3] = x; }
    { let mut x = std::mem::take(&mut l[2]); resize(b, &mut x, w - zo2); l[2] = x; }
    let nd = b.alloc_n(TRIM_LAYERS.len());
    rails_norm(b, l, &nd);
    {
        let zw = b.alloc();
        let pool = b.alloc_n(TRIM_CW - 1);
        let mut src = bin(&nd);
        while src.len() < TRIM_CW { src.push(zw); }
        for &q in &c { b.x(q); }
        super::chunked::chunk_ripple(b, &dc[..TRIM_CW], &c, &pool);
        super::chunked::chunk_ripple(b, &src, &c, &pool);
        for &q in &c { b.x(q); }
        b.free_n(&pool);
        b.free(zw);
    }
    let up = c.split_off(TRIM_LAYERS.len());
    b.free_n(&up);
    for &q in &c { b.x(q); }
    let nu: Vec<Q> = bin(&c);
    for (j, &k) in TRIM_LAYERS.iter().enumerate() {
        shift_layer(b, &l[3][lw - zo3..].to_vec(), nu[j], k, false);
        shift_layer(b, &l[2][lw - zo2..].to_vec(), nu[j], k, false);
    }
    l[3].extend(&lam);
    let (rd, ra) = (l[1].clone(), l[0].clone());
    let (sd, sa) = (rd[aw - 1], ra[aw - 1]);
    for i in s_..=top {
        let dl = l[3][i + aw - zo3];
        let tgt2: Vec<Q> = l[2][i - zo2..].to_vec();
        rowx(b, &ra, sa, &tgt2, dl, true);
        let tgt: Vec<Q> = l[3][i - zo3..i + aw - zo3].to_vec();
        row(b, &rd, &tgt, dl, true, None);
        b.x(dl); b.cx(sd, dl);
    }
    for (j, &k) in TRIM_LAYERS.iter().enumerate().rev() {
        let (ad, aa) = (l[3][lw - zo3..].to_vec(), l[2][lw - zo2..].to_vec());
        shift_layer(b, &aa, nu[j], k, true);
        shift_layer(b, &ad, nu[j], k, true);
        both_top(b, &ad, &aa, k, nu[j]);
    }
    b.free_n(&nu);
    rails_unnorm(b, l, &nd);
    b.free_n(&nd);
    cswap_lanes(b, sel, l, zo2, zo3, lw, w, aw);
    { let (a0, a1) = (l[0].clone(), l[1].clone()); rail_lt(b, &a1, &a0, sel); }
    b.free(sel);
    let (pr, put, pub_, _) = lanes_plain(tb, p.t0);
    for j in 0..2 { let mut x = std::mem::take(&mut l[j]); resize(b, &mut x, pr); l[j] = x; }
    let iu_t = 2 + (p.t0 & 1);
    let i_ub = 5 - iu_t;
    { let mut x = std::mem::take(&mut l[iu_t]); resize(b, &mut x, put); l[iu_t] = x; }
    { let mut x = std::mem::take(&mut l[i_ub]); resize(b, &mut x, pub_); l[i_ub] = x; }
}
/// X = lam 2^(lane base + C - dc) on ov + wh lanes, where lane ov is lane 256 of the integer.
fn lam_x(b: &mut B, rec: &TrimRec, dc: &[Q], tb: &[[usize; 5]], p: TrimP, inv: bool, x: &[Q]) {
    let (_, _, s_, _, _, _) = trim_geom(tb, p);
    let pp: usize = (p.t0..R).map(|t| mt(t) + 1).sum();
    let ov = lam_ov(tb, p);
    let base = (s_ + pp + ov) - 256 - TRIM_UMAX;
    let (lam, c) = (&rec.lam, &rec.c);
    let h = lam.len();
    let wx = x.len();
    let pool = b.alloc_n(TRIM_CW - 1);
    if !inv {
        // lam / 2^s in two's complement: low lane 1, then the digits, top lane the negated last digit
        b.x(x[base]);
        for i in 0..h { b.cx(lam[i], x[base + 1 + i]); }
        b.x(x[base + h]);
        for j in base + h + 1..wx { b.cx(x[base + h], x[j]); }
        for &q in c { b.x(q); }
        super::chunked::chunk_ripple(b, &dc[..TRIM_CW], c, &pool);
        for &q in c { b.x(q); }
        for j in 0..TRIM_CW { shift_layer(b, x, c[j], 1 << j, false); }
    } else {
        for j in (0..TRIM_CW).rev() { shift_layer(b, x, c[j], 1 << j, true); }
        for &q in c { b.x(q); }
        b.begin();
        super::chunked::chunk_ripple(b, &dc[..TRIM_CW], c, &pool);
        let r = b.end();
        b.play(&r, true);
        for &q in c { b.x(q); }
        for j in (base + h + 1..wx).rev() { b.cx(x[base + h], x[j]); }
        b.x(x[base + h]);
        for i in (0..h).rev() { b.cx(lam[i], x[base + 1 + i]); }
        b.x(x[base]);
    }
    b.free_n(&pool);
}
fn lam_ov(tb: &[[usize; 5]], p: TrimP) -> usize {
    let (_, _, s_, _, _, _) = trim_geom(tb, p);
    let pp: usize = (p.t0..R).map(|t| mt(t) + 1).sum();
    (256 + TRIM_UMAX).saturating_sub(s_ + pp)
}
/// e_0 + (-1)^s0 lam_f: the lanes under 256 are added in place with one carry wire, the high lanes go to a fresh hi.
fn hi_true_build(b: &mut B, u0: &[Q], rec: &mut TrimRec, dc: &[Q], s0: Q, tb: &[[usize; 5]], p: TrimP, low_too: bool) -> Vec<Q> {
    let ov = lam_ov(tb, p);
    let hi = b.alloc_n(p.wh);
    let e = &u0[256..];
    for j in 0..p.wh { b.cx(e[j.min(e.len() - 1)], hi[j]); }
    let x = b.alloc_n(ov + p.wh);
    lam_x(b, rec, dc, tb, p, false, &x);
    let zw = b.alloc();
    if ov > 0 {
        if low_too {
            let c0 = b.alloc();
            let mut t: Vec<Q> = u0[256 - ov..256].to_vec();
            t.push(c0);
            rowx(b, &x[..ov], zw, &t, s0, false);
            rec.c0 = Some(c0);
        }
        rowx(b, &[rec.c0.unwrap()], zw, &hi, s0, false);
    }
    rowx(b, &x[ov..], x[ov + p.wh - 1], &hi, s0, false);
    b.free(zw);
    lam_x(b, rec, dc, tb, p, true, &x);
    b.free_n(&x);
    hi
}
fn hi_true_undo(b: &mut B, u0: &[Q], rec: &mut TrimRec, dc: &[Q], s0: Q, tb: &[[usize; 5]], p: TrimP, hi: Vec<Q>, low_too: bool) {
    let ov = lam_ov(tb, p);
    let x = b.alloc_n(ov + p.wh);
    lam_x(b, rec, dc, tb, p, false, &x);
    let zw = b.alloc();
    rowx(b, &x[ov..], x[ov + p.wh - 1], &hi, s0, true);
    if ov > 0 {
        rowx(b, &[rec.c0.unwrap()], zw, &hi, s0, true);
        if low_too {
            let c0 = rec.c0.take().unwrap();
            let mut t: Vec<Q> = u0[256 - ov..256].to_vec();
            t.push(c0);
            rowx(b, &x[..ov], zw, &t, s0, true);
            b.free(c0);
        }
    }
    b.free(zw);
    lam_x(b, rec, dc, tb, p, true, &x);
    b.free_n(&x);
    let e = &u0[256..];
    for j in 0..p.wh { b.cx(e[j.min(e.len() - 1)], hi[j]); }
    b.free_n(&hi);
}
pub fn forward(b: &mut B, x: &[Q]) -> DwEnd {
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
    let logs = vec![];
    let trimp = trim_p();
    let mut trec = None;
    for t in 0..R {
        if let Some(p) = trimp { if p.t0 == t { trec = Some(trim_fwd(b, &mut l, &dc, &tb, p)); } }
        tick_fwd(b, &mut l, &mut tape, &dc, t, &tb, div);
        #[cfg(test)]
        MARKS.with(|m| m.borrow_mut().push(b.ops.len()));
    }
    #[cfg(test)]
    MARKS.with(|m| m.borrow_mut().push(usize::MAX));
    // end: rails +-1, signs on the top lanes; the last tick's shifted cofactor gets its zero lanes back, both to one width
    let iub = 3 - ((R - 1) & 1);
    let zl = mt(R - 1) + 1;
    let mut lowz = b.alloc_n(zl);
    lowz.extend(&l[iub]);
    l[iub] = lowz;
    let wend = l[2].len().max(l[3].len());
    { let mut x2 = std::mem::take(&mut l[2]); resize(b, &mut x2, wend); l[2] = x2; }
    { let mut x3 = std::mem::take(&mut l[3]); resize(b, &mut x3, wend); l[3] = x3; }
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
    let m0 = if let (Some(p), Some(r)) = (trimp, &mut trec) {
        let hi = hi_true_build(b, &u0, r, &dc, s0, &tb, p, true);
        let m0 = reduce_fwd_short(b, &u0[..256], &hi);
        hi_true_undo(b, &u0, r, &dc, s0, &tb, p, hi, false);
        m0
    } else { reduce_fwd(b, &u0) };
    b.cx(refl, s0);
    // D' in place mod p: hi holds only U0's top lanes, no D lanes
    let lo = u0[..256].to_vec();
    let zw = b.alloc();
    let mut ms = vec![];
    for i in 0..DB { ms.push(mod_shift_fwd(b, &lo, dc[i], 1 << i, zw)); }
    b.free(zw);
    DwEnd { tape, dc, refl, s0, s1, r0low, r1low, u0: lo, u1, ext: u0, logs, div, wc_end, sp: None, trim: trec, nsm: Some((m0, ms)) }
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
pub fn inverse(b: &mut B, e: DwEnd, x: &[Q]) {
    let tb = tab();
    let DwEnd { mut tape, dc, refl, s0, s1, r0low, r1low, u0: lo, u1, ext, logs, div, wc_end, nsm, trim: trec, .. } = e;
    let (m0, ms) = nsm.unwrap();
    let zw = b.alloc();
    for i in (0..DB).rev() { mod_shift_undo(b, &lo, dc[i], 1 << i, zw, &ms[i]); imark(b, 900 + i, "unshift"); }
    b.free(zw);
    let u0 = ext;
    b.cx(refl, s0);
    let mut trec = trec;
    if let (Some(p), Some(r)) = (trim_p(), &mut trec) {
        let hi = hi_true_build(b, &u0, r, &dc, s0, &tb, p, false);
        reduce_undo_short(b, &u0[..256], &hi, &m0);
        hi_true_undo(b, &u0, r, &dc, s0, &tb, p, hi, true);
    } else { reduce_undo(b, &u0, &m0); }
    assert_eq!(u0.len(), wc_end);
    let u1 = b.alloc_n(u1.len());
    sign_pattern(b, &u1, s0);
    imark(b, 910, "pattern");
    let nq = b.alloc();
    b.cx(s0, nq); b.cx(s1, nq); b.x(nq);
    row(b, &u0, &u1, nq, true, None);
    imark(b, 911, "row u1");
    b.x(nq); b.cx(s1, nq); b.cx(s0, nq);
    b.free(nq);
    let mut r0 = b.alloc_n(r0low.len()); r0.push(s0);
    let mut r1 = b.alloc_n(r1low.len()); r1.push(s1);
    rail_clear(b, &r0); rail_clear(b, &r1);
    let mut l = [r0, r1, u0, u1];
    // back to the state after the last tick
    {
        let last = R - 1;
        let [_, _, wu, wv, _] = tb[last];
        let zl = mt(last) + 1;
        let iub = 3 - (last & 1);
        let iut = 2 + (last & 1);
        let mut a1 = std::mem::take(&mut l[iut]); resize(b, &mut a1, wu); l[iut] = a1;
        let mut a2 = std::mem::take(&mut l[iub]); resize(b, &mut a2, wv);
        let lows: Vec<Q> = a2.drain(..zl).collect();
        b.free_n(&lows);
        l[iub] = a2;
    }
    imark(b, 999, "adapter");
    for t in (0..R).rev() {
        tick_inv(b, &mut l, &mut tape, &dc, t, &tb, div); imark(b, t, "unfit");
        if let Some(p) = trim_p() { if p.t0 == t { trim_inv(b, &mut l, &dc, &tb, p, trec.take().unwrap()); } }
    }
    let [r0, r1, u0, u1] = l;
    for i in 0..DB { if (E_INIT >> i) & 1 == 1 { b.x(dc[i]); } }
    b.free_n(&dc);
    let p = super::frogdrop_sched::p();
    b.x(u1[0]);
    b.free_n(&u0); b.free_n(&u1);
    // rail lanes may sit on any wires now: swap them back onto x (0 T)
    let mut cur = r1.clone();
    let n1 = cur.len();
    cur.extend(&r0);
    for i in 0..256 {
        if cur[i] == x[i] { continue; }
        if let Some(k) = cur.iter().position(|&q| q == x[i]) {
            b.swap(cur[i], cur[k]);
            cur.swap(i, k);
        } else {
            b.acquire(x[i]);
            b.swap(cur[i], x[i]);
            b.free(cur[i]);
            cur[i] = x[i];
        }
    }
    b.free_n(&cur[256..n1]);
    let r0 = cur[n1..].to_vec();
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
/// As reduce_fwd, with the add on the chunked plan, for the short pool at the end of a trimmed walk.
fn reduce_fwd_short(b: &mut B, lo: &[Q], hi: &[Q]) -> Vec<BitId> {
    let n = hi.len() + 34;
    let tq = b.alloc_n(n);
    let zw = b.alloc();
    let ms = Ms::alloc_room(b, cap());
    b.begin();
    tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    ms.release(b);
    rowx(b, &tq, tq[n - 1], lo, zw, false);
    let m = b.fresh_bits(n);
    for i in 0..n { b.hmr_to(tq[i], m[i]); }
    b.free(zw);
    b.free_n(&tq);
    m
}
fn reduce_undo_short(b: &mut B, lo: &[Q], hi: &[Q], m: &[BitId]) {
    let n = hi.len() + 34;
    assert_eq!(m.len(), n);
    let tq = b.alloc_n(n);
    let zw = b.alloc();
    let ms = Ms::alloc_room(b, cap());
    b.begin();
    tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    ms.release(b);
    for i in 0..n { b.z_if(tq[i], m[i]); }
    rowx(b, &tq, tq[n - 1], lo, zw, true);
    let ms = Ms::alloc_room(b, cap());
    b.begin();
    tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, true);
    ms.release(b);
    b.free(zw);
    b.free_n(&tq);
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
