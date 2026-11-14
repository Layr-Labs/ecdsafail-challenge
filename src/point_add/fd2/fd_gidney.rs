//! TRACK2 (pane so-track0): Gidney's 2025 constant adder ("A Classical-Quantum Adder with Constant Workspace and Linear
//! Gates", arXiv 2507.23079) for the folds of c and c - 1 in the Horner rounds.
//!
//! `gidney_add`: t += (ctl ? K : 0) mod 2^n on an n-lane window with TWO clean lanes and n - 2 borrowed (dirty) lanes,
//! 3n - O(1) Toffoli (a controlled add costs the same as an uncontrolled one: the control stands in for the 1 bits of K).
//!   1. streaming adder: per bit one Toffoli computes the next carry into one of the two clean lanes, the sum bit is
//!      formed in place, the carry is XORed into a dirty lane and then vented (X-basis measurement, outcome m_k);
//!   2. the vented phase (-1)^(m_k carry_k) is repaired with a second carry-xor into the same dirty lanes, conjugated by
//!      classically controlled Z on them (Z_q CX_{c->q} Z_q CX_{c->q} = Z_c), run on the complemented sum (the carries of
//!      ~(x + K) and of x agree, paper eq. 8).
//! Exact for every input except that the carry out of the top lane is dropped (the caller's fold window).
//! Line-for-line port of the paper authors' reference generator (Zenodo 10.5281/zenodo.15866587, `_add_2_clean_vented`,
//! `_carry_xor`, `_add_n_dirty_2_clean`, CC BY 4.0); `Parity` controls become CNOTs around the Toffoli.
use super::builder::B;
use crate::circuit::{BitId, QubitId};

/// r765b P3NAT: length of the recycled classical-bit range (vent bits of windows up to 67 lanes, plus one erase bit).
pub const RECYCLE_N: usize = 68;
thread_local! {
    /// r765b P3NAT: set only while fd_natinv's native rounds run (`fd_natinv::recycle_on`). While set, `gidney_add`
    /// takes its vent bits from this fixed range and `fd_clean::measured_erase` its bit from the last entry, instead of
    /// fresh ids. Each such bit is written by an HMR and read (z_if / push_cond) only inside the same call, so it is dead
    /// when the call returns: the same reuse as the builder's AndU scratch bit. None (default) = fresh ids as before.
    pub static RECYCLE: std::cell::RefCell<Option<Vec<BitId>>> = std::cell::RefCell::new(None);
}
/// n vent bits: the recycled range's first n entries while it is set, else `b.fresh_bits(n)` (the parent's ids).
fn vent_bits(b: &mut B, n: usize) -> Vec<BitId> {
    match RECYCLE.with(|r| r.borrow().clone()) {
        Some(p) => { assert!(n < p.len(), "recycled bit range too short"); p[..n].to_vec() }
        None => b.fresh_bits(n),
    }
}
/// The measured-erase bit: the recycled range's last entry while it is set, else a fresh id.
pub fn erase_bit(b: &mut B) -> BitId {
    match RECYCLE.with(|r| r.borrow().as_ref().map(|p| p[p.len() - 1])) {
        Some(m) => m,
        None => b.fresh_bits(1)[0],
    }
}

pub fn gidney_on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_GIDNEY").map(|v| v.trim() != "0").unwrap_or(true))
}
/// AND-cell ripple (fd_clean::const_add_ctl) once the pool holds enough measured-clean lanes (FD_POOLADD=0: never).
pub fn poolad_on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_POOLADD").map(|v| v.trim() != "0").unwrap_or(true))
}

#[cfg(test)]
thread_local! { pub static SABOTAGE: std::cell::Cell<bool> = std::cell::Cell::new(false); }

/// stats (builder-level, printed by mod.rs): folds taken by each path
pub static GID_STAT: [std::sync::atomic::AtomicU64; 4] = [
    std::sync::atomic::AtomicU64::new(0), // gidney adders
    std::sync::atomic::AtomicU64::new(0), // pool (AND-cell) adders
    std::sync::atomic::AtomicU64::new(0), // fallbacks to the NAF increments while the switch is on
    std::sync::atomic::AtomicU64::new(0),
];

/// a parity member: constant 0 / 1 or a qubit
#[derive(Clone, Copy)]
enum Par { Zero, One, Q(QubitId) }

/// a control = (q if any) xor p
#[derive(Clone, Copy)]
struct Ctl { q: Option<QubitId>, p: Par }
fn ctl(q: QubitId, p: Par) -> Ctl { Ctl { q: Some(q), p } }

fn toggle(b: &mut B, p: Par, t: QubitId) {
    match p { Par::Zero => {}, Par::One => b.x(t), Par::Q(c) => b.cx(c, t) }
}

/// t ^= c1 & c2 for parity controls (constants fold away; the parity members are applied as X / CX around the gate).
fn ccx_ctl(b: &mut B, c1: Ctl, c2: Ctl, t: QubitId) {
    // resolve a control to (qubit, pre-toggle) or a constant
    enum R { Const(bool), Qb(QubitId, Par) }
    let res = |c: Ctl| -> R {
        match (c.q, c.p) {
            (None, Par::Zero) => R::Const(false),
            (None, Par::One) => R::Const(true),
            (None, Par::Q(r)) => R::Qb(r, Par::Zero),
            (Some(q), p) => R::Qb(q, p),
        }
    };
    let (r1, r2) = (res(c1), res(c2));
    match (r1, r2) {
        (R::Const(false), _) | (_, R::Const(false)) => {}
        (R::Const(true), R::Const(true)) => b.x(t),
        (R::Const(true), R::Qb(q, p)) | (R::Qb(q, p), R::Const(true)) => {
            toggle(b, p, q);
            b.cx(q, t);
            toggle(b, p, q);
        }
        (R::Qb(q1, p1), R::Qb(q2, p2)) => {
            assert!(q1 != q2);
            toggle(b, p1, q1);
            toggle(b, p2, q2);
            b.ccx(q1, q2, t);
            toggle(b, p2, q2);
            toggle(b, p1, q1);
        }
    }
}

/// dst[k] ^= carry_{k+1}(src + K) for k in 0..dst.len() (carry-in 0), src.len() == dst.len() + 1; `off[k]` = bit k of K.
/// 2 dst.len() - 1 Toffoli (minus the ones whose control is the constant 0).
fn carry_xor(b: &mut B, src: &[QubitId], off: &[Par], dst: &[QubitId]) {
    let n = dst.len();
    assert!(src.len() == n + 1 || src.len() == n);
    for k in (1..n).rev() {
        ccx_ctl(b, ctl(src[k], off[k]), ctl(dst[k - 1], Par::Zero), dst[k]);
    }
    for k in 0..n {
        toggle(b, off[k], dst[k]);
    }
    ccx_ctl(b, ctl(src[0], off[0]), Ctl { q: None, p: off[0] }, dst[0]);
    for k in 1..n {
        ccx_ctl(b, ctl(src[k], off[k]), ctl(dst[k - 1], off[k]), dst[k]);
    }
}

/// t += (ctl ? kwin : 0) mod 2^n, n = t.len() >= 3, kwin < 2^127 (bit i of kwin is added at t[i]), carry out of t[n-1]
/// dropped. `clean` = two |0> lanes (returned |0>), `dirty` >= n - 2 lanes of any state (restored). All outside t and ctl.
pub fn gidney_add(b: &mut B, t: &[QubitId], kwin: u128, ctl_q: Option<QubitId>, clean: [QubitId; 2], dirty: &[QubitId]) {
    let n = t.len();
    assert!(n >= 3 && n <= 127 && dirty.len() >= n - 2 && !b.fusion_recording());
    assert!(clean[0] != clean[1]);
    let off: Vec<Par> = (0..n)
        .map(|k| if (kwin >> k) & 1 == 1 { match ctl_q { Some(c) => Par::Q(c), None => Par::One } } else { Par::Zero })
        .collect();
    let dirty = &dirty[..n - 2];
    let vent = vent_bits(b, n);
    // carries[k]: carry into lane k. carries[0] = 0 (None), carries[n-1] = the top lane itself.
    let car = |k: usize| -> Option<QubitId> { if k == 0 { None } else if k == n - 1 { Some(t[n - 1]) } else { Some(clean[k % 2]) } };
    for k in 0..n {
        toggle(b, off[k], t[k]);
    }
    for k in 0..n - 1 {
        let tgt = car(k + 1).unwrap();
        ccx_ctl(b, ctl(t[k], Par::Zero), Ctl { q: car(k), p: off[k] }, tgt);
        if let Some(ck) = car(k) {
            b.cx(ck, t[k]);
            if k >= 1 {
                b.cx(ck, dirty[k - 1]);
                b.hmr_to(ck, vent[k]);
            }
        }
        toggle(b, off[k], tgt);
    }
    for &q in t { b.x(q); }
    for j in 0..n - 2 { b.z_if(dirty[j], vent[j + 1]); }
    carry_xor(b, &t[..n - 1], &off, dirty);
    #[cfg(test)]
    let skip = SABOTAGE.with(|s| s.get());
    #[cfg(not(test))]
    let skip = false;
    if !skip {
        for j in 0..n - 2 { b.z_if(dirty[j], vent[j + 1]); }
    }
    for &q in t { b.x(q); }
}

/// Hook of `modp_frogdrop::add_small`: the fold t += ctrl * k (k = 2^32 + (low << lo)) as ONE controlled constant add over the
/// window t[lo..67) (carries leaving lane 66 are dropped: probability k / 2^67 = 2^-35 per executed fold, parent 5 x 2^-35).
/// Active only while `b.gpool` is non-empty (the Horner round loops of P1 and P4) and no recording is open. Clean lanes: the
/// pool, plus the idle overflow flag ms.k when it is not the control. Returns false when it did not emit (caller folds as before).
pub(crate) fn try_fold(b: &mut B, ms: &super::modp_frogdrop::Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) -> bool {
    use super::fd_clean::FW;
    if b.gpool.is_empty() || !gidney_on() || b.fusion_recording() {
        return false;
    }
    let c = match ctrl { Some(c) => c, None => return false };
    if t.len() < FW || (k >> lo) << lo != k {
        return false;
    }
    let wn = FW - lo;
    let kwin = (k >> lo) as u128;
    let mut cl: Vec<QubitId> = b.gpool.clone();
    if c != ms.k { cl.push(ms.k); }
    let win = &t[lo..FW];
    assert!(!win.contains(&c) && cl.iter().all(|q| !win.contains(q) && *q != c), "fold lanes overlap the window or the control");
    let need = wn - 1 - kwin.trailing_zeros() as usize;
    if poolad_on() && cl.len() >= need {
        super::fd_clean::const_add_ctl(b, win, kwin as u64, c, false, &cl[..need]);
        GID_STAT[1].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return true;
    }
    if cl.len() >= 2 && dirty.len() >= wn - 2 {
        let d = &dirty[..wn - 2];
        assert!(d.iter().all(|q| !win.contains(q) && *q != c && !cl[..2].contains(q)), "fold dirty lanes overlap");
        gidney_add(b, win, kwin, Some(c), [cl[0], cl[1]], d);
        GID_STAT[0].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return true;
    }
    GID_STAT[2].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    false
}

#[cfg(test)]
#[path = "fd_gidney_tests.rs"]
mod tests;
