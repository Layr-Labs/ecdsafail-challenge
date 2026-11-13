//! KT13 (pane op-v, q765 v4): native inverses for the compute / phase / uncompute products P2 and P5.
//!
//! The parent records the Horner rounds of P2 and P5 and plays the recording forward and backward. A recording may not
//! contain a measurement, so neither pass can use the Track 2 adder (`fd_gidney`) or the Track 1 measured flag erase. Here
//! the forward rounds are emitted straight-line and the uncompute pass is emitted as its own gate list, in which every
//! group is the exact inverse permutation of its forward group:
//!   doubling   relabel + window add of (c - 1) under the top bit on z[4..67)      <->  window subtract + relabel back
//!   add        ripple, window add of c under the overflow flag k, erase of k       <->  k := compare, window subtract, reversed ripple
//! A window add mod 2^n and "complement the window, add, complement" are inverse permutations of the window whatever
//! carries leave it. The forward erase maps k = compare to 0 (by measurement, phase repaired, or by the compare itself);
//! the inverse writes the same compare into the zero flag. The fold path (adder or the parent's increments) is chosen by
//! one predicate in both directions (`fold_ready`), and the build panics if `fd_gidney::try_fold` disagrees with it.
//! Switch FD_NATINV (default on); off re-emits the parent's stream.
use super::builder::{B, G};
use super::fd_clean::FW;
use super::modp_frogdrop::{add_small, ctrl_neg, Ms, C, CMPT};
use crate::circuit::QubitId;

pub fn on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_NATINV").map(|v| v.trim() != "0").unwrap_or(false)) // q765 v5-p5shell: default off (count of record ran FD_NATINV=0)
}
fn env_usize(name: &str) -> Option<usize> {
    std::env::var(name).ok().and_then(|v| v.trim().parse::<usize>().ok())
}
/// Extra clean lanes offered to P2's folds (beside the seed flag). One makes the add's fold a Gidney add. Override FD_P2X.
pub fn p2x() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| env_usize("FD_P2X").unwrap_or(1))
}
/// Extra clean lanes offered to P5's folds. Today's tree has none at P5 (765 live at consume width 11); a tree with no
/// stop information has one at width 6. Override FD_P5X.
pub fn p5x() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| env_usize("FD_P5X").unwrap_or(0))
}
/// P2's consume width: the parent's PCONSUME when the switch is off; PCONSUME + p2x() when on, so that P2 stays at
/// 512 + 2 + (256 - w) + p2x() = 765 lanes. Override FD_P2W.
pub fn p2w() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| {
        let base = super::pointadd_frogdrop::pconsume();
        env_usize("FD_P2W").unwrap_or(if on() { base + p2x() } else { base })
    })
}

/// COUNT-ONLY stand-in for a walk that ends with no stop information (FD_S0STUB=1). After a forward walk it hands the
/// allocator the counter lanes cnt[1..6] and the ring lane that hosts cnt[6]; cnt[0] stays live as the sign lane (the
/// stand-in for the sign hosted in the inverse's top lane). Live is then 255 + 1 + 256 = 512, the ledger of a canonical
/// design. The products may reuse those lanes, so the emitted stream is NOT a valid circuit: use it with the stream
/// discarded, for stage counts and stage peaks only.
pub fn s0stub() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| {
        let v = std::env::var("FD_S0STUB").is_ok();
        if v { eprintln!("FD_S0STUB: count-only build, the emitted stream is not a valid circuit"); }
        v
    })
}
pub fn s0_park(b: &mut B, cnt: &[QubitId], top: QubitId) {
    if !s0stub() { return; }
    for &q in &cnt[1..cnt.len() - 1] { b.free(q); }
    b.free(top);
}
pub fn s0_unpark(b: &mut B, cnt: &[QubitId], top: QubitId) {
    if !s0stub() { return; }
    b.acquire(top);
    for &q in cnt[1..cnt.len() - 1].iter().rev() { b.acquire(q); }
}

#[cfg(test)]
thread_local! { pub static SABOTAGE: std::cell::Cell<bool> = std::cell::Cell::new(false); }

/// t += a mod 2^n (TTK ripple, a restored), k ^= carry out. 2n - 1 Toffoli. (Copy of fd_shell's private ttk_add_unc.)
fn ttk_add_unc(b: &mut B, a: &[QubitId], t: &[QubitId], k: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
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

/// k ^= carry_out(t + a), t and a restored. 2n - 1 Toffoli. (Copy of fd_shell's private ttk_carry_unc.)
fn ttk_carry_unc(b: &mut B, a: &[QubitId], t: &[QubitId], k: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    b.begin();
    for i in 1..n { b.cx(a[i], t[i]); }
    let s1 = b.end();
    b.play(&s1, false);
    b.cx(a[n - 1], k);
    b.begin();
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    let s23 = b.end();
    b.play(&s23, false);
    b.ccx(t[n - 1], a[n - 1], k);
    b.play(&s23, true);
    b.play(&s1, true);
}

/// Would `fd_gidney::try_fold` emit for this call? Mirrors its conditions without emitting anything.
fn fold_ready(b: &B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64, dirty: &[QubitId]) -> bool {
    if b.gpool.is_empty() || !super::fd_gidney::gidney_on() || b.fusion_recording() {
        return false;
    }
    if t.len() < FW || (k >> lo) << lo != k {
        return false;
    }
    let wn = FW - lo;
    let kwin = (k >> lo) as u128;
    let ncl = b.gpool.len() + if ctrl != ms.k { 1 } else { 0 };
    let need = wn - 1 - kwin.trailing_zeros() as usize;
    (super::fd_gidney::poolad_on() && ncl >= need) || (ncl >= 2 && dirty.len() >= wn - 2)
}

/// t += ctrl * k on the fold window (as `modp_frogdrop::add_small`), with the path fixed by `fold_ready`.
fn fold_add(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64, dirty: &[QubitId]) {
    if fold_ready(b, ms, t, lo, ctrl, k, dirty) {
        let done = super::fd_gidney::try_fold(b, ms, t, lo, Some(ctrl), k, dirty);
        assert!(done, "fold_ready disagrees with try_fold");
    } else {
        let pool = std::mem::take(&mut b.gpool);
        add_small(b, ms, t, lo, Some(ctrl), k, dirty);
        b.gpool = pool;
    }
}

/// Exact inverse of `fold_add` with the same arguments and the same pool.
fn fold_sub(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64, dirty: &[QubitId]) {
    if fold_ready(b, ms, t, lo, ctrl, k, dirty) {
        for &q in &t[lo..FW] { b.x(q); }
        let done = super::fd_gidney::try_fold(b, ms, t, lo, Some(ctrl), k, dirty);
        assert!(done, "fold_ready disagrees with try_fold");
        for &q in &t[lo..FW] { b.x(q); }
    } else {
        let pool = std::mem::take(&mut b.gpool);
        b.begin();
        add_small(b, ms, t, lo, Some(ctrl), k, dirty);
        let r = b.end();
        b.play(&r, true);
        b.gpool = pool;
    }
}

/// z <- 2 z mod p (as `modp_frogdrop::mod_double`).
fn double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    fold_add(b, ms, z, 4, h, C - 1, dirty);
}

/// Exact inverse of `double`.
fn halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    let h = z[0];
    fold_sub(b, ms, z, 4, h, C - 1, dirty);
    let low = z.remove(0);
    z.push(low);
}

/// k ^= [z < y] read on the top CMPT lanes (carry of ~z_top + y_top); z and y restored.
fn flag_compare(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    for &q in zt { b.x(q); }
    ttk_carry_unc(b, yt, zt, ms.k);
    for &q in zt { b.x(q); }
}

/// z += y mod p, lazy (as `fd_shell::modadd_unc`); y 256 lanes, restored; ms.k |0> in and out.
fn add_fwd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    assert!(z.len() == 256 && y.len() == 256);
    ttk_add_unc(b, y, z, ms.k);
    fold_add(b, ms, z, 0, ms.k, C, y);
    if super::fd_clean::measured_ok(b) {
        super::fd_clean::measured_erase(b, ms.k, &y[256 - CMPT..], &z[256 - CMPT..], &[], ms.k, ms.k);
    } else {
        flag_compare(b, ms, z, y);
    }
}

/// Exact inverse of `add_fwd`: the flag is written back by the compare, the fold is subtracted on its window, and the
/// ripple is played backwards.
fn add_inv(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    assert!(z.len() == 256 && y.len() == 256);
    flag_compare(b, ms, z, y);
    #[cfg(test)]
    let skip = SABOTAGE.with(|s| s.get());
    #[cfg(not(test))]
    let skip = false;
    if !skip {
        fold_sub(b, ms, z, 0, ms.k, C, y);
    }
    b.begin();
    ttk_add_unc(b, y, z, ms.k);
    let r = b.end();
    b.play(&r, true);
}

/// One Horner round: z = 2z + y (bit None, the `pre` round), or 2z + y (bit 1) / 2z - y (bit 0) as `fd_shell::sround`.
fn round_fwd(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], bit: Option<QubitId>) {
    double(b, ms, z, y);
    if let Some(c) = bit {
        b.x(c);
        for &q in z.iter() { b.cx(c, q); }
    }
    add_fwd(b, ms, z, y);
    if let Some(c) = bit {
        for &q in z.iter() { b.cx(c, q); }
        b.x(c);
    }
}

/// Exact inverse of `round_fwd`.
fn round_inv(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], bit: Option<QubitId>) {
    if let Some(c) = bit {
        b.x(c);
        for &q in z.iter() { b.cx(c, q); }
    }
    add_inv(b, ms, z, y);
    if let Some(c) = bit {
        for &q in z.iter() { b.cx(c, q); }
        b.x(c);
    }
    halve(b, ms, z, y);
}

/// After the signed rounds: z = (z - y) / 2 (as `fd_shell::post`).
fn post_fwd(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId]) {
    for &q in z.iter() { b.x(q); }
    add_fwd(b, ms, z, y);
    for &q in z.iter() { b.x(q); }
    halve(b, ms, z, y);
}

/// Exact inverse of `post_fwd`.
fn post_inv(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId]) {
    double(b, ms, z, y);
    for &q in z.iter() { b.x(q); }
    add_inv(b, ms, z, y);
    for &q in z.iter() { b.x(q); }
}

/// What the uncompute pass needs from the forward pass.
pub struct Nat {
    pub on: bool,
    clean: Vec<QubitId>,
    extra: Vec<QubitId>,
    zz: Vec<QubitId>,
    z: Vec<QubitId>,
    alow: Vec<QubitId>,
    y: Vec<QubitId>,
    tail: Vec<G>,
}

impl Nat {
    /// Placeholder when the switch is off: the caller plays the parent's recording instead.
    pub fn off() -> Nat {
        Nat { on: false, clean: vec![], extra: vec![], zz: vec![], z: vec![], alow: vec![], y: vec![], tail: vec![] }
    }

    /// The uncompute pass: exact inverse of `rounds_fwd`. Frees the extra clean lanes. No-op when off.
    pub fn inverse(&self, b: &mut B, ms: &Ms) {
        if !self.on {
            return;
        }
        assert!(!b.fusion_recording());
        b.play(&self.tail, true);
        let n = self.alow.len();
        let mut zz = self.zz.clone();
        b.gpool = self.clean.clone();
        post_inv(b, ms, &mut zz, &self.y);
        for i in 0..n {
            round_inv(b, ms, &mut zz, &self.y, Some(self.alow[i]));
        }
        round_inv(b, ms, &mut zz, &self.y, None);
        b.gpool.clear();
        assert_eq!(zz, self.z);
        b.free_n(&self.extra);
    }
}

/// The Horner part of a consume product, emitted straight-line: the same map as
/// `pointadd_frogdrop::rec_rounds_ms_w(b, ms, z, alow, y, neg, false)` played forward (z holds the seed's S * y on
/// entry and (S 2^n + alow) * y, negated under `neg`, on exit). `flag` is the seed's flag lane (|0> after the seed);
/// `nx` more clean lanes are allocated here and freed by `Nat::inverse`. Returns the handle for the uncompute pass and
/// an empty recording (so the caller's `b.play(&r, ..)` lines emit nothing).
pub fn rounds_fwd(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>,
                  flag: QubitId, nx: usize) -> (Nat, Vec<G>) {
    assert!(!b.fusion_recording() && z.len() == 256 && y.len() == 256 && !alow.is_empty());
    assert!(alow.iter().all(|q| !z.contains(q) && !y.contains(q)) && !z.contains(&flag) && !y.contains(&flag));
    let extra = b.alloc_n(nx);
    let mut clean = vec![flag];
    clean.extend_from_slice(&extra);
    let n = alow.len();
    let mut zz = z.to_vec();
    b.gpool = clean.clone();
    round_fwd(b, ms, &mut zz, y, None);
    for i in (0..n).rev() {
        round_fwd(b, ms, &mut zz, y, Some(alow[i]));
    }
    post_fwd(b, ms, &mut zz, y);
    b.gpool.clear();
    // relabel back to z's lane order and apply the sign: no measurement inside, so recorded and replayed backwards
    b.begin();
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg(b, ms, z, Some(c), y);
        if flip { b.x(c); }
    }
    let tail = b.end();
    b.play(&tail, false);
    (Nat { on: true, clean, extra, zz, z: z.to_vec(), alow: alow.to_vec(), y: y.to_vec(), tail }, Vec::new())
}

#[cfg(test)]
#[path = "fd_natinv_tests.rs"]
mod tests;
