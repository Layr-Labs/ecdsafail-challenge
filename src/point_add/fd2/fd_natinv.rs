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
//! r765b: the default is the compile-time const `P3NAT` of point_add/mod.rs (the box builders wipe the environment).
//! P3NAT = true: native P2 and P5, each at consume width 6 with one extra clean lane (`p2w`, `p5w`, `p2x`, `p5x`).
//! P3NAT = false: every function here returns its old value, so the stream is the parent's.
//! P3NAT_SEED (v1, needs P3NAT): streamed seed instead of the width-6 seed and the extra lane (`stream_fwd`).
use super::builder::{B, G};
use super::fd_clean::FW;
use super::modp_frogdrop::{add_small, ctrl_neg, Ms, C, CMPT};
use crate::circuit::{BitId, QubitId};

/// Compile-time switch (point_add/mod.rs).
const P3NAT: bool = super::super::P3NAT;
/// v1 of P3NAT (sol5 P3 "streamed seed"), used only when the native rounds are on. P2 and P5 keep consume width 5 and
/// allocate no extra lane: after the five-bit seed, the multiplier's next bit (alow's top lane) is streamed into the seed
/// by one double + controlled add, then measured away (HMR); its lane is the second clean fold lane of the native rounds.
/// The uncompute runs a six-bit inverse seed (zero test on ZW_STREAM low lanes), which leaves that bit in z's lane
/// 256 - 6; a swap puts it back on its own lane and Z under the saved HMR bit repays the measurement's phase.
/// false = the v0 stream (P3NAT alone).
pub const P3NAT_SEED: bool = true;
/// Zero-test width of the six-bit inverse seed of `stream_fwd` (63 activation tests instead of 31: 2 more lanes keep
/// the per-shot 2^-ZW exposure bound of the parent's five-bit seed).
pub const ZW_STREAM: usize = 64;
/// Streamed seed on (v1).
pub fn stream_seed() -> bool {
    P3NAT_SEED && on()
}
/// Open the recycled classical-bit range for one pass of native rounds (see `fd_gidney::RECYCLE`): 68 fresh ids,
/// reused by every Gidney fold and measured erase of the pass. Without it each round takes about 126 new bit ids, and
/// P2 + P5 would need about 127k, past the u16 rows of the post-pass peephole.
fn recycle_on(b: &mut B) {
    let p = b.fresh_bits(super::fd_gidney::RECYCLE_N);
    super::fd_gidney::RECYCLE.with(|r| {
        assert!(r.borrow().is_none(), "nested recycled bit range");
        *r.borrow_mut() = Some(p);
    });
}
fn recycle_off() {
    super::fd_gidney::RECYCLE.with(|r| *r.borrow_mut() = None);
}

pub fn on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_NATINV").map(|v| v.trim() != "0").unwrap_or(P3NAT)) // q765 v5-p5shell: default off (count of record ran FD_NATINV=0); r765b: default P3NAT
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
/// stop information has one at width 6. Override FD_P5X. r765b: 1 under P3NAT (this tree's walk parks 512 lanes, so P5
/// at width 6 has room for it), else 0 as before.
pub fn p5x() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| env_usize("FD_P5X").unwrap_or(if P3NAT { 1 } else { 0 }))
}
/// P5's consume width (r765b, mirrors `p2w`): the parent's P5MS when the switch is off; P5MS + p5x() when on, so that
/// P5 stays at 512 + 2 + (256 - w) + p5x() = 765 lanes (512 = 255 inv + sign + 256 passenger). Override FD_P5W.
pub fn p5w() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| {
        let base = super::pointadd_frogdrop::p5ms();
        env_usize("FD_P5W").unwrap_or(if on() && !stream_seed() { base + p5x() } else { base })
    })
}
/// P2's consume width: the parent's PCONSUME when the switch is off; PCONSUME + p2x() when on, so that P2 stays at
/// 512 + 2 + (256 - w) + p2x() = 765 lanes. Override FD_P2W.
pub fn p2w() -> usize {
    static P: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *P.get_or_init(|| {
        let base = super::pointadd_frogdrop::pconsume();
        env_usize("FD_P2W").unwrap_or(if on() && !stream_seed() { base + p2x() } else { base })
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
    /// v1 (`stream_fwd`): the streamed bit's lane and its HMR bit.
    stream: Option<(QubitId, BitId)>,
}

impl Nat {
    /// Placeholder when the switch is off: the caller plays the parent's recording instead.
    pub fn off() -> Nat {
        Nat { on: false, clean: vec![], extra: vec![], zz: vec![], z: vec![], alow: vec![], y: vec![], tail: vec![], stream: None }
    }

    /// The caller's inverse seed (after `inverse`). Without a streamed bit: exactly `fd_seed::seed_inv(b, z, flag, k, w,
    /// dirty, add_rec)`. With one (v1): the six-bit inverse seed on z's top w + 1 lanes, which leaves the streamed bit
    /// on z[256 - (w + 1)]; swap it back onto its own lane and repay its HMR phase. The caller then pays the w-bit seed's
    /// debts on the consumed lanes as before.
    pub fn seed_inv(&self, b: &mut B, z: &[QubitId], flag: QubitId, k: QubitId, w: usize, dirty: &[QubitId], add_rec: &[G]) {
        match self.stream {
            None => super::fd_seed::seed_inv(b, z, flag, k, w, dirty, add_rec),
            Some((bit, m)) => {
                assert!(z.len() == 256 && !z.contains(&bit) && bit != flag && bit != k);
                let d: Vec<QubitId> = dirty.iter().copied().filter(|&q| q != bit).collect();
                super::fd_seed::seed_inv_zw(b, z, flag, k, w + 1, &d, add_rec, ZW_STREAM);
                b.swap(z[256 - (w + 1)], bit);
                b.z_if(bit, m);
            }
        }
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
        recycle_on(b);
        post_inv(b, ms, &mut zz, &self.y);
        for i in 0..n {
            round_inv(b, ms, &mut zz, &self.y, Some(self.alow[i]));
        }
        round_inv(b, ms, &mut zz, &self.y, None);
        recycle_off();
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
    rounds_core(b, ms, z, alow, y, neg, clean, extra)
}

/// Body of `rounds_fwd` with the clean pool given (`extra` = the part of it that `Nat::inverse` frees).
fn rounds_core(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>,
               clean: Vec<QubitId>, extra: Vec<QubitId>) -> (Nat, Vec<G>) {
    let n = alow.len();
    let mut zz = z.to_vec();
    b.gpool = clean.clone();
    recycle_on(b);
    round_fwd(b, ms, &mut zz, y, None);
    for i in (0..n).rev() {
        round_fwd(b, ms, &mut zz, y, Some(alow[i]));
    }
    post_fwd(b, ms, &mut zz, y);
    recycle_off();
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
    (Nat { on: true, clean, extra, zz, z: z.to_vec(), alow: alow.to_vec(), y: y.to_vec(), tail, stream: None }, Vec::new())
}

/// v1 (P3NAT_SEED): the same map as `rounds_fwd(.., alow, .., flag, 0)` with no lane allocated. alow's top lane `bit`
/// is streamed into the seed first (z = S y -> (2 S + bit) y: a native double with pool [flag], then the parent's
/// measured `ctrl_modadd` under `bit`, then swaps back to z's lane order), then measured away (HMR); the native rounds
/// run on alow[..n - 1] with [flag, bit] as their two clean fold lanes. `Nat::seed_inv` undoes the seed and the bit.
pub fn stream_fwd(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>,
                  flag: QubitId) -> (Nat, Vec<G>) {
    assert!(!b.fusion_recording() && z.len() == 256 && y.len() == 256 && alow.len() >= 3);
    assert!(alow.iter().all(|q| !z.contains(q) && !y.contains(q)) && !z.contains(&flag) && !y.contains(&flag));
    let n = alow.len();
    let (low, bit) = (&alow[..n - 1], alow[n - 1]);
    let mut zz = z.to_vec();
    b.gpool = vec![flag];
    double(b, ms, &mut zz, y);
    b.gpool.clear();
    super::modp_frogdrop::ctrl_modadd(b, ms, &zz, y, bit, alow[0]);
    let mut pos: Vec<QubitId> = zz;
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    let m = b.fresh_bits(1)[0];
    b.hmr_to(bit, m);
    let (mut nat, r) = rounds_core(b, ms, z, low, y, neg, vec![flag, bit], vec![]);
    nat.stream = Some((bit, m));
    (nat, r)
}

/// The native forward pass of a consume product: `stream_fwd` under P3NAT_SEED, else `rounds_fwd` (v0).
pub fn fwd(b: &mut B, ms: &Ms, z: &[QubitId], alow: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>,
           flag: QubitId, nx: usize) -> (Nat, Vec<G>) {
    if stream_seed() {
        stream_fwd(b, ms, z, alow, y, neg, flag)
    } else {
        rounds_fwd(b, ms, z, alow, y, neg, flag, nx)
    }
}

#[cfg(test)]
#[path = "fd_natinv_tests.rs"]
mod tests;
