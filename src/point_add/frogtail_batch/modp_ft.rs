//! Arithmetic modulo p = 2^256 - c (c = 2^32 + 977) for frogtail's product phase: frogdrop's ancilla-free adds and
//! overflow flag, plus a pool of clean qubits (the room under the walk's peak) for logical-AND carries (Gidney):
//! every fold of a constant (c on overflow, c - 1 for doubling / halving / negation) adds ctl * const over z's low 64
//! lanes with one AND per lane, the constant's bits taken straight from the control (credit gnuchev's carry pool);
//! a carry out of lane 63 is dropped (w.p. ~2^-32 per fold, as frogdrop's 32-lane headroom). The overflow flag's
//! erase compare runs on pool carries too.

use super::builder::{B, ONE};
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// fold register width (constant + carry headroom)
pub const RW: usize = 64;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

thread_local! {
    /// Force the hybrid (Gidney low lanes + Cuccaro) ladder: for recordings that are later played inverted, where a
    /// chunked ladder's measured carry erases would become coherent compares.
    pub static NOCHUNK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Paired fix-product mode: 0 = ordinary, 1 = save measured carry debts,
    /// 2 = regenerate and repay the saved debts during the matching uncompute.
    static FIX_PAIR_MODE: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    static FIX_PAIR_SKIP: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static FIX_PAIR_STACK: std::cell::RefCell<Vec<FixPairDebts>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static FIX_PAIR_KEYS: std::cell::RefCell<Vec<FixPairKey>> =
        const { std::cell::RefCell::new(Vec::new()) };
    #[cfg(test)]
    static FIX_PAIR_TEST_NO_REPAY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

type FixPairDebts = (Vec<(usize, crate::circuit::BitId)>, Option<crate::circuit::BitId>);
type FixPairKey = (usize, usize, Vec<usize>);

pub(crate) fn fix_pair_begin_save(skip: usize) {
    assert!(FIX_PAIR_STACK.with(|s| s.borrow().is_empty()), "paired save started with outstanding debts");
    assert!(FIX_PAIR_KEYS.with(|s| s.borrow().is_empty()), "paired save started with outstanding keys");
    FIX_PAIR_MODE.with(|m| m.set(1));
    FIX_PAIR_SKIP.with(|s| s.set(skip));
}

pub(crate) fn fix_pair_end_save() {
    FIX_PAIR_MODE.with(|m| m.set(0));
    assert_eq!(FIX_PAIR_SKIP.with(|s| s.get()), 0, "FIX_PAIR_SKIP not consumed by the compute");
    assert!(!FIX_PAIR_STACK.with(|s| s.borrow().is_empty()), "paired compute saved no debts");
    assert_eq!(FIX_PAIR_KEYS.with(|s| s.borrow().len()), FIX_PAIR_STACK.with(|s| s.borrow().len()));
}

pub(crate) fn fix_pair_begin_repay() {
    assert!(!FIX_PAIR_STACK.with(|s| s.borrow().is_empty()), "paired repay started without debts");
    assert_eq!(FIX_PAIR_KEYS.with(|s| s.borrow().len()), FIX_PAIR_STACK.with(|s| s.borrow().len()));
    FIX_PAIR_MODE.with(|m| m.set(2));
    FIX_PAIR_SKIP.with(|s| s.set(0));
}

pub(crate) fn fix_pair_end_repay() {
    FIX_PAIR_MODE.with(|m| m.set(0));
    assert!(FIX_PAIR_STACK.with(|s| s.borrow().is_empty()), "paired fix-product debts left after repay");
    assert!(FIX_PAIR_KEYS.with(|s| s.borrow().is_empty()), "paired fix-product keys left after repay");
}

#[cfg(test)]
pub(crate) fn fix_pair_test_no_repay(value: bool) {
    FIX_PAIR_TEST_NO_REPAY.with(|v| v.set(value));
}

#[cfg(test)]
pub(crate) fn fix_pair_test_reset() {
    FIX_PAIR_MODE.with(|m| m.set(0));
    FIX_PAIR_SKIP.with(|s| s.set(0));
    FIX_PAIR_STACK.with(|s| s.borrow_mut().clear());
    FIX_PAIR_KEYS.with(|s| s.borrow_mut().clear());
    FIX_PAIR_TEST_NO_REPAY.with(|v| v.set(false));
}

fn fix_pair_save_this_add() -> bool {
    if FIX_PAIR_MODE.with(|m| m.get()) != 1 || NOCHUNK.with(|c| c.get()) {
        return false;
    }
    FIX_PAIR_SKIP.with(|s| {
        if s.get() == 0 {
            true
        } else {
            s.set(s.get() - 1);
            false
        }
    })
}

fn erase_overflow_flag(
    b: &mut B,
    ms: &Ms,
    yt: &[QubitId],
    ut: &[QubitId],
    pool: &[QubitId],
    s: Option<QubitId>,
    paired: bool,
) {
    if paired {
        let bit = b.fresh_bits(1)[0];
        b.hmr_to(ms.k, bit);
        FIX_PAIR_STACK.with(|st| {
            let mut st = st.borrow_mut();
            let entry = st.last_mut().expect("paired overflow erase without an open debt entry");
            assert!(entry.1.is_none(), "paired overflow debt written twice");
            entry.1 = Some(bit);
        });
    } else {
        b.carry_erase_cin(yt, ut, super::builder::ONE, ms.k, pool, s);
    }
}

/// Scratch: overflow flag k, the carry pool (all |0> between operations) and a constant |1> control.
pub struct Ms {
    pub k: QubitId,
    pub r: Vec<QubitId>,
    pub one: QubitId,
}

impl Ms {
    /// O1 U20: `one` is the builder's ONE sentinel (lowered by the gate helpers), not an X'd lane.
    fn with(b: &mut B, room: usize) -> Ms {
        let k = b.alloc();
        let r = b.alloc_n(room);
        Ms { k, r, one: ONE }
    }
    pub fn alloc(b: &mut B) -> Ms {
        Ms::with(b, RW)
    }
    /// Pool as large as the room under `peak` allows (one qubit kept for the constant control; at least RW
    /// lanes, at most 256).
    pub fn alloc_room(b: &mut B, peak: u64) -> Ms {
        #[cfg(test)]
        let min_room = std::env::var("LILYPAD_MS_MIN_ROOM").ok().and_then(|v| v.parse().ok()).unwrap_or(52);
        #[cfg(not(test))]
        let min_room = 52;
        let room = (peak.saturating_sub(b.live + 1) as usize).clamp(min_room, 256);
        Ms::with(b, room)
    }
    pub fn release(self, b: &mut B) {
        if self.one != ONE {
            b.x(self.one);
            b.free(self.one);
        }
        b.free(self.k);
        b.free_n(&self.r);
    }
}

/// c2 = MAJ(h, t, c) into the clean c2, leaving t ^ c on t and h restored. h may be the ONE sentinel (O1 U20): then
/// MAJ(1, t, c) = c ^ (~c & (t ^ c)), with c complemented in place instead of toggling h. One AND either way.
fn maj_c(b: &mut B, h: QubitId, t: QubitId, c: QubitId, c2: QubitId) {
    if h == ONE {
        b.cx(c, t);
        b.x(c);
        b.and_c(c, t, c2);
        b.x(c);
        b.cx(c, c2);
    } else {
        b.cx(c, h);
        b.cx(c, t);
        b.and_c(h, t, c2);
        b.cx(c, c2);
        b.cx(c, h);
    }
}

/// Inverse of maj_c's carry (c2 -> 0 by measurement) with the sum bit written: t <- t ^ c ^ h.
fn maj_u_sum(b: &mut B, h: QubitId, t: QubitId, c: QubitId, c2: QubitId) {
    if h == ONE {
        b.cx(c, c2);
        b.x(c);
        b.and_u(c, t, c2);
        b.x(c);
        b.x(t);
    } else {
        b.cx(c, h);
        b.cx(c, c2);
        b.and_u(h, t, c2);
        b.cx(c, h);
        b.cx(h, t);
    }
}

/// t += h * k mod 2^len (k constant: bit i adds into lane i; h one qubit outside t), logical-AND carries on `pool`
/// (>= len - 1 - lowest set bit of k), measurement-uncomputed. One AND per lane from k's lowest set bit up.
pub(crate) fn const_add_pool(b: &mut B, t: &[QubitId], h: QubitId, k: u64, pool: &[QubitId]) {
    let n = t.len();
    if k == 0 {
        return;
    }
    let i0 = k.trailing_zeros() as usize;
    let kb = |i: usize| i < 64 && (k >> i) & 1 == 1;
    let need = n - 1 - i0;
    let shortage = need.saturating_sub(pool.len());
    // Exact odd 64-bit carry-prefix recycling at the two measured pool widths.
    if n == 64 && shortage>=2 && pool.len() > shortage {
        const_add_recycled(b, t, h, k, pool);
        return;
    }
    if (2..=5).contains(&shortage) {
        // Keep carries below a small top tail.  The tail receives its carry-in
        // and constant by exact controlled increments whose borrowed dirty
        // data lanes are restored.  This extends the Q877 one-topless fold to
        // the 57-lane Q873 shell without approximation.
        let tail_len = shortage + 1;
        let start = n - tail_len;
        assert!(i0 < start && !pool.is_empty(), "multi-topless constant fold needs a nonempty lower chain");
        assert!(start - i0 >= tail_len - 2, "multi-topless constant fold needs enough disjoint dirty data lanes");
        let c = |i: usize| pool[i - i0 - 1];
        for i in i0..start {
            if i == i0 {
                b.and_c(t[i], h, c(i + 1));
            } else if kb(i) {
                maj_c(b, h, t[i], c(i), c(i + 1));
            } else {
                b.and_c(t[i], c(i), c(i + 1));
            }
        }
        let tail = &t[start..];
        let ctrl_inc = |b: &mut B, ctl: QubitId| {
            for j in (1..tail_len).rev() {
                let mut controls = if ctl == ONE { vec![] } else { vec![(ctl, false)] };
                controls.extend(tail[..j].iter().copied().map(|q| (q, false)));
                super::mask::mc_xor(b, &controls, tail[j], &[], &t[i0..start]);
            }
            b.cx(ctl, tail[0]);
        };
        ctrl_inc(b, c(start));
        let tail_mask = (1u64 << tail_len) - 1;
        let tail_constant = ((k >> start) & tail_mask) as usize;
        // The tail is modulo 2^tail_len. Use the shorter signed constant;
        // e.g. all-one upper bits add -1 rather than 2^tail_len-1 increments.
        // Borrowed lower data are restored by each controlled increment or
        // decrement before the carry chain is measurement-uncomputed.
        if tail_constant > (1usize << (tail_len - 1)) {
            let ctrl_dec = |b: &mut B, ctl: QubitId| {
                for j in (1..tail_len).rev() {
                    let mut controls = if ctl == ONE { vec![] } else { vec![(ctl, false)] };
                    controls.extend(tail[..j].iter().copied().map(|q| (q, true)));
                    super::mask::mc_xor(b, &controls, tail[j], &[], &t[i0..start]);
                }
                b.cx(ctl, tail[0]);
            };
            for _ in 0..(1usize << tail_len) - tail_constant {
                ctrl_dec(b, h);
            }
        } else {
            for _ in 0..tail_constant {
                ctrl_inc(b, h);
            }
        }
        for i in (i0..start).rev() {
            if i == i0 {
                b.and_u(t[i], h, c(i + 1));
                b.cx(h, t[i]);
            } else if kb(i) {
                maj_u_sum(b, h, t[i], c(i), c(i + 1));
            } else {
                b.and_u(t[i], c(i), c(i + 1));
                b.cx(c(i), t[i]);
            }
        }
        return;
    }
    if pool.len() + 1 == need {
        // Do not materialize c[n-1]. Its majority polynomial toggles the top
        // sum bit directly, saving one clean carry lane.
        if i0 == n - 2 {
            b.ccx(t[i0], h, t[n - 1]);
            if kb(n - 1) {
                b.cx(h, t[n - 1]);
            }
            b.cx(h, t[i0]);
            return;
        }
        let c = |i: usize| pool[i - i0 - 1];
        for i in i0..n - 2 {
            if i == i0 {
                b.and_c(t[i], h, c(i + 1));
            } else if kb(i) {
                maj_c(b, h, t[i], c(i), c(i + 1));
            } else {
                b.and_c(t[i], c(i), c(i + 1));
            }
        }
        let i = n - 2;
        let ci = c(i);
        if kb(i) {
            b.ccx(t[i], h, t[n - 1]);
            b.ccx(t[i], ci, t[n - 1]);
            b.ccx(h, ci, t[n - 1]);
        } else {
            b.ccx(t[i], ci, t[n - 1]);
        }
        if kb(n - 1) {
            b.cx(h, t[n - 1]);
        }
        b.cx(ci, t[i]);
        if kb(i) {
            b.cx(h, t[i]);
        }
        for i in (i0..n - 2).rev() {
            if i == i0 {
                b.and_u(t[i], h, c(i + 1));
                b.cx(h, t[i]);
            } else if kb(i) {
                maj_u_sum(b, h, t[i], c(i), c(i + 1));
            } else {
                b.and_u(t[i], c(i), c(i + 1));
                b.cx(c(i), t[i]);
            }
        }
        return;
    }
    assert!(pool.len() >= need);
    // c[i] = carry into lane i (i0 < i < n) lives in pool[i - i0 - 1]
    let c = |i: usize| pool[i - i0 - 1];
    for i in i0..n - 1 {
        if i == i0 {
            b.and_c(t[i], h, c(i + 1));
        } else if kb(i) {
            maj_c(b, h, t[i], c(i), c(i + 1));
        } else {
            b.and_c(t[i], c(i), c(i + 1));
        }
    }
    // top lane: sum only
    let top = n - 1;
    if top > i0 {
        b.cx(c(top), t[top]);
    }
    if kb(top) {
        b.cx(h, t[top]);
    }
    for i in (i0..n - 1).rev() {
        if i == i0 {
            b.and_u(t[i], h, c(i + 1));
            b.cx(h, t[i]);
        } else if kb(i) {
            maj_u_sum(b, h, t[i], c(i), c(i + 1));
        } else {
            b.and_u(t[i], c(i), c(i + 1));
            b.cx(c(i), t[i]);
        }
    }
}

/// Exact constant fold with an internal carry loan. Erase the low prefix
/// temporarily, reuse those lanes above the retained bridge carry, then
/// recompute the prefix before the original low sum/cleanup. No data lane
/// or external live endpoint wire is borrowed.
pub(crate) fn const_add_recycled(b: &mut B, t: &[QubitId], h: QubitId, k: u64, pool: &[QubitId]) {
    let n=t.len();
    // O1 U21: windows wider than the 64-bit constant (the 65-lane offset window) see zero constant bits above 63.
    assert!(k!=0 && n<=128);
    let i0=k.trailing_zeros() as usize;
    assert!(i0<n);
    let need=n-1-i0;
    assert!(pool.len()<need);
    let loan=need-pool.len();
    assert!(pool.len()>loan, "carry loan must retain a distinct bridge");
    assert!(!pool.contains(&h) && !t.contains(&h));
    assert!(pool.iter().all(|q| !t.contains(q)));
    assert_eq!(pool.iter().collect::<std::collections::BTreeSet<_>>().len(),pool.len());
    assert_eq!(t.iter().collect::<std::collections::BTreeSet<_>>().len(),t.len());
    let bridge=i0+pool.len();
    let kb=|i:usize| i<64 && (k>>i)&1!=0;
    let c=|i:usize| if i<=bridge {pool[i-i0-1]} else {pool[i-bridge-1]};
    let compute=|b:&mut B,i:usize| {
        if i==i0 { b.and_c(t[i],h,c(i+1)); }
        else if kb(i) { maj_c(b,h,t[i],c(i),c(i+1)); }
        else { b.and_c(t[i],c(i),c(i+1)); }
    };
    let sum_erase=|b:&mut B,i:usize| {
        if i==i0 { b.and_u(t[i],h,c(i+1)); b.cx(h,t[i]); }
        else if kb(i) { maj_u_sum(b,h,t[i],c(i),c(i+1)); }
        else { b.and_u(t[i],c(i),c(i+1)); b.cx(c(i),t[i]); }
    };
    b.begin();
    for i in i0..i0+loan { compute(b,i); }
    let prefix=b.end();
    b.play(&prefix,false);
    for i in i0+loan..bridge { compute(b,i); }
    b.play(&prefix,true);
    for i in bridge..n-1 { compute(b,i); }
    b.cx(c(n-1),t[n-1]);
    if kb(n-1) { b.cx(h,t[n-1]); }
    for i in (bridge..n-1).rev() { sum_erase(b,i); }
    b.play(&prefix,false);
    for i in (i0..bridge).rev() { sum_erase(b,i); }
}

/// Constant add with the one-lane Q877 carry shortfall repaired by a scratch
/// qubit already owned by `Ms`. The borrowed lane is clean for this fold and
/// is restored before returning.
/// C51/U20 precondition: when ONE replaces the owned one lane and ms.k is
/// borrowed at a short pool, ms.k MUST be |0> on supported inputs. A dirty
/// flag is not in this helper's contract; the dedicated C51 test pins this.
/// Callers that use ms.k as the control do not lend it.
fn const_add_ms(b: &mut B, ms: &Ms, t: &[QubitId], h: QubitId, k: u64) {
    if k == 0 {
        return;
    }
    let need = t.len() - 1 - k.trailing_zeros() as usize;
    if ms.r.len() >= need {
        const_add_pool(b, t, h, k, &ms.r);
        return;
    }
    // WQ4/WQ5: use the same exact bridge construction at every short pool.
    if ms.r.len() < need && ms.r.len() > need-ms.r.len() {
        const_add_recycled(b,t,h,k,&ms.r);return;
    }
    let recycled_seven_short = t.len() == 64 && k & 1 == 1 && ms.r.len() == 56;
    assert!(ms.r.len() + 6 >= need || recycled_seven_short || (ms.one == ONE && ms.r.len() + 7 >= need),
        "constant fold lacks a supported exact carry route");
    let mut pool = ms.r.clone();
    if h == ms.one {
        pool.push(ms.k);
        const_add_pool(b, t, h, k, &pool);
    } else if ms.one == ONE {
        // O1 U20: no constant lane to lend; the flag k is clean whenever it is not the control.
        if h != ms.k {
            assert!(!t.contains(&ms.k) && !pool.contains(&ms.k), "U20 clean-flag loan must be disjoint");
            pool.push(ms.k);
        }
        const_add_pool(b, t, h, k, &pool);
    } else {
        b.x(ms.one);
        pool.push(ms.one);
        const_add_pool(b, t, h, k, &pool);
        b.x(ms.one);
    }
}

/// k ^= ctl & carry_out(t + a) (carry-in 0), t and a restored, logical-AND carries on `pool` (>= n - 1).
fn carry_pool(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId, k: QubitId, pool: &[QubitId]) {
    let n = t.len();
    // c[i] (carry into lane i, 1 <= i <= n): pool[i - 1]; carry out = c[n] in pool[n - 1]
    for i in 0..n {
        if i == 0 {
            b.and_c(a[0], t[0], pool[0]);
        } else {
            let ci = pool[i - 1];
            b.cx(ci, a[i]);
            b.cx(ci, t[i]);
            b.and_c(a[i], t[i], pool[i]);
            b.cx(ci, pool[i]);
        }
    }
    b.ccx(ctl, pool[n - 1], k);
    for i in (0..n).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], pool[0]);
        } else {
            let ci = pool[i - 1];
            b.cx(ci, pool[i]);
            b.and_u(a[i], t[i], pool[i]);
            b.cx(ci, t[i]);
            b.cx(ci, a[i]);
        }
    }
}

/// t[lo..lo + RW) += ctl * (k >> lo) (k's low lo bits zero), carry out of the window dropped. ctl outside the window
/// (None: unconditional, the constant's lanes are X'd in place of the AND carries' source).
fn fold_add(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctl: Option<QubitId>, k: u64) {
    assert_eq!(k & ((1u64 << lo) - 1), 0);
    match ctl {
        Some(h) => const_add_ms(b, ms, &t[lo..lo + RW], h, k >> lo),
        None if ms.one == ONE => const_add_ms(b, ms, &t[lo..lo + RW], ONE, k >> lo),
        None => {
            if ms.r.len() >= RW {
                let one = ms.r[RW - 1];
                b.x(one);
                const_add_pool(b, &t[lo..lo + RW], one, k >> lo, &ms.r[..RW - 1]);
                b.x(one);
            } else {
                const_add_ms(b, ms, &t[lo..lo + RW], ms.one, k >> lo);
            }
        }
    }
}

/// t[lo..lo + RW) -= ctl * (k >> lo) as ~(~t + ctl k).
fn fold_sub(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctl: Option<QubitId>, k: u64) {
    for &q in &t[lo..lo + RW] {
        b.x(q);
    }
    fold_add(b, ms, t, lo, ctl, k);
    for &q in &t[lo..lo + RW] {
        b.x(q);
    }
}

/// t += A mod 2^|t| where bit i of A is the qubit add[i] (None: 0); a qubit may serve several lanes. Logical-AND
/// carries on `pool` (>= |t| - 1 - lowest used lane), measurement-uncomputed (const_add_pool with per-lane sources).
pub(crate) fn var_add_pool(b: &mut B, t: &[QubitId], add: &[Option<QubitId>], pool: &[QubitId]) {
    let n = t.len();
    let Some(i0) = add.iter().position(|a| a.is_some()) else {
        return;
    };
    if pool.len()+i0+1<n {
        var_add_recycled(b,t,add,pool);
        return;
    }
    let c = |i: usize| pool[i - i0 - 1];
    for i in i0..n - 1 {
        match add[i] {
            Some(h) if i == i0 => b.and_c(t[i], h, c(i + 1)),
            Some(h) => {
                b.cx(c(i), h);
                b.cx(c(i), t[i]);
                b.and_c(h, t[i], c(i + 1));
                b.cx(c(i), c(i + 1));
                b.cx(c(i), h);
            }
            None => b.and_c(t[i], c(i), c(i + 1)),
        }
    }
    let top = n - 1;
    if top > i0 {
        b.cx(c(top), t[top]);
    }
    if let Some(h) = add[top] {
        b.cx(h, t[top]);
    }
    for i in (i0..n - 1).rev() {
        match add[i] {
            Some(h) if i == i0 => {
                b.and_u(t[i], h, c(i + 1));
                b.cx(h, t[i]);
            }
            Some(h) => {
                b.cx(c(i), h);
                b.cx(c(i), c(i + 1));
                b.and_u(h, t[i], c(i + 1));
                b.cx(c(i), h);
                b.cx(h, t[i]);
            }
            None => {
                b.and_u(t[i], c(i), c(i + 1));
                b.cx(c(i), t[i]);
            }
        }
    }
}

/// Lanes of the 4-fold window (from lane 4): (c - 1)/16 = 61 + 2^28 times a 4-bit H, plus 32 lanes of headroom.
const W4: usize = 64;

/// t += val(vars) mod 2^|t| (sub: t -= val(vars)), val a classical table over the assignments of the few control
/// qubits `vars` (index bit i = vars[i]; val(0) = 0), the controls outside t. Each addend bit is a Boolean function of
/// the controls: its algebraic normal form's monomials of degree >= 2 are computed once (one AND each,
/// measurement-uncomputed), each bit's function is XORed into a scratch lane by CNOTs (single-variable bits use the
/// control itself), then one logical-AND carry chain adds them (var_add_pool). Scratch and carries from `pool`.
fn add_table(b: &mut B, pool: &[QubitId], t: &[QubitId], vars: &[QubitId], val: &dyn Fn(usize) -> u128, sub: bool) {
    let nv = vars.len();
    let na = 1usize << nv;
    let w = t.len();
    assert!(w <= 128 && val(0) == 0);
    let anf = |j: usize| -> Vec<usize> {
        let mut f: Vec<u8> = (0..na).map(|a| ((val(a) >> j) & 1) as u8).collect();
        for i in 0..nv {
            for m in 0..na {
                if m & (1 << i) != 0 {
                    f[m] ^= f[m ^ (1 << i)];
                }
            }
        }
        (0..na).filter(|&m| f[m] == 1).collect()
    };
    let bits: Vec<Vec<usize>> = (0..w).map(anf).collect();
    let mut pool: Vec<QubitId> = pool.to_vec();
    let mut mono: std::collections::BTreeMap<usize, QubitId> = std::collections::BTreeMap::new();
    let mut need: std::collections::BTreeSet<usize> =
        bits.iter().flatten().cloned().filter(|m| m.count_ones() >= 2).collect();
    let topbit = |m: usize| 1usize << (usize::BITS - 1 - m.leading_zeros());
    let mut stack: Vec<usize> = need.iter().cloned().collect();
    while let Some(m) = stack.pop() {
        let r = m ^ topbit(m);
        if r.count_ones() >= 2 && need.insert(r) {
            stack.push(r);
        }
    }
    let var = |m: usize, mono: &std::collections::BTreeMap<usize, QubitId>| -> QubitId {
        if m.count_ones() == 1 {
            vars[m.trailing_zeros() as usize]
        } else {
            mono[&m]
        }
    };
    let mut order: Vec<(usize, QubitId, QubitId)> = vec![];
    for &m in &need {
        let tb = topbit(m);
        let (x, y) = (var(m ^ tb, &mono), vars[tb.trailing_zeros() as usize]);
        let q = pool.pop().unwrap();
        b.and_c(x, y, q);
        mono.insert(m, q);
        order.push((m, x, y));
    }
    let mut add: Vec<Option<QubitId>> = vec![None; w];
    let mut built: Vec<(QubitId, Vec<usize>)> = vec![];
    let mut cache: std::collections::BTreeMap<Vec<usize>, QubitId> = std::collections::BTreeMap::new();
    for (j, ms_j) in bits.iter().enumerate() {
        if ms_j.is_empty() {
            continue;
        }
        assert!(!ms_j.contains(&0), "table with a constant addend bit");
        if ms_j.len() == 1 {
            add[j] = Some(var(ms_j[0], &mono));
        } else if let Some(&q) = cache.get(ms_j) {
            add[j] = Some(q);
        } else {
            let q = pool.pop().unwrap();
            for &m in ms_j {
                b.cx(var(m, &mono), q);
            }
            add[j] = Some(q);
            cache.insert(ms_j.clone(), q);
            built.push((q, ms_j.clone()));
        }
    }
    let i0 = add.iter().position(|a| a.is_some()).unwrap_or(w);
    assert!(pool.len() + i0 + 1 >= w || pool.len() > (w-1-i0).saturating_sub(pool.len()), "recycled table must retain a distinct bridge");
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    if pool.len()+i0+1<w {
        let recipes:Vec<_>=built.iter().map(|(q,ms)|(*q,ms.iter().map(|&m|var(m,&mono)).collect())).collect();
        c58_var_add_lean(b,t,&add,&pool,&recipes);
    }else{var_add_pool(b,t,&add,&pool);}
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    for (q, ms_j) in built.iter().rev() {
        for &m in ms_j {
            b.cx(var(m, &mono), *q);
        }
    }
    for &(m, x, y) in order.iter().rev() {
        b.and_u(x, y, mono[&m]);
    }
}

/// Adds (sub: subtracts) H (c - 1) into z[4..4 + W4), H = the 4-bit value in `hq` (LSB first, outside the window):
/// (c - 1) / 16 = 61 + 2^28, so the addend's bits are functions of H (add_table).
fn fold4(b: &mut B, ms: &Ms, z: &[QubitId], hq: [QubitId; 4], sub: bool) {
    let val = |h: usize| -> u128 { (h as u128) * ((C as u128 - 1) >> 4) };
    add_table(b, &ms.r, &z[4..4 + W4], &hq, &val, sub);
}

/// Window of the merged fold (lane 0 up): |delta| c < 2^35 plus 31 lanes of carry headroom.
const WM: usize = 66;
/// A merged signed table needs eight pool lanes beyond its active arithmetic
/// window (monomials, value functions, and the halving helper). Below the
/// original 74-lane room, narrow the window to fit instead of falling back to
/// two separate operations. The 56-lane floor is source-pinned and audited.
const SIGNED_TABLE_OVERHEAD: usize = 8;
const SIGNED_WM_MIN: usize = 56;
const SIGNED_WM_MAX: usize = WM;

#[cfg(test)]
thread_local! {
    static TEST_SIGNED_WM_MAX: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn test_signed_wm_max(value: Option<usize>) {
    TEST_SIGNED_WM_MAX.with(|v| v.set(value.unwrap_or(0)));
}

fn signed_wm_max() -> usize {
    #[cfg(test)]
    {
        let value = TEST_SIGNED_WM_MAX.with(|v| v.get());
        if value != 0 {
            return value;
        }
    }
    SIGNED_WM_MAX
}

fn signed_wm(pool: usize) -> Option<usize> {
    // Low-room fused folds retain the full 66-bit window. Recycle internal
    // carries rather than dropping guard bits or adding a second fold.
    // O1 U20: the ONE sentinel adds one lane to every pool; shift the inherited full-window range by that lane so the
    // narrowed (pool - 8) fused window starts at the same cap as before (pool 65 here = 64 in the base), never earlier.
    if (47..65).contains(&pool) { return Some(signed_wm_max()); }
    pool.checked_sub(SIGNED_TABLE_OVERHEAD)
        .map(|w| w.min(signed_wm_max()))
        .filter(|&w| w >= SIGNED_WM_MIN)
}

/// z <- (z + (-1)^s y) / 2 mod p (signed_modadd then mod_halve, one fold for both). The raw add (in the
/// complemented domain where s is set) leaves z~ (flipped back) and its carry k; the reduced sum is
/// u = z~ + (-1)^s k c, its halving (u + h p) / 2 with h = u_0 = z~_0 ^ k is (z~ + delta c) / 2 + h 2^255 with
/// delta = (-1)^s k - h in {-2..1}: one table add of delta c over lanes 0..WM (lane 0 ends 0), then the relabel puts
/// h on the freed top lane. k is erased as signed_modadd's, by the top-lane compare on u's top 32 bits = the halved
/// value's lanes 223..254 (complemented domain).
pub fn signed_modadd_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], s: Option<QubitId>) {
    let Some(wm) = signed_wm(ms.r.len()) else {
        signed_modadd(b, ms, z, y, s);
        mod_halve(b, ms, z);
        return;
    };
    let flip = |b: &mut B, z: &[QubitId]| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b, z);
    let paired = add_flag_u(b, ms, z, y);
    flip(b, z);
    let (hq, pool) = ms.r.split_last().unwrap();
    let hq = *hq;
    b.cx(z[0], hq);
    b.cx(ms.k, hq);
    let mut vars = vec![ms.k, hq];
    let sconst = s == Some(ONE);
    if let Some(q) = s.filter(|&q| q != ONE) {
        vars.push(q);
    }
    let val = |a: usize| -> u128 {
        let (k, h, sg) = ((a & 1) as i128, ((a >> 1) & 1) as i128, sconst || (a >> 2) & 1 == 1);
        let d = if sg { -k } else { k } - h;
        let m = (1u128 << wm) - 1;
        ((d * C as i128).rem_euclid(1i128 << wm) as u128) & m
    };
    add_table(b, pool, &z[..wm], &vars, &val, false);
    z.rotate_left(1);
    b.cx(hq, z[255]);
    b.cx(z[255], hq);
    // erase k: [w' < y + s] on the top 32 lanes, w' = u in the complemented domain, u's bits 224..255 = z[223..255)
    let ut: Vec<QubitId> = z[223..255].to_vec();
    let yt = &y[256 - CMPT..];
    flip(b, &ut);
    for &q in &ut {
        b.x(q);
    }
    erase_overflow_flag(b, ms, yt, &ut, pool, s, paired);
    for &q in &ut {
        b.x(q);
    }
    flip(b, &ut);
}

/// z <- 16 z mod p in place: the top 4 lanes are relabeled to the bottom (16 z_low + H), then H (c - 1) is added
/// (c - 1 = 0 mod 16, so lanes 0..3 keep H). One fold for four doublings.
pub fn mod_double4(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    z.rotate_right(4);
    let hq = [z[0], z[1], z[2], z[3]];
    fold4(b, ms, z, hq, false);
}

/// Inverse of mod_double4 (z <- z / 16 mod p): c = 1 mod 16, so z + m p = 0 mod 16 for m = z mod 16; subtract
/// m (c - 1) (lanes >= 4, m's lanes kept) and relabel m's 4 lanes to the top: (z - m c) / 16 + m 2^252.
pub fn mod_halve4(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let hq = [z[0], z[1], z[2], z[3]];
    fold4(b, ms, z, hq, true);
    z.rotate_left(4);
}

/// z <- 2 (z + (-1)^s y) mod p (signed_modadd then mod_double, one fold for both). After the raw add (z~ and its
/// carry k), the doubling's relabel moves z~'s top bit h to lane 0; the reduced sum u = z~ + (-1)^s k c doubles to
/// (2 z~_low + h) + h (c - 1) + 2 (-1)^s k c, so one table add of (-1)^s k c + h (c - 1)/2 over lanes 1..WM + 1
/// (lane 0 keeps h). h is u's top bit except w.p. ~2^-222. k is erased as signed_modadd's, on u's top 32 bits =
/// lanes 225..255 and lane 0 (complemented domain).
pub fn signed_modadd_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], s: Option<QubitId>) {
    let Some(wm) = signed_wm(ms.r.len()) else {
        signed_modadd(b, ms, z, y, s);
        mod_double(b, ms, z);
        return;
    };
    let flip = |b: &mut B, z: &[QubitId]| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b, z);
    let paired = add_flag_u(b, ms, z, y);
    flip(b, z);
    z.rotate_right(1);
    let mut vars = vec![ms.k, z[0]];
    let sconst = s == Some(ONE);
    if let Some(q) = s.filter(|&q| q != ONE) {
        vars.push(q);
    }
    let val = |a: usize| -> u128 {
        let (k, h, sg) = ((a & 1) as i128, ((a >> 1) & 1) as i128, sconst || (a >> 2) & 1 == 1);
        let d = if sg { -k } else { k } * C as i128 + h * ((C as i128 - 1) >> 1);
        (d.rem_euclid(1i128 << wm) as u128) & ((1u128 << wm) - 1)
    };
    add_table(b, &ms.r, &z[1..1 + wm], &vars, &val, false);
    let mut ut: Vec<QubitId> = z[225..256].to_vec();
    ut.push(z[0]);
    let yt = &y[256 - CMPT..];
    flip(b, &ut);
    for &q in &ut {
        b.x(q);
    }
    erase_overflow_flag(b, ms, yt, &ut, &ms.r, s, paired);
    for &q in &ut {
        b.x(q);
    }
    flip(b, &ut);
}

/// Legacy conservative bound retained for callers/provenance. The actual
/// merged signed tables use 3 monomials + 6 functions + 65 carries (double),
/// or 3 + 5 + 65 + one reserved hq (halve). Pure fold4 uses11+8+63=82.
pub const TABLE_POOL: usize = 90;
pub const SIGNED_TABLE_POOL: usize = 74;
pub const FOUR_BIT_TABLE_POOL: usize = 82;

// ---------------------------------------------------------------- O1 U11: k-bit Montgomery scale blocks
/// Largest block: W = 61 S (lanes 4..k+10 of the window) must not overlap S 2^32 (lanes 32..32+k).
const MONT_KMAX: usize = 22;
/// Carry headroom of a block's window above its addend Y = S (c - 1) < 2^(32+k): 31 lanes, as fold4's.
const MONT_HEAD: usize = 31;

/// Signed binary digits (NAF) of 977^-1 mod 2^k, LSB first, with their positions.
pub(crate) fn mont_naf(k: usize) -> Vec<(usize, i8)> {
    let m = 1u64 << k;
    // 977^-1 mod 2^k by Newton iteration on odd 977
    let mut u: u64 = 1;
    for _ in 0..6 {
        u = u.wrapping_mul(2u64.wrapping_sub(977u64.wrapping_mul(u))) & (m - 1);
    }
    assert_eq!(977u64.wrapping_mul(u) & (m - 1), 1);
    let mut d = vec![];
    let (mut n, mut j) = (u as i64, 0usize);
    while n != 0 {
        if n & 1 == 1 {
            let z = 2 - (n & 3);
            d.push((j, z as i8));
            n -= z;
        }
        n >>= 1;
        j += 1;
    }
    d.retain(|&(j, _)| j < k);
    d
}

/// Window lanes of a k-bit block (from lane 4): Y's 28 + k lanes plus the headroom.
fn mont_win(k: usize) -> usize {
    28 + k + MONT_HEAD
}

/// Pool lanes a k-bit block needs: S (k), W (k + 6) and the window's carries.
pub(crate) fn mont_pool(k: usize) -> usize {
    k + (k + 6) + mont_win(k) - 1
}

/// Expected Toffoli of a k-bit block (halving or doubling), as emitted below.
pub(crate) fn mont_cost(k: usize, double: bool) -> usize {
    let s: usize = mont_naf(k).iter().filter(|&&(j, _)| j > 0).map(|&(j, _)| k - j - 1).sum();
    let w = 2 * k + 2;
    s + 2 * w + (mont_win(k) - 1) + if double { k - 1 } else { 0 }
}


// R24 C73: self-quotient REDC. The final low k output lanes themselves
// hold m = z/c mod 2^k. Four column-interleaved rows subtract (c-1)m,
// using c-1 = 2^4 - 2^6 + 2^10 + 2^32. No new owner is allocated.
// Guard 32 is above the largest operand bit. The dropped window boundary
// remains an inherited approximation, admitted by total rate, not containment.
#[derive(Clone, Copy, Debug)]
struct RedcRec {
    col: usize,
    x: QubitId,
    o: Option<QubitId>,
    ci: Option<QubitId>,
    co: Option<QubitId>,
    neg: bool,
}

fn redc_plan(z: &[QubitId], pool: &[QubitId], k: usize) -> Vec<RedcRec> {
    assert_eq!(z.len(),256);
    assert!((23..=128).contains(&k));
    assert!(pool.len()>=redc_pool(k));
    let rec=redc_plan_general(z,pool,k,[4,6,10,32],32);
    assert_eq!(rec.iter().filter(|r|r.co.is_some()).count(),redc_pool(k));
    rec
}

fn redc_plan_general(z:&[QubitId],pool:&[QubitId],k:usize,shifts:[usize;4],guard:usize)->Vec<RedcRec> {
    let top=(k+shifts[3]+guard+1).min(z.len());
    let mut carry=[None;4];
    let mut dead=[false;4];
    let mut rec=Vec::new();
    let mut used=0;
    for col in 0..top {
        let mut feed=[None;4];
        for (at,a,d) in [(k+shifts[2],0,2),(k+shifts[3],2,3)] {
            if col==at {feed[d]=carry[a];carry[a]=None;dead[a]=true;}
        }
        for (row,(neg,shift)) in shifts.into_iter().enumerate().map(|(r,sh)|(r,(r!=1,sh))) {
            if dead[row] {continue;}
            let own=(col>=shift && col-shift<k).then(||z[col-shift]);
            if feed[row].is_some() {assert!(own.is_none());}
            let o=feed[row].or(own);
            if o.is_none() && carry[row].is_none() {continue;}
            let co=if col+1<top {let q=pool[used];used+=1;Some(q)} else {None};
            rec.push(RedcRec{col,x:z[col],o,ci:carry[row],co,neg});
            carry[row]=co;
        }
    }
    rec
}

fn redc_pool(k: usize) -> usize {4*k+118}

fn redc_emit(b:&mut B, rec:&[RedcRec]) {
    // Compute all carries, retaining their exact affine reconstruction inputs.
    for r in rec {
        if r.neg {b.x(r.x);}
        match (r.o,r.ci,r.co) {
            (Some(o),Some(ci),Some(co))=>{
                b.cx(ci,r.x);b.cx(ci,o);b.and_c(r.x,o,co);
                b.cx(ci,co);b.cx(ci,o);b.cx(o,r.x);
            },
            (Some(o),None,Some(co))=>{b.and_c(r.x,o,co);b.cx(o,r.x);},
            (None,Some(ci),Some(co))=>{b.and_c(r.x,ci,co);b.cx(ci,r.x);},
            (o,ci,None)=>{if let Some(q)=o {b.cx(q,r.x);}if let Some(q)=ci {b.cx(q,r.x);}},
            _=>unreachable!(),
        }
        if r.neg {b.x(r.x);}
    }
    for (i,r) in rec.iter().enumerate().rev() {
        let Some(co)=r.co else {continue;};
        // Later rows in the same column changed x by these affine updates.
        let later=&rec[i+1..];
        for s in later.iter().take_while(|s|s.col==r.col) {
            if let Some(q)=s.o {b.cx(q,r.x);}if let Some(q)=s.ci {b.cx(q,r.x);}
        }
        if r.neg {b.x(r.x);}
        match (r.o,r.ci) {
            (Some(o),Some(ci))=>{
                b.cx(o,r.x);b.cx(ci,o);b.cx(ci,co);b.and_u(r.x,o,co);
                b.cx(ci,o);b.cx(o,r.x);
            },
            (Some(o),None)=>{b.cx(o,r.x);b.and_u(r.x,o,co);b.cx(o,r.x);},
            (None,Some(ci))=>{b.cx(ci,r.x);b.and_u(r.x,ci,co);b.cx(ci,r.x);},
            _=>unreachable!(),
        }
        if r.neg {b.x(r.x);}
        for s in later.iter().take_while(|s|s.col==r.col) {
            if let Some(q)=s.o {b.cx(q,r.x);}if let Some(q)=s.ci {b.cx(q,r.x);}
        }
    }
}

fn redc_halve_k(b:&mut B,pool:&[QubitId],z:&mut Vec<QubitId>,k:usize) {
    redc_emit(b,&redc_plan(z,pool,k));
    z.rotate_left(k);
}

fn redc_double_k(b:&mut B,pool:&[QubitId],z:&mut Vec<QubitId>,k:usize) {
    z.rotate_right(k);
    b.begin();
    redc_emit(b,&redc_plan(z,pool,k));
    let rec=b.end();
    b.play(&rec,true);
}

/// Block plan for 2^-n (2^n) scaling: sizes 1 (one fold), 4 (fold4) or k in 5..=22 (Montgomery block), by DP on the
/// costs above. None when the pool cannot hold the smallest Montgomery block.
pub(crate) fn mont_plan(n: usize, pool: usize, double: bool) -> Option<Vec<usize>> {
    if pool < mont_pool(5) {
        return None;
    }
    let mut best = vec![(0usize, 0usize); n + 1];
    for i in 1..=n {
        let mut opt = (best[i - 1].0 + 60, 1);
        if i >= 4 && pool >= FOUR_BIT_TABLE_POOL {
            opt = opt.min((best[i - 4].0 + 74, 4));
        }
        for k in 5..=MONT_KMAX.min(i) {
            if pool >= mont_pool(k) {
                opt = opt.min((best[i - k].0 + mont_cost(k, double), k));
            }
        }
        for k in 23..=128.min(i) {
            if pool >= redc_pool(k) {
                opt = opt.min((best[i-k].0+redc_pool(k),k));
            }
        }
        best[i] = opt;
    }
    let mut plan = vec![];
    let mut i = n;
    while i > 0 {
        plan.push(best[i].1);
        i -= best[i].1;
    }
    Some(plan)
}

/// w = 61 s mod 2^(k+6) into clean w (s + s<<6 - s<<2), recorded.
fn mont_w(b: &mut B, s: &[QubitId], w: &[QubitId], pool: &[QubitId]) -> Vec<super::builder::G> {
    let k = s.len();
    assert_eq!(w.len(), k + 6);
    b.begin();
    for j in 0..k {
        b.cx(s[j], w[j]);
    }
    let a6: Vec<Option<QubitId>> = s.iter().map(|&q| Some(q)).collect();
    var_add_pool(b, &w[6..k + 6], &a6, pool);
    let mut a2: Vec<Option<QubitId>> = s.iter().map(|&q| Some(q)).collect();
    a2.extend([None; 4]);
    for &q in &w[2..k + 6] {
        b.x(q);
    }
    var_add_pool(b, &w[2..k + 6], &a2, pool);
    for &q in &w[2..k + 6] {
        b.x(q);
    }
    b.end()
}

/// t +=/-= d * (src << j) mod 2^|t| over t[j..] (d = +-1), src truncated to the lanes above j.
fn mont_term(b: &mut B, t: &[QubitId], src: &[QubitId], j: usize, d: i8, pool: &[QubitId]) {
    let k = t.len();
    let add: Vec<Option<QubitId>> = src[..k - j].iter().map(|&q| Some(q)).collect();
    if d < 0 {
        for &q in &t[j..] {
            b.x(q);
        }
    }
    var_add_pool(b, &t[j..], &add, pool);
    if d < 0 {
        for &q in &t[j..] {
            b.x(q);
        }
    }
}

/// z[4..4+win) +=/-= Y, Y = 16 w + 2^32 s (disjoint lanes).
fn mont_window(b: &mut B, z: &[QubitId], s: &[QubitId], w: &[QubitId], pool: &[QubitId], sub: bool) {
    let k = s.len();
    let win = mont_win(k);
    let t = &z[4..4 + win];
    let mut add: Vec<Option<QubitId>> = vec![None; win];
    for (j, &q) in w.iter().enumerate() {
        add[j] = Some(q);
    }
    for (j, &q) in s.iter().enumerate() {
        assert!(add[28 + j].is_none());
        add[28 + j] = Some(q);
    }
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    var_add_pool(b, t, &add, pool);
    if sub {
        for &q in t {
            b.x(q);
        }
    }
}

/// z <- 2^-k z mod p (k-bit Montgomery reduction): S = 977^-1 z_low mod 2^k (so S c = z_low mod 2^k), z -= S (c - 1)
/// = 16 (61 S) + 2^32 S over the window (lanes 0..k then hold S), S cleared from those lanes, which relabel to the top:
/// (z + S p) / 2^k. Exact for z in [0, p) except a window borrow drop (<= 2^-31) and z < S c (~2^-200).
pub(crate) fn mont_halve_k(b: &mut B, pool: &[QubitId], z: &mut Vec<QubitId>, k: usize) {
    assert!((5..=MONT_KMAX).contains(&k) && pool.len() >= mont_pool(k));
    let (s, rest) = pool.split_at(k);
    let (w, carries) = rest.split_at(k + 6);
    let naf = mont_naf(k);
    assert_eq!(naf[0], (0, 1));
    for j in 0..k {
        b.cx(z[j], s[j]);
    }
    for &(j, d) in &naf[1..] {
        mont_term(b, s, &z[..k], j, d, carries);
    }
    let rw = mont_w(b, s, w, carries);
    b.play(&rw, false);
    mont_window(b, z, s, w, carries, true);
    b.play(&rw, true);
    for j in 0..k {
        b.cx(z[j], s[j]);
    }
    z.rotate_left(k);
}

/// z <- 2^k z mod p: the top k lanes H relabel to the bottom (2^k z_low + H), S = H copied, += 16 (61 S) + 2^32 S over the
/// window (H c in all), then S -= 977^-1 (lanes 0..k = 977 H mod 2^k) mod 2^k = 0.
pub(crate) fn mont_double_k(b: &mut B, pool: &[QubitId], z: &mut Vec<QubitId>, k: usize) {
    assert!((5..=MONT_KMAX).contains(&k) && pool.len() >= mont_pool(k));
    let (s, rest) = pool.split_at(k);
    let (w, carries) = rest.split_at(k + 6);
    z.rotate_right(k);
    for j in 0..k {
        b.cx(z[j], s[j]);
    }
    let rw = mont_w(b, s, w, carries);
    b.play(&rw, false);
    mont_window(b, z, s, w, carries, false);
    b.play(&rw, true);
    for &(j, d) in &mont_naf(k) {
        mont_term(b, s, &z[..k], j, -d, carries);
    }
}

/// z <- 2^n z mod p (four at a time).
pub fn mod_double_n(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, n: usize) {
    // S5a scales before the next 256-lane output is allocated. Ms caps its
    // own carry bank at 256; use the remaining room under the actual cap.
    // The overflow flag is clean on entry and unused by scale blocks.
    if n >= 23 && ms.r.len() >= redc_pool(23) {
        let extra=b.alloc_n(super::pointadd_lilypad::peak().saturating_sub(b.live) as usize);
        let mut pool=ms.r.clone();pool.push(ms.k);pool.extend_from_slice(&extra);
        let plan=mont_plan(n,pool.len(),true).unwrap();
        for k in plan {
            match k {
                1=>mod_double(b,ms,z),
                4=>mod_double4(b,ms,z),
                k if k>MONT_KMAX=>redc_double_k(b,&pool,z,k),
                _=>mont_double_k(b,&pool,z,k),
            }
        }
        b.free_n(&extra);
        return;
    }
    if let Some(plan) = mont_plan(n, ms.r.len(), true) {
        for k in plan {
            match k {
                1 => mod_double(b, ms, z),
                4 => mod_double4(b, ms, z),
                k if k > MONT_KMAX => redc_double_k(b, &ms.r, z, k),
                _ => mont_double_k(b, &ms.r, z, k),
            }
        }
        return;
    }
    if ms.r.len() < FOUR_BIT_TABLE_POOL {
        for _ in 0..n {
            mod_double(b, ms, z);
        }
        return;
    }
    for _ in 0..n / 4 {
        mod_double4(b, ms, z);
    }
    for _ in 0..n % 4 {
        mod_double(b, ms, z);
    }
}

/// z <- 2^-n z mod p (four at a time).
pub fn mod_halve_n(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, n: usize) {
    // Scale blocks do not use the clean overflow flag.
    let mut pool=ms.r.clone();pool.push(ms.k);
    if let Some(plan) = mont_plan(n, pool.len(), false) {
        for k in plan {
            match k {
                1 => mod_halve(b, ms, z),
                4 => mod_halve4(b, ms, z),
                k if k > MONT_KMAX => redc_halve_k(b, &pool, z, k),
                _ => mont_halve_k(b, &pool, z, k),
            }
        }
        return;
    }
    if ms.r.len() < FOUR_BIT_TABLE_POOL {
        for _ in 0..n {
            mod_halve(b, ms, z);
        }
        return;
    }
    for _ in 0..n / 4 {
        mod_halve4(b, ms, z);
    }
    for _ in 0..n % 4 {
        mod_halve(b, ms, z);
    }
}

/// z <- 2 z mod p in place (relabel z[0] <- old top bit h, then add h (c - 1); c - 1 is even so lane 0 keeps h).
pub fn mod_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    fold_add(b, ms, z, 1, Some(h), C - 1);
}

/// Inverse of mod_double (z <- z / 2 mod p).
pub fn mod_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let h = z[0];
    fold_sub(b, ms, z, 1, Some(h), C - 1);
    let low = z.remove(0);
    z.push(low);
}

/// z += ctl y mod 2^n and k ^= ctl & carry_out (y restored). The low P lanes (P = pool size, < n) keep logical-AND
/// carries on the pool (2 Toffoli a lane: carry, controlled sum bit), the rest is a Cuccaro ladder whose carry-in is
/// the pool's top carry (3 a lane); the carry out is read between its two passes.
fn ctrl_add_flag(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    if super::chunked::try_add(b, y, z, ctl, Some(ms.k), &ms.r) {
        return;
    }
    use super::arith::{down_m, up_m, Dm};
    let n = z.len();
    let pn = ms.r.len().min(n - 2);
    let c = &ms.r;
    // low part forward: c[i] = carry into lane i + 1 in pool[i]
    for i in 0..pn {
        if i == 0 {
            b.and_c(y[0], z[0], c[0]);
        } else {
            b.cx(c[i - 1], y[i]);
            b.cx(c[i - 1], z[i]);
            b.and_c(y[i], z[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    // high part: Cuccaro with carry-in c[pn - 1]
    let (th, sh) = (&z[pn..], &y[pn..]);
    let up = up_m(b, th, sh, c[pn - 1], false);
    let dn = down_m(b, th, sh, c[pn - 1], Dm::Cond(ctl), false);
    b.play(&up, false);
    b.ccx(ctl, sh[sh.len() - 1], ms.k);
    b.play(&dn, false);
    // low part backward: uncompute each carry by measurement, then the controlled sum bit
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(y[0], z[0], c[0]);
            b.ccx(ctl, y[0], z[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(y[i], z[i], c[i]);
            b.cx(c[i - 1], z[i]);
            b.ccx(ctl, y[i], z[i]);
            b.cx(c[i - 1], y[i]);
        }
    }
}

/// t += ctl a mod 2^n (a restored). The low lanes (as many as `pool` has, < n) keep logical-AND carries on the pool
/// (2 Toffoli a lane), the lanes above a Cuccaro ladder whose carry-in is the pool's top carry (3 a lane); the top
/// lane takes the sum bit only (1). No pool: Takahashi-Tani-Kunihiro.
pub fn ctrl_add_pool(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId, pool: &[QubitId]) {
    if super::chunked::try_add(b, a, t, ctl, None, pool) {
        return;
    }
    use super::arith::{down_m, ttk_add, up_m, Dm};
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    let pn = pool.len().min(n - 1);
    if pn == 0 {
        ttk_add(b, a, t, Some(ctl), None);
        return;
    }
    let c = pool;
    for i in 0..pn {
        if i == 0 {
            b.and_c(a[0], t[0], c[0]);
        } else {
            b.cx(c[i - 1], a[i]);
            b.cx(c[i - 1], t[i]);
            b.and_c(a[i], t[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    // lanes pn..n-1: Cuccaro, the carry into the top lane ends in a[n - 2]
    let (th, sh) = (&t[pn..n - 1], &a[pn..n - 1]);
    if !th.is_empty() {
        let up = up_m(b, th, sh, c[pn - 1], false);
        b.play(&up, false);
    }
    let ct = if th.is_empty() { c[pn - 1] } else { a[n - 2] };
    b.cx(ct, a[n - 1]);
    b.ccx(ctl, a[n - 1], t[n - 1]);
    b.cx(ct, a[n - 1]);
    if !th.is_empty() {
        let dn = down_m(b, th, sh, c[pn - 1], Dm::Cond(ctl), false);
        b.play(&dn, false);
    }
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], c[0]);
            b.ccx(ctl, a[0], t[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(a[i], t[i], c[i]);
            b.cx(c[i - 1], t[i]);
            b.ccx(ctl, a[i], t[i]);
            b.cx(c[i - 1], a[i]);
        }
    }
}

/// add_flag_u with the low P lanes on pool carries (1 Toffoli a lane) and a Cuccaro ladder (2 a lane) above, whose
/// carry-in is the pool's top carry; the carry out is copied out between its two passes.
fn add_flag_u_hybrid(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    use super::arith::{down_m, up_m, Dm};
    let n = z.len();
    let pn = ms.r.len().min(n - 2);
    let c = &ms.r;
    for i in 0..pn {
        if i == 0 {
            b.and_c(y[0], z[0], c[0]);
        } else {
            b.cx(c[i - 1], y[i]);
            b.cx(c[i - 1], z[i]);
            b.and_c(y[i], z[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    let (th, sh) = (&z[pn..], &y[pn..]);
    let up = up_m(b, th, sh, c[pn - 1], false);
    let dn = down_m(b, th, sh, c[pn - 1], Dm::Sum, false);
    b.play(&up, false);
    b.cx(sh[sh.len() - 1], ms.k);
    b.play(&dn, false);
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(y[0], z[0], c[0]);
            b.cx(y[0], z[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(y[i], z[i], c[i]);
            b.cx(c[i - 1], z[i]);
            b.cx(y[i], z[i]);
            b.cx(c[i - 1], y[i]);
        }
    }
}

/// z += y mod 2^n and k = carry_out (k clean on entry, y restored), uncontrolled, every lane a logical-AND carry (1
/// Toffoli). The carry out is formed directly on k. With a pool shorter than n - 1 the ladder runs in chunks of at
/// most P - j - 1 lanes (j = chunk index): each chunk's sums are written at once and its carry out is held on a
/// reserved pool lane as the next chunk's carry-in; after the last chunk the held carries are erased top-down by X
/// measurement, with the exact compare [z' < y + carry-in] over their chunk as the phase oracle under the measured
/// bit (half the chunk's ANDs on average).
fn add_flag_u(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) -> bool {
    let n = z.len();
    let p = ms.r.len();
    // fewest chunks: chunk j < nch - 1 takes at most p - j - 1 lanes (j held carries plus its own carry out live
    // during its erase), the last at most p - nch + 2 (nch - 1 held carries, its carry out on k); the last is made
    // maximal so that the erased chunks (half their lanes on average) are as short as possible
    let last_cap = |nch: usize| p + 2 - nch;
    let mut nch = 1;
    while (0..nch - 1).map(|j| p - j - 1).sum::<usize>() + last_cap(nch) < n {
        nch += 1;
    }
    let mut rest = n - last_cap(nch).min(n);
    let mut bounds = vec![0usize];
    for j in 0..nch - 1 {
        let l = rest.min(p - j - 1);
        assert!(l > 0);
        bounds.push(bounds[j] + l);
        rest -= l;
    }
    bounds.push(n);
    // average Toffoli: chunked n + sum of half the erased chunks; hybrid (Gidney low lanes, Cuccaro rest) 2n - pn
    let chunked2 = 2 * n + (bounds[nch - 1] - bounds[0]);
    let pn = p.min(n - 2);
    if NOCHUNK.with(|c| c.get()) || 2 * (2 * n - pn) <= chunked2 {
        add_flag_u_hybrid(b, ms, z, y);
        return false;
    }
    let paired = fix_pair_save_this_add();
    let shape: FixPairKey = (n, p, bounds.clone());
    if paired {
        FIX_PAIR_STACK.with(|st| st.borrow_mut().push((Vec::new(), None)));
        FIX_PAIR_KEYS.with(|keys| keys.borrow_mut().push(shape.clone()));
    }
    let debts = if FIX_PAIR_MODE.with(|m| m.get()) == 2 {
        let debts = FIX_PAIR_STACK.with(|st| st.borrow_mut().pop())
            .expect("paired repay encountered a chunked add with an empty debt stack");
        let key = FIX_PAIR_KEYS.with(|keys| keys.borrow_mut().pop())
            .expect("paired repay encountered an empty key stack");
        assert_eq!(key, shape, "paired fix-product add shape differs between compute and repay");
        Some(debts)
    } else {
        None
    };
    let repaid = std::cell::Cell::new(0usize);
    let repay = |b: &mut B, pos: usize, q: QubitId| {
        if let Some((carry_debts, overflow_debt)) = &debts {
            for &(debt_pos, bit) in carry_debts {
                if debt_pos == pos {
                    #[cfg(test)]
                    let skip = FIX_PAIR_TEST_NO_REPAY.with(|v| v.get());
                    #[cfg(not(test))]
                    let skip = false;
                    if !skip {
                        b.z_if(q, bit);
                    }
                    repaid.set(repaid.get() + 1);
                }
            }
            if pos == n {
                if let Some(bit) = overflow_debt {
                    #[cfg(test)]
                    let skip = FIX_PAIR_TEST_NO_REPAY.with(|v| v.get());
                    #[cfg(not(test))]
                    let skip = false;
                    if !skip {
                        b.z_if(q, *bit);
                    }
                    repaid.set(repaid.get() + 1);
                }
            }
        }
    };
    let h = |j: usize| ms.r[p - j];
    for ch in 0..nch {
        let (lo, hi) = (bounds[ch], bounds[ch + 1]);
        let last = ch + 1 == nch;
        let cin = if ch == 0 { None } else { Some(h(ch)) };
        // carry into lane i (lo < i <= hi); the carry out (i = n) is formed on k
        let cr = |i: usize| if i == hi && !last { h(ch + 1) } else if i == n { ms.k } else { ms.r[i - lo - 1] };
        let ci = |i: usize| if i == lo { cin } else { Some(cr(i)) };
        for i in lo..hi {
            match ci(i) {
                None => b.and_c(y[i], z[i], cr(i + 1)),
                Some(c) => {
                    b.cx(c, y[i]);
                    b.cx(c, z[i]);
                    b.and_c(y[i], z[i], cr(i + 1));
                    b.cx(c, cr(i + 1));
                }
            }
            if i + 1 == hi {
                repay(b, i + 1, cr(i + 1));
            }
        }
        if last {
            if let Some((carry_debts, overflow_debt)) = &debts {
                assert_eq!(
                    repaid.get(),
                    carry_debts.len() + usize::from(overflow_debt.is_some()),
                    "paired fix-product debts were not all consumed",
                );
            }
        }
        for i in (lo..hi).rev() {
            // a chunk's carry out stays: held for the next chunk, or (last chunk) on k
            let keep = i + 1 == hi;
            match ci(i) {
                None => {
                    if !keep {
                        b.and_u(y[i], z[i], cr(i + 1));
                    }
                    b.cx(y[i], z[i]);
                }
                Some(c) => {
                    if !keep {
                        b.cx(c, cr(i + 1));
                        b.and_u(y[i], z[i], cr(i + 1));
                    }
                    b.cx(c, z[i]);
                    b.cx(y[i], z[i]);
                    b.cx(c, y[i]);
                }
            }
        }
    }
    for ch in (1..nch).rev() {
        let (lo, hi) = (bounds[ch - 1], bounds[ch]);
        let cin = if ch == 1 { None } else { Some(h(ch - 1)) };
        // C58: a fold between compute and repay can change low carry values.
        // Discharge every boundary inside the inherited 66-lane fold locally,
        // using the exact original carry oracle, rather than deferring its phase.
        // Higher boundaries and overflow retain their inherited pairing contract.
        if paired && hi >= WM {
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(h(ch), bit);
            FIX_PAIR_STACK.with(|st| {
                st.borrow_mut().last_mut().expect("missing paired debt entry").0.push((hi, bit));
            });
            continue;
        }
        for &q in &z[lo..hi] {
            b.x(q);
        }
        b.carry_erase_cin(&y[lo..hi], &z[lo..hi], super::builder::ONE, h(ch), &ms.r[..hi - lo], cin);
        for &q in &z[lo..hi] {
            b.x(q);
        }
    }
    paired
}

/// z <- z + (-1)^s y mod p; `s` (a qubit outside z and y) subtracts where it is 1 (None: add). No quantum control
/// on the ladder: a subtraction runs as ~(~z + y). In the complemented domain w the overflow k of ~z + y folds +c as
/// for an add (~(~z + y - 2^256 + c) = z - y + p), and k = [w < y + s c] exactly; the 32-lane erase compares
/// w_top < y_top + s, so ties (z near 0 when subtracting) count as a borrow and the approximation misses only for z
/// within 2^-32 p of p (as an add's for z near p).
pub fn signed_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], s: Option<QubitId>) {
    let flip = |b: &mut B| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b);
    let paired = add_flag_u(b, ms, z, y);
    fold_add(b, ms, z, 0, Some(ms.k), C);
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    for &q in zt {
        b.x(q);
    }
    erase_overflow_flag(b, ms, yt, zt, &ms.r, s, paired);
    for &q in zt {
        b.x(q);
    }
    flip(b);
}

/// t += sext(a) mod 2^|t| (a two's complement, |a| <= |t|, a restored), uncontrolled: logical-AND carries on `pool`
/// (>= |t| - 1). The lanes above a take carry - sign as ~(~u + (carry ^ sign)) (complemented where the sign is set).
pub fn add_sext(b: &mut B, a: &[QubitId], t: &[QubitId], pool: &[QubitId]) {
    let (la, lt) = (a.len(), t.len());
    assert!(la >= 2 && lt >= la && pool.len() + 1 >= lt);
    let c = pool;
    let u = &t[la..];
    let sg = a[la - 1];
    for &q in u {
        b.cx(sg, q);
    }
    for i in 0..la {
        if i == 0 {
            b.and_c(a[0], t[0], c[0]);
        } else if i + 1 < la || !u.is_empty() {
            b.cx(c[i - 1], a[i]);
            b.cx(c[i - 1], t[i]);
            b.and_c(a[i], t[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    if !u.is_empty() {
        // carry-in of u: c[la - 1] ^ sign (sign = a[la - 1] ^ c[la - 2] here)
        let d = c[la - 1];
        b.cx(a[la - 1], d);
        b.cx(c[la - 2], d);
        let e = |j: usize| if j == 0 { d } else { c[la - 1 + j] };
        for j in 0..u.len() - 1 {
            b.and_c(u[j], e(j), e(j + 1));
        }
        for j in (0..u.len()).rev() {
            if j + 1 < u.len() {
                b.and_u(u[j], e(j), e(j + 1));
            }
            b.cx(e(j), u[j]);
        }
        b.cx(c[la - 2], d);
        b.cx(a[la - 1], d);
    }
    for i in (0..la).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], c[0]);
            b.cx(a[0], t[0]);
        } else if i + 1 < la || !u.is_empty() {
            b.cx(c[i - 1], c[i]);
            b.and_u(a[i], t[i], c[i]);
            b.cx(c[i - 1], t[i]);
            b.cx(a[i], t[i]);
            b.cx(c[i - 1], a[i]);
        } else {
            // top lane, no carry out kept: sum only
            b.cx(c[i - 1], t[i]);
            b.cx(a[i], t[i]);
        }
    }
    for &q in u {
        b.cx(sg, q);
    }
}

/// t -= sext(a) mod 2^|t| as ~(~t + sext(a)).
pub fn sub_sext(b: &mut B, a: &[QubitId], t: &[QubitId], pool: &[QubitId]) {
    for &q in t {
        b.x(q);
    }
    add_sext(b, a, t, pool);
    for &q in t {
        b.x(q);
    }
}

/// C_T on `r` (two's complement: lo = r[0..256) unsigned, hi = r[256..) signed) -> lo' = lo + hi c, hi kept, so lo'
/// = C_T (mod p) as a 256-lane unsigned multiplier. lo' leaves [0, 2^256) only if lo is within |hi c| < 2^94 of either
/// end (~2^-160). `tq` (>= |hi| + 10 clean lanes, 72 for frogtail) holds hi * 977 meanwhile.
pub fn reduce_hi(b: &mut B, r: &[QubitId], tq: &[QubitId], pool: &[QubitId]) {
    let (lo, hi) = (&r[..256], &r[256..]);
    let h = hi.len();
    assert!(h + 10 <= tq.len() && tq.len() <= 224);
    add_sext(b, hi, &lo[32..], pool);
    b.begin();
    for j in 0..tq.len() {
        b.cx(hi[j.min(h - 1)], tq[j]);
    }
    add_sext(b, hi, &tq[10..], pool);
    sub_sext(b, hi, &tq[5..], pool);
    sub_sext(b, hi, &tq[4..], pool);
    let r977 = b.end();
    b.play(&r977, false);
    add_sext(b, tq, lo, pool);
    b.play(&r977, true);
}

/// z <- z - ctl y mod p (inverse of ctrl_modadd).
pub fn ctrl_modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    b.begin();
    ctrl_modadd(b, ms, z, y, ctl, ctl);
    let r = b.end();
    b.play(&r, true);
}

/// z <- z + (ctl ? y : 0) mod p. `d` is one borrowed qubit (unused here; kept for the call shape).
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId, d: QubitId) {
    // z += ctl y mod 2^256, k = ctl & carry out
    ctrl_add_flag(b, ms, z, y, ctl);
    fold_add(b, ms, z, 0, Some(ms.k), C);
    // erase k = ctl & [z < y] = ctl & carry(~z_top + y_top) (top-lane compare; differs w.p. <= 2^-32)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    let _ = d;
    for &q in zt {
        b.x(q);
    }
    b.carry_erase(yt, zt, ctl, ms.k, &ms.r);
    for &q in zt {
        b.x(q);
    }
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], d: QubitId) {
    signed_modadd(b, ms, z, y, None);
    let _ = d;
}

pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], d: QubitId) {
    signed_modadd(b, ms, z, y, Some(ms.one));
    let _ = d;
}

/// z <- (ctl ? p - z : z) for z in [1, p) (ctl None: always): complement, then subtract c - 1.
pub fn ctrl_neg(b: &mut B, ms: &Ms, z: &[QubitId], ctl: Option<QubitId>) {
    for &q in z {
        match ctl {
            Some(c) => b.cx(c, q),
            None => b.x(q),
        }
    }
    fold_sub(b, ms, z, 1, ctl, C - 1);
}

/// O1 U33: phase (-1)^(sum_j m_j c_j) of the carries c_j (into window lanes i0+1..n-1) of v + h k (k constant, h one
/// qubit outside v), v restored, no sum written: each carry is formed once (one AND, or a recycled-prefix replay when
/// the pool is short), its phase applied by a classically conditioned Z, and erased by measurement.
fn carry_phase_const(b: &mut B, v: &[QubitId], h: QubitId, k: u64, m: &[crate::circuit::BitId], pool: &[QubitId]) {
    let n = v.len();
    assert!(k != 0 && n <= 64 && m.len() == n);
    let i0 = k.trailing_zeros() as usize;
    if i0 + 1 >= n {
        return;
    }
    let kb = |i: usize| (k >> i) & 1 == 1;
    let need = n - 1 - i0;
    let loan = need.saturating_sub(pool.len());
    assert!(loan == 0 || pool.len() > loan, "phase chain loan must retain a distinct bridge");
    let bridge = if loan == 0 { n - 1 } else { i0 + pool.len() };
    let c = |i: usize| if i <= bridge { pool[i - i0 - 1] } else { pool[i - bridge - 1] };
    let compute = |b: &mut B, i: usize| {
        if i == i0 {
            b.and_c(v[i], h, c(i + 1));
        } else if kb(i) {
            b.cx(c(i), h);
            b.cx(c(i), v[i]);
            b.and_c(h, v[i], c(i + 1));
            b.cx(c(i), c(i + 1));
            b.cx(c(i), h);
        } else {
            b.and_c(v[i], c(i), c(i + 1));
        }
    };
    // inverse of compute (v restored, no sum)
    let erase = |b: &mut B, i: usize| {
        if i == i0 {
            b.and_u(v[i], h, c(i + 1));
        } else if kb(i) {
            b.cx(c(i), h);
            b.cx(c(i), c(i + 1));
            b.and_u(h, v[i], c(i + 1));
            b.cx(c(i), h);
            b.cx(c(i), v[i]);
        } else {
            b.and_u(v[i], c(i), c(i + 1));
        }
    };
    if loan == 0 {
        for i in i0..n - 1 {
            compute(b, i);
            b.z_if(c(i + 1), m[i + 1]);
        }
        for i in (i0..n - 1).rev() {
            erase(b, i);
        }
        return;
    }
    b.begin();
    for i in i0..i0 + loan {
        compute(b, i);
    }
    let prefix = b.end();
    b.play(&prefix, false);
    for i in i0..i0 + loan {
        b.z_if(c(i + 1), m[i + 1]);
    }
    for i in i0 + loan..bridge {
        compute(b, i);
        b.z_if(c(i + 1), m[i + 1]);
    }
    b.play(&prefix, true);
    for i in bridge..n - 1 {
        compute(b, i);
        b.z_if(c(i + 1), m[i + 1]);
    }
    for i in (bridge..n - 1).rev() {
        erase(b, i);
    }
    b.play(&prefix, false);
    for i in (i0..bridge).rev() {
        erase(b, i);
    }
}

/// O1 U33: the L3 lambda fix's ctrl_neg(z, key); z_if(z_i, m_i) x256; ctrl_neg(z, key) as one phase oracle of
/// (-1)^(m . w), w = ctrl_neg(z, key) = (z ^ key) with key (c - 1) subtracted on the window z[1..65): outside the window
/// w_i = z_i ^ key; inside, w = ~(v + key k') with v = ~(z ^ key) and k' = (c - 1)/2, so w_j = z_j ^ key ^ key k'_j ^
/// carry_j. z is never changed (the replaced pair's second fold is gone); the carries' phases cost one chain.
pub(crate) fn ctrl_neg_phase(b: &mut B, ms: &Ms, z: &[QubitId], key: QubitId, m: &[crate::circuit::BitId]) {
    assert_eq!(z.len(), 256);
    let kp = (C - 1) >> 1;
    for i in 0..256 {
        b.z_if(z[i], m[i]);
        let inside = (1..1 + RW).contains(&i);
        if !inside || (kp >> (i - 1)) & 1 == 0 {
            b.z_if(key, m[i]);
        }
    }
    let v = &z[1..1 + RW];
    for &q in v {
        b.cx(key, q);
        b.x(q);
    }
    carry_phase_const(b, v, key, kp, &m[1..1 + RW], &ms.r);
    for &q in v {
        b.x(q);
        b.cx(key, q);
    }
}

// C72: position-keyed, paired lazy S2 arithmetic. All quantum scratch is
// partitioned from the caller's already allocated Ms bank.
#[derive(Default)]
struct LazyStepDebt {
    carries: Vec<(usize, crate::circuit::BitId)>,
    kappa: Option<crate::circuit::BitId>,
}
struct LazyBlockDebt {
    digits: Vec<QubitId>,
    steps: Vec<LazyStepDebt>,
    low: Vec<crate::circuit::BitId>,
    high: Vec<QubitId>,
}
pub(crate) struct LazyFixPair {
    pool: Vec<QubitId>,
    blocks: Vec<LazyBlockDebt>,
    min_pool: usize,
    cap: u64,
    rng_start: usize,
    baseline_draws: usize,
}

// Unlike FixPair's shape stack, each receipt names a mathematical carry
// position. Compute and inverse may use different chunk plans and widths.
fn lazy_position_add(
    b: &mut B, z: &[QubitId], y: &[QubitId], pool: &[QubitId],
    flag: Option<QubitId>, save: bool, debt: Option<(&LazyStepDebt, QubitId)>,
) -> LazyStepDebt {
    let n = z.len(); let p = pool.len();
    assert!(p >= 3 && y.len() <= n);
    let mut nch = 1;
    while (0..nch-1).map(|j| p-j-1).sum::<usize>() + p-(nch-1) < n {
        nch += 1;
        assert!(nch < p, "lazy chunk plan infeasible");
    }
    let mut rest = n-(p-(nch-1)).min(n);
    let mut bounds = vec![0];
    for j in 0..nch-1 {
        let len = rest.min(p-j-1); assert!(len>0);
        bounds.push(bounds[j]+len); rest-=len;
    }
    bounds.push(n);
    let h = |j:usize| pool[p-j];
    let mut out = LazyStepDebt::default();
    let mut consumed = 0;
    for ch in 0..nch {
        let (lo,hi)=(bounds[ch],bounds[ch+1]); let last=ch+1==nch;
        let cin=if ch==0 {None} else {Some(h(ch))};
        let cr=|i:usize| if i==hi && !last {h(ch+1)} else {pool[i-lo-1]};
        let ci=|i:usize| if i==lo {cin} else {Some(cr(i))};
        let upto=hi-usize::from(last && flag.is_none());
        for i in lo..upto {
            match (y.get(i),ci(i)) {
                (Some(&a),None)=>b.and_c(a,z[i],cr(i+1)),
                (Some(&a),Some(c))=>{
                    b.cx(c,a);b.cx(c,z[i]);b.and_c(a,z[i],cr(i+1));
                    b.cx(c,cr(i+1));
                },
                (None,Some(c))=>b.and_c(c,z[i],cr(i+1)),
                (None,None)=>{},
            }
            if let Some((d,digit))=debt {
                for &(pos,m) in &d.carries {
                    if pos==i+1 {b.z_if(cr(i+1),m);consumed+=1;}
                }
                if i+1==y.len() {
                    if let Some(m)=d.kappa {
                        b.z_if(cr(i+1),m);
                        // The measured lane was kappa XOR !digit.
                        b.x(digit);b.z_if(digit,m);b.x(digit);consumed+=1;
                    }
                }
            }
        }
        if last {
            if let Some(q)=flag {b.cx(cr(n),q);} else {
                if let Some(c)=ci(n-1) {b.cx(c,z[n-1]);}
                if let Some(&a)=y.get(n-1) {b.cx(a,z[n-1]);}
            }
        }
        for i in (lo..upto).rev() {
            let keep=i+1==hi && !last;
            match (y.get(i),ci(i)) {
                (Some(&a),None)=>{
                    if !keep {b.and_u(a,z[i],cr(i+1));}b.cx(a,z[i]);
                },
                (Some(&a),Some(c))=>{
                    if !keep {b.cx(c,cr(i+1));b.and_u(a,z[i],cr(i+1));}
                    b.cx(c,z[i]);b.cx(a,z[i]);b.cx(c,a);
                },
                (None,Some(c))=>{
                    if !keep {b.and_u(c,z[i],cr(i+1));}b.cx(c,z[i]);
                },
                (None,None)=>{},
            }
        }
    }
    if let Some((d,_))=debt {
        assert_eq!(consumed,d.carries.len()+usize::from(d.kappa.is_some()),"lazy carry receipts not consumed");
    }
    for ch in (1..nch).rev() {
        let (lo,hi)=(bounds[ch-1],bounds[ch]);
        if save {
            let m=b.fresh_bits(1)[0];b.hmr_to(h(ch),m);out.carries.push((hi,m));
        } else {
            assert!(hi<=y.len(),"extended zero source entered a measured chunk");
            for &q in &z[lo..hi] {b.x(q);}
            let cin=if ch==1 {None} else {Some(h(ch-1))};
            b.carry_erase_cin(&y[lo..hi],&z[lo..hi],ONE,h(ch),&pool[..hi-lo],cin);
            for &q in &z[lo..hi] {b.x(q);}
        }
    }
    out
}

fn lazy_t_assemble_inplace(
    b:&mut B, bs:Vec<QubitId>, ks:&[QubitId], digits:&[QubitId], pool:&mut Vec<QubitId>,
) -> (Vec<QubitId>,Vec<crate::circuit::BitId>) {
    let k=bs.len();let mut t:Vec<_>=bs.into_iter().rev().collect();
    t.push(pool.pop().unwrap());t.push(pool.pop().unwrap());
    for (&q,&d) in ks.iter().zip(digits) {b.x(d);b.cx(d,q);}
    let mut add:Vec<_>=ks.iter().rev().map(|&q|Some(q)).collect();add.resize(k+2,None);
    var_add_pool(b,&t,&add,pool);
    let mut sub:Vec<_>=digits.iter().rev().map(|&q|Some(q)).collect();sub.resize(k+2,None);
    for &q in &t {b.x(q);}var_add_pool(b,&t,&sub,pool);for &q in &t {b.x(q);}
    for &d in digits {b.x(d);}
    let m=b.fresh_bits(k);
    for (&q,&bit) in ks.iter().zip(&m) {b.hmr_to(q,bit);pool.push(q);}
    (t,m)
}

// Signed NAF: C=2^32+2^10-2^5-2^4+1. Each chain retains the
// K+66 window; var_add_pool supplies an exact recycled-prefix loan.
fn lazy_fold(b:&mut B,z:&[QubitId],t:&[QubitId],pool:&[QubitId],c:u64,sub:bool) {
    let w=z.len().min(t.len()-2+66);
    let mut v=c as i128;let mut sh=0;
    while v!=0 {
        if v&1!=0 {
            let digit=if v&3==1 {1} else {-1};v-=digit;
            if sh<w {
                let dst=&z[sh..w];
                let src:Vec<_>=(0..dst.len()).map(|i|Some(t[i.min(t.len()-1)])).collect();
                let i0=0;let need=dst.len()-1-i0;
                if need>pool.len() {assert!(pool.len()>need-pool.len(),"lazy fold bridge aliases");}
                let neg=(digit<0)^sub;
                if neg {for &q in dst {b.x(q);}}
                var_add_pool(b,dst,&src,pool);
                if neg {for &q in dst {b.x(q);}}
            }
        }
        v>>=1;sh+=1;
    }
}
fn lazy_unfold(b:&mut B,z:&[QubitId],t:&[QubitId],pool:&[QubitId],c:u64) {
    lazy_fold(b,z,t,pool,c,true);
}

fn lazy_quotient(b:&mut B,z:&[QubitId],y:&[QubitId],digits:&[QubitId],pool:&mut Vec<QubitId>,c:u64) -> Vec<QubitId> {
    let k=digits.len();let d:Vec<_>=(0..k).map(|_|pool.pop().unwrap()).collect();
    for (j,&sign) in digits.iter().enumerate() {
        let sh=k-1-j;let dst=&d[sh..];
        b.x(sign);for &q in dst {b.cx(sign,q);}
        let add:Vec<_>=y[..dst.len()].iter().map(|&q|Some(q)).collect();
        var_add_pool(b,dst,&add,pool);
        for &q in dst {b.cx(sign,q);}b.x(sign);
    }
    for &q in &d {b.x(q);}
    let add:Vec<_>=z[..k].iter().map(|&q|Some(q)).collect();var_add_pool(b,&d,&add,pool);
    for &q in &d {b.x(q);}
    // D_i is retained as q_i; the would-be zero low digit is omitted.
    // Upper D += q_i*(c+1)/2 after subtracting q_i*p.
    for i in 0..k-1 {
        let src:Vec<_>=(0..k-i-1).map(|j|if ((c+1)/2>>j)&1!=0 {Some(d[i])} else {None}).collect();
        var_add_pool(b,&d[i+1..],&src,pool);
    }
    d
}

fn lazy_double_block(b:&mut B,z:&mut Vec<QubitId>,y:&[QubitId],digits:&[QubitId],pair:&mut LazyFixPair,c:u64) {
    let mut bs=Vec::new();let mut ks=Vec::new();let mut steps=Vec::new();
    for &digit in digits {
        bs.push(z.pop().unwrap());z.insert(0,pair.pool.pop().unwrap());
        let kap=pair.pool.pop().unwrap();
        pair.min_pool=pair.min_pool.min(pair.pool.len());
        b.x(digit);for &q in z.iter() {b.cx(digit,q);}
        steps.push(lazy_position_add(b,z,y,&pair.pool,Some(kap),true,None));
        for &q in z.iter() {b.cx(digit,q);}b.x(digit);
        ks.push(kap);
    }
    let (t,km)=lazy_t_assemble_inplace(b,bs,&ks,digits,&mut pair.pool);
    for (d,m) in steps.iter_mut().zip(km) {d.kappa=Some(m);}
    lazy_fold(b,z,&t,&pair.pool,c,false);
    let k=digits.len();let m=b.fresh_bits(k);
    for (&q,&bit) in t[..k].iter().zip(&m) {b.hmr_to(q,bit);pair.pool.push(q);}
    pair.blocks.push(LazyBlockDebt{digits:digits.to_vec(),steps,low:m,high:t[k..].to_vec()});
    assert!(b.live<=pair.cap);
}

fn exact_halve_back_step(b:&mut B,z:&mut Vec<QubitId>,y:&[QubitId],digit:QubitId,debt:&LazyStepDebt,pool:&mut Vec<QubitId>) {
    // Inverse sign is digit itself (compute sign was !digit).
    for &q in z.iter() {b.cx(digit,q);}
    lazy_position_add(b,z,y,pool,None,false,Some((debt,digit)));
    for &q in z.iter() {b.cx(digit,q);}
    // The exact even low bit is |0>; arithmetic halve is a relabel.
    pool.push(z.remove(0));
}

pub(crate) fn product_lazy(b:&mut B,ms:&Ms,z:&mut Vec<QubitId>,a:&[QubitId],y:&[QubitId]) -> LazyFixPair {
    assert_eq!(z.len(),256);assert_eq!(a.len(),256);assert_eq!(y.len(),256);
    // Preserve the inherited downstream simulator tape offset. This reference
    // generation is host-only and does not emit into b. Its count determines
    // padding exactly; it is never varied or selected by a cohort outcome.
    let baseline_draws = {
        let mut probe=B::new();let pa=probe.alloc_n(256);let py=probe.alloc_n(256);let mut pz=probe.alloc_n(256);
        let pm=Ms::alloc_room(&mut probe,b.live);
        assert_eq!(pm.r.len(),ms.r.len());
        fix_pair_begin_save(0);product(&mut probe,&pm,&mut pz,&pa,&py);fix_pair_end_save();
        fix_pair_begin_repay();product_inv(&mut probe,&pm,&mut pz,&pa,&py);fix_pair_end_repay();
        probe.ops.iter().filter(|op|matches!(op.kind,crate::circuit::OperationType::R|crate::circuit::OperationType::Hmr)).count()
    };
    let mut pair=LazyFixPair{pool:ms.r.iter().copied().chain(std::iter::once(ms.k)).collect(),blocks:Vec::new(),min_pool:usize::MAX,cap:b.live,rng_start:b.ops.len(),baseline_draws};
    for i in 0..256 {b.cx(y[i],z[i]);}
    let digits:Vec<_>=a[1..].iter().rev().copied().collect();
    for block in digits.chunks(16) {lazy_double_block(b,z,y,block,&mut pair,C);}
    let k=pair.pool.pop().unwrap();let tmp=Ms{k,r:pair.pool.clone(),one:ONE};
    b.x(a[0]);ctrl_modsub(b,&tmp,z,y,a[0]);b.x(a[0]);pair.pool.push(k);
    pair
}
pub(crate) fn product_inv_lazy(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],y:&[QubitId],mut pair:LazyFixPair) {
    let k=pair.pool.pop().unwrap();let tmp=Ms{k,r:pair.pool.clone(),one:ONE};
    b.x(a[0]);ctrl_modadd(b,&tmp,z,y,a[0],a[0]);b.x(a[0]);pair.pool.push(k);
    while let Some(block)=pair.blocks.pop() {
        let tlo=lazy_quotient(b,z,y,&block.digits,&mut pair.pool,C);
        for (&q,&m) in tlo.iter().zip(&block.low) {b.z_if(q,m);}
        let mut t=tlo;t.extend(block.high);
        lazy_unfold(b,z,&t,&pair.pool,C);z.extend(t);
        for i in (0..block.digits.len()).rev() {
            pair.min_pool=pair.min_pool.min(pair.pool.len());
            exact_halve_back_step(b,z,y,block.digits[i],&block.steps[i],&mut pair.pool);
        }
        assert_eq!(z.len(),258);
        pair.pool.extend(z.drain(256..));
        assert!(b.live<=pair.cap);
    }
    for i in 0..256 {b.cx(y[i],z[i]);}
    let used=b.ops[pair.rng_start..].iter().filter(|op|matches!(op.kind,crate::circuit::OperationType::R|crate::circuit::OperationType::Hmr)).count();
    assert!(used<=pair.baseline_draws,"lazy pair consumes more random words than its base");
    let pad=pair.baseline_draws-used;
    if pad!=0 {
        // z is now exactly zero (the complete product inverse has returned).
        // Measuring it consumes a random word, with zero quantum/phase effect.
        let m=b.fresh_bits(1)[0];
        for _ in 0..pad {b.hmr_to(z[0],m);}
    }
    eprintln!("C72 RNG base={} used={} pad={} aligned={}",pair.baseline_draws,used,pad,used+pad);
    eprintln!("C72 lazy S2 cap={} min_add_pool={} fused_signed_calls=0 signed_wm_max={}",pair.cap,pair.min_pool,signed_wm_max());
    assert_eq!(signed_wm_max(),66,"C72 forbids narrowed fused windows");
}

/// z = a * y mod p into a zero register z: signed-digit Horner, top digit first. For n-bit a,
/// a = 2^(n-1) + sum_{k<n-1} (2 a_{k+1} - 1) 2^k - (1 - a_0): every step adds or subtracts y with no control on the
/// ladder, and one controlled subtraction fixes a_0. `a` must not overlap `y`.
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
    // doublings fused with the preceding add (signed_modadd_double): D, (A D)..., A
    mod_double(b, ms, z);
    for k in (0..n - 1).rev() {
        b.x(a[k + 1]);
        if k > 0 {
            signed_modadd_double(b, ms, z, y, Some(a[k + 1]));
        } else {
            signed_modadd(b, ms, z, y, Some(a[k + 1]));
        }
        b.x(a[k + 1]);
    }
    b.x(a[0]);
    ctrl_modsub(b, ms, z, y, a[0]);
    b.x(a[0]);
}

/// Inverse of `product` (z = a y -> 0) built from forward operations, so its measured erases stay measured.
pub fn product_inv(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    b.x(a[0]);
    ctrl_modadd(b, ms, z, y, a[0], a[0]);
    b.x(a[0]);
    for k in 0..n - 1 {
        signed_modadd_halve(b, ms, z, y, Some(a[k + 1]));
    }
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
}

/// z += y^2 mod p (any z), y restored: z is halved n - 1 times, then the signed-digit Horner of `product` runs on
/// z with y's own lanes as the digit signs. `tmp` is a clean qubit (holds !y_0 for the a_0 fix).
pub fn square_acc(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], tmp: QubitId) {
    let n = y.len();
    mod_halve_n(b, ms, z, n - 1);
    // each add fused with the following doubling: (A D)..., A
    signed_modadd_double(b, ms, z, y, None);
    for k in (0..n - 1).rev() {
        b.cx(y[k + 1], tmp);
        b.x(tmp);
        if k > 0 {
            signed_modadd_double(b, ms, z, y, Some(tmp));
        } else {
            signed_modadd(b, ms, z, y, Some(tmp));
        }
        b.x(tmp);
        b.cx(y[k + 1], tmp);
    }
    b.cx(y[0], tmp);
    b.x(tmp);
    ctrl_modsub(b, ms, z, y, tmp);
    b.x(tmp);
    b.cx(y[0], tmp);
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd(b, ms, z, y, a[i], a[(i + 1) % 256]);
        if i != 255 {
            mod_double(b, ms, y);
        }
    }
    for _ in 0..255 {
        mod_halve(b, ms, y);
    }
}

/// z = -y * C * 2^-tt mod p into a zero register z (relabeled in place by the halvings), C = two's complement value
/// of `c` (LSB first, top lane weighs -2^(M-1)), y in [1, p) restored. Bottom-up halving Horner over signed digits:
/// -C = sum_{k<M-1} (1 - 2 c_{k+1}) 2^k + (2 c_{M-1} - 1) 2^(M-1) + (1 - c_0), so z starts at (1 - c_0) y and every
/// step adds or subtracts y with no control on the ladder; then tt - M more halvings. (Accumulating -C, the partial
/// sums reach 0 only by a subtraction y - y, which lands on the canonical 0; with +C an addition (p - y) + y would
/// leave the non-canonical p.)
pub fn product_tail_neg(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    product_tail_neg_s(b, ms, z, c, y, tt, true);
}

/// product_tail_neg for a two's complement (`signed`) or unsigned C (top digit -1: -C = sum_{k<M-1} (1 - 2 c_{k+1})
/// 2^k - 2^(M-1) + (1 - c_0)).
pub fn product_tail_neg_s(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    signed: bool,
) {
    let m = c.len();
    assert!(tt >= m);
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], z[i]);
    }
    b.x(c[0]);
    for k in 0..m {
        if k + 1 < m {
            signed_modadd_halve(b, ms, z, y, Some(c[k + 1]));
        } else if signed {
            b.x(c[m - 1]);
            signed_modadd_halve(b, ms, z, y, Some(c[m - 1]));
            b.x(c[m - 1]);
        } else {
            signed_modadd_halve(b, ms, z, y, Some(ms.one));
        }
    }
    for _ in m..tt {
        mod_halve(b, ms, z);
    }
}

/// Uncompute of product_tail_neg_s's result (z as that call left it, vector order included): the tt - m trailing
/// halvings and steps m-1..k0 run backwards as forward operations (a doubling, then the opposite signed add), so their
/// measured erases stay measured; the start and steps 0..k0-1, where a partial sum can be exactly 0 (an addition
/// would then leave the non-canonical p; a zero at step k has probability ~2^-k), run as the inverse of their
/// hybrid-ladder recording. z ends |0>, in the vector order the compute started from.
#[allow(clippy::too_many_arguments)]
pub fn product_tail_neg_s_uncompute(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    signed: bool,
    k0: usize,
) {
    let m = c.len();
    assert!(k0 < m && tt >= m);
    for _ in m..tt {
        mod_double(b, ms, z);
    }
    // D, (A D)..., A: each add fused with the next step's doubling
    mod_double(b, ms, z);
    for k in (k0..m).rev() {
        let fused = k > k0;
        let mut add = |b: &mut B, z: &mut Vec<QubitId>, s: Option<QubitId>| {
            if fused {
                signed_modadd_double(b, ms, z, y, s);
            } else {
                signed_modadd(b, ms, z, y, s);
            }
        };
        if k + 1 < m {
            b.x(c[k + 1]);
            add(b, z, Some(c[k + 1]));
            b.x(c[k + 1]);
        } else if signed {
            add(b, z, Some(c[m - 1]));
        } else {
            add(b, z, None);
        }
    }
    let mut za = z.clone();
    za.rotate_right(k0);
    let v0 = za.clone();
    NOCHUNK.with(|f| f.set(true));
    b.begin();
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], za[i]);
    }
    b.x(c[0]);
    for k in 0..k0 {
        signed_modadd_halve(b, ms, &mut za, y, Some(c[k + 1]));
    }
    let r = b.end();
    NOCHUNK.with(|f| f.set(false));
    assert_eq!(&za, z);
    b.play(&r, true);
    *z = v0;
}

/// product_tail_neg_s for an unsigned digit source `c` that is X-measured as it is used (bit c_k into `mbits[k]`
/// right after its last use, the phase left for the caller's recompute to fix): every measured lane joins the carry
/// pool of the later adds. Emitted directly (not recordable).
#[allow(clippy::too_many_arguments)]
pub fn product_tail_neg_stream(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    mbits: &[crate::circuit::BitId],
) {
    let m = c.len();
    assert!(tt >= m);
    let mut ms2 = Ms { k: ms.k, r: ms.r.clone(), one: ms.one };
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], z[i]);
    }
    b.x(c[0]);
    b.hmr_to(c[0], mbits[0]);
    ms2.r.push(c[0]);
    for k in 0..m {
        if k + 1 < m {
            signed_modadd_halve(b, &ms2, z, y, Some(c[k + 1]));
            b.hmr_to(c[k + 1], mbits[k + 1]);
            ms2.r.push(c[k + 1]);
        } else {
            signed_modadd_halve(b, &ms2, z, y, Some(ms.one));
        }
    }
    mod_halve_n(b, &ms2, z, tt - m);
}

/// z = y * C * 2^-tt mod p (product_tail_neg, then a negation).
pub fn product_tail(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    product_tail_neg(b, ms, z, c, y, tt);
    ctrl_neg(b, ms, z, None);
}

// L3 offset lambda-fix tail. The additive offset makes every generic partial
// sum eligible for the same forward-operation uncompute, so TAIL_K0 can be
// zero and every chunked add can participate in L1 pairing. The independent
// audit prices the moved v2(C) degeneracy band and one borrow event at about
// +1.6e-5 failing shots per 9,024; this is booked against L1's larger error
// reduction under inherited-contract term 3.
const OFFSET_R: u64 = 0x9E37_79B9;
const OFFSET_LANE: usize = 0;

#[cfg(test)]
thread_local! {
    static OFFSET_TEST_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
pub(crate) fn offset_test_disabled(value: bool) {
    OFFSET_TEST_DISABLED.with(|v| v.set(value));
}

fn offset_enabled() -> bool {
    #[cfg(test)]
    {
        return !OFFSET_TEST_DISABLED.with(|v| v.get());
    }
    #[cfg(not(test))]
    {
        true
    }
}

fn offset_constant(tt: usize) -> super::frogdrop_sched::N {
    use super::frogdrop_sched::{p, N};
    let pm = p();
    N::from(OFFSET_R).mul_mod(N::from(2u64).pow_mod(N::from(tt as u64), pm), pm)
}

fn xor_constant(b: &mut B, z: &[QubitId], value: super::frogdrop_sched::N) {
    for i in 0..256 {
        if value.bit(i) {
            b.x(z[i]);
        }
    }
}

/// The offset constant as a 64-bit value when it fits (tt = 256: OFFSET_R c < 2^64).
fn offset_constant_u64(tt: usize) -> Option<u64> {
    let k = offset_constant(tt);
    if k < (super::frogdrop_sched::N::from(1u64) << 64) { Some(k.as_limbs()[0]) } else { None }
}

/// z[0..65) +=/-= K (sub as ~(~z + K)) mod 2^65: the 64-bit constant over a 65-lane window, so lane 64 (clean on the
/// add) receives the carry out of lane 63; the |1> lane as control, carry-prefix recycling when the pool is short.
fn offset_lo_add(b: &mut B, ms: &Ms, z: &[QubitId], k: u64, sub: bool) {
    let t = &z[..65];
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    let need = 65 - 1 - k.trailing_zeros() as usize;
    if ms.r.len() >= need {
        const_add_pool(b, t, ms.one, k, &ms.r);
    } else {
        const_add_recycled(b, t, ms.one, k, &ms.r);
    }
    if sub {
        for &q in t {
            b.x(q);
        }
    }
}

/// O1 U21 (exact): z (zero) <- [c_0 = 0] y + K mod 2^256 exactly, K = offset constant < 2^64. AND copy of the low 64
/// lanes; K added over a 65-lane window whose lane 64 takes the carry out kappa; the increment's carry chain t_64 =
/// kappa, t_{j+1} = t_j & y_j kept in z's own clean lanes (kappa = 1 only when c_0 = 0, so [c_0 = 0] y_j = y_j there);
/// then z_j ^= [c_0 = 0] y_j for j >= 64, leaving z_j = a_j ^ t_j, the incremented high word. No truncation: equal to
/// the inherited xor(K) + ctrl_modadd except where [c_0 = 0] y + K reaches p (both leave a ~2^-192 class).
fn offset_start_exact(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], c0: QubitId, k: u64) {
    b.x(c0);
    for i in 0..64 {
        b.and_c(c0, y[i], z[i]);
    }
    b.x(c0);
    offset_lo_add(b, ms, z, k, false);
    for j in 64..255 {
        b.and_c(z[j], y[j], z[j + 1]);
    }
    b.x(c0);
    for j in 64..256 {
        b.ccx(c0, y[j], z[j]);
    }
    b.x(c0);
}

/// Inverse of offset_start_exact (z -> 0): high XORs, the chain measured away from the top, K subtracted over the
/// window (lane 64 cleared), the low AND copy measured away.
fn offset_end_exact(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], c0: QubitId, k: u64) {
    b.x(c0);
    for j in 64..256 {
        b.ccx(c0, y[j], z[j]);
    }
    b.x(c0);
    for j in (64..255).rev() {
        b.and_u(z[j], y[j], z[j + 1]);
    }
    offset_lo_add(b, ms, z, k, true);
    b.x(c0);
    for i in 0..64 {
        b.and_u(c0, y[i], z[i]);
    }
    b.x(c0);
}

#[cfg(test)]
thread_local! {
    static TEST_OFFSET_BASE_START: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Test-only: route the offset tail's start/end through the inherited xor + ctrl_modadd form (differential reference).
#[cfg(test)]
pub(crate) fn test_offset_base_start(value: bool) {
    TEST_OFFSET_BASE_START.with(|v| v.set(value));
}

fn offset_exact_u64(tt: usize) -> Option<u64> {
    #[cfg(test)]
    if TEST_OFFSET_BASE_START.with(|v| v.get()) {
        return None;
    }
    offset_enabled().then(|| offset_constant_u64(tt)).flatten()
}

#[cfg(test)]
pub(crate) fn test_offset_exact(args: Option<(&mut B, &Ms, &[QubitId], &[QubitId], QubitId, bool)>) -> u64 {
    let k = offset_constant_u64(256).expect("offset constant fits 64 bits at tt = 256");
    if let Some((b, ms, z, y, c0, end)) = args {
        if end { offset_end_exact(b, ms, z, y, c0, k) } else { offset_start_exact(b, ms, z, y, c0, k) }
    }
    k
}

/// Compute -y*C*2^-tt with the L3 offset, starting and ending in the same
/// external representation as product_tail_neg_s.
pub fn product_tail_neg_s_offset(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    let m = c.len();
    assert!(tt >= m && m == 256);
    if offset_enabled() {
        xor_constant(b, z, offset_constant(tt));
    }
    b.x(c[0]);
    ctrl_modadd(b, ms, z, y, c[0], c[0]);
    b.x(c[0]);
    for k in 0..m {
        if k + 1 < m {
            signed_modadd_halve(b, ms, z, y, Some(c[k + 1]));
        } else {
            signed_modadd_halve(b, ms, z, y, Some(ms.one));
        }
    }
    for _ in m..tt {
        mod_halve(b, ms, z);
    }
    if offset_enabled() {
        const_add_ms(b, ms, &z[OFFSET_LANE..OFFSET_LANE + 64], ms.one, OFFSET_R.wrapping_neg());
    }
}

/// Forward-operation uncompute of product_tail_neg_s_offset. Every one of the
/// 256 tail steps is paired; no hybrid-recording prefix remains.
pub fn product_tail_neg_s_offset_uncompute(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    let m = c.len();
    assert!(tt >= m && m == 256);
    if offset_enabled() {
        const_add_ms(b, ms, &z[OFFSET_LANE..OFFSET_LANE + 64], ms.one, OFFSET_R);
    }
    for _ in m..tt {
        mod_double(b, ms, z);
    }
    mod_double(b, ms, z);
    for k in (0..m).rev() {
        let fused = k > 0;
        let add = |b: &mut B, z: &mut Vec<QubitId>, s: Option<QubitId>| {
            if fused {
                signed_modadd_double(b, ms, z, y, s);
            } else {
                signed_modadd(b, ms, z, y, s);
            }
        };
        if k + 1 < m {
            b.x(c[k + 1]);
            add(b, z, Some(c[k + 1]));
            b.x(c[k + 1]);
        } else {
            add(b, z, None);
        }
    }
    b.x(c[0]);
    ctrl_modsub(b, ms, z, y, c[0]);
    b.x(c[0]);
    if offset_enabled() {
        xor_constant(b, z, offset_constant(tt));
    }
}

/// Exact variable-source extension of the donor's carry-prefix recycling.
/// Erase a lower prefix while the independent bridge carry stays live; lend
/// its clean wires to the upper carries, then regenerate before low cleanup.
fn var_add_recycled(b:&mut B,t:&[QubitId],add:&[Option<QubitId>],pool:&[QubitId]) {
    let n=t.len();let i0=add.iter().position(|a|a.is_some()).unwrap();
    let need=n-1-i0;let loan=need-pool.len();assert!(pool.len()>loan);
    let bridge=i0+pool.len();
    let c=|i:usize| if i<=bridge {pool[i-i0-1]} else {pool[i-bridge-1]};
    let compute=|b:&mut B,i:usize| {
        match add[i] {
            Some(h) if i==i0=>b.and_c(t[i],h,c(i+1)),
            Some(h)=>{b.cx(c(i),h);b.cx(c(i),t[i]);b.and_c(h,t[i],c(i+1));b.cx(c(i),c(i+1));b.cx(c(i),h);},
            None=>b.and_c(t[i],c(i),c(i+1)),
        }
    };
    let erase_sum=|b:&mut B,i:usize| {
        match add[i] {
            Some(h) if i==i0=>{b.and_u(t[i],h,c(i+1));b.cx(h,t[i]);},
            Some(h)=>{b.cx(c(i),h);b.cx(c(i),c(i+1));b.and_u(h,t[i],c(i+1));b.cx(c(i),h);b.cx(h,t[i]);},
            None=>{b.and_u(t[i],c(i),c(i+1));b.cx(c(i),t[i]);},
        }
    };
    b.begin();for i in i0..i0+loan {compute(b,i);}let prefix=b.end();
    b.play(&prefix,false);for i in i0+loan..bridge {compute(b,i);}
    b.play(&prefix,true);for i in bridge..n-1 {compute(b,i);}
    b.cx(c(n-1),t[n-1]);if let Some(h)=add[n-1] {b.cx(h,t[n-1]);}
    for i in (bridge..n-1).rev() {erase_sum(b,i);}
    b.play(&prefix,false);for i in (i0..bridge).rev() {erase_sum(b,i);}
}

/// Classical-source n-bit add with carry-out. Source bits remain classical.
/// The first carry is a classically controlled CX; every higher lane is one AND.
/// Each majority is (t XOR y)(ci XOR y) XOR y, where y is a classical bit.
pub(crate) fn classical_add_flag(b:&mut B,t:&[QubitId],y:&[crate::circuit::BitId],k:QubitId,pool:&[QubitId]) {
    let n=t.len();assert_eq!(n,y.len());assert!(pool.len()>=n);
    b.cx_if(t[0],pool[0],y[0]);
    for i in 1..n {
        b.x_if(t[i],y[i]);b.x_if(pool[i-1],y[i]);
        b.and_c(t[i],pool[i-1],pool[i]);b.x_if(pool[i],y[i]);
        b.x_if(t[i],y[i]);b.x_if(pool[i-1],y[i]);
    }
    b.cx(pool[n-1],k);
    for i in (1..n).rev() {
        b.x_if(t[i],y[i]);b.x_if(pool[i-1],y[i]);b.x_if(pool[i],y[i]);
        b.and_u(t[i],pool[i-1],pool[i]);
        b.x_if(t[i],y[i]);b.x_if(pool[i-1],y[i]);
        b.cx(pool[i-1],t[i]);b.x_if(t[i],y[i]);
    }
    b.measure_and_push(pool[0]);b.z_if(t[0],y[0]);b.pop_classical();
    b.x_if(t[0],y[0]);
}

/// Same signed modular operation and inherited fold/compare support as modadd/modsub.
/// Only the low-cost classical operand representation and carry allocation differ.
pub(crate) fn modadd_classical(b:&mut B,ms:&Ms,z:&[QubitId],y:&[crate::circuit::BitId],sub:bool) {
    assert_eq!(z.len(),256);assert!(ms.r.len()>=256);
    if sub {for &q in z {b.x(q);}}
    classical_add_flag(b,z,y,ms.k,&ms.r);
    fold_add(b,ms,z,0,Some(ms.k),C);
    let zt=&z[256-CMPT..];let yt=&ms.r[..CMPT];
    for i in 0..CMPT {b.x_if(yt[i],y[256-CMPT+i]);b.x(zt[i]);}
    b.carry_erase_cin(yt,zt,super::builder::ONE,ms.k,&ms.r[CMPT..2*CMPT],if sub {Some(ms.one)} else {None});
    for i in 0..CMPT {b.x_if(yt[i],y[256-CMPT+i]);b.x(zt[i]);}
    if sub {for &q in z {b.x(q);}}
}

// C58/U35 exact value-lifetime carry reuse.
fn c58_var_add_lean(b:&mut B,t:&[QubitId],add:&[Option<QubitId>],pool:&[QubitId],recipes:&[(QubitId,Vec<QubitId>)]) {
    let n=t.len();let i0=add.iter().position(|a|a.is_some()).unwrap();
    let need=n-1-i0;let gap=need-pool.len();let bridge=i0+pool.len();
    let freed:Vec<_>=recipes.iter().filter(|(q,_)|!add[bridge..].contains(&Some(*q))).take(gap).collect();
    if freed.is_empty(){var_add_recycled(b,t,add,pool);return;}
    let loan=gap-freed.len();assert!(pool.len()>loan);
    let mut upper=pool[..loan].to_vec();upper.extend(freed.iter().map(|(q,_)|*q));
    let c=|i:usize| if i<=bridge {pool[i-i0-1]} else {upper[i-bridge-1]};
    let compute=|b:&mut B,i:usize| {
        match add[i] {
            Some(h) if i==i0=>b.and_c(t[i],h,c(i+1)),
            Some(h)=>{b.cx(c(i),h);b.cx(c(i),t[i]);b.and_c(h,t[i],c(i+1));b.cx(c(i),c(i+1));b.cx(c(i),h);},
            None=>b.and_c(t[i],c(i),c(i+1)),
        }
    };
    let erase_sum=|b:&mut B,i:usize| {
        match add[i] {
            Some(h) if i==i0=>{b.and_u(t[i],h,c(i+1));b.cx(h,t[i]);},
            Some(h)=>{b.cx(c(i),h);b.cx(c(i),c(i+1));b.and_u(h,t[i],c(i+1));b.cx(c(i),h);b.cx(h,t[i]);},
            None=>{b.and_u(t[i],c(i),c(i+1));b.cx(c(i),t[i]);},
        }
    };
    b.begin();for i in i0..i0+loan {compute(b,i);}let prefix=b.end();
    b.play(&prefix,false);for i in i0+loan..bridge {compute(b,i);}
    b.play(&prefix,true);
    for(q,terms)in &freed{for &a in terms{b.cx(a,*q);}}
    for i in bridge..n-1 {compute(b,i);}
    b.cx(c(n-1),t[n-1]);if let Some(h)=add[n-1] {b.cx(h,t[n-1]);}
    for i in (bridge..n-1).rev() {erase_sum(b,i);}
    for(q,terms)in freed.iter().rev(){for &a in terms{b.cx(a,*q);}}
    b.play(&prefix,false);for i in (i0..bridge).rev() {erase_sum(b,i);}
}


#[cfg(test)]
mod c58_table_tests {
    use super::*;
    use crate::{circuit::analyze_ops,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
    #[test]
    fn c58_table_lean_exact() {
        let mut count=0;
        for n in [8usize,10,16,66] {
            for room in [n/2+1,n/2+2,n-2] {
                let mut b=B::new();let t=b.alloc_n(n);let v=b.alloc_n(3);let f=b.alloc_n(2);let pool=b.alloc_n(room);
                let mut add=vec![None;n];for i in 0..n {add[i]=Some(if i<2{f[0]}else if i<4{f[1]}else{v[i%3]});}
                let recipes=vec![(f[0],vec![v[0],v[1]]),(f[1],vec![v[1],v[2]])];
                b.begin();var_add_recycled(&mut b,&t,&add,&pool);let old=b.end();b.play(&old,false);let oo=std::mem::take(&mut b.ops);
                b.begin();c58_var_add_lean(&mut b,&t,&add,&pool,&recipes);let new=b.end();b.play(&new,false);let no=std::mem::take(&mut b.ops);
                let(nq,nb,_,_)=analyze_ops(oo.iter().chain(&no));
                let samples=if n<=10 {1usize<<n}else{256};
                for byte in [0u8,255,170,85] {for x in 0..8usize {for base in (0..samples).step_by(64) {
                    let mut tape=Fixed(byte);let mut a=Simulator::new(nq as usize,nb as usize,&mut tape);
                    for k in 0..64.min(samples-base) {
                        let z=if n<=10 {(base+k)as u128}else{((base+k)as u128).wrapping_mul(0x9e3779b97f4a7c159e3779b9u128)};
                        for i in 0..n{if z>>i&1!=0{a.qubits[t[i].0 as usize]|=1<<k;}}
                        for i in 0..3{if x>>i&1!=0{a.qubits[v[i].0 as usize]|=1<<k;}}
                        if(x^(x>>1))&1!=0{a.qubits[f[0].0 as usize]|=1<<k;}
                        if((x>>1)^(x>>2))&1!=0{a.qubits[f[1].0 as usize]|=1<<k;}
                    }
                    let init=a.qubits.clone();a.apply_iter(oo.iter());let oq=a.qubits.clone();let op=a.phase;
                    let mut nt=Fixed(byte);let mut z=Simulator::new(nq as usize,nb as usize,&mut nt);z.qubits=init;z.apply_iter(no.iter());
                    assert_eq!(oq,z.qubits,"n={n} room={room} x={x} base={base} tape={byte}");assert_eq!(op,z.phase);assert_eq!(z.phase,0);
                    count+=64.min(samples-base);
                }}}
            }
        }
        eprintln!("C58_TABLE_LEAN PASS scalar_cases={count} widths8,10_exhaustive widths16,66_sampled tapes4 all_wire_phase");
    }
}
