//! Masked ripple ladders for froghop-double.
//!
//! A ladder runs over lanes l = 0..L (carry order) with target T[l] and source S[l]. Most lanes are ordinary
//! Cuccaro majority cells (carry stored in the source lane). Lanes inside a mask window are "masked cells" that keep
//! the carry on a running wire and apply the carry transition only where the running mask f = 1 (the shot's own
//! lane); elsewhere the carry passes through and both lanes are restored untouched. (Mask-the-carry-transition
//! idea: bulengerk's masked majority cell on gnuchev's packed inversion.)
//!
//! The running mask f starts at a known constant before lane 0 and is toggled by "sources": a source flips f when
//! entering ladder lane l iff its quantum value v equals tv(l) = a + d*l (l in its window). One-hot matches come from
//! an incrementally updated decoder (~2 Toffoli per lane, n-1 prefix ancillas). After the last lane f is cleaned with
//! comparators (f_end = f0 ^ sum_s [v_s in the interval its window covers]), so values outside a window are harmless.

use super::builder::{B, G};
use crate::circuit::{BitId, QubitId};

/// A toggle source: entering ladder lane l (lo <= l < hi) toggles f iff v == a + d*l. `pre` = prefix ancillas
/// (len v.len()-1 for a retained decoder, or v.len()-2 for a transient
/// equality per toggle), disjoint from overlapping sources.
#[derive(Clone)]
pub struct Src {
    pub lo: usize,
    pub hi: usize,
    pub v: Vec<QubitId>,
    pub a: isize,
    pub d: isize,
    pub pre: Vec<QubitId>,
    /// late source: at its matching lane, flip T there before the cell and toggle f only after the cell (the lane
    /// stays in the old mask region, with T's bit inverted)
    pub late: bool,
}

impl Src {
    fn tv(&self, l: usize) -> isize {
        // d=0 is the pi-parity decoder: a is the known low bit and v=pi>>1.
        if self.d == 0 {
            if l & 1 == self.a as usize { (l >> 1) as isize } else { -1 }
        } else { self.a + self.d * l as isize }
    }
    /// interval of matched values over the window: [min, max]
    fn span(&self) -> (isize, isize) {
        let mut vals = (self.lo..self.hi).map(|l| self.tv(l)).filter(|&j| j >= 0);
        if let Some(first) = vals.next() {
            vals.fold((first, first), |(lo, hi), j| (lo.min(j), hi.max(j)))
        } else { (0, -1) }
    }
}

/// Scratch for masked passes: running mask f, AND temps, comparator chain ancillas (len >= max value bits).
#[derive(Clone)]
pub struct Mscr {
    pub f: QubitId,
    pub t: QubitId,
    pub gf: QubitId,
    pub chain: Vec<QubitId>,
}

thread_local! {
    /// R5-FIT799 R5_MROWY: the masked TERM-NC top cell's source is the row's flipped zero source m, held on no lane:
    /// Some(sign lane) gives m = !sign (Some(NO_LANE): row 0, m = 1); s ^ x is formed on the carry wire x instead
    pub static TOPM: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
/// row 0's marker for TOPM (m = 1, no sign lane)
pub const NO_LANE: QubitId = QubitId(u64::MAX);
thread_local! {
    /// retake799 (r801): decoders with n - 2 prefix lanes keep them RETAINED (levels 0 .. n-3, bits n-1 .. 1) and
    /// toggle with CCX(prefix, bit-0 literal) instead of rebuilding a transient equality
    pub static RSHORT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R10_SH2 (claude-r8): decoders with n - 3 prefix lanes keep them RETAINED (levels 0 .. n-4, bits n-1 .. 2) and
    /// toggle by the AND of the last level and the bit-1 and bit-0 literals through one borrowed lane (any state,
    /// restored; 4 Toffoli per toggle)
    pub static RSHORT2: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R12_SH3 (fable 796b): decoders with n - 4 prefix lanes keep them RETAINED (levels 0 .. n-5, bits n-1 .. 3) and
    /// toggle by the AND of the last level and the bit-2, bit-1 and bit-0 literals through two borrowed lanes (any
    /// state, restored; 8 Toffoli per toggle)
    pub static RSHORT3: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R11_LA5 (fable, 797): toggle sources whose matched value tv(l) exceeds this write nothing into their target at
    /// that lane (the lane stays a masked cell); a retained decoder still moves its prefix to tv(l), so the paired
    /// down pass finds it where it expects it. Default: no limit.
    pub static TVMAX: std::cell::Cell<isize> = const { std::cell::Cell::new(isize::MAX) };
    /// R9_PREFIX (r9 "prefix" worker, dev knob): decoders with n - 5 prefix lanes keep them RETAINED (levels 0 .. n-6,
    /// bits n-1 .. 4) and form the next level (bit 3) transiently on the ladder's AND temp `sc.t`, which is |0> between
    /// cells; the toggle is then RSHORT3's 4-input AND (that level, bits 2, 1, 0) through two borrowed lanes and the
    /// level is uncomputed by measurement: one lane fewer than RSHORT3 for one more Toffoli per toggle
    pub static RSHORT4T: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R9_PREFIX: the same transient-level form one level up: n - 4 prefix lanes retained (bits n-1 .. 3), bit 2 formed
    /// on the AND temp, bits 1 and 0 through one borrowed lane (RSHORT2's toggle): one lane fewer than RSHORT2 for one
    /// more Toffoli per toggle. Takes precedence over RSHORT3 (same prefix length) while set.
    pub static RSHORT3T: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 fwd94 "Vollgasbuebe" L: set while a masked ladder whose RSHORT4T form greedyfrog's R14_FWD94 chose is open
    /// (its decoders toggle by `Dec::xor_ret_tmp_cc`, R9_PREFIX's RSHORT4T sites keep `xor_ret_tmp`)
    pub static R14L: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 läckBobby-b F (fotl765 R14 pfx94): decoders with n - 3 prefix lanes keep them RETAINED (bits n-1 .. 2) and form
    /// the bit-1 level transiently on the ladder's AND temp `sc.t` (|0> between cells; uncomputed by measurement); the
    /// toggle is then one CCX with the bit-0 literal: one lane fewer than RSHORT for one more Toffoli per toggle (and three
    /// fewer than RSHORT2's borrowed-lane toggle). Takes precedence over RSHORT2 (same prefix length) while set.
    pub static RSHORT2T: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 läckBobby-b U: 6-bit decoders with NO retained level: bits 5 and 4 are ANDed onto the AND temp `sc.t` at each
    /// toggle and the toggle is the 5-input AND (that temp, bits 3 .. 0) through three borrowed lanes (Barenco, 12 CCX):
    /// one lane fewer than RSHORT4T for four more Toffoli per toggle
    pub static RSHORT5T: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// R14 läckBobby: negative controls (dev, inert unless R14P_BRK is set): `f` forms the transient bit-1 level without its
/// literal, `u` drops the bit-4 literal from the transient level
pub(crate) fn pfx94_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14P_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}
/// R14 fwd94 negative controls (dev only, inert unless set; read in release builds so the fixed-input A/B can run them,
/// the official environment is empty): `R14_FWD94_BRK=lvl` forms the R14 ladders' transient level without its literal,
/// `cc` leaves the toggle's CCX chain on the literal lane lit(3) un-undone
pub(crate) fn r14_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14_FWD94_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}
/// R9_PREFIX: negative control (dev only, inert unless R9_BRK is set): R9_BRK=lvl forms the transient level without
/// its literal (a = o instead of o & lit), so the toggle fires on the wrong values
pub(crate) fn r9_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R9_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}
/// One-hot decoder: pre[i] = AND of literal matches for value bits n-1 .. n-2-i at the current j.
struct Dec<'a> {
    v: &'a [QubitId],
    pre: &'a [QubitId],
    cur: Option<usize>,
}

impl<'a> Dec<'a> {
    fn n(&self) -> usize {
        self.v.len()
    }
    /// retake799 (r801): a retained prefix one level short (see RSHORT)
    fn short(&self) -> bool {
        RSHORT.with(|c| c.get()) && self.pre.len() + 2 == self.n()
    }
    fn short2(&self) -> bool {
        RSHORT2.with(|c| c.get()) && self.n() >= 4 && self.pre.len() + 3 == self.n()
    }
    fn short3(&self) -> bool {
        RSHORT3.with(|c| c.get()) && self.n() >= 5 && self.pre.len() + 4 == self.n()
    }
    /// R9_PREFIX: retained levels 0 .. n-6 plus a transient level on the AND temp (see RSHORT4T)
    fn short4t(&self) -> bool {
        RSHORT4T.with(|c| c.get()) && self.n() >= 6 && self.pre.len() + 5 == self.n()
    }
    /// R9_PREFIX: retained levels 0 .. n-5 plus a transient level on the AND temp (see RSHORT3T)
    fn short3t(&self) -> bool {
        RSHORT3T.with(|c| c.get()) && self.n() >= 5 && self.pre.len() + 4 == self.n()
    }
    /// R14 läckBobby-b F: retained levels 0 .. n-4 plus a transient bit-1 level on the AND temp (see RSHORT2T)
    fn short2t(&self) -> bool {
        RSHORT2T.with(|c| c.get()) && self.n() >= 4 && self.pre.len() + 3 == self.n()
    }
    /// R14 läckBobby-b U: no retained level (6-bit decoders only, see RSHORT5T)
    fn short5t(&self) -> bool {
        RSHORT5T.with(|c| c.get()) && self.n() == 6 && self.pre.is_empty()
    }
    /// R14 läckBobby-b U: target ^= [v == j] with no retained level: tmp = lit5 & lit4 on the clean AND temp (|0> before
    /// and after: uncomputed by measurement), then target ^= tmp & lit3 & lit2 & lit1 & lit0 through three borrowed lanes
    /// (any state, restored; Barenco et al. 1995 Lemma 7.2, 12 CCX)
    fn xor_t0(&mut self, b: &mut B, j: usize, target: QubitId, tmp: QubitId) {
        assert!(self.n() == 6 && self.pre.is_empty());
        let l: Vec<(QubitId, bool)> = (0..6).map(|k| self.lit(k, j)).collect();
        assert!(tmp != target && !self.v.contains(&tmp) && !self.v.contains(&target),
                "R14 U: the AND temp collides with the decoder");
        let ds: Vec<QubitId> = borrowed().into_iter().filter(|&q| q != tmp && q != target && !self.v.contains(&q)).take(3).collect();
        assert!(ds.len() == 3, "R14 U: three borrowed lanes");
        let (a1, a2, a3) = (ds[0], ds[1], ds[2]);
        for &(q, ng) in &l { if ng { b.x(q); } }
        if pfx94_brk("u") { b.cx(l[5].0, tmp); } else { b.and_c(l[5].0, l[4].0, tmp); }
        let (c1, c2, c3, c4, c5) = (tmp, l[3].0, l[2].0, l[1].0, l[0].0);
        for _ in 0..2 {
            b.ccx(c5, a3, target);
            b.ccx(c4, a2, a3);
            b.ccx(c3, a1, a2);
            b.ccx(c1, c2, a1);
            b.ccx(c3, a1, a2);
            b.ccx(c4, a2, a3);
        }
        if pfx94_brk("u") { b.cx(l[5].0, tmp); } else { b.and_u(l[5].0, l[4].0, tmp); }
        for &(q, ng) in &l { if ng { b.x(q); } }
    }
    /// R9_PREFIX: target ^= [v == j] with the last retained level o, the transient level a = o & lit(k) on the clean
    /// AND temp `tmp` (|0> before, |0> after: uncomputed by measurement), and the remaining literals k-1 .. 0 through
    /// k - 1 borrowed lanes (k = 3: RSHORT3's 8-CCX toggle on a; k = 2: RSHORT2's 4-CCX toggle on a)
    fn xor_ret_tmp(&mut self, b: &mut B, j: usize, target: QubitId, tmp: QubitId, k: usize) {
        let o = self.goto_impl(b, j, true);
        let (qk, nk) = self.lit(k, j);
        assert!(tmp != o && tmp != qk && tmp != target && !self.pre.contains(&tmp) && !self.v.contains(&tmp),
                "R9_PREFIX: the AND temp collides with the decoder");
        if nk { b.x(qk); }
        if r9_brk("lvl") || (k == 1 && pfx94_brk("f")) { b.cx(o, tmp); } else { b.and_c(o, qk, tmp); }
        if k == 1 {
            // R14 läckBobby-b F: RSHORT's toggle with the transient level a = tmp in place of the retained level
            let (q0, n0) = self.lit(0, j);
            if n0 { b.x(q0); }
            b.ccx(tmp, q0, target);
            if n0 { b.x(q0); }
        } else if k == 3 {
            let (q2, n2) = self.lit(2, j);
            let (q1, n1) = self.lit(1, j);
            let (q0, n0) = self.lit(0, j);
            let ds: Vec<QubitId> = borrowed().into_iter()
                .filter(|&q| q != o && q != tmp && q != qk && q != q2 && q != q1 && q != q0 && q != target && !self.pre.contains(&q))
                .take(2).collect();
            assert!(ds.len() == 2, "R9_PREFIX: two borrowed lanes");
            let (d1, d2) = (ds[0], ds[1]);
            if n2 { b.x(q2); }
            if n1 { b.x(q1); }
            if n0 { b.x(q0); }
            // xor_ret_short3's sequence with the transient level a = tmp in place of the retained level o
            b.ccx(q0, d2, target);
            b.ccx(q1, d1, d2);
            b.ccx(tmp, q2, d1);
            b.ccx(q1, d1, d2);
            b.ccx(q0, d2, target);
            b.ccx(q1, d1, d2);
            b.ccx(tmp, q2, d1);
            b.ccx(q1, d1, d2);
            if n0 { b.x(q0); }
            if n1 { b.x(q1); }
            if n2 { b.x(q2); }
        } else {
            assert_eq!(k, 2);
            let (q1, n1) = self.lit(1, j);
            let (q0, n0) = self.lit(0, j);
            let d = borrowed().into_iter()
                .find(|&q| q != o && q != tmp && q != qk && q != q1 && q != q0 && q != target && !self.pre.contains(&q))
                .expect("R9_PREFIX: a borrowed lane");
            if n1 { b.x(q1); }
            if n0 { b.x(q0); }
            // xor_ret_short2's sequence with a = tmp in place of o
            b.ccx(q0, d, target);
            b.ccx(tmp, q1, d);
            b.ccx(q0, d, target);
            b.ccx(tmp, q1, d);
            if n0 { b.x(q0); }
            if n1 { b.x(q1); }
        }
        if r9_brk("lvl") || (k == 1 && pfx94_brk("f")) { b.cx(o, tmp); } else { b.and_u(o, qk, tmp); }
        if nk { b.x(qk); }
    }
    /// R14 fwd94 "Vollgasbuebe" L: `xor_ret_tmp`'s k = 3 toggle (target ^= [v == j] with the last retained level o and
    /// the transient level a = o & lit(3) on the clean AND temp `tmp`) with the remaining literals 2, 1, 0 on the two
    /// literal lanes of a instead of two borrowed lanes (R8_CC's conditionally clean lanes): where a = 1 both o and
    /// lit(3) are 1, so after an X each is |0> and carries the CCX chain o' = lit(2) lit(1), l3' = o' lit(0); the target
    /// takes a & l3', which is 0 where a = 0 whatever the chain left there; the chain is then undone by the same CCX
    /// (exact on every shot) and the X, and a is uncomputed by measurement. 6 Toffoli per toggle (RSHORT3's: 8).
    fn xor_ret_tmp_cc(&mut self, b: &mut B, j: usize, target: QubitId, tmp: QubitId) {
        let o = self.goto_impl(b, j, true);
        let (q3, n3) = self.lit(3, j);
        let (q2, n2) = self.lit(2, j);
        let (q1, n1) = self.lit(1, j);
        let (q0, n0) = self.lit(0, j);
        let ls = [o, q3, q2, q1, q0, target, tmp];
        assert!((0..ls.len()).all(|i| (i + 1..ls.len()).all(|k| ls[i] != ls[k])) && !self.pre.contains(&tmp)
                && !self.v.contains(&tmp) && !self.pre.contains(&target) && !self.v.contains(&target),
                "R14_FWD94: the toggle's lanes collide");
        let brk = r14_brk("lvl");
        if n3 { b.x(q3); }
        if n2 { b.x(q2); }
        if n1 { b.x(q1); }
        if n0 { b.x(q0); }
        if brk { b.cx(o, tmp); } else { b.and_c(o, q3, tmp); }
        b.x(o);
        b.x(q3);
        b.ccx(q2, q1, o);
        b.ccx(o, q0, q3);
        b.ccx(tmp, q3, target);
        if !r14_brk("cc") { b.ccx(o, q0, q3); }
        b.ccx(q2, q1, o);
        b.x(q3);
        b.x(o);
        if brk { b.cx(o, tmp); } else { b.and_u(o, q3, tmp); }
        if n0 { b.x(q0); }
        if n1 { b.x(q1); }
        if n2 { b.x(q2); }
        if n3 { b.x(q3); }
    }
    fn xor_ret_short3(&mut self, b: &mut B, j: usize, target: QubitId) {
        let o = self.goto_impl(b, j, true);
        let (q2, n2) = self.lit(2, j);
        let (q1, n1) = self.lit(1, j);
        let (q0, n0) = self.lit(0, j);
        let ds: Vec<QubitId> = borrowed().into_iter()
            .filter(|&q| q != o && q != q2 && q != q1 && q != q0 && q != target && !self.pre.contains(&q))
            .take(2).collect();
        assert!(ds.len() == 2, "R12_SH3: two borrowed lanes");
        let (d1, d2) = (ds[0], ds[1]);
        if n2 { b.x(q2); }
        if n1 { b.x(q1); }
        if n0 { b.x(q0); }
        // target ^= q0 d2; d2 ^= q1 d1; d1 ^= o q2; d2 ^= q1 d1; target ^= q0 d2; d2 ^= q1 d1; d1 ^= o q2; d2 ^= q1 d1
        // => target ^= q0 q1 q2 o, d1 and d2 restored
        b.ccx(q0, d2, target);
        b.ccx(q1, d1, d2);
        b.ccx(o, q2, d1);
        b.ccx(q1, d1, d2);
        // negative control for the gate tests only: R12_BRK=sh3 drops the second target CCX (target ^= q0 d2_0 instead
        // of q0 q1 q2 o: the toggle writes garbage), R12_BRK=sh3d leaves the second borrowed lane unrestored
        let brk = cfg!(test).then(|| std::env::var("R12_BRK").unwrap_or_default()).unwrap_or_default();
        if brk != "sh3" { b.ccx(q0, d2, target); }
        b.ccx(q1, d1, d2);
        b.ccx(o, q2, d1);
        if brk != "sh3d" { b.ccx(q1, d1, d2); }
        if n0 { b.x(q0); }
        if n1 { b.x(q1); }
        if n2 { b.x(q2); }
    }
    fn xor_ret_short2(&mut self, b: &mut B, j: usize, target: QubitId) {
        let o = self.goto_impl(b, j, true);
        let (q1, n1) = self.lit(1, j);
        let (q0, n0) = self.lit(0, j);
        let d = borrowed().into_iter().find(|&q| q != o && q != q1 && q != q0 && q != target && !self.pre.contains(&q))
            .expect("R10_SH2: a borrowed lane");
        if n1 { b.x(q1); }
        if n0 { b.x(q0); }
        // target ^= q0 d; d ^= o q1; target ^= q0 d; d ^= o q1  =>  target ^= q0 o q1, d restored
        b.ccx(q0, d, target);
        b.ccx(o, q1, d);
        b.ccx(q0, d, target);
        b.ccx(o, q1, d);
        if n0 { b.x(q0); }
        if n1 { b.x(q1); }
    }
    fn xor_ret_short(&mut self, b: &mut B, j: usize, target: QubitId) {
        let o = self.goto_impl(b, j, true);
        let (q0, neg) = self.lit(0, j);
        if neg { b.x(q0); }
        b.ccx(o, q0, target);
        if neg { b.x(q0); }
    }
    fn lit(&self, k: usize, j: usize) -> (QubitId, bool) {
        (self.v[k], (j >> k) & 1 == 0)
    }
    fn comp(&self, b: &mut B, i: usize, j: usize, undo: bool) {
        let n = self.n();
        let (q2, neg2) = self.lit(n - 2 - i, j);
        let (q1, neg1) = if i == 0 { self.lit(n - 1, j) } else { (self.pre[i - 1], false) };
        if neg1 {
            b.x(q1);
        }
        if neg2 {
            b.x(q2);
        }
        if undo { b.and_u(q1, q2, self.pre[i]) } else { b.and_c(q1, q2, self.pre[i]) }
        if neg2 {
            b.x(q2);
        }
        if neg1 {
            b.x(q1);
        }
    }
    /// prefixes live for j; returns the qubit holding [v == j]
    fn goto(&mut self, b: &mut B, j: usize) -> QubitId {
        assert_eq!(self.pre.len(), self.n() - 1, "goto needs a retained prefix");
        self.goto_impl(b, j, true)
    }
    /// Toggle a target by the exact equality without retaining the final
    /// prefix. The n-2 prefix lanes are zero again after each toggle.
    fn xor_into(&self, b: &mut B, j: usize, target: QubitId) {
        let n = self.n();
        assert!(n >= 3 && self.pre.len() == n - 2);
        b.begin();
        for i in 0..n - 2 {
            let (lhs, n1) = if i == 0 { self.lit(n - 1, j) } else { (self.pre[i - 1], false) };
            let (rhs, n2) = self.lit(n - 2 - i, j);
            if n1 { b.x(lhs); }
            if n2 { b.x(rhs); }
            b.and_c(lhs, rhs, self.pre[i]);
            if n2 { b.x(rhs); }
            if n1 { b.x(lhs); }
        }
        let r = b.end();
        b.play(&r, false);
        let (last, neg) = self.lit(0, j);
        if neg { b.x(last); }
        b.ccx(self.pre[n - 3], last, target);
        if neg { b.x(last); }
        b.play(&r, true);
    }
    fn goto_impl(&mut self, b: &mut B, j: usize, fast: bool) -> QubitId {
        let n = self.n();
        let levels = self.pre.len();
        let keep = match self.cur {
            None => 0,
            Some(c) => {
                let mut kp = 0;
                while kp < levels && ((c ^ j) >> (n - 2 - kp)) == 0 {
                    kp += 1;
                }
                kp
            }
        };
        if fast {
            if let Some(c) = self.cur {
                if keep < levels && ((c ^ j) >> (n - 1)) == 0 {
                    // At the first changed bit, the parent equality is the
                    // same for c and j, while that bit's literal flips.
                    // Toggle its prefix with CNOT, then rebuild only below it.
                    for i in ((keep + 1)..levels).rev() {
                        self.comp(b, i, c, true);
                    }
                    let (parent, negative) = if keep == 0 {
                        self.lit(n - 1, j)
                    } else {
                        (self.pre[keep - 1], false)
                    };
                    if negative { b.x(parent); }
                    b.cx(parent, self.pre[keep]);
                    if negative { b.x(parent); }
                    for i in (keep + 1)..levels {
                        self.comp(b, i, j, false);
                    }
                    self.cur = Some(j);
                    return self.pre[levels - 1];
                }
            }
        }
        if let Some(c) = self.cur {
            for i in (keep..levels).rev() {
                self.comp(b, i, c, true);
            }
        }
        for i in keep..levels {
            self.comp(b, i, j, false);
        }
        self.cur = Some(j);
        self.pre[levels - 1]
    }
    fn clear(&mut self, b: &mut B) {
        if self.pre.len() == self.n() - 2 && !self.short() {
            assert!(self.cur.is_none());
            return;
        }
        if let Some(c) = self.cur {
            for i in (0..self.pre.len()).rev() {
                self.comp(b, i, c, true);
            }
        }
        self.cur = None;
    }
}

/// t ^= [v >= k] for a classical k (v little-endian, n bits), using `chain` ancillas (len >= n). All ANDs are
/// measurement-uncomputed, so the cost is <= n - 1 Toffoli.
pub fn ge_const(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId]) {
    let n = v.len();
    if k <= 0 {
        b.x(t);
        return;
    }
    if k >= (1isize << n) {
        return;
    }
    let kk = k as usize;
    // v >= k  <=>  carry out of v + (2^n - k).  c_0 = 0; addend bits a_i = bit i of (2^n - k).
    // carry: c_{i+1} = a_i ? (v_i | c_i) : (v_i & c_i). Track c as Const(bool) or Q(qubit, negated).
    #[derive(Clone, Copy)]
    enum C {
        K(bool),
        Q(QubitId, bool),
    }
    let addend = (1usize << n) - kk;
    b.begin();
    let mut c = C::K(false);
    let mut used = 0usize;
    for i in 0..n {
        let a = (addend >> i) & 1 == 1;
        let vi = C::Q(v[i], false);
        c = match (a, c) {
            (true, C::K(true)) => C::K(true),
            (true, C::K(false)) => vi,
            (false, C::K(true)) => vi,
            (false, C::K(false)) => C::K(false),
            (_, C::Q(q, ng)) => {
                // AND: v_i & c ; OR: !( !v_i & !c )
                let out = chain[used];
                used += 1;
                let (nv, nc) = if a { (true, !ng) } else { (false, ng) };
                if nv {
                    b.x(v[i]);
                }
                if nc {
                    b.x(q);
                }
                b.and_c(v[i], q, out);
                if nc {
                    b.x(q);
                }
                if nv {
                    b.x(v[i]);
                }
                C::Q(out, a) // OR result is the negation of the AND of negations
            }
        };
    }
    let rec = b.end();
    b.play(&rec, false);
    match c {
        C::K(true) => b.x(t),
        C::K(false) => {}
        C::Q(q, ng) => {
            b.cx(q, t);
            if ng {
                b.x(t);
            }
        }
    }
    b.play(&rec, true);
}

/// The phase (-1)^[v >= k] (ge_const with a phase in place of the XOR), for a measured erase.
pub fn ge_const_phase(b: &mut B, v: &[QubitId], k: isize, chain: &[QubitId]) {
    let n = v.len();
    if k <= 0 {
        neg_one(b);
        return;
    }
    if k >= (1isize << n) {
        return;
    }
    let kk = k as usize;
    // v >= k  <=>  carry out of v + (2^n - k).  c_0 = 0; addend bits a_i = bit i of (2^n - k).
    // carry: c_{i+1} = a_i ? (v_i | c_i) : (v_i & c_i). Track c as Const(bool) or Q(qubit, negated).
    #[derive(Clone, Copy)]
    enum C {
        K(bool),
        Q(QubitId, bool),
    }
    let addend = (1usize << n) - kk;
    b.begin();
    let mut c = C::K(false);
    let mut used = 0usize;
    for i in 0..n {
        let a = (addend >> i) & 1 == 1;
        let vi = C::Q(v[i], false);
        c = match (a, c) {
            (true, C::K(true)) => C::K(true),
            (true, C::K(false)) => vi,
            (false, C::K(true)) => vi,
            (false, C::K(false)) => C::K(false),
            (_, C::Q(q, ng)) => {
                // AND: v_i & c ; OR: !( !v_i & !c )
                let out = chain[used];
                used += 1;
                let (nv, nc) = if a { (true, !ng) } else { (false, ng) };
                if nv {
                    b.x(v[i]);
                }
                if nc {
                    b.x(q);
                }
                b.and_c(v[i], q, out);
                if nc {
                    b.x(q);
                }
                if nv {
                    b.x(v[i]);
                }
                C::Q(out, a) // OR result is the negation of the AND of negations
            }
        };
    }
    let rec = b.end();
    b.play(&rec, false);
    match c {
        C::K(true) => neg_one(b),
        C::K(false) => {}
        C::Q(q, ng) => {
            if ng {
                b.x(q);
            }
            b.z(q);
            if ng {
                b.x(q);
            }
        }
    }
    b.play(&rec, true);
}

/// R6-ROOM799 (R6_GEC): ge_const / ge_const_phase whose last carry step goes straight to the target (a Toffoli onto
/// t, or a CZ-form phase), so the chain needs one lane fewer: `ge_const_lanes(n, k)` lanes. Same Toffoli count as
/// ge_const (the last AND becomes one CCX); the phase form saves the last AND's Toffoli. Exact.
pub fn ge_const_lanes(n: usize, k: isize) -> usize {
    if k <= 0 || k >= (1isize << n) { return 0; }
    let addend = (1usize << n) - k as usize;
    let (mut q, mut used, mut last) = (false, 0usize, false);
    let mut kc = false;
    for i in 0..n {
        let a = (addend >> i) & 1 == 1;
        last = false;
        if q { used += 1; last = true; } else if a != kc { q = true; } // a=1,K(false) -> v_i ; a=0,K(true) -> v_i
        else if a { kc = true; }
    }
    if last { used - 1 } else { used }
}
fn ge_lean(b: &mut B, v: &[QubitId], k: isize, chain: &[QubitId], fin: &mut dyn FnMut(&mut B, Option<(QubitId, bool, QubitId, bool, bool)>, Option<(QubitId, bool)>, bool)) {
    let n = v.len();
    let addend = (1usize << n) - k as usize;
    #[derive(Clone, Copy)]
    enum C { K(bool), Q(QubitId, bool) }
    b.begin();
    let mut c = C::K(false);
    let mut used = 0usize;
    let mut tail = None;
    for i in 0..n {
        let a = (addend >> i) & 1 == 1;
        let vi = C::Q(v[i], false);
        c = match (a, c) {
            (true, C::K(true)) => C::K(true),
            (true, C::K(false)) => vi,
            (false, C::K(true)) => vi,
            (false, C::K(false)) => C::K(false),
            (_, C::Q(q, ng)) => {
                let (nv, nc) = if a { (true, !ng) } else { (false, ng) };
                if i == n - 1 { tail = Some((v[i], nv, q, nc, a)); break; }
                let out = chain[used];
                used += 1;
                if nv { b.x(v[i]); }
                if nc { b.x(q); }
                b.and_c(v[i], q, out);
                if nc { b.x(q); }
                if nv { b.x(v[i]); }
                C::Q(out, a)
            }
        };
    }
    let rec = b.end();
    b.play(&rec, false);
    match (tail, c) {
        (Some(_), _) => fin(b, tail, None, false),
        (None, C::K(kb)) => fin(b, None, None, kb),
        (None, C::Q(q, ng)) => fin(b, None, Some((q, ng)), false),
    }
    b.play(&rec, true);
}
/// t ^= [v >= k] on a chain of ge_const_lanes(v.len(), k) clean lanes.
pub fn ge_const_lean(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId]) {
    if k <= 0 { b.x(t); return; }
    if k >= (1isize << v.len()) { return; }
    ge_lean(b, v, k, chain, &mut |b, tail, q, kb| {
        if let Some((vi, nv, q, nc, neg)) = tail {
            // t ^= (vi^nv) & (q^nc), negated when the step is an OR
            if nv { b.x(vi); }
            if nc { b.x(q); }
            b.ccx(vi, q, t);
            if nc { b.x(q); }
            if nv { b.x(vi); }
            if neg { b.x(t); }
        } else if let Some((q, ng)) = q {
            b.cx(q, t);
            if ng { b.x(t); }
        } else if kb { b.x(t); }
    });
}
/// The phase (-1)^[v >= k] on a chain of ge_const_lanes(v.len(), k) clean lanes; the last step is Toffoli-free.
pub fn ge_const_phase_lean(b: &mut B, v: &[QubitId], k: isize, chain: &[QubitId]) {
    if k <= 0 { neg_one(b); return; }
    if k >= (1isize << v.len()) { return; }
    ge_lean(b, v, k, chain, &mut |b, tail, q, kb| {
        if let Some((vi, nv, q, nc, neg)) = tail {
            // AND step: (-1)^(l1 l2) = CZ on the literals. OR step: value = !(l1 & l2) with l = negated literals, i.e.
            // (-1)^(x | y) for x = !l1, y = !l2: Z(x) Z(y) CZ(x, y)
            let (lv, lq) = if neg { (!nv, !nc) } else { (nv, nc) };
            if lv { b.x(vi); }
            if lq { b.x(q); }
            b.cz(vi, q);
            if neg { b.z(vi); b.z(q); }
            if lq { b.x(q); }
            if lv { b.x(vi); }
        } else if let Some((q, ng)) = q {
            if ng { b.x(q); }
            b.z(q);
            if ng { b.x(q); }
        } else if kb { neg_one(b); }
    });
}

/// A phase of -1 on every shot that reaches it (through a |0> lane flipped to |1>).
fn neg_one(b: &mut B) {
    let a = b.alloc();
    b.x(a);
    b.z(a);
    b.x(a);
    b.free(a);
}

thread_local! {
    /// Lanes in an unknown state that comparators may borrow when a pass carries no clean chain (set by greedyfrog
    /// for its slots; froghop passes always carry a chain).
    static BORROWED: std::cell::RefCell<Vec<QubitId>> = std::cell::RefCell::new(vec![]);
}

/// P2-REBASE: the current borrowed lanes.
pub fn borrowed() -> Vec<QubitId> {
    BORROWED.with(|v| v.borrow().clone())
}
/// Set the borrowed lanes for passes whose scratch has an empty `chain`.
pub fn set_borrowed(lanes: &[QubitId]) {
    BORROWED.with(|v| *v.borrow_mut() = lanes.to_vec());
}

/// t ^= [v >= k] for a classical k with borrowed lanes in any state (restored): the cubes "v agrees with k above bit i,
/// v_i = 1 where k_i = 0" and "v == k" are disjoint, so their ANDs add up to the comparison.
pub fn ge_const_dirty(b: &mut B, v: &[QubitId], k: isize, t: QubitId, dirty: &[QubitId]) {
    ge_const_dirty_gated(b, v, k, t, &[], dirty);
}

/// t ^= AND(gate literals) & [v >= k], the gate literals joining every cube of `ge_const_dirty`.
pub fn ge_const_dirty_gated(b: &mut B, v: &[QubitId], k: isize, t: QubitId, gate: &[(QubitId, bool)], dirty: &[QubitId]) {
    let n = v.len();
    if k >= (1isize << n) {
        return;
    }
    if k <= 0 {
        if gate.is_empty() {
            b.x(t);
        } else {
            super::arith::and_dirty(b, gate, t, dirty);
        }
        return;
    }
    let kk = k as usize;
    let eq = |j: usize| (v[j], (kk >> j) & 1 == 0);
    for i in (0..n).rev() {
        if (kk >> i) & 1 == 0 {
            let mut lits: Vec<(QubitId, bool)> = gate.to_vec();
            lits.extend((i + 1..n).map(eq));
            lits.push((v[i], false));
            super::arith::and_dirty(b, &lits, t, dirty);
        }
    }
    let mut lits: Vec<(QubitId, bool)> = gate.to_vec();
    lits.extend((0..n).map(eq));
    super::arith::and_dirty(b, &lits, t, dirty);
}

/// t ^= [v in [lo, hi]] (inclusive interval, classical bounds)
fn in_range(b: &mut B, v: &[QubitId], lo: isize, hi: isize, t: QubitId, chain: &[QubitId]) {
    if chain.is_empty() {
        let d = BORROWED.with(|v| v.borrow().clone());
        ge_const_dirty(b, v, lo, t, &d);
        ge_const_dirty(b, v, hi + 1, t, &d);
        return;
    }
    ge_const(b, v, lo, t, chain);
    ge_const(b, v, hi + 1, t, chain);
}

/// Ladder pass description.
pub struct Lad<'a> {
    pub t: &'a [QubitId],
    pub s: &'a [QubitId],
    pub c0: QubitId,
    pub srcs: &'a [Src],
    /// value of f before lane 0 (same for every shot)
    pub f0: bool,
    pub cmpl: bool,
    pub sc: &'a Mscr,
    /// clean qubits (|0> before and after a pass pair): the first g.len() ordinary lanes keep their carry there as
    /// a logical AND (uncomputed by measurement on the return pass) instead of in the source lane
    pub g: &'a [QubitId],
}

fn masked(ld: &Lad, l: usize) -> bool {
    ld.srcs.iter().any(|s| l >= s.lo && l < s.hi)
}

/// The pi-parity source marks lane zero masked even when pi is known odd.
/// No cell acts there: f starts at zero, c0 is zero, and no other source covers it.
fn skip_zero_pi_lane(ld: &Lad, l: usize) -> bool {
    l == 0 && !ld.f0
        && ld.srcs.iter().any(|s| s.d == 0 && s.a == 1 && s.lo == 0 && s.hi > 0)
        && ld.srcs.iter().all(|s| s.lo > 0 || (s.d == 0 && s.a == 1))
}

/// Pair two pi-only masked lanes whose one-hot source toggles f at the first lane.
fn pi_pair(ld: &Lad, l: usize) -> bool {
    if ld.f0 || ld.srcs.is_empty() || ld.sc.chain.len() < 2 { return false; }
    let pi = &ld.srcs[0];
    if pi.d != 0 || pi.lo != 0 || pi.a < 0 || pi.a > 1 { return false; }
    let next = ld.srcs.iter().skip(1).map(|s| s.lo).min().unwrap_or(ld.t.len());
    l % 2 == pi.a as usize && l + 1 < pi.hi.min(next).min(ld.t.len())
}

fn masked_pair_up(b: &mut B, ld: &Lad, l: usize, x: QubitId) {
    let (ta, sa, tb, sb) = (ld.t[l], ld.s[l], ld.t[l + 1], ld.s[l + 1]);
    let (a, c) = (ld.sc.t, ld.sc.chain[0]);
    b.cx(x, ta); b.cx(x, sa); b.and_c(ta, sa, a);
    b.cx(x, tb); b.cx(a, tb); b.cx(x, sb); b.cx(a, sb);
    b.and_c(tb, sb, c); b.cx(c, a); b.ccx(ld.sc.f, a, x);
    b.cx(c, a); b.and_u(tb, sb, c); b.and_u(ta, sa, a);
}

fn masked_pair_down(b: &mut B, ld: &Lad, l: usize, x: QubitId, g: QubitId) {
    let (ta, sa, tb, sb) = (ld.t[l], ld.s[l], ld.t[l + 1], ld.s[l + 1]);
    let (a, c, fg) = (ld.sc.t, ld.sc.chain[0], ld.sc.chain[1]);
    b.and_c(ta, sa, a); b.and_c(tb, sb, c); b.cx(c, a);
    b.ccx(ld.sc.f, a, x); b.cx(c, a); b.and_u(tb, sb, c);
    b.and_c(ld.sc.f, g, fg); b.ccx(fg, sb, tb);
    b.cx(x, tb); b.cx(a, tb); b.cx(x, sb); b.cx(a, sb);
    b.and_u(ta, sa, a); b.ccx(fg, sa, ta);
    b.cx(x, ta); b.cx(x, sa); b.and_u(ld.sc.f, g, fg);
}

/// Pool index of ordinary lane l if it takes a logical-AND carry.
fn gidx(ld: &Lad, l: usize) -> Option<usize> {
    if masked(ld, l) || ld.g.is_empty() {
        return None;
    }
    let k = (0..l).filter(|&m| !masked(ld, m)).count();
    (k < ld.g.len()).then_some(k)
}

/// Wire holding c_l (carry into ladder lane l).
fn carry_wire(ld: &Lad, l: usize) -> QubitId {
    let mut w = ld.c0;
    let mut k = 0;
    for m in 0..l {
        if !masked(ld, m) {
            w = if k < ld.g.len() { ld.g[k] } else { ld.s[m] };
            k += 1;
        }
    }
    w
}

/// Wire holding the carry out of the last lane after `mup`.
pub fn top_carry(ld: &Lad) -> QubitId {
    carry_wire(ld, ld.t.len())
}

/// f ^= f0 ^ sum_s [v_s in span_s]  (the value f has after the last lane)
fn f_end(b: &mut B, ld: &Lad) {
    if ld.f0 {
        b.x(ld.sc.f);
    }
    for s in ld.srcs {
        let (lo, hi) = s.span();
        in_range(b, &s.v, lo, hi, ld.sc.f, &ld.sc.chain);
    }
}

/// Per-lane source actions. `pre`: before lane l's cell (up pass) / after it (down pass): early sources toggle f,
/// late sources flip T[l]. Otherwise (`pre` false): after the cell (up) / before it (down): late sources toggle f.
fn toggles(b: &mut B, ld: &Lad, decs: &mut [Dec], l: usize, pre: bool, up: bool) {
    for (si, s) in ld.srcs.iter().enumerate() {
        if l >= s.lo && l < s.hi {
            if !pre && !s.late {
                continue;
            }
            let j = s.tv(l);
            if j >= 0 && (j as usize) < (1usize << s.v.len()) {
                let target = if s.late && pre { ld.t[l] } else { ld.sc.f };
                if j > TVMAX.with(|c| c.get()) {
                    // R11_LA5: no write; a retained prefix (full, RSHORT or RSHORT2) still moves to j
                    if decs[si].short4t() || decs[si].short3t() || decs[si].short3() || decs[si].short2t() || decs[si].short2()
                        || decs[si].short() || decs[si].pre.len() + 1 == decs[si].n() {
                        decs[si].goto_impl(b, j as usize, true);
                    }
                    continue;
                }
                if pre && t8_enabled() && t8_leaf(b, ld, &mut decs[si], s, l, j as usize, up, target) { continue; }
                if pre && t4_enabled() && tile_leaf(b, ld, &mut decs[si], s, l, j as usize, up, target) { continue; }
                if decs[si].short4t() && R14L.with(|c| c.get()) {
                    decs[si].xor_ret_tmp_cc(b, j as usize, target, ld.sc.t);
                } else if decs[si].short5t() {
                    decs[si].xor_t0(b, j as usize, target, ld.sc.t);
                } else if decs[si].short2t() {
                    decs[si].xor_ret_tmp(b, j as usize, target, ld.sc.t, 1);
                } else if decs[si].short4t() {
                    decs[si].xor_ret_tmp(b, j as usize, target, ld.sc.t, 3);
                } else if decs[si].short3t() {
                    decs[si].xor_ret_tmp(b, j as usize, target, ld.sc.t, 2);
                } else if decs[si].short3() {
                    decs[si].xor_ret_short3(b, j as usize, target);
                } else if decs[si].short2() {
                    decs[si].xor_ret_short2(b, j as usize, target);
                } else if decs[si].short() {
                    decs[si].xor_ret_short(b, j as usize, target);
                } else if decs[si].pre.len() == decs[si].n() - 2 {
                    decs[si].xor_into(b, j as usize, target);
                } else {
                    let o = decs[si].goto(b, j as usize);
                    b.cx(o, target);
                }
            }
        }
    }
}

fn clear_ended(b: &mut B, ld: &Lad, decs: &mut [Dec], l: usize, up: bool) {
    for (si, s) in ld.srcs.iter().enumerate() {
        let end = if up { l + 1 == s.hi } else { l == s.lo };
        if end {
            decs[si].clear(b);
        }
    }
}

/// Masked majority ladder (up pass). With `cmpl` the target is complemented first (subtract/compare form).
pub fn mup(b: &mut B, ld: &Lad) -> Vec<G> {
    mup_impl(b, ld, false, None, false, None, &[])
}

/// Paired ladder form: leave the end mask and final decoder prefix live across
/// a middle region that does not read either scratch object.
pub fn mup_mid(b: &mut B, ld: &Lad) -> Vec<G> {
    mup_impl(b, ld, true, None, false, None, &[])
}

/// In a paired inverse, the ordinary MAJ writes the exact carry measured by
/// the forward rolling chain. Put the phase repair on that regenerated wire.
pub fn mup_mid_repair(b: &mut B, ld: &Lad, carry_receipts: &[BitId]) -> Vec<G> {
    mup_impl(b, ld, true, None, false, Some(carry_receipts), &[])
}

pub fn mup_mid_from(b: &mut B, ld: &Lad, start: usize) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, Some(start), false, None, &[])
}

pub fn mup_mid_from_repair(b: &mut B, ld: &Lad, start: usize, carry_receipts: &[BitId]) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, Some(start), false, Some(carry_receipts), &[])
}

pub fn mup_mid_spare_masked_from(b: &mut B, ld: &Lad, start: Option<usize>) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, start, true, None, &[])
}

/// K1 banked masked carries (S3-001, after SnehalRaj 29f13bac): the paired form whose masked cells keep f & s' on
/// `bank` (one clean lane per masked cell, in lane order; a short bank covers the lowest cells) until the return
/// pass, which then spends one Toffoli per banked cell instead of two. The bank is |0> again after the return pass
/// (`mdown_mid_bank`, or the inverted recording).
pub fn mup_mid_bank(b: &mut B, ld: &Lad, bank: &[QubitId]) -> Vec<G> {
    mup_impl(b, ld, true, None, false, None, bank)
}

pub fn mdown_mid_bank(b: &mut B, ld: &Lad, g: Option<QubitId>, bank: &[QubitId]) -> Vec<G> {
    mdown_impl(b, ld, g, g, true, None, bank)
}

/// `mdown_mid2` with a K1 bank.
pub fn mdown_mid2_bank(b: &mut B, ld: &Lad, g_masked: Option<QubitId>, g_ord: Option<QubitId>, bank: &[QubitId]) -> Vec<G> {
    mdown_impl(b, ld, g_ord, g_masked, true, None, bank)
}

/// K1: bank index of masked lane l (masked cells before l), if it has a bank lane.
fn fs_idx(ld: &Lad, l: usize, bank: &[QubitId]) -> Option<usize> {
    if bank.is_empty() { return None; }
    let k = (0..l).filter(|&m| masked(ld, m) && !skip_zero_pi_lane(ld, m)).count();
    (k < bank.len()).then_some(k)
}

pub fn clear_onehot_dec(b: &mut B, v: &[QubitId], pre: &[QubitId], start: usize) {
    let mut dec = Dec { v, pre, cur: Some(start) };
    dec.clear(b);
}

/// TERMINAL-CARRY SKIP (B-CRUMBS): mid passes whose caller never reads the top carry (a write follows and the carry out
/// of the last lane is discarded: division rows, cofactor chains). The last lane's carry cell is not built on the way up
/// and its down cell only writes the sum t ^= g & f & (s ^ c) (`mdown_*_nc`), so its carry Toffoli(s) go.
pub fn mup_mid_nc(b: &mut B, ld: &Lad) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, true, &[], None)
}
pub fn mdown_mid_nc(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    assert!(g.is_some());
    mdown_impl_nc(b, ld, g, g, true, None, true, &[], None)
}
/// TERM-NC with a K1 bank (B-PORT3 K2 on the cofactor passes): the top lane's sum-only cell uses no bank lane.
pub fn mup_mid_nc_bank(b: &mut B, ld: &Lad, bank: &[QubitId]) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, true, bank, None)
}
pub fn mdown_mid_nc_bank(b: &mut B, ld: &Lad, g: Option<QubitId>, bank: &[QubitId]) -> Vec<G> {
    assert!(g.is_some());
    mdown_impl_nc(b, ld, g, g, true, None, true, bank, None)
}
pub fn mdown_mid2_nc_bank(b: &mut B, ld: &Lad, g_masked: Option<QubitId>, g_ord: Option<QubitId>, bank: &[QubitId]) -> Vec<G> {
    assert!(g_ord.is_some());
    mdown_impl_nc(b, ld, g_ord, g_masked, true, None, true, bank, None)
}
pub fn mdown_mid2_nc(b: &mut B, ld: &Lad, g_masked: Option<QubitId>, g_ord: Option<QubitId>) -> Vec<G> {
    assert!(g_ord.is_some());
    mdown_impl_nc(b, ld, g_ord, g_masked, true, None, true, &[], None)
}

/// ROLL-ROWS: the mid down pass of a ladder whose forward twin was rolled (`roll_fwd`) and which is played INVERTED as
/// that twin's inverse: z_if on the carry wire of lane l + 1 right before lane l's cell, i.e. right after the inverted
/// cell regenerates c_(l+1).
pub fn mdown_mid_roll(b: &mut B, ld: &Lad, g: Option<QubitId>, rec: &RollRec) -> Vec<G> {
    mdown_impl_nc(b, ld, g, g, true, None, false, &[], Some(rec))
}
/// `mdown_mid_roll` with the TERMINAL-CARRY SKIP.
pub fn mdown_mid_nc_roll(b: &mut B, ld: &Lad, g: Option<QubitId>, rec: &RollRec) -> Vec<G> {
    assert!(g.is_some());
    mdown_impl_nc(b, ld, g, g, true, None, true, &[], Some(rec))
}

/// TC-PHASE (MICRO-WALK M-011): the phase (-1)^(carry out of the top lane) of a mid compare, with no top carry cell.
/// The up pass runs without the last lane's cell (`mup_impl_nc`); with c the carry into that lane and t, s its lanes,
/// carry out = c ^ (t ^ c)(s ^ c) (ordinary) or c ^ f (t ^ c)(s ^ c) (masked), so the phase is Z(c) CZ(t ^ c, s ^ c)
/// or Z(c) CCZ(f, t ^ c, s ^ c) (one AND on the mask's temp lane). Returns false (nothing emitted) where the last
/// lane is in a pi pair or the zero pi lane; the caller then runs the ordinary pass.
pub fn mid_phase_top(b: &mut B, ld: &Lad, bank: &[QubitId], brk: bool) -> bool {
    let l_n = ld.t.len();
    if !nc_top(ld, true) {
        return false;
    }
    let l = l_n - 1;
    if masked(ld, l) && (ld.sc.t == ld.sc.f || ld.t.contains(&ld.sc.t) || ld.s.contains(&ld.sc.t)) {
        return false;
    }
    // a late source at the top lane toggles f after the cell: not handled
    if ld.srcs.iter().any(|s| s.late && l >= s.lo && l < s.hi) {
        return false;
    }
    // K1 bank (B-PORT3): the masked cells below the top keep f & s' on the bank; replaying the recording inverted
    // uncomputes them (1 Toffoli per banked cell, as `mdown_mid_bank`). The top lane takes no bank lane.
    if bank.contains(&ld.sc.t) {
        return false;
    }
    let ru = mup_impl_nc(b, ld, true, None, false, None, true, bank, None);
    b.play(&ru, false);
    let x = carry_wire(ld, l);
    let (t, s) = (ld.t[l], ld.s[l]);
    b.cx(x, t);
    b.cx(x, s);
    if !brk {
        b.z(x);
    }
    if masked(ld, l) {
        b.and_c(t, s, ld.sc.t);
        b.cz(ld.sc.f, ld.sc.t);
        b.and_u(t, s, ld.sc.t);
    } else {
        b.cz(t, s);
    }
    b.cx(x, s);
    b.cx(x, t);
    b.play(&ru, true);
    true
}

/// Whether the TERMINAL-CARRY SKIP applies to the last lane (handled alone, not in a pi pair or the zero pi lane).
fn nc_top(ld: &Lad, nc: bool) -> bool {
    let l_n = ld.t.len();
    nc && l_n >= 2 && !pi_pair(ld, l_n - 2) && !skip_zero_pi_lane(ld, l_n - 1)
}

fn mup_impl(b: &mut B, ld: &Lad, mid: bool, start: Option<usize>, bank_masked: bool,
            repair: Option<&[BitId]>, bank: &[QubitId]) -> Vec<G> {
    mup_impl_nc(b, ld, mid, start, bank_masked, repair, false, bank, None)
}

/// ROLL-FWD inverse side: the mid up pass with the rolled forward's phase repairs (`roll_fwd`): z_if on every carry
/// wire the up pass regenerates (Cuccaro source lane, pooled AND lane, masked running wire, each right after its cell)
/// and on the running mask's end value.
pub fn mup_mid_roll(b: &mut B, ld: &Lad, rec: &RollRec) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, false, &[], Some(rec))
}
/// `mup_mid_roll` with the TERMINAL-CARRY SKIP (`mup_mid_nc`).
pub fn mup_mid_nc_roll(b: &mut B, ld: &Lad, rec: &RollRec) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, true, &[], Some(rec))
}

/// K2 bank x ROLL-FWD (INTEGRATOR): the inverse passes' up pass with both the K1 bank on the masked cells and the
/// rolled forward's phase repairs (a banked cell regenerates the same carry on the same running wire, so the repair
/// sits where it does without the bank).
pub fn mup_mid_bank_roll(b: &mut B, ld: &Lad, bank: &[QubitId], roll: Option<&RollRec>) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, false, bank, roll)
}
pub fn mup_mid_nc_bank_roll(b: &mut B, ld: &Lad, bank: &[QubitId], roll: Option<&RollRec>) -> Vec<G> {
    mup_impl_nc(b, ld, true, None, false, None, true, bank, roll)
}

/// Negative controls for the ROLL-FWD gate tests only (ROLL_BREAK=k): 1 drops the repair of the middle ordinary lane's
/// carry, 2 the middle masked lane's, 3 the running mask's end value, 4 the top carry's; 5 (ROLL-ROWS) the middle lane's
/// repair in the inverted rows pass.
pub(crate) fn roll_break(k: u32) -> bool {
    cfg!(test) && std::env::var("ROLL_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

fn mup_impl_nc(b: &mut B, ld: &Lad, mid: bool, start: Option<usize>, bank_masked: bool,
            repair: Option<&[BitId]>, nc: bool, bank: &[QubitId], roll: Option<&RollRec>) -> Vec<G> {
    let l_n = ld.t.len();
    let nc = nc_top(ld, nc) && !bank_masked && repair.is_none();
    assert!(bank.is_empty() || (!bank_masked && ld.srcs.iter().all(|s| s.d != 0 && !s.late)),
            "K1 bank: no pi pairs, late sources or masked carry bank");
    assert_eq!(ld.s.len(), l_n);
    if let Some(bits) = repair { assert!(bits.len() <= l_n); }
    b.begin();
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    let _tx = tile_extra(bank);
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: start }).collect();
    if ld.f0 {
        b.x(ld.sc.f);
    }
    let ordinary_total = if bank_masked { (0..l_n).filter(|&i| !masked(ld, i)).count() } else { 0 };
    let mut masked_seen = 0usize;
    let mut l = 0;
    while l < l_n {
        let x = carry_wire(ld, l);
        toggles(b, ld, &mut decs, l, true, true);
        let receipt = roll.and_then(|r| r.payload.get(l)).copied().flatten();
        if let Some(bit) = receipt {
            if !masked(ld, l) {
                b.z_if(ld.s[l], bit);
                b.z_if(x, bit);
            }
        }
        if pi_pair(ld, l) {
            assert!(receipt.is_none());
            masked_pair_up(b, ld, l, x);
            toggles(b, ld, &mut decs, l, false, true);
            clear_ended(b, ld, &mut decs, l, true);
            toggles(b, ld, &mut decs, l + 1, true, true);
            toggles(b, ld, &mut decs, l + 1, false, true);
            if !(mid && l + 2 == l_n) { clear_ended(b, ld, &mut decs, l + 1, true); }
            l += 2;
            continue;
        }
        if skip_zero_pi_lane(ld, l) {
            // Both the masked cell and its return are identity on this lane.
        } else if nc && l + 1 == l_n {
            // TERMINAL-CARRY SKIP: no carry out of the last lane
        } else if masked(ld, l) {
            let bank_idx = ordinary_total + masked_seen;
            masked_seen += 1;
            if bank_masked && bank_idx < ld.g.len() {
                let (t, s) = (ld.t[l], ld.s[l]);
                b.cx(x, t);
                b.cx(x, s);
                b.and_c(t, s, ld.g[bank_idx]);
                b.ccx(ld.sc.f, ld.g[bank_idx], x);
            } else if let Some(k) = fs_idx(ld, l, bank) {
                // K1: carry x ^= f & (t ^ x)(s ^ x) with f & s' kept on the bank lane for the return pass
                let (t, s) = (ld.t[l], ld.s[l]);
                b.cx(x, t);
                b.cx(x, s);
                b.and_c(ld.sc.f, s, bank[k]);
                if let Some(bit) = receipt { b.z_if(bank[k], bit); }
                // negative control for the gate tests only: P3_BREAK=1 takes the carry's t literal from s
                let tl = if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |v| v.trim() == "1") { s } else { t };
                b.ccx(bank[k], tl, x);
            } else if let Some(bit) = receipt {
                // Same carry cost as masked_up_cell, with the spent forward payload on the temp.
                assert!(!notemp() && !bank_masked);
                let (t, s, p) = (ld.t[l], ld.s[l], ld.sc.t);
                b.cx(x, t);
                b.cx(x, s);
                b.and_c(ld.sc.f, s, p);
                b.z_if(p, bit);
                b.ccx(p, t, x);
                b.and_u(ld.sc.f, s, p);
            } else { masked_up_cell(b, ld, l, x); }
        } else if let Some(k) = gidx(ld, l) {
            // carry MAJ(x, t, s) = x ^ (t ^ x)(s ^ x) on a fresh qubit
            let gq = ld.g[k];
            b.cx(x, ld.t[l]);
            b.cx(x, ld.s[l]);
            b.and_c(ld.t[l], ld.s[l], gq);
            b.cx(x, gq);
        } else {
            b.cx(ld.s[l], ld.t[l]);
            b.cx(ld.s[l], x);
            b.ccx(x, ld.t[l], ld.s[l]);
        }
        if let Some(bits) = repair {
            if l < bits.len() {
                assert!(!masked(ld, l) && gidx(ld, l).is_none(), "repair requires ordinary MAJ");
                b.z_if(ld.s[l], bits[l]);
            }
        }
        if let Some(r) = roll {
            if let Some(Some(bit)) = r.rc.get(l) {
                let m_n = (0..l_n).take_while(|&i| masked(ld, i)).count();
                let drop = (roll_break(1) && l == (m_n + l_n) / 2) || (roll_break(2) && l == m_n / 2)
                    || (roll_break(4) && l + 1 == l_n);
                if !drop { b.z_if(carry_wire(ld, l + 1), *bit); }
            }
        }
        toggles(b, ld, &mut decs, l, false, true);
        if !(mid && l + 1 == l_n) {
            clear_ended(b, ld, &mut decs, l, true);
        }
        l += 1;
    }
    if !mid { f_end(b, ld); }
    if let Some(fb) = roll.and_then(|r| r.fb) {
        if !roll_break(3) { b.z_if(ld.sc.f, fb); }
    }
    b.end()
}

/// Forward-ghost S5 ordinary prefix. Two clean lanes carry c_l and c_(l+1)
/// alternately. Each spent carry is measured after its last consumer. The
/// source lanes stay intact and the conditional sum write costs one T/lane.
/// If a masked suffix exists, the boundary carry is moved to the usual source
/// lane while ld.c0 temporarily holds that lane's original value.
pub fn s5_rolling_prefix(b: &mut B, ld: &Lad, gate: QubitId,
                         partner: QubitId, receipts: &[BitId]) {
    let ordinary = ld.srcs.iter().map(|s| s.lo).min().unwrap_or(ld.t.len());
    assert_eq!(ordinary, receipts.len());
    assert!(ordinary > 0 && ld.f0 && ld.cmpl && ld.g.is_empty());
    assert!(ld.srcs.iter().all(|s| s.lo == ordinary && s.hi == ld.t.len() && !s.late));
    let mut cur = ld.c0;
    let mut next = partner;
    for l in 0..ordinary {
        let (t, s) = (ld.t[l], ld.s[l]);
        // The forward path is mdown_mid^{-1} then mup_mid^{-1}: its gated
        // write comes before MAJ, so the carry uses the updated target.
        b.x(t);
        b.cx(s, cur);
        b.ccx(gate, cur, t);
        b.cx(s, cur);
        b.cx(cur, t);
        b.cx(cur, s);
        b.and_c(t, s, next);
        b.cx(cur, next);
        b.cx(cur, s);
        b.cx(cur, t);
        b.x(t);
        if l > 0 { b.hmr_to(cur, receipts[l - 1]); }
        std::mem::swap(&mut cur, &mut next);
    }
    if ordinary == ld.t.len() {
        b.hmr_to(cur, receipts[ordinary - 1]);
    } else {
        let boundary = ld.s[ordinary - 1];
        b.swap(cur, boundary);
        if cur != ld.c0 { b.swap(cur, ld.c0); }
    }
}

/// Finish the masked suffix after its down/up pair has restored the window.
pub fn s5_rolling_finish(b: &mut B, ld: &Lad, receipts: &[BitId]) {
    let ordinary = receipts.len();
    assert!(ordinary > 0 && ordinary < ld.t.len());
    let boundary = ld.s[ordinary - 1];
    b.hmr_to(boundary, receipts[ordinary - 1]);
    b.swap(boundary, ld.c0);
}

/// ROLL-FWD receipts of one rolled forward ladder: `rc[l]` = the X-measurement record of the carry formed at lane l
/// (c_(l+1)), None where nothing was measured; `fb` = the record of the running mask's end value.
#[derive(Clone, Debug, Default)]
pub struct RollRec {
    pub rc: Vec<Option<BitId>>,
    pub fb: Option<BitId>,
    // L8: spent f_l (s_l XOR c_l) on the inverse input.
    pub payload: Vec<Option<BitId>>,
}

/// L8: rolled forward value/cofactor ladder using only the parent's c0 and AND temp.
/// P=f(s^c). If P=1 then s^c=1, so the next carry on the written target is
/// c ^ P(t_written^c) = c ^ P(t_old^s^g^1). The inverse pays the measurement
/// phase on the same P before it changes the incoming carry.
pub fn l8_roll_fwd(b: &mut B, ld: &Lad, g_ord: QubitId, g_masked: QubitId,
                   nc: bool, top: Option<(QubitId, QubitId)>) -> RollRec {
    let n = ld.t.len();
    assert!(n > 0 && n == ld.s.len() && !ld.f0 && ld.g.is_empty());
    assert!(ld.srcs.len() == 1 && ld.srcs[0].lo == 0 && !ld.srcs[0].late && ld.srcs[0].d != 0);
    assert!(!notemp() && ld.c0 != ld.sc.t && ld.c0 != ld.sc.f && ld.sc.f != ld.sc.t);
    let nc = nc_top(ld, nc);
    assert!(!nc || top.is_none());
    if std::env::var("L8_ROLL_CENSUS").ok().as_deref() == Some("1") {
        eprintln!("L8ROLL kind={} n={} m={} nc={} masked_control={} ordinary_control={}",
                  if ld.cmpl { "cof" } else { "value" }, n, ld.srcs[0].hi, nc as u8,
                  (g_masked != ALWAYS) as u8, (g_ord != ALWAYS) as u8);
    }
    let (c, p, f) = (ld.c0, ld.sc.t, ld.sc.f);
    let mut txv = vec![g_ord, g_masked];
    if let Some((tg, tt)) = top { txv.extend([tg, tt]); }
    let _tx = tile_extra(&txv);
    let mut rec = RollRec { rc: vec![None; n], fb: None, payload: vec![None; n] };
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|src| Dec {
        v: &src.v, pre: &src.pre, cur: None
    }).collect();
    if ld.cmpl { for &t in ld.t { b.x(t); } }
    for l in 0..n {
        let (s, t) = (ld.s[l], ld.t[l]);
        let masked_cell = masked(ld, l);
        let g = if masked_cell { g_masked } else { g_ord };
        toggles(b, ld, &mut decs, l, true, true);
        let terminal = nc && l + 1 == n;
        // The terminal cell can use the ordinary, immediate AND uncompute.
        if terminal {
            b.cx(c, s);
            if masked_cell && g == ALWAYS { b.ccx(f, s, t); }
            else if masked_cell {
                b.and_c(f, s, p);
                b.ccx(g, p, t);
                b.and_u(f, s, p);
            } else if g == ALWAYS { b.cx(s, t); }
            else { b.ccx(g, s, t); }
            b.cx(c, s);
        } else {
            b.cx(c, s);
            if masked_cell { b.and_c(f, s, p); } else { b.cx(s, p); }
            b.cx(c, s);
            b.cx(s, t);
            if g != ALWAYS { b.cx(g, t); b.x(t); }
            b.ccx(p, t, c);
            if g != ALWAYS { b.x(t); b.cx(g, t); }
            b.cx(s, t);
            if g == ALWAYS { b.cx(p, t); } else { b.ccx(g, p, t); }
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(p, bit);
            rec.payload[l] = Some(bit);
        }
        toggles(b, ld, &mut decs, l, false, true);
        clear_ended(b, ld, &mut decs, l, true);
    }
    if let Some((g, target)) = top {
        if g == ALWAYS { b.cx(c, target); } else { b.ccx(g, c, target); }
    }
    let carry_bit = b.fresh_bits(1)[0];
    b.hmr_to(c, carry_bit);
    rec.rc[if nc { n - 2 } else { n - 1 }] = Some(carry_bit);
    if ld.cmpl { for &t in ld.t { b.x(t); } }
    for d in &mut decs { d.clear(b); }
    let mask_bit = b.fresh_bits(1)[0];
    b.hmr_to(f, mask_bit);
    rec.fb = Some(mask_bit);
    rec
}

/// ROLL-FWD (R-028; the froghop S5 rolling prefix generalised to masked-prefix ladders and masked cells): run a forward
/// ladder as the exact inverse of its matching inverse ladder `ld` (the I-ladder's own description: lanes, sources, c0,
/// cmpl; its pool `g` is not read) in ONE upward traversal. Per lane l, with c = c_l on `cur`: write first,
/// t ^= g f (s ^ c) (f = 1 on ordinary lanes; gates `g_ord` / `g_masked`, ALWAYS for none), then form the I-ladder's
/// next carry on the UPDATED target in a clean lane, c_(l+1) = c ^ f (s ^ c)(t' ^ c) (in the I-ladder's frame: t
/// complemented iff `ld.cmpl`), and X-measure the spent c_l into a receipt. The I-ladder's up pass regenerates every
/// c_(l+1) on an addressable wire and repays the phase there (`mup_mid_roll`); the running mask's end value is measured
/// and repaid the same way. Ordinary lane: 1 gated CCX + 1 AND (ALWAYS: 1 AND); masked cell: 2 AND + one decoder
/// traversal (the up+down pair: 2 AND + 2 CCX + two traversals).
/// `roll_masked` false (stage 1): the masked prefix runs its usual up pass in the forward's frame, the ordinary suffix
/// rolls from the prefix's carry out (held on c0, never measured), then the masked down pass writes.
/// `nc` (TERMINAL-CARRY SKIP, as the I-ladder's): the last lane only writes. `top` = Some((gate or ALWAYS, target)):
/// target ^= gate & c_L before c_L is measured. `lanes`: clean lanes, 1 (`roll_masked`) or 2.
pub fn roll_fwd(b: &mut B, ld: &Lad, g_ord: QubitId, g_masked: QubitId, roll_masked: bool, nc: bool,
                lanes: &[QubitId], top: Option<(QubitId, QubitId)>) -> RollRec {
    let l_n = ld.t.len();
    assert_eq!(ld.s.len(), l_n);
    assert!(l_n >= 1 && !ld.f0 && ld.srcs.len() <= 1 && (ld.srcs.len() == 1 || !roll_masked));
    assert!(ld.srcs.iter().all(|s| !s.late && s.d != 0 && s.lo == 0), "ROLL-FWD: one early non-pi source at lane 0");
    let m = (0..l_n).take_while(|&l| masked(ld, l)).count();
    assert!((m..l_n).all(|l| !masked(ld, l)), "ROLL-FWD: masked lanes must form a prefix");
    let nc = nc_top(ld, nc);
    assert!(!(nc && top.is_some()));
    assert_eq!(lanes.len(), if roll_masked { 1 } else { 2 });
    let mut rec = RollRec { rc: vec![None; l_n], ..RollRec::default() };
    let mut txv: Vec<QubitId> = lanes.to_vec();
    txv.extend([g_ord, g_masked]);
    if let Some((tg, tt)) = top { txv.extend([tg, tt]); }
    let _tx = tile_extra(&txv);
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: None }).collect();
    let start = if roll_masked { 0 } else { m };
    if !roll_masked {
        // stage 1: the masked prefix's up pass in the forward's frame (the complement of the I-ladder's)
        if !ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
        for l in 0..m {
            toggles(b, ld, &mut decs, l, true, true);
            masked_up_cell(b, ld, l, ld.c0);
            toggles(b, ld, &mut decs, l, false, true);
            if l + 1 < m { clear_ended(b, ld, &mut decs, l, true); }
        }
    }
    if ld.cmpl { for &q in &ld.t[start..] { b.x(q); } }
    // c_start lives on c0 (c_0 = 0, or the masked prefix's carry out): never measured here
    let mut cur = ld.c0;
    let mut held = true;
    let mut free: Vec<QubitId> = lanes.to_vec();
    let (f, tmp) = (ld.sc.f, ld.sc.t);
    for l in start..l_n {
        let (t, s) = (ld.t[l], ld.s[l]);
        let last_nc = nc && l + 1 == l_n;
        toggles(b, ld, &mut decs, l, true, true);
        let nxt = if last_nc { None } else { Some(free.pop().expect("ROLL-FWD lane")) };
        if masked(ld, l) {
            // tmp = f (s ^ c); t ^= g tmp; next = c ^ tmp (t' ^ c)
            b.cx(cur, s);
            b.and_c(f, s, tmp);
            b.cx(cur, s);
            if g_masked == ALWAYS { b.cx(tmp, t); } else { b.ccx(g_masked, tmp, t); }
            if let Some(n) = nxt {
                b.cx(cur, t);
                b.and_c(tmp, t, n);
                b.cx(cur, t);
                b.cx(cur, n);
            }
            b.cx(cur, s);
            b.and_u(f, s, tmp);
            b.cx(cur, s);
        } else {
            // t ^= g (s ^ c); next = c ^ (t' ^ c)(s ^ c)
            b.cx(cur, s);
            if g_ord == ALWAYS { b.cx(s, t); } else { b.ccx(g_ord, s, t); }
            if let Some(n) = nxt {
                b.cx(cur, t);
                b.and_c(t, s, n);
                b.cx(cur, t);
            }
            b.cx(cur, s);
            if let Some(n) = nxt { b.cx(cur, n); }
        }
        toggles(b, ld, &mut decs, l, false, true);
        if roll_masked || l + 1 != m { clear_ended(b, ld, &mut decs, l, true); }
        // c_l is spent (formed at lane l - 1)
        if !held {
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(cur, bit);
            rec.rc[l - 1] = Some(bit);
            free.push(cur);
        } else if roll_masked {
            free.push(cur); // c_0 = 0: clean
        }
        if let Some(n) = nxt { cur = n; held = false; }
    }
    if !nc {
        // cur = c_L
        if let Some((g, tgt)) = top {
            if g == ALWAYS { b.cx(cur, tgt); } else { b.ccx(g, cur, tgt); }
        }
        if !held {
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(cur, bit);
            rec.rc[l_n - 1] = Some(bit);
        }
    }
    if ld.cmpl { for &q in &ld.t[start..] { b.x(q); } }
    if roll_masked {
        for d in decs.iter_mut() { d.clear(b); }
        let bit = b.fresh_bits(1)[0];
        b.hmr_to(f, bit);
        rec.fb = Some(bit);
    } else {
        // stage 1: the masked prefix's down pass (writes), its carry out c_m back on c0
        for l in (0..m).rev() {
            toggles(b, ld, &mut decs, l, false, false);
            masked_down_cell(b, ld, l, ld.c0, Some(g_masked));
            toggles(b, ld, &mut decs, l, true, false);
            clear_ended(b, ld, &mut decs, l, false);
        }
        if !ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    }
    rec
}

/// Write gate meaning "always": `mdown(.., Some(ALWAYS))` writes the masked sum on every shot (no gate qubit, one
/// Toffoli less per lane).
pub const ALWAYS: QubitId = QubitId(u64::MAX - 1);

/// Return pass. `g = Some(q)`: write the (masked) sum where q = 1, restore elsewhere; None: exact inverse of `mup`.
pub fn mdown(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    mdown_impl(b, ld, g, g, false, None, &[])
}

pub fn mdown_mid(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    mdown_impl(b, ld, g, g, true, None, &[])
}

/// `mdown_mid` with separate write gates for the masked cells (`g_masked`, e.g. `ALWAYS` where the caller has made the
/// running mask zero on every shot that must not be written) and the ordinary lanes (`g_ord`). WK19 route (c2).
pub fn mdown_mid2(b: &mut B, ld: &Lad, g_masked: Option<QubitId>, g_ord: Option<QubitId>) -> Vec<G> {
    mdown_impl(b, ld, g_ord, g_masked, true, None, &[])
}

pub fn mdown_mid_probe(b: &mut B, ld: &Lad, g: Option<QubitId>, ta: QubitId, dl: QubitId,
                       pb0: usize, pb1: usize) -> Vec<G> {
    mdown_impl(b, ld, g, g, true, Some((ta, dl, pb0, pb1)), &[])
}

fn mdown_impl(b: &mut B, ld: &Lad, g: Option<QubitId>, gm: Option<QubitId>, mid: bool,
              probe: Option<(QubitId, QubitId, usize, usize)>, bank: &[QubitId]) -> Vec<G> {
    mdown_impl_nc(b, ld, g, gm, mid, probe, false, bank, None)
}

fn mdown_impl_nc(b: &mut B, ld: &Lad, g: Option<QubitId>, gm: Option<QubitId>, mid: bool,
              probe: Option<(QubitId, QubitId, usize, usize)>, nc: bool, bank: &[QubitId],
              roll: Option<&RollRec>) -> Vec<G> {
    assert_eq!(g.is_some(), gm.is_some());
    let l_n = ld.t.len();
    let nc = nc_top(ld, nc) && probe.is_none() && g.is_some();
    assert!(bank.is_empty() || (probe.is_none() && ld.srcs.iter().all(|s| s.d != 0 && !s.late)),
            "K1 bank: no pi pairs, late sources or probes");
    assert!(g.is_none() || ld.srcs.iter().all(|s| !s.late), "late sources only in compare passes");
    let mut tx: Vec<QubitId> = bank.to_vec();
    tx.extend(g); tx.extend(gm);
    if let Some((ta, dl, _, _)) = probe { tx.extend([ta, dl]); }
    let _tx = tile_extra(&tx);
    b.begin();
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| {
        let cur = if mid && s.hi == l_n {
            (s.lo..s.hi).rev().map(|l| s.tv(l))
                .find(|&j| j >= 0 && (j as usize) < (1usize << s.v.len()))
                .map(|j| j as usize)
        } else { None };
        Dec { v: &s.v, pre: &s.pre,
              cur: if s.pre.len() == s.v.len() - 2 && !RSHORT.with(|c| c.get()) { None } else { cur } }
    }).collect();
    if !mid { f_end(b, ld); } // f = value after the last lane
    let mut l = l_n;
    while l > 0 {
        l -= 1;
        if l > 0 && pi_pair(ld, l - 1) {
            let lo = l - 1;
            let x = carry_wire(ld, lo);
            toggles(b, ld, &mut decs, l, false, false);
            toggles(b, ld, &mut decs, lo, false, false);
            assert_eq!(g, gm, "pi pair: one write gate");
            masked_pair_down(b, ld, lo, x, g.expect("pi pair needs S2 write gate"));
            toggles(b, ld, &mut decs, l, true, false);
            clear_ended(b, ld, &mut decs, l, false);
            toggles(b, ld, &mut decs, lo, true, false);
            clear_ended(b, ld, &mut decs, lo, false);
            l = lo;
            continue;
        }
        let x = carry_wire(ld, l);
        // undo lane l's late toggles so that f = the mask lane l's cell saw
        toggles(b, ld, &mut decs, l, false, false);
        if let Some(r) = roll {
            if let Some(Some(bit)) = r.rc.get(l) {
                assert!(!masked(ld, l), "ROLL-ROWS repairs ordinary lanes only");
                if !(roll_break(5) && l == l_n / 2) { b.z_if(carry_wire(ld, l + 1), *bit); }
            }
        }
        if skip_zero_pi_lane(ld, l) {
            // No arithmetic on the classically inactive lane.
        } else if nc && l + 1 == l_n {
            // TERMINAL-CARRY SKIP: the up pass left lane l untouched; write t ^= g & f & (s ^ x)
            let (t, s) = (ld.t[l], ld.s[l]);
            if masked(ld, l) && TOPM.with(|c| c.get()).is_some() {
                // R5_MROWY: t ^= f & (m ^ x), m ^ x formed on x and restored
                let gq = gm.expect("nc write gate");
                let sg = TOPM.with(|c| c.get()).unwrap();
                if sg != NO_LANE { b.cx(sg, x); }
                b.x(x);
                b.and_c(ld.sc.f, x, ld.sc.t);
                if gq == ALWAYS { b.cx(ld.sc.t, t); } else { b.ccx(ld.sc.t, gq, t); }
                b.and_u(ld.sc.f, x, ld.sc.t);
                b.x(x);
                if sg != NO_LANE { b.cx(sg, x); }
            } else if masked(ld, l) {
                let gq = gm.expect("nc write gate");
                b.cx(x, s);
                b.and_c(ld.sc.f, s, ld.sc.t);
                if gq == ALWAYS { b.cx(ld.sc.t, t); } else { b.ccx(ld.sc.t, gq, t); }
                b.and_u(ld.sc.f, s, ld.sc.t);
                b.cx(x, s);
            } else {
                let gq = g.expect("nc write gate");
                // negative control for the gate tests only (CR_BREAK=5: the carry-in is dropped from the sum)
                let brk = cfg!(test) && std::env::var("CR_BREAK").map_or(false, |v| v.trim() == "5");
                if !brk { b.cx(x, s); }
                if gq == ALWAYS { b.cx(s, t); } else { b.ccx(gq, s, t); }
                if !brk { b.cx(x, s); }
            }
        } else if masked(ld, l) {
            match fs_idx(ld, l, bank) {
                Some(k) => masked_down_cell_bank(b, ld, l, x, gm, bank[k]),
                None => masked_down_cell(b, ld, l, x, gm),
            }
        } else if let Some(k) = gidx(ld, l) {
            let gq = ld.g[k];
            b.cx(x, gq);
            b.and_u(ld.t[l], ld.s[l], gq);
            b.cx(x, ld.t[l]);
            b.cx(x, ld.s[l]);
            if let Some(gc) = g {
                b.cx(x, ld.s[l]);
                if gc == ALWAYS { b.cx(ld.s[l], ld.t[l]); } else { b.ccx(gc, ld.s[l], ld.t[l]); }
                b.cx(x, ld.s[l]);
            }
        } else {
            b.ccx(x, ld.t[l], ld.s[l]);
            b.cx(ld.s[l], x);
            b.cx(ld.s[l], ld.t[l]);
            if let Some(gq) = g {
                b.cx(ld.s[l], x);
                if gq == ALWAYS { b.cx(x, ld.t[l]); } else { b.ccx(gq, x, ld.t[l]); }
                b.cx(ld.s[l], x);
            }
        }
        if let Some((ta, dl, pb0, pb1)) = probe {
            if l >= pb0 && l < pb1 && ld.srcs.len() > 1 {
                let src = &ld.srcs[1];
                if l + 1 >= src.lo && l + 1 < src.hi {
                    let j = src.tv(l + 1);
                    if j >= 0 && (j as usize) < (1usize << src.v.len()) {
                        let o = decs[1].goto(b, j as usize);
                        let tmp = ld.sc.t;
                        b.and_c(ta, o, tmp);
                        b.x(ld.s[l]);
                        b.ccx(tmp, ld.s[l], dl);
                        b.x(ld.s[l]);
                        b.and_u(ta, o, tmp);
                    }
                }
            }
        }
        toggles(b, ld, &mut decs, l, true, false); // leave lane l downward: f becomes mask(l-1), late T flips undone
        clear_ended(b, ld, &mut decs, l, false);
    }
    if ld.f0 {
        b.x(ld.sc.f);
    }
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    b.end()
}

fn masked_up_cell(b: &mut B, ld: &Lad, l: usize, x: QubitId) {
    let (t, s) = (ld.t[l], ld.s[l]);
    b.cx(x, t);
    b.cx(x, s);
    b.and_c(t, s, ld.sc.t);
    b.ccx(ld.sc.f, ld.sc.t, x);
    b.and_u(t, s, ld.sc.t);
}

/// K1: `masked_down_cell` with a = f & s' already on the bank lane from the up pass (no recompute).
fn masked_down_cell_bank(b: &mut B, ld: &Lad, l: usize, x: QubitId, g: Option<QubitId>, a: QubitId) {
    let (t, s) = (ld.t[l], ld.s[l]);
    // negative control for the gate tests only: P3_BREAK=2 drops the banked carry restore
    if !(cfg!(test) && std::env::var("P3_BREAK").map_or(false, |v| v.trim() == "2")) {
        b.ccx(a, t, x);
    }
    if let Some(gq) = g {
        if gq == ALWAYS { b.cx(a, t); } else { b.ccx(a, gq, t); }
    }
    b.and_u(ld.sc.f, s, a);
    b.cx(x, t);
    b.cx(x, s);
}

fn masked_down_cell(b: &mut B, ld: &Lad, l: usize, x: QubitId, g: Option<QubitId>) {
    let (t, s) = (ld.t[l], ld.s[l]);
    if let Some(gq) = g {
        // One temporary f&s drives both the carry undo and the sum bit.
        // Neither f nor s changes before the measurement uncompute.
        b.and_c(ld.sc.f, s, ld.sc.t);
        b.ccx(ld.sc.t, t, x);
        if gq == ALWAYS { b.cx(ld.sc.t, t); } else { b.ccx(ld.sc.t, gq, t); }
        b.and_u(ld.sc.f, s, ld.sc.t);
    } else {
        b.and_c(t, s, ld.sc.t);
        b.ccx(ld.sc.f, ld.sc.t, x);
        b.and_u(t, s, ld.sc.t);
    }
    b.cx(x, t);
    b.cx(x, s);
}

/// M3 REPARK-X0 (M-008): for each j of `ls` (any order), call `per(b, j, o, q0, one)` with o = [v[1..] == (j + off) >> 1]
/// live on the retained prefix `pre` (v.len() - 2 lanes); the caller completes the equality with the bit-0 literal
/// (q0, positive iff `one`), e.g. by a CCX into its flag. One lane fewer than `onehot_scan`.
pub fn onehot_scan_hi(b: &mut B, v: &[QubitId], pre: &[QubitId], ls: &[usize], off: isize,
                      mut per: impl FnMut(&mut B, usize, QubitId, QubitId, bool)) {
    let mut dec = Dec { v: &v[1..], pre, cur: None };
    for &j in ls {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << v.len()) {
            continue;
        }
        let o = dec.goto(b, val as usize >> 1);
        per(b, j, o, v[0], val & 1 == 1);
    }
    dec.clear(b);
}

/// For j in lanes [lo, hi): call `per(b, j, o_j)` with o_j = [v == j + off] live.
pub fn onehot_scan(b: &mut B, v: &[QubitId], pre: &[QubitId], lo: usize, hi: usize, off: isize,
                   mut per: impl FnMut(&mut B, usize, QubitId)) {
    let mut dec = Dec { v, pre, cur: None };
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << v.len()) {
            continue;
        }
        let o = dec.goto(b, val as usize);
        per(b, j, o);
    }
    dec.clear(b);
}

#[cfg(test)]
pub(crate) fn onehot_scan_old(b: &mut B, v: &[QubitId], pre: &[QubitId], lo: usize, hi: usize, off: isize,
                              mut per: impl FnMut(&mut B, usize, QubitId)) {
    let mut dec = Dec { v, pre, cur: None };
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << v.len()) { continue; }
        let o = dec.goto_impl(b, val as usize, false);
        per(b, j, o);
    }
    dec.clear(b);
}
use super::greedyfrog::l8_site;
// Included in point_add::mask. The F6 traversal is invertible as a builder recording.
fn l8_enabled(flag: &str) -> bool { std::env::var(flag).as_deref() == Ok("1") }
// shipped defaults: on unless set to 0 (the official build reads no environment)
fn l8_on(flag: &str) -> bool { std::env::var(flag).as_deref() != Ok("0") }

fn l8_triple(b: &mut B, a: QubitId, k: QubitId, c: QubitId, out: QubitId, dirty: QubitId) {
    for _ in 0..2 { b.ccx(a, k, dirty); b.ccx(dirty, c, out); }
}

fn l8_normalize(b: &mut B, high: &[QubitId], word: usize) {
    for (i, &q) in high.iter().enumerate() {
        if word >> i & 1 != 0 { b.x(q); }
    }
}

// Make ab, ac, abc on three input literals that are zero when the guard holds.
// Use the third host as the pivot. It also holds bc while visiting the low half.
fn l8_basis(b: &mut B, v: &[QubitId], group: usize, inverse: bool) {
    let (a, k, c) = (v[2], v[1], v[0]);
    if !inverse { l8_normalize(b, &v[3..6], group); }
    if inverse { b.ccx(v[3], c, v[5]); }
    b.ccx(a, k, v[3]); b.ccx(a, c, v[4]);
    if !inverse { b.ccx(v[3], c, v[5]); }
    if inverse { l8_normalize(b, &v[3..6], group); }
}

fn l8_leaf(b: &mut B, v: &[QubitId], guard: QubitId, j: usize, flag: QubitId) {
    let p = v[5];
    b.begin();
    if j & 1 == 0 { b.cx(v[3], p); } // ab
    if j & 2 == 0 { b.cx(v[4], p); } // ac
    for i in 0..3 {
        if j & (7 ^ (1 << i)) == 0 { b.cx(v[i], p); }
    }
    if j == 0 { b.x(p); }
    let affine = b.end();
    b.play(&affine, false);
    b.ccx(guard, p, flag);
    b.play(&affine, true);
}

fn l8_high(b: &mut B, v: &[QubitId], guard: QubitId, group: usize, d: QubitId) {
    let hs = &v[3..6];
    l8_normalize(b, hs, group ^ 7);
    l8_triple(b, hs[0], hs[1], hs[2], guard, d);
    l8_normalize(b, hs, group ^ 7);
}

// The union of two distinct three-bit points is an affine line. Its indicator
// changes a high-match bit from [v==old] into [v==new] with a single CCX.
fn l8_advance(b: &mut B, hs: &[QubitId], out: QubitId, old: usize, new: usize) {
    let delta = old ^ new;
    let pivot = delta.trailing_zeros() as usize;
    let mut controls = Vec::new();
    b.begin();
    for i in 0..3 {
        if i == pivot { continue; }
        let slope = delta >> i & 1;
        if slope == 1 { b.cx(hs[pivot], hs[i]); }
        if ((old >> i) ^ ((old >> pivot) & slope)) & 1 == 0 { b.x(hs[i]); }
        controls.push(hs[i]);
    }
    let affine = b.end();
    b.play(&affine, false);
    b.ccx(controls[0], controls[1], out);
    b.play(&affine, true);
}

fn l8_move(b: &mut B, v: &[QubitId], guard: QubitId, d: QubitId,
           old: Option<usize>, new: Option<usize>) {
    let (og, ng) = (old.map(|j| j / 8), new.map(|j| j / 8));
    if og == ng {
        if old.map(|j| j & 4) != new.map(|j| j & 4) { b.ccx(v[1], v[0], v[5]); }
        return;
    }
    if let Some(j) = old {
        if j & 4 == 0 { b.ccx(v[1], v[0], v[5]); }
        l8_basis(b, v, j / 8, true);
    }
    match (og, ng) {
        (Some(i), Some(j)) => l8_advance(b, &v[3..6], guard, i, j),
        (Some(j), None) | (None, Some(j)) => l8_high(b, v, guard, j, d),
        (None, None) => unreachable!(),
    }
    if let Some(j) = new {
        l8_basis(b, v, j / 8, false);
        if j & 4 == 0 { b.ccx(v[1], v[0], v[5]); }
    }
}

// s comprises real source bits after the parent's sign flip. The top two
// virtual bits are sign and !sign. The entry carry m equals !sign (row 0: 1).
pub(super) fn l8_folded(b: &mut B, t: &[QubitId], s: &[QubitId], v: &[QubitId],
        base: isize, flag: QubitId, clean: QubitId, sign: Option<QubitId>, bank: &[QubitId], ptmp: QubitId) -> bool {
    if !l8_on("L8_F6") || v.len()!=6 || t.len()!=s.len()+2 { return false; }
    let mut fixed: Vec<_> = t.iter().chain(s).chain(v).copied().collect();
    fixed.extend([flag, clean]); fixed.extend(sign);
    let mut seen = std::collections::BTreeSet::new();
    if !fixed.iter().all(|q| *q != NO_LANE && seen.insert(*q)) { return false; }
    // L8_HYB (795): the AND temp exists here (no notemp mode); use the parent's temp cells, 2 up + 2 down per bit.
    let hyb = l8_on("L8_HYB") && ptmp != NO_LANE && !seen.contains(&ptmp);
    if hyb { seen.insert(ptmp); }
    let ds: Vec<_> = bank.iter().copied().filter(|q| *q != NO_LANE && seen.insert(*q)).collect();
    if ds.len() < 2 { return false; }
    let (carry, tmp) = (ds[0], ds[1]);
    let cache = !hyb && l8_enabled("L8_BANK") && ds.len() >= s.len()+2;
    let reset_m = |b: &mut B| { b.x(clean); if let Some(sg) = sign { b.cx(sg, clean); } };
    for &q in t.iter().chain(s) { b.cx(carry, q); }
    b.cx(clean, carry); reset_m(b);
    let (lo_top, top) = (t[s.len()], t[s.len()+1]);
    for down in [false, true] {
        let mut current = None;
        for step in 0..s.len() {
            let i = if down { s.len()-1-step } else { step };
            let address = base + i as isize;
            let next = (address >= 0 && address < 64 && address <= TVMAX.with(|c| c.get())).then_some(address as usize);
            if !down {
                l8_move(b, v, clean, tmp, current, next);
                if let Some(j) = next { l8_leaf(b, v, clean, j%8, flag); }
                b.cx(carry, t[i]); b.cx(carry, s[i]);
            }
            if hyb {
                if !down { b.and_c(t[i], s[i], ptmp); b.ccx(flag, ptmp, carry); b.and_u(t[i], s[i], ptmp); }
                else { b.and_c(flag, s[i], ptmp); b.ccx(ptmp, t[i], carry); b.cx(ptmp, t[i]); b.and_u(flag, s[i], ptmp); }
            } else if cache {
                // Between traversals ds[i+2] holds its input XOR (f & framed_s).
                let d = ds[i+2];
                b.ccx(d, t[i], carry); b.ccx(flag, s[i], d); b.ccx(d, t[i], carry);
                if down { b.ccx(flag, s[i], t[i]); }
            } else if !down {
                l8_triple(b, flag, s[i], t[i], carry, tmp);
            } else {
                // Parent down4_dirty with an explicit, disjoint borrowed lane.
                b.cx(tmp, t[i]); b.ccx(flag,s[i],tmp); b.cx(tmp,t[i]); b.x(t[i]);
                b.ccx(tmp,t[i],carry); b.ccx(flag,s[i],tmp); b.ccx(tmp,t[i],carry); b.x(t[i]);
            }
            if down {
                b.cx(carry, t[i]); b.cx(carry, s[i]);
                l8_move(b, v, clean, tmp, current, next);
                if let Some(j) = next { l8_leaf(b, v, clean, j%8, flag); }
            }
            current = next;
        }
        l8_move(b, v, clean, tmp, current, None);
        if !down {
            b.ccx(lo_top, carry, top); b.cx(carry, lo_top);
            if let Some(sg) = sign { b.ccx(sg,lo_top,top); b.cx(sg,lo_top); b.cx(sg,top); }
            b.x(top);
        }
    }
    reset_m(b); b.cx(clean,carry);
    for &q in t.iter().chain(s) { b.cx(carry,q); }
    if let Some(sg) = sign { b.cx(sg,lo_top); }
    b.ccx(carry,lo_top,top);
    if let Some(sg) = sign { b.cx(sg,lo_top); }
    b.cx(carry,lo_top);
    if l8_enabled("L8_PRICE") {
        let (div,slot,sect)=l8_site();
        eprintln!("L8F6 div {div} slot {slot} sect {sect} bits {} base {} vmax {} bank {} hyb {}",s.len(),base,TVMAX.with(|c| c.get()),cache as u8,hyb as u8);
    }
    true
}


// Limit temporary edits of the read-only address to the three audited callers.
// Their external controls and outputs are part of the disjointness check.
thread_local! {
    static L8_EXTRA: std::cell::Cell<Option<[QubitId;3]>> = const { std::cell::Cell::new(None) };
}
pub(super) struct L8Window(Option<[QubitId;3]>);
impl Drop for L8Window {
    fn drop(&mut self) { L8_EXTRA.with(|x| x.set(self.0)); }
}
pub(super) fn l8_window(q: [QubitId;3]) -> L8Window {
    L8Window(L8_EXTRA.with(|x| x.replace(Some(q))))
}


// 795 has no b793 F6 'notemp' mode (the AND temp always exists); the rolled ladder asserts it.
pub fn notemp() -> bool { false }



// ---- T4 tile (g795b): grouped address test for the retained-prefix decoders whose last retained level o covers
// address bits n-1 .. 2 (RSHORT2 and RSHORT2T forms). The four leaves j = 4g .. 4g+3 of a group share o = [v >> 2 == g].
// Where o = 1 the physical bit-2 literal v[2] is the known constant g & 1, so after an X it holds 0 and can carry the
// product w = v[1] v[0] (one CCX, undone after the last leaf). Each leaf indicator [v[1:0] == y] is then w plus an
// affine function of v[1], v[0] (CX/X on w), and one CCX(o, w, f) toggles the mask. Where o = 0 the wire holds
// arbitrary data, the leaf CCX does nothing, and everything is restored. A run of m leaves costs m + 2 Toffoli
// (RSHORT2: 4 m, RSHORT2T: 2 m). All gates are X, CX, CCX: basis permutations, valid in recordings and inverses.
thread_local! {
    static TILE_EXTRA: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
}
pub struct TileExtra(Vec<QubitId>);
impl Drop for TileExtra {
    fn drop(&mut self) { TILE_EXTRA.with(|x| *x.borrow_mut() = std::mem::take(&mut self.0)); }
}
/// Pass-level wires the ladder's cells read besides its own fields (write gates, probes, top target).
pub fn tile_extra(q: &[QubitId]) -> TileExtra {
    TileExtra(TILE_EXTRA.with(|x| { let mut x = x.borrow_mut(); let old = x.clone(); *x = q.iter().copied().filter(|&q| q != NO_LANE && q != ALWAYS).collect(); old }))
}
pub fn t4_enabled() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("T4_TILE").map_or(true, |v| v.trim() != "0"));
    *E
}
fn tile_leaf(b: &mut B, ld: &Lad, dec: &mut Dec, s: &Src, l: usize, j: usize, up: bool, target: QubitId) -> bool {
    if s.late || !matches!(s.d, -1 | 1) || ld.srcs.len() != 1 || s.hi > ld.t.len() { return false; }
    let n = dec.n();
    // the dispatch chain of `toggles`, restricted to the two forms
    let cost1: u64 = if (dec.short4t() && R14L.with(|c| c.get())) || dec.short5t() { return false; }
        else if dec.short2t() { 2 }
        else if dec.short4t() || dec.short3t() || dec.short3() { return false; }
        else if dec.short2() { 4 }
        else { return false; };
    if n < 4 || dec.pre.len() + 3 != n || target != ld.sc.f { return false; }
    let (v0, v1, v2) = (dec.v[0], dec.v[1], dec.v[2]);
    let o_q = dec.pre[dec.pre.len() - 1];
    let extra: Vec<QubitId> = TILE_EXTRA.with(|x| x.borrow().clone());
    let sign = TOPM.with(|c| c.get());
    let busy = |q: QubitId| ld.t.contains(&q) || ld.s.contains(&q) || ld.g.contains(&q) || ld.sc.chain.contains(&q)
        || [ld.c0, ld.sc.t, ld.sc.f, ld.sc.gf, target].contains(&q) || extra.contains(&q) || Some(q) == sign;
    if [v0, v1, v2].iter().any(|&q| busy(q) || q == o_q) || o_q == target || v0 == v1 || v0 == v2 || v1 == v2 { return false; }
    if dec.pre.iter().any(|&q| q == v0 || q == v1 || q == v2) { return false; }
    let group = j >> 2;
    let pres = |ll: isize| -> Option<usize> {
        if ll < s.lo as isize || ll >= s.hi as isize { return None; }
        let jj = s.tv(ll as usize);
        if jj < 0 || (jj as usize) >= (1usize << n) || jj > TVMAX.with(|c| c.get()) { return None; }
        Some(jj as usize)
    };
    let mut m = 0u64;
    for jj in group * 4..group * 4 + 4 {
        let ll = (jj as isize - s.a) * s.d;
        if pres(ll).map_or(false, |x| x == jj) { m += 1; }
    }
    if 2 + m >= cost1 * m { return false; }
    let li = l as isize;
    let (prev, next) = if up { (li - 1, li + 1) } else { (li + 1, li - 1) };
    let first = !pres(prev).map_or(false, |x| x >> 2 == group);
    let last = !pres(next).map_or(false, |x| x >> 2 == group);
    let o = dec.goto_impl(b, j, true);
    assert_eq!(o, o_q);
    let hi_one = group & 1 == 1;
    if first {
        if hi_one { b.x(v2); }
        b.ccx(v1, v0, v2);
    }
    let (alpha, beta) = (((j >> 1) & 1) ^ 1, (j & 1) ^ 1);
    let brk = t4_brk("leaf");
    if beta == 1 && !brk { b.cx(v1, v2); }
    if alpha == 1 { b.cx(v0, v2); }
    if alpha & beta == 1 { b.x(v2); }
    b.ccx(o, v2, target);
    if alpha & beta == 1 { b.x(v2); }
    if alpha == 1 { b.cx(v0, v2); }
    if beta == 1 && !brk { b.cx(v1, v2); }
    if last {
        if !t4_brk("close") { b.ccx(v1, v0, v2); }
        if hi_one { b.x(v2); }
    }
    true
}
/// negative controls (dev only, inert unless T4_BRK is set): `leaf` drops one affine edit of the leaf indicator, `close`
/// leaves the product on the address wire
pub(crate) fn t4_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("T4_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}


// ---- T8 persistent tile (f796): grouped address test for the retained-prefix decoders RSHORT2 / RSHORT2T (low bits
// 1, 0) and RSHORT3 (low bits 2, 1, 0) whose products stay on the address wires ACROSS groups. An address wire v[k]
// above the low bits is XORed with a product P of low bits and holds v[k] ^ P on every shot; where the last retained
// level o = [v >> low == j >> low] is 1, v[k] is the known bit k of j, so after Clifford edits one wire holds the leaf
// indicator and the leaf is one CCX(o, w, f). Where o = 0 that CCX does nothing. A wire is restored (one CCX) only
// before a prefix move that reads it (`t8_reads`) and at the ends of a run.
//   low = 2: w = v[kd] ^ v1 v0.
//   low = 3: wa = v[ka] ^ v2 v1, wb = v[kb] ^ v2 v0, wd = v[kd] ^ v0 (v[ka] ^ v2 v1) ^ m v1 v0, m = 1 on leaves with
//   bit 2 clear (one CCX(v1, v0, wd) where m changes).
// All gates are X, CX, CCX: basis permutations, valid in recordings and inverses.
pub fn t8_enabled() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("T8_TILE").map_or(true, |v| v.trim() != "0"));
    *E
}
/// negative controls (dev only, inert unless T8_BRK is set): `leaf` drops the constant edit of a leaf, `close` leaves
/// a product on its address wire at a prefix move, `mode` drops the v1 v0 mode change
pub(crate) fn t8_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("T8_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}
/// does the prefix move c -> j (`Dec::goto_impl`, fast form) read address bit k (k >= low)?
fn t8_reads(n: usize, low: usize, c: usize, j: usize, k: usize) -> bool {
    let x = c ^ j;
    if x == 0 { return false; }
    let h = usize::BITS as usize - 1 - x.leading_zeros() as usize;
    if h >= n - 1 { return true; }
    if h < low { return false; }
    (k < h) || (h == n - 2 && k == n - 1)
}
fn t8_leaf(b: &mut B, ld: &Lad, dec: &mut Dec, s: &Src, l: usize, j: usize, up: bool, target: QubitId) -> bool {
    if s.late || !matches!(s.d, -1 | 1) || ld.srcs.len() != 1 || s.hi > ld.t.len() { return false; }
    let n = dec.n();
    // the dispatch chain of `toggles`, restricted to the three forms
    let (cost1, low): (u64, usize) = if (dec.short4t() && R14L.with(|c| c.get())) || dec.short5t() { return false; }
        else if dec.short2t() { (2, 2) }
        else if dec.short4t() || dec.short3t() { return false; }
        else if dec.short3() { (8, 3) }
        else if dec.short2() { (4, 2) }
        else { return false; };
    if dec.pre.len() + low + 1 != n || target != ld.sc.f { return false; }
    if (low == 2 && n < 4) || (low == 3 && n < 6) { return false; }
    // wires: kd = n-2 (read only by a move across the top bit), then n-1 and n-3
    let ks: Vec<usize> = if low == 2 { vec![n - 2] } else { vec![n - 2, n - 1, n - 3] };
    let o_q = dec.pre[dec.pre.len() - 1];
    let extra: Vec<QubitId> = TILE_EXTRA.with(|x| x.borrow().clone());
    let sign = TOPM.with(|c| c.get());
    let busy = |q: QubitId| ld.t.contains(&q) || ld.s.contains(&q) || ld.g.contains(&q) || ld.sc.chain.contains(&q)
        || [ld.c0, ld.sc.t, ld.sc.f, ld.sc.gf, target].contains(&q) || extra.contains(&q) || Some(q) == sign;
    let mut used: Vec<QubitId> = (0..low).map(|i| dec.v[i]).collect();
    used.extend(ks.iter().map(|&k| dec.v[k]));
    if used.iter().any(|&q| busy(q) || q == o_q || dec.pre.contains(&q)) { return false; }
    if (0..used.len()).any(|i| (i + 1..used.len()).any(|k| used[i] == used[k])) { return false; }
    let pres = |ll: isize| -> Option<usize> {
        if ll < s.lo as isize || ll >= s.hi as isize { return None; }
        let jj = s.tv(ll as usize);
        if jj < 0 || (jj as usize) >= (1usize << n) || jj > TVMAX.with(|c| c.get()) { return None; }
        Some(jj as usize)
    };
    let li = l as isize;
    // the run of written lanes around l, and its cost under the tile
    let (mut lo, mut hi) = (li, li);
    while pres(lo - 1).is_some() { lo -= 1; }
    while pres(hi + 1).is_some() { hi += 1; }
    let m = (hi - lo + 1) as u64;
    let mode = |jj: usize| low == 3 && (jj >> 2) & 1 == 0;
    let setup_cost = |jj: usize, k: usize| -> u64 { if low == 3 && k == ks[0] && mode(jj) { 2 } else { 1 } };
    let mut cost = m;
    for ll in lo..=hi {
        let jj = pres(ll).unwrap();
        if ll == lo { for &k in &ks { cost += setup_cost(jj, k); } }
        if ll == hi { for &k in &ks { cost += setup_cost(jj, k); } }
        else {
            let jn = pres(ll + 1).unwrap();
            for &k in &ks { if t8_reads(n, low, jj, jn, k) { cost += setup_cost(jj, k) + setup_cost(jn, k); } }
            if low == 3 && !t8_reads(n, low, jj, jn, ks[0]) && mode(jj) != mode(jn) { cost += 1; }
        }
    }
    if cost >= cost1 * m { return false; }
    let (prev, next) = if up { (pres(li - 1), pres(li + 1)) } else { (pres(li + 1), pres(li - 1)) };
    let o = dec.goto_impl(b, j, true);
    assert_eq!(o, o_q);
    let (v0, v1) = (dec.v[0], dec.v[1]);
    let w = |i: usize| dec.v[ks[i]];
    let g = |i: usize| (j >> ks[i]) & 1 == 1;
    let rd = |a: Option<usize>, i: usize| a.map_or(true, |a| t8_reads(n, low, a, j, ks[i]));
    if low == 2 {
        if rd(prev, 0) { b.ccx(v1, v0, w(0)); }
        let (a1, a0) = (((j >> 1) & 1) ^ 1 == 1, (j & 1) ^ 1 == 1);
        let kx = ((a1 && a0) ^ g(0)) && !t8_brk("leaf");
        if a0 { b.cx(v1, w(0)); }
        if a1 { b.cx(v0, w(0)); }
        if kx { b.x(w(0)); }
        b.ccx(o, w(0), target);
        if kx { b.x(w(0)); }
        if a1 { b.cx(v0, w(0)); }
        if a0 { b.cx(v1, w(0)); }
        if rd(next, 0) && !(t8_brk("close") && next.is_some()) { b.ccx(v1, v0, w(0)); }
    } else {
        let v2 = dec.v[2];
        let (wd, wa, wb) = (w(0), w(1), w(2));
        // setup: wa, wb, then wd (its CCX reads wa)
        if rd(prev, 1) { b.ccx(v2, v1, wa); }
        if rd(prev, 2) { b.ccx(v2, v0, wb); }
        if rd(prev, 0) {
            b.ccx(wa, v0, wd);
            if mode(j) { b.ccx(v1, v0, wd); }
        } else if mode(prev.unwrap()) != mode(j) && !t8_brk("mode") { b.ccx(v1, v0, wd); }
        let (a2, a1, a0) = (((j >> 2) & 1) ^ 1 == 1, ((j >> 1) & 1) ^ 1 == 1, (j & 1) ^ 1 == 1);
        let (gd, ga, gb) = (g(0), g(1), g(2));
        let kx = (gd ^ (a0 && ga) ^ (a1 && gb) ^ (a2 && a1 && a0)) && !t8_brk("leaf");
        let e0 = (a2 && a1) ^ ga;
        if a0 { b.cx(wa, wd); }
        if a1 { b.cx(wb, wd); }
        if a1 && a0 { b.cx(v2, wd); }
        if a2 && a0 { b.cx(v1, wd); }
        if e0 { b.cx(v0, wd); }
        if kx { b.x(wd); }
        b.ccx(o, wd, target);
        if kx { b.x(wd); }
        if e0 { b.cx(v0, wd); }
        if a2 && a0 { b.cx(v1, wd); }
        if a1 && a0 { b.cx(v2, wd); }
        if a1 { b.cx(wb, wd); }
        if a0 { b.cx(wa, wd); }
        // teardown: wd first (its CCX reads wa), then wb, wa
        if rd(next, 0) {
            if mode(j) { b.ccx(v1, v0, wd); }
            b.ccx(wa, v0, wd);
        }
        if rd(next, 2) { b.ccx(v2, v0, wb); }
        if rd(next, 1) && !(t8_brk("close") && next.is_some()) { b.ccx(v2, v1, wa); }
    }
    true
}
