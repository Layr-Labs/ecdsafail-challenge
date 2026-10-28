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
    fn lit(&self, k: usize, j: usize) -> (QubitId, bool) {
        (self.v[k], (j >> k) & 1 == 0)
    }
    fn comp(&self, b: &mut B, i: usize, j: usize, undo: bool) {
        let n = self.n();
        assert!(!self.skip() || i > self.skipk(), "skip decoder level {i} has no stored parent");
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
    /// Short retained decoder (lane A1b, marked by `short_pre`): only the n-2 prefixes of bits n-1 .. 1 are kept;
    /// a toggle ANDs the bit-0 literal in with one CCX. One prefix lane fewer than a retained decoder.
    fn short(&self) -> bool {
        let n = self.n();
        n >= 3 && self.pre.len() == n - 1 && self.pre[n - 2] == self.pre[n - 3] && !self.short2()
    }
    fn levels(&self) -> usize {
        if self.short2() { self.n() - 3 } else if self.short() { self.n() - 2 } else { self.n() - 1 }
    }
    /// Lane A1d (`short2_pre`): only the prefixes of bits n-1 .. 2 are kept (levels k .. n-4); a toggle ANDs the bit-1
    /// and bit-0 literals in through the clean lane `tmp2()` (one logical AND, one CCX). Two prefix lanes fewer than a
    /// retained decoder; skip-k (k >= 2) only.
    fn short2(&self) -> bool {
        let l = self.pre.len();
        l >= 2 && self.pre[l - 2] == SHORT2_LVL
    }
    fn tmp2(&self) -> QubitId {
        assert!(self.short2());
        *self.pre.last().unwrap()
    }
    /// clean lanes for the level-k chain of a skip-k decoder: the (cleared) deeper levels, plus the short2 temp
    fn ktemps(&self) -> Vec<QubitId> {
        let (k, lv) = (self.skipk(), self.levels());
        let mut v = self.pre[k + 1..lv].to_vec();
        if self.short2() { v.push(self.tmp2()); }
        v
    }
    /// Lane A1c (`skip_pre`): the top level (bits n-1, n-2) has no lane; level 1 is the first stored one.
    fn skip(&self) -> bool {
        self.pre.first() == Some(&SKIP_LVL)
    }
    /// number of lane-less top levels (lane A1c, `skip_pre_k`)
    fn skipk(&self) -> usize {
        self.pre.iter().take_while(|&&q| q == SKIP_LVL).count()
    }
    /// literals of the top m bits (n-1 .. n-m) of j
    fn top_lits(&self, m: usize, j: usize) -> Vec<(QubitId, bool)> {
        (0..m).map(|i| self.lit(self.n() - 1 - i, j)).collect()
    }
    /// Skip-k decoders (k >= 2): make / erase level k = AND of the literals of bits n-1 .. n-2-k of j, the chain in
    /// the (clean) lanes of the levels above k, the last step a Barenco toggle on the dirty lane v[0] when one lane short.
    fn comp_first_k(&self, b: &mut B, j: usize, undo: bool) {
        let (n, k, lv) = (self.n(), self.skipk(), self.levels());
        assert!(k >= 2 && k + 3 <= n && lv > k);
        let lits = self.top_lits(k + 2, j);
        let temps = self.ktemps();
        let mode = if undo { Tm::Erase } else { Tm::Make };
        if lits.len() > temps.len() + 3 {
            // lane A1e (a short skip-k decoder): two or more temps short, a Barenco V-chain on the value's low bits
            // (below the k + 2 literals, so outside the gate)
            mctn(b, &lits, self.pre[k], &temps, &self.v[..n - 2 - k], mode);
        } else {
            mct(b, &lits, self.pre[k], &temps, self.v[0], mode);
        }
    }
    /// Skip-k decoders (k >= 2), level k changes with lanes above k clear: keep == k -> toggle by the virtual parent
    /// (bits n-1 .. n-1-k of j); keep < k -> by m(c) ^ m(j) on bits n-1 .. n-2-k = [common bits match] & [the
    /// differing bits form j's or c's pattern] (parities, made in place and restored). k + 1 literals: k Toffoli.
    fn toggle_k(&self, b: &mut B, c: usize, j: usize, keep: usize) {
        let (n, k, lv) = (self.n(), self.skipk(), self.levels());
        let temps_v = self.ktemps();
        let temps = &temps_v[..];
        if keep == k {
            let lits = self.top_lits(k + 1, j);
            mct(b, &lits, self.pre[k], temps, self.v[0], Tm::Xor);
            return;
        }
        let bits: Vec<usize> = (0..k + 2).map(|i| n - 1 - i).collect();
        let d: Vec<usize> = bits.iter().copied().filter(|&x| ((c ^ j) >> x) & 1 == 1).collect();
        assert!(!d.is_empty());
        let mut lits: Vec<(QubitId, bool)> = bits.iter().copied().filter(|&x| ((c ^ j) >> x) & 1 == 0)
            .map(|x| self.lit(x, j)).collect();
        // v[d_i] ^= v[d_{i-1}] for i = |d|-1 .. 1 (each from the original lower one)
        for i in (1..d.len()).rev() { b.cx(self.v[d[i - 1]], self.v[d[i]]); }
        for i in 1..d.len() {
            let par = ((j >> d[i]) ^ (j >> d[i - 1])) & 1;
            let neg = (par == 0) ^ (super::froghop_one::a1b_mut("skiptogk") && i == 1);
            lits.push((self.v[d[i]], neg));
        }
        mct(b, &lits, self.pre[k], temps, self.v[0], Tm::Xor);
        for i in 1..d.len() { b.cx(self.v[d[i - 1]], self.v[d[i]]); }
    }
    /// Skip decoders: compute (undo = false) or measure away level 1 = AND of the literals of bits n-1, n-2, n-3 of j,
    /// with level 2's lane (clean whenever level 1 is (un)made) as the transient pair AND. 2 Toffoli to make, 1 to
    /// erase.
    fn comp_first(&self, b: &mut B, j: usize, undo: bool) {
        let n = self.n();
        assert!(self.skip() && self.levels() >= 3);
        let t = self.pre[2];
        let (q1, g1) = self.lit(n - 1, j);
        let (q2, g2) = self.lit(n - 2, j);
        let (q3, g3) = self.lit(n - 3, j);
        if g1 { b.x(q1); }
        if g2 { b.x(q2); }
        b.and_c(q1, q2, t);
        if g3 { b.x(q3); }
        if undo { b.and_u(t, q3, self.pre[1]) } else { b.and_c(t, q3, self.pre[1]) }
        if g3 { b.x(q3); }
        b.and_u(q1, q2, t);
        if g2 { b.x(q2); }
        if g1 { b.x(q1); }
    }
    /// Skip decoders: level 1 ^= m(c) ^ m(j), the two 3-literal minterms of bits n-1, n-2, n-3 (c and j differ in d of
    /// them): d = 1 -> AND of the two common literals; d = 2 -> common literal & [v_x ^ v_y == j_x ^ j_y]; d = 3 ->
    /// [v_x ^ v_y == j_x ^ j_y] & [v_y ^ v_z == j_y ^ j_z] (the two patterns are complements on the differing bits).
    /// One Toffoli; the value bits are XOR'd in place and restored.
    fn toggle_first(&self, b: &mut B, c: usize, j: usize) {
        let n = self.n();
        let bits = [n - 1, n - 2, n - 3];
        let d: Vec<usize> = bits.iter().copied().filter(|&k| ((c ^ j) >> k) & 1 == 1).collect();
        let s: Vec<usize> = bits.iter().copied().filter(|&k| ((c ^ j) >> k) & 1 == 0).collect();
        let t = self.pre[1];
        let mutate = super::froghop_one::a1b_mut("skiptog");
        match d.len() {
            1 => {
                let (a, ga) = self.lit(s[0], j);
                let (q, gq) = self.lit(s[1], j);
                if ga { b.x(a); }
                if gq { b.x(q); }
                b.ccx(a, q, t);
                if gq { b.x(q); }
                if ga { b.x(a); }
            }
            2 => {
                let (x, y) = (d[0], d[1]);
                let (a, ga) = self.lit(s[0], j);
                let (vx, vy) = (self.v[x], self.v[y]);
                b.cx(vx, vy);
                let gy = (((j >> x) ^ (j >> y)) & 1 == 0) ^ mutate;
                if ga { b.x(a); }
                if gy { b.x(vy); }
                b.ccx(a, vy, t);
                if gy { b.x(vy); }
                if ga { b.x(a); }
                b.cx(vx, vy);
            }
            3 => {
                let (vx, vy, vz) = (self.v[n - 1], self.v[n - 2], self.v[n - 3]);
                b.cx(vy, vz); // z' = y ^ z
                b.cx(vx, vy); // y' = x ^ y
                let gy = ((j >> (n - 1)) ^ (j >> (n - 2))) & 1 == 0;
                let gz = (((j >> (n - 2)) ^ (j >> (n - 3))) & 1 == 0) ^ mutate;
                if gy { b.x(vy); }
                if gz { b.x(vz); }
                b.ccx(vy, vz, t);
                if gz { b.x(vz); }
                if gy { b.x(vy); }
                b.cx(vx, vy);
                b.cx(vy, vz);
            }
            _ => unreachable!("level 1 unchanged"),
        }
    }
    /// Dirty transient decoder (lane A1b, marked by `dirty_pre`): n-3 clean prefix lanes and one borrowed lane of
    /// any state; a toggle ANDs the top n-2 literals into the clean chain and finishes with a dirty-ancilla Toffoli
    /// (Barenco: 4 CCX) on the two low literals. One clean lane fewer than `xor_into`, two Toffolis more per toggle.
    fn dirty_xor(&self) -> bool {
        let n = self.n();
        n >= 4 && self.pre.len() == n && self.pre[n - 1] == self.pre[n - 2] && self.pre[n - 2] == self.pre[n - 3]
            && self.pre[..n - 3].iter().all(|&q| q != self.pre[n - 1])
    }
    /// no prefix state is kept between toggles
    fn transient(&self) -> bool {
        self.pre.len() == self.n() - 2 || self.dirty_xor()
    }
    fn xor_into_dirty(&self, b: &mut B, j: usize, target: QubitId) {
        let n = self.n();
        assert!(self.dirty_xor());
        let d = self.pre[n - 1];
        b.begin();
        for i in 0..n - 3 {
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
        let c = self.pre[n - 4];
        let (l1, g1) = self.lit(1, j);
        let (l0, g0) = self.lit(0, j);
        if g1 { b.x(l1); }
        if g0 { b.x(l0); }
        b.ccx(c, l1, d);
        b.ccx(d, l0, target);
        if !super::froghop_one::a1b_mut("dirtypi") { b.ccx(c, l1, d); }
        b.ccx(d, l0, target);
        if g0 { b.x(l0); }
        if g1 { b.x(l1); }
        b.play(&r, true);
    }
    /// prefixes live for j; returns the qubit holding [v == j]
    fn goto(&mut self, b: &mut B, j: usize) -> QubitId {
        assert_eq!(self.pre.len(), self.n() - 1, "goto needs a retained prefix");
        assert!(!self.short(), "a short decoder has no [v == j] lane");
        assert!(!self.short2(), "a short2 decoder has no [v == j] lane");
        self.goto_impl(b, j, true)
    }
    /// Short2 decoder (lane A1d): prefixes live for j's bits n-1 .. 2; returns (that level's lane, bit-1 literal,
    /// bit-0 literal of j).
    fn goto_short2(&mut self, b: &mut B, j: usize) -> (QubitId, (QubitId, bool), (QubitId, bool)) {
        assert!(self.short2() && self.skipk() >= 2);
        let p = self.goto_impl(b, j, true);
        (p, self.lit(1, j), self.lit(0, j))
    }
    /// Short2 toggle (lane A1d): target ^= [v == j] = L & lit1 & lit0, the pair AND in the clean temp (made, then
    /// measured away): 1 Toffoli.
    fn xor_short2(&mut self, b: &mut B, j: usize, target: QubitId) {
        let tmp = self.tmp2();
        let (p, (q1, g1), (q0, g0)) = self.goto_short2(b, j);
        let g0 = g0 ^ super::froghop_one::a1b_mut("short2");
        if g1 { b.x(q1); }
        b.and_c(p, q1, tmp);
        if g0 { b.x(q0); }
        b.ccx(tmp, q0, target);
        if g0 { b.x(q0); }
        b.and_u(p, q1, tmp);
        if g1 { b.x(q1); }
    }
    /// Short decoder: prefixes live for j's bits n-1 .. 1; returns (that prefix lane, bit-0 literal of j).
    fn goto_short(&mut self, b: &mut B, j: usize) -> (QubitId, (QubitId, bool)) {
        assert!(self.short());
        let p = self.goto_impl(b, j, true);
        (p, self.lit(0, j))
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
        let levels = self.levels();
        if self.skipk() >= 2 {
            let k = self.skipk();
            match self.cur {
                None => {
                    self.comp_first_k(b, j, false);
                    for i in k + 1..levels { self.comp(b, i, j, false); }
                }
                Some(c) => {
                    let mut kp = 0;
                    while kp < levels && ((c ^ j) >> (n - 2 - kp)) == 0 { kp += 1; }
                    if kp < levels {
                        let from = kp.max(k) + 1;
                        for i in (from..levels).rev() { self.comp(b, i, c, true); }
                        if kp > k { b.cx(self.pre[kp - 1], self.pre[kp]); } else { self.toggle_k(b, c, j, kp); }
                        for i in from..levels { self.comp(b, i, j, false); }
                    }
                }
            }
            self.cur = Some(j);
            return self.pre[levels - 1];
        }
        if self.skip() {
            assert!(levels >= 3, "a skip decoder needs three stored levels");
            match self.cur {
                None => {
                    self.comp_first(b, j, false);
                    for i in 2..levels { self.comp(b, i, j, false); }
                }
                Some(c) => {
                    let mut kp = 0;
                    while kp < levels && ((c ^ j) >> (n - 2 - kp)) == 0 { kp += 1; }
                    if kp < levels {
                        let from = kp.max(1) + 1;
                        for i in (from..levels).rev() { self.comp(b, i, c, true); }
                        if kp == 0 {
                            self.toggle_first(b, c, j);
                        } else if kp == 1 {
                            // level 1's bit flips under the (virtual) top level: toggle by lit(n-1) & lit(n-2)
                            let (q1, g1) = self.lit(n - 1, j);
                            let (q2, g2) = self.lit(n - 2, j);
                            if g1 { b.x(q1); }
                            if g2 { b.x(q2); }
                            b.ccx(q1, q2, self.pre[1]);
                            if g2 { b.x(q2); }
                            if g1 { b.x(q1); }
                        } else {
                            b.cx(self.pre[kp - 1], self.pre[kp]);
                        }
                        for i in from..levels { self.comp(b, i, j, false); }
                    }
                }
            }
            self.cur = Some(j);
            return self.pre[levels - 1];
        }
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
        if self.transient() {
            assert!(self.cur.is_none());
            return;
        }
        if let Some(c) = self.cur {
            if self.skipk() >= 2 {
                let k = self.skipk();
                for i in (k + 1..self.levels()).rev() { self.comp(b, i, c, true); }
                self.comp_first_k(b, c, true);
            } else if self.skip() {
                for i in (2..self.levels()).rev() { self.comp(b, i, c, true); }
                self.comp_first(b, c, true);
            } else {
                for i in (0..self.levels()).rev() {
                    self.comp(b, i, c, true);
                }
            }
        }
        self.cur = None;
    }
}

/// Mark a transient decoder for an n-bit value as dirty (`Dec::dirty_xor`): `clean` holds n-3 clean prefix lanes,
/// `dirty` is any lane that is not an operand of the toggles (it comes back unchanged).
pub fn dirty_pre(clean: &[QubitId], dirty: QubitId) -> Vec<QubitId> {
    assert!(!clean.contains(&dirty));
    let mut v = clean.to_vec();
    v.extend([dirty, dirty, dirty]);
    v
}

/// Target mode of `mct`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Tm {
    /// target ^= AND (any target value)
    Xor,
    /// target |0> -> AND (logical-AND compute)
    Make,
    /// target AND -> |0> (measured uncompute)
    Erase,
}

/// Lane A1c: target ^= AND of literals with the chain in clean `temps` (logical ANDs, measured away); when one temp
/// short, the last step is a Barenco toggle (4 Toffoli) on the dirty lane `dq` (any qubit outside the gate; restored).
pub(crate) fn mct(b: &mut B, lits: &[(QubitId, bool)], target: QubitId, temps: &[QubitId], dq: QubitId, mode: Tm) {
    let m = lits.len();
    assert!(m >= 1);
    for &(q, g) in lits { if g { b.x(q); } }
    if m == 1 {
        b.cx(lits[0].0, target);
    } else {
        let nt = (m - 2).min(temps.len());
        let mut acc = lits[0].0;
        for i in 0..nt {
            b.and_c(acc, lits[i + 1].0, temps[i]);
            acc = temps[i];
        }
        let rest = &lits[nt + 1..];
        if rest.len() == 1 {
            match mode {
                Tm::Xor => b.ccx(acc, rest[0].0, target),
                Tm::Make => b.and_c(acc, rest[0].0, target),
                Tm::Erase => b.and_u(acc, rest[0].0, target),
            }
        } else {
            assert_eq!(rest.len(), 2, "mct: at most one temp short");
            assert!(lits.iter().all(|l| l.0 != dq) && dq != target && !temps.contains(&dq));
            b.ccx(acc, rest[0].0, dq);
            b.ccx(dq, rest[1].0, target);
            b.ccx(acc, rest[0].0, dq);
            b.ccx(dq, rest[1].0, target);
        }
        for i in (0..nt).rev() {
            let p = if i == 0 { lits[0].0 } else { temps[i - 1] };
            b.and_u(p, lits[i + 1].0, temps[i]);
        }
    }
    for &(q, g) in lits.iter().rev() { if g { b.x(q); } }
}

/// Lane A1c: the lane-less top level of a skip decoder (`skip_pre`).
pub const SKIP_LVL: QubitId = QubitId(u64::MAX - 2);

/// Mark a retained (or, wrapped in `short_pre`, short) decoder prefix as a skip decoder: `pre` holds levels 1 .. of
/// the decoder (one lane fewer); the top level (bits n-1, n-2) is never stored (lane A1c). Needs >= 3 levels.
pub fn skip_pre(pre: &[QubitId]) -> Vec<QubitId> {
    let mut v = vec![SKIP_LVL];
    v.extend_from_slice(pre);
    v
}

/// `skip_pre` with k lane-less top levels (k >= 2: level k is made from k + 2 literals, toggled with k Toffoli).
pub fn skip_pre_k(pre: &[QubitId], k: usize) -> Vec<QubitId> {
    let mut v = vec![SKIP_LVL; k];
    v.extend_from_slice(pre);
    v
}

/// Lane A1d: marker of a short2 decoder (`Dec::short2`).
pub const SHORT2_LVL: QubitId = QubitId(u64::MAX - 3);

/// Mark a skip-k prefix (`skip_pre_k`, k >= 2) holding levels k .. n-4 as a short2 decoder whose toggles use the clean
/// lane `tmp` (clean at every toggle and at the first / last level change; lane A1d).
pub fn short2_pre(pre: &[QubitId], tmp: QubitId) -> Vec<QubitId> {
    assert!(!pre.contains(&tmp));
    let mut v = pre.to_vec();
    v.push(SHORT2_LVL);
    v.push(tmp);
    v
}

/// Lane A1d: target ^= AND of literals (`mode` as in `mct`) with the chain in clean `temps` (logical ANDs, measured
/// away) as far as they go, the rest a Barenco V-chain on the dirty lanes `dirty` (any state, restored; r controls
/// left need r - 2 of them, 4 (r - 2) Toffoli). A dirty finish is always in XOR form.
pub(crate) fn mctn(b: &mut B, lits: &[(QubitId, bool)], target: QubitId, temps: &[QubitId], dirty: &[QubitId], mode: Tm) {
    let m = lits.len();
    assert!(m >= 1);
    for &(q, g) in lits { if g { b.x(q); } }
    if m == 1 {
        b.cx(lits[0].0, target);
    } else {
        let nt = (m - 2).min(temps.len());
        let mut acc = lits[0].0;
        for i in 0..nt {
            b.and_c(acc, lits[i + 1].0, temps[i]);
            acc = temps[i];
        }
        let mut x: Vec<QubitId> = vec![acc];
        x.extend(lits[nt + 1..].iter().map(|l| l.0));
        let r = x.len();
        if r == 2 {
            match mode {
                Tm::Xor => b.ccx(x[0], x[1], target),
                Tm::Make => b.and_c(x[0], x[1], target),
                Tm::Erase => b.and_u(x[0], x[1], target),
            }
        } else {
            assert!(dirty.len() >= r - 2, "mctn: {} dirty lanes for {} controls", dirty.len(), r);
            let a = &dirty[..r - 2];
            for &q in a {
                assert!(lits.iter().all(|l| l.0 != q) && q != target && !temps.contains(&q), "mctn: dirty lane in the gate");
            }
            let mid = |b: &mut B| {
                for i in (1..r - 2).rev() { b.ccx(x[i + 1], a[i - 1], a[i]); }
                b.ccx(x[0], x[1], a[0]);
                for i in 1..r - 2 { b.ccx(x[i + 1], a[i - 1], a[i]); }
            };
            b.ccx(x[r - 1], a[r - 3], target);
            mid(b);
            b.ccx(x[r - 1], a[r - 3], target);
            mid(b);
        }
        for i in (0..nt).rev() {
            let p = if i == 0 { lits[0].0 } else { temps[i - 1] };
            b.and_u(p, lits[i + 1].0, temps[i]);
        }
    }
    for &(q, g) in lits.iter().rev() { if g { b.x(q); } }
}

/// Mark a decoder prefix of n-2 lanes as a short retained decoder (`Src::pre` / `clear_onehot_dec`): the last lane
/// is repeated, which no ordinary retained prefix can be.
pub fn short_pre(pre: &[QubitId]) -> Vec<QubitId> {
    assert!(!pre.is_empty());
    let mut v = pre.to_vec();
    v.push(*pre.last().unwrap());
    v
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

/// t ^= [v in [lo, hi]] (inclusive interval, classical bounds)
fn in_range(b: &mut B, v: &[QubitId], lo: isize, hi: isize, t: QubitId, chain: &[QubitId]) {
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

/// Lane A1c: a ladder source lane that is the constant 0 and has no qubit. Allowed at ladder lane 0 only, where the
/// carry-in is c0 = 0 as well: the cell (ordinary or masked) is then the identity with carry out 0, so it is skipped
/// and the carry into lane 1 stays on the running wire c0; the lane's source toggles are kept.
pub const ZERO_SRC: QubitId = QubitId(u64::MAX - 1);

fn zero_lane(ld: &Lad, l: usize) -> bool {
    let z = ld.s[l] == ZERO_SRC;
    // FH1-805: zero source lanes form a prefix from ladder lane 0 (the S7 MSB-window cut skips lanes [0, c))
    assert!(!z || l == 0 || ld.s[l - 1] == ZERO_SRC, "zero source lanes must be a prefix from ladder lane 0");
    z
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
    if ld.f0 || ld.srcs.is_empty() || ld.sc.chain.len() < 2 || zero_lane(ld, l) { return false; }
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
    if masked(ld, l) || ld.g.is_empty() || zero_lane(ld, l) {
        return None;
    }
    let k = (0..l).filter(|&m| !masked(ld, m) && !zero_lane(ld, m)).count();
    (k < ld.g.len()).then_some(k)
}

/// Wire holding c_l (carry into ladder lane l).
fn carry_wire(ld: &Lad, l: usize) -> QubitId {
    let mut w = ld.c0;
    let mut k = 0;
    for m in 0..l {
        if !masked(ld, m) && !zero_lane(ld, m) {
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
fn toggles(b: &mut B, ld: &Lad, decs: &mut [Dec], l: usize, pre: bool) {
    for (si, s) in ld.srcs.iter().enumerate() {
        if l >= s.lo && l < s.hi {
            if !pre && !s.late {
                continue;
            }
            let j = s.tv(l);
            if j >= 0 && (j as usize) < (1usize << s.v.len()) {
                let target = if s.late && pre { ld.t[l] } else { ld.sc.f };
                if decs[si].dirty_xor() {
                    decs[si].xor_into_dirty(b, j as usize, target);
                } else if decs[si].short2() {
                    decs[si].xor_short2(b, j as usize, target);
                } else if decs[si].pre.len() == decs[si].n() - 2 {
                    decs[si].xor_into(b, j as usize, target);
                } else if decs[si].short() {
                    let (p, (q, neg)) = decs[si].goto_short(b, j as usize);
                    let neg = neg ^ super::froghop_one::a1b_mut("short");
                    if neg { b.x(q); }
                    b.ccx(p, q, target);
                    if neg { b.x(q); }
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
    mup_impl(b, ld, false, None, false, None)
}

/// Paired ladder form: leave the end mask and final decoder prefix live across
/// a middle region that does not read either scratch object.
pub fn mup_mid(b: &mut B, ld: &Lad) -> Vec<G> {
    mup_impl(b, ld, true, None, false, None)
}

/// In a paired inverse, the ordinary MAJ writes the exact carry measured by
/// the forward rolling chain. Put the phase repair on that regenerated wire.
pub fn mup_mid_repair(b: &mut B, ld: &Lad, carry_receipts: &[BitId]) -> Vec<G> {
    mup_impl(b, ld, true, None, false, Some(carry_receipts))
}

pub fn mup_mid_from(b: &mut B, ld: &Lad, start: usize) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, Some(start), false, None)
}

pub fn mup_mid_from_repair(b: &mut B, ld: &Lad, start: usize, carry_receipts: &[BitId]) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, Some(start), false, Some(carry_receipts))
}

pub fn mup_mid_spare_masked_from(b: &mut B, ld: &Lad, start: Option<usize>) -> Vec<G> {
    assert_eq!(ld.srcs.len(), 1);
    mup_impl(b, ld, true, start, true, None)
}

pub fn clear_onehot_dec(b: &mut B, v: &[QubitId], pre: &[QubitId], start: usize) {
    let mut dec = Dec { v, pre, cur: Some(start) };
    dec.clear(b);
}

fn mup_impl(b: &mut B, ld: &Lad, mid: bool, start: Option<usize>, bank_masked: bool,
            repair: Option<&[BitId]>) -> Vec<G> {
    let l_n = ld.t.len();
    assert_eq!(ld.s.len(), l_n);
    if let Some(bits) = repair { assert!(bits.len() <= l_n); }
    b.begin();
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: start }).collect();
    if ld.f0 {
        b.x(ld.sc.f);
    }
    let ordinary_total = if bank_masked { (0..l_n).filter(|&i| !masked(ld, i) && !zero_lane(ld, i)).count() } else { 0 };
    let mut masked_seen = 0usize;
    let mut l = 0;
    while l < l_n {
        let x = carry_wire(ld, l);
        toggles(b, ld, &mut decs, l, true);
        if pi_pair(ld, l) {
            masked_pair_up(b, ld, l, x);
            toggles(b, ld, &mut decs, l, false);
            clear_ended(b, ld, &mut decs, l, true);
            toggles(b, ld, &mut decs, l + 1, true);
            toggles(b, ld, &mut decs, l + 1, false);
            if !(mid && l + 2 == l_n) { clear_ended(b, ld, &mut decs, l + 1, true); }
            l += 2;
            continue;
        }
        if zero_lane(ld, l) {
            // Constant-0 source with carry-in 0: identity, carry out 0 (stays on c0).
            assert!(repair.map_or(true, |bits| bits.is_empty()), "repair on a zero source lane");
        } else if skip_zero_pi_lane(ld, l) {
            // Both the masked cell and its return are identity on this lane.
        } else if masked(ld, l) {
            let bank_idx = ordinary_total + masked_seen;
            masked_seen += 1;
            if bank_masked && bank_idx < ld.g.len() {
                let (t, s) = (ld.t[l], ld.s[l]);
                b.cx(x, t);
                b.cx(x, s);
                b.and_c(t, s, ld.g[bank_idx]);
                b.ccx(ld.sc.f, ld.g[bank_idx], x);
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
        toggles(b, ld, &mut decs, l, false);
        if !(mid && l + 1 == l_n) {
            clear_ended(b, ld, &mut decs, l, true);
        }
        l += 1;
    }
    if !mid { f_end(b, ld); }
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

/// Return pass. `g = Some(q)`: write the (masked) sum where q = 1, restore elsewhere; None: exact inverse of `mup`.
pub fn mdown(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    mdown_impl(b, ld, g, false, None)
}

pub fn mdown_mid(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    mdown_impl(b, ld, g, true, None)
}

pub fn mdown_mid_probe(b: &mut B, ld: &Lad, g: Option<QubitId>, ta: QubitId, dl: QubitId,
                       pb0: usize, pb1: usize) -> Vec<G> {
    mdown_impl(b, ld, g, true, Some((ta, dl, pb0, pb1)))
}

fn mdown_impl(b: &mut B, ld: &Lad, g: Option<QubitId>, mid: bool,
              probe: Option<(QubitId, QubitId, usize, usize)>) -> Vec<G> {
    let l_n = ld.t.len();
    assert!(g.is_none() || ld.srcs.iter().all(|s| !s.late), "late sources only in compare passes");
    b.begin();
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| {
        let cur = if mid && s.hi == l_n {
            (s.lo..s.hi).rev().map(|l| s.tv(l))
                .find(|&j| j >= 0 && (j as usize) < (1usize << s.v.len()))
                .map(|j| j as usize)
        } else { None };
        let mut dec = Dec { v: &s.v, pre: &s.pre, cur };
        if dec.transient() { dec.cur = None; }
        dec
    }).collect();
    if !mid { f_end(b, ld); } // f = value after the last lane
    let mut l = l_n;
    while l > 0 {
        l -= 1;
        if l > 0 && pi_pair(ld, l - 1) {
            let lo = l - 1;
            let x = carry_wire(ld, lo);
            toggles(b, ld, &mut decs, l, false);
            toggles(b, ld, &mut decs, lo, false);
            masked_pair_down(b, ld, lo, x, g.expect("pi pair needs S2 write gate"));
            toggles(b, ld, &mut decs, l, true);
            clear_ended(b, ld, &mut decs, l, false);
            toggles(b, ld, &mut decs, lo, true);
            clear_ended(b, ld, &mut decs, lo, false);
            l = lo;
            continue;
        }
        let x = carry_wire(ld, l);
        // undo lane l's late toggles so that f = the mask lane l's cell saw
        toggles(b, ld, &mut decs, l, false);
        if zero_lane(ld, l) {
            // Constant-0 source lane: no cell (see mup_impl).
        } else if skip_zero_pi_lane(ld, l) {
            // No arithmetic on the classically inactive lane.
        } else if masked(ld, l) {
            masked_down_cell(b, ld, l, x, g);
        } else if let Some(k) = gidx(ld, l) {
            let gq = ld.g[k];
            b.cx(x, gq);
            b.and_u(ld.t[l], ld.s[l], gq);
            b.cx(x, ld.t[l]);
            b.cx(x, ld.s[l]);
            if let Some(gc) = g {
                b.cx(x, ld.s[l]);
                b.ccx(gc, ld.s[l], ld.t[l]);
                b.cx(x, ld.s[l]);
            }
        } else {
            b.ccx(x, ld.t[l], ld.s[l]);
            b.cx(ld.s[l], x);
            b.cx(ld.s[l], ld.t[l]);
            if let Some(gq) = g {
                b.cx(ld.s[l], x);
                b.ccx(gq, x, ld.t[l]);
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
        toggles(b, ld, &mut decs, l, true); // leave lane l downward: f becomes mask(l-1), late T flips undone
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

fn masked_down_cell(b: &mut B, ld: &Lad, l: usize, x: QubitId, g: Option<QubitId>) {
    let (t, s) = (ld.t[l], ld.s[l]);
    if let Some(gq) = g {
        // One temporary f&s drives both the carry undo and the sum bit.
        // Neither f nor s changes before the measurement uncompute.
        b.and_c(ld.sc.f, s, ld.sc.t);
        b.ccx(ld.sc.t, t, x);
        b.ccx(ld.sc.t, gq, t);
        b.and_u(ld.sc.f, s, ld.sc.t);
    } else {
        b.and_c(t, s, ld.sc.t);
        b.ccx(ld.sc.f, ld.sc.t, x);
        b.and_u(t, s, ld.sc.t);
    }
    b.cx(x, t);
    b.cx(x, s);
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

/// Lane A1e, the pair action of a short scan that moves x into the matching lane (`onehot_scan_short`): lanes a0, a1
/// decode 2c, 2c + 1 and p = [v >> 1 == c]; swap x with a_{v0} where p, as cswap(v0, a0, a1) cswap(p, x, a0)
/// cswap(v0, a0, a1) (3 Toffoli, no scratch).
pub(crate) fn fredkin_pair(b: &mut B, v0: QubitId, p: QubitId, x: QubitId, a0: QubitId, a1: QubitId) {
    b.cswap(v0, a0, a1);
    if !super::froghop_one::a1b_mut("e9push") { b.cswap(p, x, a0); }
    b.cswap(v0, a0, a1);
}

/// Lane A1e, the unpaired action: cswap(p & lit, x, t) = cx(t, x); t ^= p & lit & x (Barenco on the dirty lane dq,
/// any qubit outside the gate, restored); cx(t, x). 4 Toffoli, no scratch.
pub(crate) fn fredkin_single(b: &mut B, p: QubitId, lit: (QubitId, bool), x: QubitId, t: QubitId, dq: QubitId) {
    let (q, g) = lit;
    let g = g ^ super::froghop_one::a1b_mut("e9push1");
    assert!(dq != p && dq != q && dq != x && dq != t);
    b.cx(t, x);
    if g { b.x(q); }
    b.ccx(p, q, dq);
    b.ccx(dq, x, t);
    b.ccx(p, q, dq);
    b.ccx(dq, x, t);
    if g { b.x(q); }
    b.cx(t, x);
}

/// Lane A1e: `onehot_scan` with a short retained decoder (`short_pre`: no level for the value's bit 0). Lanes go in
/// pairs (j, j + 1) decoding 2c, 2c + 1, which share the decoder's last stored level p = [v >> 1 == c]:
/// `pair(b, j, p, v[0])` (the match is at j iff p & !v[0], at j + 1 iff p & v[0]); a lane without its partner in the
/// window calls `single(b, j, p, lit0)` (match iff p & lit0).
pub fn onehot_scan_short(b: &mut B, v: &[QubitId], pre: &[QubitId], lo: usize, hi: usize, off: isize,
                         mut pair: impl FnMut(&mut B, usize, QubitId, QubitId),
                         mut single: impl FnMut(&mut B, usize, QubitId, (QubitId, bool))) {
    let mut dec = Dec { v, pre, cur: None };
    assert!(dec.short(), "onehot_scan_short needs a short decoder");
    let ok = |j: usize| { let val = j as isize + off; val >= 0 && (val as usize) < (1usize << v.len()) };
    let mut j = lo;
    while j < hi {
        if !ok(j) { j += 1; continue; }
        let val = (j as isize + off) as usize;
        let (p, l0) = dec.goto_short(b, val);
        if val & 1 == 0 && j + 1 < hi && ok(j + 1) {
            pair(b, j, p, v[0]);
            j += 2;
        } else {
            single(b, j, p, l0);
            j += 1;
        }
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

#[cfg(test)]
mod a1d_kernel_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    fn xof_for(tag: &[u8]) -> sha3::Shake256Reader {
        let mut h = sha3::Shake256::default();
        h.update(tag);
        h.finalize_xof()
    }

    /// Lane A1d: short2 decoders (n = 6..=8, skip k = 2..=n-4, n >= 2k + 2) against the plain AND chain on every value of v: after
    /// every toggle (consecutive up / down walks from every start, and pseudo-random jumps) each stored level holds
    /// the AND of its literals, the target holds the XOR of [v == j] over the toggles so far, v is unchanged, the temp
    /// is clean and the phase is zero; after the clear every lane is 0.
    #[test]
    fn a1d_short2_decoder_exhaustive() {
        let mut checked = 0usize;
        for n in 6usize..=8 {
            // supported: the level-k chain (k + 2 literals) fits the n - 3 - k clean lanes plus v[0] as one dirty step
            for k in (2..=n - 4).filter(|&k| n >= 2 * k + 2) {
                let levels = n - 3;
                let top = 1usize << n;
                let mut walks: Vec<Vec<usize>> = vec![];
                for st in 0..top { walks.push((st..top.min(st + 40)).collect()); walks.push((st.saturating_sub(40)..=st).rev().collect()); }
                let mut r = 0x9876_5432u64 ^ (n * 7 + k) as u64;
                for _ in 0..64 {
                    let w: Vec<usize> = (0..24).map(|_| { r ^= r << 13; r ^= r >> 7; r ^= r << 17; (r as usize) % top }).collect();
                    walks.push(w);
                }
                for walk in &walks {
                    let mut b = B::new();
                    let v = b.alloc_n(n);
                    let lanes = b.alloc_n(levels - k);
                    let tmp = b.alloc();
                    let tgt = b.alloc();
                    let pre = short2_pre(&skip_pre_k(&lanes, k), tmp);
                    let mut dec = Dec { v: &v, pre: &pre, cur: None };
                    assert!(dec.short2() && !dec.short() && !dec.transient() && dec.levels() == levels);
                    let mut marks = vec![];
                    for &j in walk {
                        dec.xor_short2(&mut b, j, tgt);
                        marks.push(b.ops.len());
                    }
                    dec.clear(&mut b);
                    let nq = b.width() as usize;
                    for batch in 0..(top + 63) / 64 {
                        let mut xof = xof_for(b"a1d-short2");
                        let mut sim = Simulator::new(nq, 1, &mut xof);
                        let val = |sh: usize| (batch * 64 + sh) % top;
                        for (i, &q) in v.iter().enumerate() {
                            let mut w = 0u64;
                            for sh in 0..64 { if (val(sh) >> i) & 1 == 1 { w |= 1 << sh; } }
                            sim.qubits[q.0 as usize] = w;
                        }
                        let v0: Vec<u64> = v.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                        let mut at = 0;
                        let mut want_t = 0u64;
                        for (wi, &j) in walk.iter().enumerate() {
                            sim.apply_iter(b.ops[at..marks[wi]].iter());
                            at = marks[wi];
                            for sh in 0..64 { if val(sh) == j { want_t ^= 1 << sh; } }
                            for lv in k..levels {
                                let mut want = 0u64;
                                for sh in 0..64 {
                                    let x = val(sh);
                                    if (n - 2 - lv..n).all(|bit| (x >> bit) & 1 == (j >> bit) & 1) { want |= 1 << sh; }
                                }
                                assert_eq!(sim.qubits[lanes[lv - k].0 as usize], want, "n {n} k {k} level {lv} after {j}");
                            }
                            assert_eq!(sim.qubits[tgt.0 as usize], want_t, "target n {n} k {k} after {j}");
                            assert_eq!(sim.qubits[tmp.0 as usize], 0, "temp n {n} k {k}");
                            for (i, &q) in v.iter().enumerate() { assert_eq!(sim.qubits[q.0 as usize], v0[i]); }
                            assert_eq!(sim.phase, 0, "phase n {n} k {k} after {j}");
                            checked += 1;
                        }
                        sim.apply_iter(b.ops[at..].iter());
                        for &q in lanes.iter().chain([tmp].iter()) { assert_eq!(sim.qubits[q.0 as usize], 0, "lane after clear"); }
                        assert_eq!(sim.phase, 0);
                    }
                }
            }
        }
        eprintln!("A1d short2 decoders: {checked} (toggle, 64-value batch) states exact, n = 6..=8, k = 2..=n-4 with n >= 2k + 2");
    }

    /// Lane A1d: `mctn` against the AND of its literals, exhaustive over every input of 1..=8 literals (random
    /// polarities), every number of clean temps 0..=m-2 with enough dirty lanes, every mode: target ^= AND (Make: from
    /// 0, Erase: to 0), literals, temps and random dirty lanes restored, zero phase.
    #[test]
    fn a1d_mctn_exhaustive() {
        let mut r = 0x5151_aa77u64;
        let mut checked = 0usize;
        for m in 1usize..=8 {
            for nt in 0..=m.saturating_sub(2) {
                for mode in [Tm::Xor, Tm::Make, Tm::Erase] {
                    let mut b = B::new();
                    let x = b.alloc_n(m);
                    let tgt = b.alloc();
                    let temps = b.alloc_n(nt);
                    let dirty = b.alloc_n(m);
                    let negs: Vec<bool> = (0..m).map(|_| { r ^= r << 13; r ^= r >> 7; r ^= r << 17; r & 1 == 1 }).collect();
                    let lits: Vec<(QubitId, bool)> = x.iter().zip(&negs).map(|(&q, &g)| (q, g)).collect();
                    mctn(&mut b, &lits, tgt, &temps, &dirty, mode);
                    let nq = b.width() as usize;
                    let rows = 1usize << (m + 1);
                    for batch in 0..(rows + 63) / 64 {
                        let mut xof = xof_for(b"a1d-mctn");
                        let mut sim = Simulator::new(nq, 1, &mut xof);
                        let mut init = vec![0u64; nq];
                        let mut want = 0u64;
                        let mut live = 0u64;
                        for sh in 0..64 {
                            let row = (batch * 64 + sh) % rows;
                            let xs = row & ((1 << m) - 1);
                            let t0 = (row >> m) & 1;
                            for i in 0..m { if (xs >> i) & 1 == 1 { init[x[i].0 as usize] |= 1 << sh; } }
                            let and = (0..m).all(|i| (((xs >> i) & 1) == 1) != negs[i]);
                            let ok = match mode { Tm::Xor => true, Tm::Make => t0 == 0, Tm::Erase => (t0 == 1) == and };
                            if !ok { continue; }
                            live |= 1 << sh;
                            if t0 == 1 { init[tgt.0 as usize] |= 1 << sh; }
                            if (t0 == 1) ^ and { want |= 1 << sh; }
                        }
                        for &q in &dirty { r ^= r << 13; r ^= r >> 7; r ^= r << 17; init[q.0 as usize] = r; }
                        // shots outside the mode's contract get a valid input too (their lanes are masked out below)
                        sim.qubits.copy_from_slice(&init);
                        sim.apply_iter(b.ops.iter());
                        assert_eq!(sim.qubits[tgt.0 as usize] & live, want & live, "m {m} nt {nt}");
                        for q in x.iter().chain(dirty.iter()) { assert_eq!(sim.qubits[q.0 as usize], init[q.0 as usize]); }
                        for &q in &temps { assert_eq!(sim.qubits[q.0 as usize] & live, 0); }
                        assert_eq!(sim.phase & live, 0, "phase m {m} nt {nt}");
                        checked += live.count_ones() as usize;
                    }
                }
            }
        }
        eprintln!("A1d mctn: {checked} exact (shot, gate) cases, m = 1..=8");
    }
}

#[cfg(test)]
mod a1c_skip_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    /// Lane A1c: skip decoders (retained n = 4..=8, short n = 5..=8) against the plain AND chain on every value of v:
    /// after every goto (consecutive up / down walks from every start, and pseudo-random jumps) each stored level
    /// holds the AND of its literals, v is unchanged, the phase is zero; after the clear every prefix lane is 0.
    /// The transitions are exercised through the gate stream (64 shots = 64 values of v per batch).
    #[test]
    fn a1c_skip_decoder_exhaustive() {
        let mut checked = 0usize;
        for (n, short, k) in (4usize..=8).flat_map(|n| [false, true].into_iter().flat_map(move |s| (1usize..=3).map(move |k| (n, s, k)))) {
            {
                let levels = if short { n - 2 } else { n - 1 };
                // supported shapes: k = 1 needs 3 levels; k >= 2 needs k + 3 <= n and enough lanes above level k
                if short && n < 5 { continue; }
                if k == 1 && levels < 3 { continue; }
                if k >= 2 && (k + 3 > n || levels <= k || levels - 1 - k + 1 < k) { continue; }
                let mut walks: Vec<Vec<usize>> = vec![];
                let top = 1usize << n;
                for st in 0..top { walks.push((st..top.min(st + 40)).collect()); walks.push((st.saturating_sub(40)..=st).rev().collect()); }
                let mut r = 0x1234_5678u64 ^ n as u64;
                for _ in 0..64 {
                    let w: Vec<usize> = (0..24).map(|_| { r ^= r << 13; r ^= r >> 7; r ^= r << 17; (r as usize) % top }).collect();
                    walks.push(w);
                }
                for walk in &walks {
                    let mut b = B::new();
                    let v = b.alloc_n(n);
                    let lanes = b.alloc_n(levels - k);
                    let mut pre = skip_pre_k(&lanes, k);
                    if short { pre = short_pre(&pre); }
                    let mut dec = Dec { v: &v, pre: &pre, cur: None };
                    assert_eq!(dec.short(), short);
                    let mut marks = vec![];
                    for &j in walk {
                        if short { dec.goto_short(&mut b, j); } else { dec.goto(&mut b, j); }
                        marks.push(b.ops.len());
                    }
                    dec.clear(&mut b);
                    let nq = b.width() as usize;
                    for batch in 0..(top + 63) / 64 {
                        let mut h = sha3::Shake256::default();
                        h.update(b"a1c-skip");
                        let mut xof = h.finalize_xof();
                        let mut sim = Simulator::new(nq, 1, &mut xof);
                        let val = |sh: usize| (batch * 64 + sh) % top;
                        for (i, &q) in v.iter().enumerate() {
                            let mut w = 0u64;
                            for sh in 0..64 { if (val(sh) >> i) & 1 == 1 { w |= 1 << sh; } }
                            sim.qubits[q.0 as usize] = w;
                        }
                        let v0: Vec<u64> = v.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                        let mut at = 0;
                        for (wi, &j) in walk.iter().enumerate() {
                            sim.apply_iter(b.ops[at..marks[wi]].iter());
                            at = marks[wi];
                            for lv in k..levels {
                                let mut want = 0u64;
                                for sh in 0..64 {
                                    let x = val(sh);
                                    let ok = (n - 2 - lv..n).all(|bit| (x >> bit) & 1 == (j >> bit) & 1);
                                    if ok { want |= 1 << sh; }
                                }
                                assert_eq!(sim.qubits[lanes[lv - k].0 as usize], want, "n {n} short {short} k {k} level {lv} after goto {j} walk {walk:?}");
                            }
                            for (i, &q) in v.iter().enumerate() { assert_eq!(sim.qubits[q.0 as usize], v0[i], "v restored"); }
                            assert_eq!(sim.phase, 0, "phase n {n} short {short} goto {j}");
                            checked += 1;
                        }
                        sim.apply_iter(b.ops[at..].iter());
                        for &q in &lanes { assert_eq!(sim.qubits[q.0 as usize], 0, "lane after clear n {n} short {short}"); }
                        assert_eq!(sim.phase, 0, "phase after clear n {n} short {short}");
                    }
                }
            }
        }
        eprintln!("A1c skip decoders: {checked} (goto, 64-value batch) states exact, n = 4..=8, retained and short, k = 1..=3");
    }
}
