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

/// Diagnostic only; empty-environment builds emit no profile and exactly the same gates.
pub const L3_MASK_PROFILE: bool = false;
fn l3_profile() -> bool {
    static P: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_L3_MASK_PROFILE").map_or(L3_MASK_PROFILE, |s| s == "1")
    });
    *P
}
fn l3_cell(b: &B, ld: &Lad, l: usize, pass: &str, banked: bool, pre: f64, cell: f64, post: f64) {
    if !l3_profile() { return; }
    let (slot, stage) = super::greedyfrog::l3_profile_context();
    eprintln!("L3CELL\t{slot}\t{stage}\t{pass}\t{l}\t{}\t{}\t{}\t{pre}\t{cell}\t{post}\t{}\t{}\t{}",
        usize::from(masked(ld, l)), usize::from(banked), ld.t.len(), b.live, ld.g.len(), masked_prefix(ld));
}

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
        } else if self.d.abs() == 2 {
            // GAP-MASK: d = +-2 reads v = the length >> 1 and toggles f at the first lane of each pair (and at the window's first)
            let j = self.a + (self.d / 2) * l as isize;
            let g = 1isize << super::greedyfrog_model::GAP_LOG;
            if j < 0 { -1 } else if j & (g - 1) == if self.d < 0 { g - 1 } else { 0 } || l == self.lo { j >> super::greedyfrog_model::GAP_LOG } else { -1 }
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
        let levels = n - 1;
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
        if self.pre.len() == self.n() - 2 {
            assert!(self.cur.is_none());
            return;
        }
        if let Some(c) = self.cur {
            for i in (0..self.n() - 1).rev() {
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
    ld.srcs.iter().any(|s| l >= s.lo && l < s.hi) || (l < LAD_EXT.with(|c| c.get()) && !ld.srcs.is_empty())
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
fn toggles(b: &mut B, ld: &Lad, decs: &mut [Dec], l: usize, pre: bool) {
    if pre {
        LAD_TOGS.with(|c| for (tl, qs, neg) in c.borrow().iter() {
            if *tl == l {
                for &q in qs { b.cx(q, ld.sc.f); }
                if *neg { b.x(ld.sc.f); }
            }
        });
    }
    for (si, s) in ld.srcs.iter().enumerate() {
        if l >= s.lo && l < s.hi {
            if !pre && !s.late {
                continue;
            }
            let j = s.tv(l);
            if j >= 0 && (j as usize) < (1usize << s.v.len()) {
                let target = if s.late && pre { ld.t[l] } else { ld.sc.f };
                if decs[si].pre.len() == decs[si].n() - 2 {
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

pub fn onehot_goto(b:&mut B,v:&[QubitId],pre:&[QubitId],j:usize){let mut dec=Dec{v,pre,cur:None};dec.goto(b,j);}
pub fn mup_mid_bank_from(b:&mut B,ld:&Lad,bank:&[QubitId],start:Option<usize>)->Vec<G>{assert!(start.is_none()||ld.srcs.len()==1);mup_impl_nc(b,ld,true,start,false,None,false,bank,None)}

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
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: start }).collect();
    if ld.f0 {
        b.x(ld.sc.f);
    }
    let ordinary_total = if bank_masked { (0..l_n).filter(|&i| !masked(ld, i)).count() } else { 0 };
    let mut masked_seen = 0usize;
    let mut l = 0;
    while l < l_n {
        let x = carry_wire(ld, l);
        let l3p = b.mark_pos();
        toggles(b, ld, &mut decs, l, true);
        let l3pre = if l3_profile() { b.diagnostic_expected_from(l3p) } else { 0.0 };
        let l3c = b.mark_pos();
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
                // negative control for the gate tests only: P3_BREAK=1 takes the carry's t literal from s
                let tl = if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |v| v.trim() == "1") { s } else { t };
                b.ccx(bank[k], tl, x);
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
        let l3cost = if l3_profile() { b.diagnostic_expected_from(l3c) } else { 0.0 };
        let l3e = b.mark_pos();
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
        toggles(b, ld, &mut decs, l, false);
        if !(mid && (l + 1 == l_n || DEC_KEEP.with(|c| c.get()))) {
            clear_ended(b, ld, &mut decs, l, true);
        }
        if l3_profile() { l3_cell(b, ld, l, "up", fs_idx(ld, l, bank).is_some(), l3pre, l3cost, b.diagnostic_expected_from(l3e)); }
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
    roll_fwd_from(b,ld,g_ord,g_masked,roll_masked,nc,lanes,top,None)
}
pub fn roll_fwd_from(b: &mut B, ld: &Lad, g_ord: QubitId, g_masked: QubitId, roll_masked: bool, nc: bool,
                lanes: &[QubitId], top: Option<(QubitId, QubitId)>, start:Option<usize>) -> RollRec {
    let l_n = ld.t.len();
    assert_eq!(ld.s.len(), l_n);
    assert!(l_n >= 1 && !ld.f0 && ld.srcs.len() <= 1 && (ld.srcs.len() == 1 || !roll_masked));
    assert!(ld.srcs.iter().all(|s| !s.late && s.d != 0 && s.lo == 0), "ROLL-FWD: one early non-pi source at lane 0");
    let m = (0..l_n).take_while(|&l| masked(ld, l)).count();
    assert!((m..l_n).all(|l| !masked(ld, l)), "ROLL-FWD: masked lanes must form a prefix");
    let nc = nc_top(ld, nc);
    assert!(!(nc && top.is_some()));
    assert_eq!(lanes.len(), if roll_masked { 1 } else { 2 });
    let mut rec = RollRec { rc: vec![None; l_n], fb: None };
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: start }).collect();
    let start = if roll_masked { 0 } else { m };
    if !roll_masked {
        // stage 1: the masked prefix's up pass in the forward's frame (the complement of the I-ladder's)
        if !ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
        for l in 0..m {
            toggles(b, ld, &mut decs, l, true);
            masked_up_cell(b, ld, l, ld.c0);
            toggles(b, ld, &mut decs, l, false);
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
        let l3p = b.mark_pos();
        toggles(b, ld, &mut decs, l, true);
        let l3pre = if l3_profile() { b.diagnostic_expected_from(l3p) } else { 0.0 };
        let l3c = b.mark_pos();
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
            ord_write(b, g_ord, l, l_n, s, t);
            if let Some(n) = nxt {
                b.cx(cur, t);
                b.and_c(t, s, n);
                b.cx(cur, t);
            }
            b.cx(cur, s);
            if let Some(n) = nxt { b.cx(cur, n); }
        }
        let l3cost = if l3_profile() { b.diagnostic_expected_from(l3c) } else { 0.0 };
        let l3e = b.mark_pos();
        toggles(b, ld, &mut decs, l, false);
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
        if l3_profile() { l3_cell(b, ld, l, "roll", false, l3pre, l3cost, b.diagnostic_expected_from(l3e)); }
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
            toggles(b, ld, &mut decs, l, false);
            masked_down_cell(b, ld, l, ld.c0, Some(g_masked));
            toggles(b, ld, &mut decs, l, true);
            clear_ended(b, ld, &mut decs, l, false);
        }
        if !ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    }
    rec
}

/// STALL-PAIR: a ladder's masked prefix runs to lane `ext` (past its sources' windows) and each toggle
/// (lane, controls, negated) flips f on entering that lane: f ^= XOR(controls) ^ negated.
pub struct LadX {
    pub ext: usize,
    pub togs: Vec<(usize, Vec<QubitId>, bool)>,
    /// ORD-IDLE: the toggles past the prefix's end, after which f = 1 on every passing shot (None: f is not known there)
    pub fix: Option<Vec<(Vec<QubitId>, bool)>>,
}
thread_local! {
    static LAD_EXT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// CK-LADDER: the masked prefix's decoder stays live between its up and down passes
    static DEC_KEEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static LAD_TOGS: std::cell::RefCell<Vec<(usize, Vec<QubitId>, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
    static LAD_FIX: std::cell::RefCell<Option<Vec<(Vec<QubitId>, bool)>>> = const { std::cell::RefCell::new(None) };
}
pub fn set_ladx(x: Option<LadX>) {
    match x {
        Some(x) => {
            LAD_EXT.with(|c| c.set(x.ext));
            LAD_TOGS.with(|c| *c.borrow_mut() = x.togs);
            LAD_FIX.with(|c| *c.borrow_mut() = x.fix);
        }
        None => {
            LAD_EXT.with(|c| c.set(0));
            LAD_TOGS.with(|c| c.borrow_mut().clear());
            LAD_FIX.with(|c| *c.borrow_mut() = None);
        }
    }
}
/// ORD-IDLE: the masked scratch is idle across a ladder's ordinary section and joins its carry pool: c0 (|0> once a bank lane
/// carries), the cell temp t (|0> unless it is the hosted |1> lane), and f, which reads 1 there on every passing shot.
/// Dev override `WL_ORD_IDLE=0|1`.
pub const ORD_IDLE: bool = true;
fn ord_idle_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_ORD_IDLE").map_or(ORD_IDLE, |v| v.trim() == "1")
    });
    *E
}
/// Lanes joining the pool besides c0.
pub fn ord_idle_fixed(ld: &Lad) -> usize {
    if !ord_idle_on() { return 0; }
    usize::from(TEMP_ONE_HOST.with(|h| h.get()) != Some(ld.sc.t)) + usize::from(LAD_FIX.with(|c| c.borrow().is_some()))
}
pub fn ord_idle_c0() -> usize { usize::from(ord_idle_on()) }
/// ORD-DEC: with a bank (the passes that own their decoders) the retained decoder prefix is erased before the ordinary section
/// and rebuilt after it (one AND per lane) instead of idling across it. Dev override `WL_ORD_DEC=0|1`.
fn ord_dec_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_ORD_DEC").map_or(true, |v| v.trim() == "1")
    });
    ord_idle_on() && *E
}
thread_local! { static ORD_DEC_USE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
pub fn set_ord_dec(on: bool) { ORD_DEC_USE.with(|c| c.set(on)); }
pub fn ord_dec_use() -> bool { ORD_DEC_USE.with(|c| c.get()) }
pub fn ord_idle_bank(ld: &Lad) -> usize {
    if !ord_idle_on() { return 0; }
    1 + if ORD_DEC_USE.with(|c| c.get()) { ord_dec_lanes(ld) } else { 0 }
}
pub fn ord_dec_lanes(ld: &Lad) -> usize {
    if ord_dec_on() { ld.srcs.iter().filter(|s| s.pre.len() + 1 == s.v.len()).map(|s| s.pre.len()).sum::<usize>() } else { 0 }
}
fn ord_dec_clear(b: &mut B, decs: &mut [Dec]) -> Vec<QubitId> {
    if !ORD_DEC_USE.with(|c| c.get()) { return vec![]; }
    let mut l = vec![];
    for d in decs.iter_mut() {
        if d.pre.len() + 1 == d.v.len() {
            d.clear(b);
            l.extend_from_slice(d.pre);
        }
    }
    l
}
fn ord_fix(b: &mut B, ld: &Lad) {
    LAD_FIX.with(|c| if let Some(fx) = c.borrow().as_ref() {
        for (qs, neg) in fx {
            for &q in qs { b.cx(q, ld.sc.f); }
            if *neg { b.x(ld.sc.f); }
        }
    });
}
fn ord_run(b: &mut B, ld: &Lad, m: usize, bank: &[QubitId], cin: QubitId, pool: &[QubitId], rc: &[Option<BitId>], nc: bool,
           extra: &[QubitId], top: impl FnOnce(&mut B, QubitId)) {
    let on = ord_idle_on() && m < ld.t.len();
    let mut p = pool.to_vec();
    if on { p.extend_from_slice(extra); }
    let ff = on && LAD_FIX.with(|c| c.borrow().is_some());
    if on {
        if !bank.is_empty() { p.push(ld.c0); }
        if TEMP_ONE_HOST.with(|h| h.get()) != Some(ld.sc.t) { p.push(ld.sc.t); }
        if ff {
            ord_fix(b, ld);
            if !(cfg!(test) && std::env::var("ORD_BREAK").map_or(false, |v| v.trim() == "1")) { b.x(ld.sc.f); }
            p.push(ld.sc.f);
        }
        super::greedyfrog::zero_probe(b, &p);
    }
    ck_ordinary(b, &ld.t[m..], &ld.s[m..], cin, &p, rc, nc, top);
    if on {
        super::greedyfrog::zero_probe(b, &p);
        if ff {
            if !(cfg!(test) && std::env::var("ORD_BREAK").map_or(false, |v| v.trim() == "1")) { b.x(ld.sc.f); }
            ord_fix(b, ld);
        }
    }
}
thread_local! {
    /// STALL-PAIR: overrides the ordinary lanes' write gate of the ladders run while set (ALWAYS: no gate)
    static G_ORD: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
    /// STALL-PAIR: the last n ordinary ladder lanes write under this literal (q, negated) instead
    static G_TAIL: std::cell::Cell<Option<(usize, QubitId, bool)>> = const { std::cell::Cell::new(None) };
}
pub fn set_ord_gate(g: Option<QubitId>, tail: Option<(usize, QubitId, bool)>) {
    G_ORD.with(|c| c.set(g));
    G_TAIL.with(|c| c.set(tail));
}
/// t ^= g & src on an ordinary lane l of a ladder of l_n lanes (with the STALL-PAIR overrides).
fn ord_write(b: &mut B, g: QubitId, l: usize, l_n: usize, src: QubitId, t: QubitId) {
    if let Some((n, q, neg)) = G_TAIL.with(|c| c.get()) {
        if l + n >= l_n {
            if neg { b.x(q); }
            b.ccx(q, src, t);
            if neg { b.x(q); }
            return;
        }
    }
    let g = G_ORD.with(|c| c.get()).unwrap_or(g);
    if g == ALWAYS { b.cx(src, t); } else { b.ccx(g, src, t); }
}

/// CK-LADDER: the smallest pool for `carries` carries of an ordinary section.
pub fn ck_need(carries: usize) -> usize {
    let mut r = 0;
    while r * (r + 1) / 2 < carries { r += 1; }
    r
}
/// CK-LADDER: closed segment sizes and the top segment's size for `carries` carries on r lanes (as few segments as fit;
/// a segment that holds i anchors has r - i lanes).
pub fn ck_plan(carries: usize, r: usize) -> (Vec<usize>, usize) {
    if carries == 0 { return (vec![], 0); }
    let mut m = 1;
    while (0..m).map(|i| r - i).sum::<usize>() < carries { m += 1; }
    let top_n = (r + 1 - m).min(carries);
    let mut sizes = vec![];
    let mut left = carries - top_n;
    for i in 0..m - 1 {
        let k = left.min(r - i);
        sizes.push(k);
        left -= k;
    }
    assert_eq!(left, 0);
    sizes.retain(|&k| k > 0);
    (sizes, top_n)
}
/// Negative controls for the gate tests only (CK_BREAK=k): 1 drops the anchors' phase repair, 2 drops the regenerated
/// carries' reach (the repair reads the anchor below), 3 drops one forward receipt's repair.
fn ck_break(k: u32) -> bool {
    cfg!(test) && std::env::var("CK_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// CK-LADDER: the ordinary section of an inverse ladder (t[l] += s[l], carry-in on `cin`, no write gate; `rc` the forward's
/// receipts per carry formed; `nc`: the top lane forms no carry), on r clean lanes, for any length up to r (r + 1) / 2.
/// A segment's carries are formed on the pool, its lanes are written and its interior carries erased by measurement
/// while their predecessors are live; its last carry stays as the next segment's anchor. The top segment's carries all
/// erase freely after `top` has read the carry out. An anchor is erased last, top down: its X outcome is 1 on half the
/// shots, and only there its segment's carries are formed again from the anchor below, on the written targets, to apply
/// the phase. So N carries cost N + (N - r) / 2 expected Toffoli, where the Cuccaro fallback costs 2 per lane past the pool.
pub fn ck_ordinary(b: &mut B, t: &[QubitId], s: &[QubitId], cin: QubitId, pool: &[QubitId], rc: &[Option<BitId>],
                   nc: bool, top: impl FnOnce(&mut B, QubitId)) {
    let n = t.len();
    let carries = if nc { n.saturating_sub(1) } else { n };
    // (the masked prefix's segments may have held the pool wider than the chain needs)
    let r = pool.len().min(carries);
    assert!(r >= ck_need(carries), "CK-LADDER: {carries} carries on {r} lanes");
    let (sizes, _) = ck_plan(carries, r);
    let mut free: Vec<QubitId> = pool[..r].to_vec();
    // c_(l+1) on q from the unwritten target, x = c_l: x ^ (t ^ x)(s ^ x)
    let form = |b: &mut B, x: QubitId, l: usize, q: QubitId| {
        b.cx(x, t[l]);
        b.cx(x, s[l]);
        b.and_c(t[l], s[l], q);
        b.cx(x, t[l]);
        b.cx(x, s[l]);
        b.cx(x, q);
    };
    let erase = |b: &mut B, x: QubitId, l: usize, q: QubitId| {
        b.cx(x, q);
        b.cx(x, t[l]);
        b.cx(x, s[l]);
        b.and_u(t[l], s[l], q);
        b.cx(x, t[l]);
        b.cx(x, s[l]);
    };
    // t[l] ^= s[l] ^ x; on a written target t' the same carry is x ^ (t' ^ s)(s ^ x)
    let write = |b: &mut B, x: QubitId, l: usize| {
        b.cx(x, s[l]);
        ord_write(b, ALWAYS, l, n, s[l], t[l]);
        b.cx(x, s[l]);
    };
    let flip_w = |b: &mut B, x: QubitId, l: usize| {
        b.cx(s[l], t[l]);
        b.cx(x, s[l]);
    };
    let unflip_w = |b: &mut B, x: QubitId, l: usize| {
        b.cx(x, s[l]);
        b.cx(s[l], t[l]);
    };
    let receipt = |b: &mut B, l: usize, q: QubitId| {
        if let Some(Some(bit)) = rc.get(l) {
            if !(ck_break(3) && l == carries / 2) { b.z_if(q, *bit); }
        }
    };
    // (anchor below, first lane, carries, the segment's last carry)
    let mut segs: Vec<(QubitId, usize, usize, QubitId)> = vec![];
    let mut cur = cin;
    let mut l = 0;
    for &k in &sizes {
        let (start, a) = (l, cur);
        let mut held: Vec<QubitId> = vec![];
        for _ in 0..k {
            let q = free.pop().expect("CK-LADDER lane");
            form(b, cur, l, q);
            receipt(b, l, q);
            held.push(q);
            cur = q;
            l += 1;
        }
        for j in (0..k).rev() {
            write(b, if j == 0 { a } else { held[j - 1] }, start + j);
            if j > 0 {
                erase(b, if j == 1 { a } else { held[j - 2] }, start + j - 1, held[j - 1]);
                free.push(held[j - 1]);
            }
        }
        segs.push((a, start, k, cur));
    }
    // the top segment
    let (start, a) = (l, cur);
    let mut held: Vec<QubitId> = vec![];
    while l < carries {
        let q = free.pop().expect("CK-LADDER lane");
        form(b, cur, l, q);
        receipt(b, l, q);
        held.push(q);
        cur = q;
        l += 1;
    }
    top(b, cur);
    if nc && n > 0 {
        write(b, cur, n - 1);
    }
    for j in (0..held.len()).rev() {
        let x = if j == 0 { a } else { held[j - 1] };
        erase(b, x, start + j, held[j]);
        write(b, x, start + j);
        free.push(held[j]);
    }
    // the anchors, top down
    for &(a, st, k, ck) in segs.iter().rev() {
        let m = b.fresh_bits(1)[0];
        b.hmr_to(ck, m);
        free.push(ck);
        if ck_break(1) { continue; }
        b.push_condition(m);
        let mut x = a;
        let mut reg: Vec<QubitId> = vec![];
        for j in 0..k - 1 {
            let q = free.pop().expect("CK-LADDER lane");
            flip_w(b, x, st + j);
            b.and_c(t[st + j], s[st + j], q);
            unflip_w(b, x, st + j);
            b.cx(x, q);
            reg.push(q);
            x = q;
        }
        let lt = st + k - 1;
        b.z(x);
        flip_w(b, x, lt);
        b.cz(t[lt], s[lt]);
        unflip_w(b, x, lt);
        for j in (0..k - 1).rev() {
            let xj = if j == 0 { a } else { reg[j - 1] };
            let q = reg[j];
            b.cx(xj, q);
            flip_w(b, xj, st + j);
            b.and_u(t[st + j], s[st + j], q);
            unflip_w(b, xj, st + j);
            free.push(q);
        }
        b.pop_condition();
    }
    assert_eq!(free.len(), r, "CK-LADDER pool not returned");
}
/// CK-LADDER: masked prefix length of a ladder.
pub fn masked_prefix(ld: &Lad) -> usize {
    (0..ld.t.len()).take_while(|&l| masked(ld, l)).count()
}
/// CK-LADDER: whether the ordinary lanes run with no write gate here.
pub fn ord_gate_free() -> bool {
    G_ORD.with(|c| c.get()) == Some(ALWAYS)
}
/// CK-LADDER: lanes of the tail that must lie in the top segment.
pub fn ord_tail() -> usize {
    G_TAIL.with(|c| c.get()).map_or(0, |x| x.0)
}
/// CK-LADDER: a whole inverse ladder pass: the masked prefix's up pass (its decoder stays live), the ordinary section,
/// the masked prefix's down pass.
pub fn ck_pass(b: &mut B, ld: &Lad, bank: &[QubitId], pool: &[QubitId], roll: Option<&RollRec>, nc: bool,
               top: impl FnOnce(&mut B, QubitId)) {
    if l3_profile() {
        let (slot, stage) = super::greedyfrog::l3_profile_context();
        let m = masked_prefix(ld);
        eprintln!("L3PLAN\t{slot}\t{stage}\t{m}\t{}\t{}\t{}", ld.t.len() - m, bank.len(), pool.len());
    }
    if mask_carry_bank() && mask_carry_segments() && !bank.is_empty() && !pool.is_empty() && mask_carry_segments_compatible(ld) {
        mask_carry_segments_pass(b, ld, bank, pool, roll, nc, top);
        return;
    }
    if mask_carry_bank() && !bank.is_empty() {
        mask_carry_bank_pass(b, ld, bank, pool, roll, nc, top);
        return;
    }
    let m = masked_prefix(ld);
    let sub = Lad { t: &ld.t[..m], s: &ld.s[..m], c0: ld.c0, srcs: ld.srcs, f0: false, cmpl: ld.cmpl, sc: ld.sc, g: &[] };
    DEC_KEEP.with(|c| c.set(true));
    let ru = mup_mid_bank_roll(b, &sub, bank, roll);
    b.play(&ru, false);
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    let rc: Vec<Option<BitId>> = roll.map_or(vec![], |r| r.rc.iter().skip(m).copied().collect());
    ord_run(b, ld, m, bank, ld.c0, pool, &rc, nc, &[], top);
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    let rd = mdown_mid2_bank(b, &sub, Some(ALWAYS), Some(ALWAYS), bank);
    b.play(&rd, false);
    DEC_KEEP.with(|c| c.set(false));
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
    b.begin();
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| {
        let cur = if mid && (s.hi == l_n || DEC_KEEP.with(|c| c.get())) {
            (s.lo..s.hi).rev().map(|l| s.tv(l))
                .find(|&j| j >= 0 && (j as usize) < (1usize << s.v.len()))
                .map(|j| j as usize)
        } else { None };
        Dec { v: &s.v, pre: &s.pre,
              cur: if s.pre.len() == s.v.len() - 2 { None } else { cur } }
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
            assert_eq!(g, gm, "pi pair: one write gate");
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
        let l3p = b.mark_pos();
        toggles(b, ld, &mut decs, l, false);
        let l3pre = if l3_profile() { b.diagnostic_expected_from(l3p) } else { 0.0 };
        let l3c = b.mark_pos();
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
            if masked(ld, l) {
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
                ord_write(b, gq, l, l_n, s, t);
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
                ord_write(b, gc, l, l_n, ld.s[l], ld.t[l]);
                b.cx(x, ld.s[l]);
            }
        } else {
            b.ccx(x, ld.t[l], ld.s[l]);
            b.cx(ld.s[l], x);
            b.cx(ld.s[l], ld.t[l]);
            if let Some(gq) = g {
                b.cx(ld.s[l], x);
                ord_write(b, gq, l, l_n, x, ld.t[l]);
                b.cx(ld.s[l], x);
            }
        }
        let l3cost = if l3_profile() { b.diagnostic_expected_from(l3c) } else { 0.0 };
        let l3e = b.mark_pos();
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
        if l3_profile() { l3_cell(b, ld, l, "down", fs_idx(ld, l, bank).is_some(), l3pre, l3cost, b.diagnostic_expected_from(l3e)); }
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

thread_local! {
    /// L3 VALUE-TEMP-HOST: one explicitly borrowed |1> source lane, restored around every masked-cell use.
    /// This is set only by greedyfrog's inverse value pass, whose actual top cell is proved ordinary.
    static TEMP_ONE_HOST: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
pub fn set_temp_one_host(q: Option<QubitId>) {
    TEMP_ONE_HOST.with(|h| {
        assert!(q.is_none() || h.get().is_none(), "nested one-valued mask temporary");
        h.set(q);
    });
}
fn temp_one_flip(b: &mut B, ld: &Lad, site: u32, entering: bool) {
    if TEMP_ONE_HOST.with(|h| h.get()) != Some(ld.sc.t) { return; }
    // Per-site negative controls: 1 omits the up-cell preparation, 2 the down-cell preparation.
    let broken = cfg!(test) && entering && std::env::var("VTH_BREAK").map_or(false, |v| v.trim() == site.to_string());
    if !broken { b.x(ld.sc.t); }
}

fn masked_up_cell(b: &mut B, ld: &Lad, l: usize, x: QubitId) {
    let (t, s) = (ld.t[l], ld.s[l]);
    temp_one_flip(b, ld, 1, true);
    b.cx(x, t);
    b.cx(x, s);
    b.and_c(t, s, ld.sc.t);
    b.ccx(ld.sc.f, ld.sc.t, x);
    b.and_u(t, s, ld.sc.t);
    temp_one_flip(b, ld, 1, false);
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
    temp_one_flip(b, ld, 2, true);
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
    temp_one_flip(b, ld, 2, false);
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

/// L3 MASK-CARRY-BANK: use the existing K1 bank for carries, with immediate masked writes, instead of f & s'.
/// A banked masked cell costs 2 computed ANDs and a CCZ on half the shots when its carry is erased: 2.5 expected T
/// instead of K1's 3. The unbanked masked suffix retains the parent's in-place cells, and the ordinary section
/// retains CK-LADDER. No additional qubits, mask scans, window changes or probabilistic arithmetic shortcut.
pub const MASK_CARRY_BANK: bool = true;
fn mask_carry_bank() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_MASK_CARRY_BANK").map_or(MASK_CARRY_BANK, |v| v.trim() == "1")
    });
    *E
}

/// Test-only mutants: 1 omits the early sum write, 2 omits the measured carry's CCZ repair,
/// 3 omits the forward ROLL carry receipts. Each changes only this new rewrite site.
fn mcb_break(k: u32) -> bool {
    cfg!(test) && std::env::var("MCB_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

fn mask_carry_bank_pass(b: &mut B, ld: &Lad, bank: &[QubitId], pool: &[QubitId],
                        roll: Option<&RollRec>, nc: bool, top: impl FnOnce(&mut B, QubitId)) {
    let m = masked_prefix(ld);
    let k = bank.len();
    assert!(k > 0 && k <= m && !ld.f0 && (ord_gate_free() || m == ld.t.len()));
    assert!(ld.srcs.iter().all(|s| !s.late && s.d != 0), "MASK-CARRY-BANK: early non-pi masks only");
    DEC_KEEP.with(|c| c.set(true));
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: None }).collect();
    if ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    // q_(l+1) = c ^ f(s ^ c)(t ^ c), followed by t' = t ^ f(s ^ c).
    // The final banked carry is then the running carry for the entire unbanked suffix.
    let cin = bank[k - 1];
    for l in 0..m {
        toggles(b, ld, &mut decs, l, true);
        let carry = if l < k {
            let (t, s, q) = (ld.t[l], ld.s[l], bank[l]);
            let prev = if l == 0 { ld.c0 } else { bank[l - 1] };
            temp_one_flip(b, ld, 1, true);
            b.cx(prev, s);
            b.and_c(ld.sc.f, s, ld.sc.t);
            b.cx(prev, s);
            b.cx(prev, t);
            b.and_c(ld.sc.t, t, q);
            b.cx(prev, t);
            b.cx(prev, q);
            if !mcb_break(1) && !(m == ld.t.len() && full_mcb_break(1)) { b.cx(ld.sc.t, t); }
            b.cx(prev, s);
            b.and_u(ld.sc.f, s, ld.sc.t);
            b.cx(prev, s);
            temp_one_flip(b, ld, 1, false);
            q
        } else {
            masked_up_cell(b, ld, l, cin);
            cin
        };
        if let Some(Some(bit)) = roll.and_then(|r| r.rc.get(l)) {
            if !mcb_break(3) && !(roll_break(2) && l == m / 2) { b.z_if(carry, *bit); }
        }
        toggles(b, ld, &mut decs, l, false);
        // As in CK-LADDER's DEC_KEEP path, retain every decoder through the ordinary section.
    }
    if let Some(bit) = roll.and_then(|r| r.fb) {
        if !roll_break(3) { b.z_if(ld.sc.f, bit); }
    }
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    let rc: Vec<Option<BitId>> = roll.map_or(vec![], |r| r.rc.iter().skip(m).copied().collect());
    let ex = if m < ld.t.len() { ord_dec_clear(b, &mut decs) } else { vec![] };
    ord_run(b, ld, m, bank, cin, pool, &rc, nc, &ex, top);
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    for l in (0..m).rev() {
        toggles(b, ld, &mut decs, l, false);
        if l >= k {
            masked_down_cell(b, ld, l, cin, Some(ALWAYS));
        } else {
            let (t, s, q) = (ld.t[l], ld.s[l], bank[l]);
            let prev = if l == 0 { ld.c0 } else { bank[l - 1] };
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(q, bit);
            b.push_condition(bit);
            // On the written target, q = c ^ f(s ^ c)(t' ^ c ^ 1). This identity is valid for all
            // inputs, including f=0 and either carry value; no c=>f promise is needed.
            b.z(prev);
            b.cx(prev, s);
            b.cx(prev, t);
            b.x(t);
            if !mcb_break(2) && !(m == ld.t.len() && full_mcb_break(2)) { b.ccz(ld.sc.f, s, t); }
            b.x(t);
            b.cx(prev, t);
            b.cx(prev, s);
            b.pop_condition();
        }
        toggles(b, ld, &mut decs, l, true);
        clear_ended(b, ld, &mut decs, l, false);
    }
    if ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    DEC_KEEP.with(|c| c.set(false));
}

/// L3 non-CK coverage: the same bank rewrite on a completely masked value ladder, with no ordinary schedule.
pub const MASK_CARRY_FULL: bool = true;
fn mask_carry_full_enabled() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_MASK_CARRY_FULL").map_or(MASK_CARRY_FULL, |v| v.trim() == "1")
    });
    *E
}
fn full_mcb_break(k: u32) -> bool {
    cfg!(test) && std::env::var("FULLMCB_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
pub fn mask_carry_full_on(ld: &Lad) -> bool {
    mask_carry_full_enabled() && mask_carry_bank() && masked_prefix(ld) == ld.t.len()
}
/// Returns true only when the whole ladder was emitted. Caller supplies an ungated masked write and its unchanged
/// top-carry consumer. The empty ordinary pool makes the existing helper perform only masked arithmetic.
pub fn mask_carry_full(b: &mut B, ld: &Lad, bank: &[QubitId], roll: Option<&RollRec>,
                       top: impl FnOnce(&mut B, QubitId)) -> bool {
    if !mask_carry_full_enabled() || !mask_carry_bank() || bank.is_empty() || masked_prefix(ld) != ld.t.len() {
        return false;
    }
    if l3_profile() {
        let (slot, stage) = super::greedyfrog::l3_profile_context();
        eprintln!("L3PLAN\t{slot}\t{stage}\t{}\t0\t{}\t0", ld.t.len(), bank.len());
    }
    mask_carry_bank_pass(b, ld, bank, &[], roll, false, top);
    true
}

/// L3 MASK-CARRY-SEGMENTS: one banked anchor covers an aligned two/three-cell masked segment. Interior carries
/// borrow one/two lanes from the ordinary CK pool while it is idle. All those lanes are clean again before CK.
/// Mask recovery uses only already-retained decoder prefixes and LadX Cliffords, so the two mask scans are unchanged.
pub const MASK_CARRY_SEGMENTS: bool = true;
fn mask_carry_segments() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_MASK_CARRY_SEGMENTS").map_or(MASK_CARRY_SEGMENTS, |v| v.trim() == "1")
    });
    *E
}
/// Expected Toffoli of the masked prefix's arithmetic on `nb` bank lanes with `spare` idle pool lanes (a cell off the bank 4, a
/// segment of L cells 3 L - 1/2): the split of a ladder's lanes between anchors, the segments' interiors and the chain.
pub fn ck_masked_cost(ld: &Lad, nb: usize, spare: usize) -> f64 {
    let m = masked_prefix(ld);
    if nb == 0 { return 4.0 * m as f64; }
    if !(mask_carry_bank() && mask_carry_segments() && spare > 0 && mask_carry_segments_compatible(ld)) {
        return 4.0 * m as f64 - 1.5 * nb as f64;
    }
    let segs = mcs_plan(ld, nb, spare);
    let cov: usize = segs.iter().map(|s| s.len).sum();
    segs.iter().map(|s| 3.0 * s.len as f64 - 0.5).sum::<f64>() + 4.0 * (m - cov) as f64
}
fn mask_carry_segments_compatible(ld: &Lad) -> bool {
    ld.srcs.len() == 1 && ld.srcs.iter().all(|s| !s.late && (s.d.abs() == 1 || s.d.abs() == 2)
        && s.v.len() >= 2 && s.pre.len() == s.v.len() - 1)
}
/// Test-only mutants: 1 early writes, 2 interior phase repair, 3 anchor phase repair, 4 written-target replay frame,
/// 5 retained-prefix mask recovery, 6 initial ROLL receipts. No mutant changes the disabled path.
fn mcs_break(k: u32) -> bool {
    cfg!(test) && std::env::var("MCS_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

#[derive(Clone, Copy, Debug)]
struct MaskCarrySegment { start: usize, len: usize }

fn mcs_source_toggle(s: &Src, l: usize) -> bool {
    if l < s.lo || l >= s.hi { return false; }
    let j = s.tv(l);
    j >= 0 && (j as usize) < (1usize << s.v.len())
}
fn mcs_segment_allowed(ld: &Lad, start: usize, len: usize, spare: usize) -> bool {
    if len == 1 { return true; }
    let needed = (len - 1) * if mask_carry_products() { 2 } else { 1 };
    let s = &ld.srcs[0];
    // GAP-MASK: every second lane toggles, so a segment with one toggle past its first cell keeps that equality on the decoder
    if s.d.abs() == 2 {
        return spare >= needed && len <= 4 && (start + 1..start + len).filter(|&l| mcs_source_toggle(s, l)).count() <= 1;
    }
    if spare < needed || len > 3 { return false; }
    if len == 2 { return true; } // current endpoint equality, if any, is retained
    if s.v.len() < 3 || !(start..start + 3).all(|l| mcs_source_toggle(s, l)) { return false; }
    let j = s.tv(start + 2);
    // The last two equality values are siblings; their XOR is the current decoder's penultimate prefix.
    (s.d == 1 && j & 1 == 1) || (s.d == -1 && j & 1 == 0)
}

/// Maximize bank-covered cells with exactly `anchors` segments; unbanked gaps may align later triples cheaply.
fn mcs_plan(ld: &Lad, anchors: usize, spare: usize) -> Vec<MaskCarrySegment> {
    let m = masked_prefix(ld);
    assert!(anchors > 0 && anchors <= m);
    let stride = anchors + 1;
    let mut score: Vec<Option<usize>> = vec![None; (m + 1) * stride];
    let mut choice: Vec<usize> = vec![0; (m + 1) * stride];
    score[m * stride] = Some(0);
    for l in (0..m).rev() {
        for left in 0..=anchors {
            let at = l * stride + left;
            score[at] = score[(l + 1) * stride + left];
            if left == 0 { continue; }
            for len in 1..=4.min(m - l) {
                if !mcs_segment_allowed(ld, l, len, spare) { continue; }
                if let Some(rest) = score[(l + len) * stride + left - 1] {
                    let candidate = rest + len;
                    if score[at].map_or(true, |best| candidate >= best) {
                        score[at] = Some(candidate);
                        choice[at] = len;
                    }
                }
            }
        }
    }
    let mut result = vec![];
    let (mut l, mut left) = (0, anchors);
    while l < m && left > 0 {
        let len = choice[l * stride + left];
        if len == 0 { l += 1; }
        else { result.push(MaskCarrySegment { start: l, len }); l += len; left -= 1; }
    }
    assert_eq!(left, 0, "masked segment planner left an unused anchor");
    result
}

/// Affine STALL-PAIR mask toggles at one lane; source equalities are handled separately below.
fn mcs_ladx_toggle(b: &mut B, ld: &Lad, l: usize) {
    LAD_TOGS.with(|c| for (tl, qs, neg) in c.borrow().iter() {
        if *tl == l {
            for &q in qs { b.cx(q, ld.sc.f); }
            if *neg { b.x(ld.sc.f); }
        }
    });
}

/// Self-inverse Clifford change from the segment-end mask to one earlier cell's mask. The decoder remains at
/// the endpoint throughout. Pair: delta=E_end. Aligned triple: delta_mid=E_end, delta_first=parent(E_end).
fn mcs_mask_from_end(b: &mut B, ld: &Lad, seg: MaskCarrySegment, j: usize) {
    if j + 1 == seg.len || mcs_break(5) { return; }
    let end = seg.start + seg.len - 1;
    let s = &ld.srcs[0];
    if s.d.abs() == 2 {
        if (seg.start + j + 1..=end).any(|l| mcs_source_toggle(s, l)) { b.cx(s.pre[s.v.len() - 2], ld.sc.f); }
    } else if seg.len == 3 && j == 0 {
        assert!(mcs_segment_allowed(ld, seg.start, seg.len, 4));
        b.cx(s.pre[s.v.len() - 3], ld.sc.f);
    } else if mcs_source_toggle(s, end) {
        b.cx(s.pre[s.v.len() - 2], ld.sc.f);
    }
    for l in seg.start + j + 1..=end { mcs_ladx_toggle(b, ld, l); }
}

/// Two-AND carry formation. `written` uses the inverse recurrence on a target already updated by this cell;
/// `write` performs the initial sum update. The two flags are mutually exclusive.
fn mcs_form(b: &mut B, ld: &Lad, l: usize, prev: QubitId, q: QubitId, written: bool, write: bool) {
    assert!(!(written && write));
    let (t, s) = (ld.t[l], ld.s[l]);
    temp_one_flip(b, ld, 1, true);
    b.cx(prev, s);
    b.and_c(ld.sc.f, s, ld.sc.t);
    b.cx(prev, s);
    b.cx(prev, t);
    if written && !mcs_break(4) { b.x(t); }
    b.and_c(ld.sc.t, t, q);
    if written && !mcs_break(4) { b.x(t); }
    b.cx(prev, t);
    b.cx(prev, q);
    if write && !mcs_break(1) { b.cx(ld.sc.t, t); }
    b.cx(prev, s);
    b.and_u(ld.sc.f, s, ld.sc.t);
    b.cx(prev, s);
    temp_one_flip(b, ld, 1, false);
}

fn mcs_carry_phase(b: &mut B, ld: &Lad, l: usize, prev: QubitId, site: u32) {
    let (t, s) = (ld.t[l], ld.s[l]);
    b.z(prev);
    b.cx(prev, s);
    b.cx(prev, t);
    b.x(t);
    if !mcs_break(site) { b.ccz(ld.sc.f, s, t); }
    b.x(t);
    b.cx(prev, t);
    b.cx(prev, s);
}

fn mcs_erase_interior(b: &mut B, ld: &Lad, seg: MaskCarrySegment, j: usize, prev: QubitId, q: QubitId) {
    let bit = b.fresh_bits(1)[0];
    b.hmr_to(q, bit);
    b.push_condition(bit);
    mcs_mask_from_end(b, ld, seg, j);
    mcs_carry_phase(b, ld, seg.start + j, prev, 2);
    mcs_mask_from_end(b, ld, seg, j);
    b.pop_condition();
}

fn mask_carry_segments_pass(b: &mut B, ld: &Lad, bank: &[QubitId], pool: &[QubitId],
                            roll: Option<&RollRec>, nc: bool, top: impl FnOnce(&mut B, QubitId)) {
    let m = masked_prefix(ld);
    assert!(!bank.is_empty() && bank.len() <= m && !ld.f0 && (ord_gate_free() || m == ld.t.len()));
    assert!(mask_carry_segments_compatible(ld));
    let segments = mcs_plan(ld, bank.len(), pool.len());
    if l3_profile() {
        let (slot, stage) = super::greedyfrog::l3_profile_context();
        let covered: usize = segments.iter().map(|s| s.len).sum();
        let saved_per_extra = if mask_carry_products() { 1.0 } else { 0.25 };
        eprintln!("L3SEG\t{slot}\t{stage}\t{m}\t{}\t{covered}\t{}\t{}\t{}",
            bank.len(), segments.iter().filter(|s| s.len == 2).count(),
            segments.iter().filter(|s| s.len == 3).count(), -saved_per_extra * (covered - bank.len()) as f64);
    }
    DEC_KEEP.with(|c| c.set(true));
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: None }).collect();
    if ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    let receipt = |b: &mut B, l: usize, q: QubitId| {
        if let Some(Some(bit)) = roll.and_then(|r| r.rc.get(l)) {
            if !mcs_break(6) && !(roll_break(2) && l == m / 2) { b.z_if(q, *bit); }
        }
    };
    let (mut l, mut si, mut cur) = (0, 0, ld.c0);
    while l < m {
        if si < segments.len() && segments[si].start == l {
            let seg = segments[si];
            let entry = cur;
            for j in 0..seg.len {
                let at = l + j;
                toggles(b, ld, &mut decs, at, true);
                let q = if j + 1 == seg.len { bank[si] } else { pool[j] };
                if mask_carry_products() && j + 1 < seg.len {
                    mcp_form(b, ld, at, cur, q, pool[seg.len - 1 + j], false, true);
                } else {
                    mcs_form(b, ld, at, cur, q, false, true);
                }
                receipt(b, at, q);
                toggles(b, ld, &mut decs, at, false);
                cur = q;
            }
            for j in (0..seg.len - 1).rev() {
                let prev = if j == 0 { entry } else { pool[j - 1] };
                if mask_carry_products() {
                    mcp_erase_interior(b, ld, seg, j, prev, pool[j], pool[seg.len - 1 + j]);
                } else {
                    mcs_erase_interior(b, ld, seg, j, prev, pool[j]);
                }
            }
            l += seg.len;
            si += 1;
        } else {
            toggles(b, ld, &mut decs, l, true);
            masked_up_cell(b, ld, l, cur);
            receipt(b, l, cur);
            toggles(b, ld, &mut decs, l, false);
            l += 1;
        }
    }
    if let Some(bit) = roll.and_then(|r| r.fb) {
        if !roll_break(3) { b.z_if(ld.sc.f, bit); }
    }
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    let rc: Vec<Option<BitId>> = roll.map_or(vec![], |r| r.rc.iter().skip(m).copied().collect());
    let ex = if m < ld.t.len() { ord_dec_clear(b, &mut decs) } else { vec![] };
    ord_run(b, ld, m, bank, cur, pool, &rc, nc, &ex, top);
    if ld.cmpl { for &q in &ld.t[m..] { b.x(q); } }
    l = m;
    si = segments.len();
    while l > 0 {
        if si > 0 && segments[si - 1].start + segments[si - 1].len == l {
            si -= 1;
            let seg = segments[si];
            let entry = if si == 0 { ld.c0 } else { bank[si - 1] };
            // The ordinary backwards loop moves a decoder only after its cell's arithmetic. Move that same
            // endpoint update before this segment's phase repair so the retained equality really is E_end.
            // The later endpoint toggle then reuses this cursor; no additional decoder traversal is introduced.
            for (di, src) in ld.srcs.iter().enumerate() {
                if src.d.abs() == 2 {
                    if let Some(t) = (seg.start + 1..l).rev().find(|&t| mcs_source_toggle(src, t)) { decs[di].goto(b, src.tv(t) as usize); }
                } else if mcs_source_toggle(src, l - 1) { decs[di].goto(b, src.tv(l - 1) as usize); }
            }
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(bank[si], bit);
            b.push_condition(bit);
            let mut prev = entry;
            for j in 0..seg.len - 1 {
                mcs_mask_from_end(b, ld, seg, j);
                if mask_carry_products() {
                    mcp_form(b, ld, seg.start + j, prev, pool[j], pool[seg.len - 1 + j], true, false);
                } else {
                    mcs_form(b, ld, seg.start + j, prev, pool[j], true, false);
                }
                mcs_mask_from_end(b, ld, seg, j);
                prev = pool[j];
            }
            mcs_carry_phase(b, ld, l - 1, prev, 3);
            for j in (0..seg.len - 1).rev() {
                let prev = if j == 0 { entry } else { pool[j - 1] };
                if mask_carry_products() {
                    mcp_erase_interior(b, ld, seg, j, prev, pool[j], pool[seg.len - 1 + j]);
                } else {
                    mcs_erase_interior(b, ld, seg, j, prev, pool[j]);
                }
            }
            b.pop_condition();
            for at in (seg.start..l).rev() {
                toggles(b, ld, &mut decs, at, false);
                toggles(b, ld, &mut decs, at, true);
                clear_ended(b, ld, &mut decs, at, false);
            }
            l = seg.start;
            cur = entry;
        } else {
            l -= 1;
            toggles(b, ld, &mut decs, l, false);
            masked_down_cell(b, ld, l, cur, Some(ALWAYS));
            toggles(b, ld, &mut decs, l, true);
            clear_ended(b, ld, &mut decs, l, false);
        }
    }
    if ld.cmpl { for &q in &ld.t[..m] { b.x(q); } }
    DEC_KEEP.with(|c| c.set(false));
}

/// L3 MASK-CARRY-PRODUCTS: retain each segment interior's A=f(s^c) beside its carry until that carry is erased.
/// Its phase then needs only Z(c) CZ(A,t_written^c^1); AndU returns A for no Toffoli. The same retention in the
/// conditional replay removes nested cubic repair. Pair/triple expected arithmetic costs become 5.5 / 8.5 T,
/// using 2 / 4 idle ordinary-pool lanes. This flag is consumed only by MASK-CARRY-SEGMENTS.
pub const MASK_CARRY_PRODUCTS: bool = true;
fn mask_carry_products() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_MASK_CARRY_PRODUCTS").map_or(MASK_CARRY_PRODUCTS, |v| v.trim() == "1")
    });
    *E
}
/// Test-only mutants: 1 drops interior q's phase, 2 clears A before its phase consumer,
/// 3 uses the segment-end mask for A's AndU, 4 drops the written-target complement in replay.
fn mcp_break(k: u32) -> bool {
    cfg!(test) && std::env::var("MCP_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

fn mcp_form(b: &mut B, ld: &Lad, l: usize, prev: QubitId, q: QubitId, a: QubitId,
            written: bool, write: bool) {
    assert!(!(written && write));
    let (t, s) = (ld.t[l], ld.s[l]);
    b.cx(prev, s);
    b.and_c(ld.sc.f, s, a);
    b.cx(prev, s);
    b.cx(prev, t);
    if written && !mcs_break(4) && !mcp_break(4) { b.x(t); }
    b.and_c(a, t, q);
    if written && !mcs_break(4) && !mcp_break(4) { b.x(t); }
    b.cx(prev, t);
    b.cx(prev, q);
    if write && !mcs_break(1) { b.cx(a, t); }
    if mcp_break(2) {
        b.cx(prev, s);
        b.and_u(ld.sc.f, s, a);
        b.cx(prev, s);
    }
}

fn mcp_erase_interior(b: &mut B, ld: &Lad, seg: MaskCarrySegment, j: usize,
                      prev: QubitId, q: QubitId, a: QubitId) {
    let (t, s) = (ld.t[seg.start + j], ld.s[seg.start + j]);
    let bit = b.fresh_bits(1)[0];
    b.hmr_to(q, bit);
    b.push_condition(bit);
    if !mcp_break(1) {
        b.z(prev);
        b.cx(prev, t);
        b.x(t);
        if !mcs_break(2) { b.cz(a, t); }
        b.x(t);
        b.cx(prev, t);
    }
    b.pop_condition();
    // q has been reset, but its predecessor is still live. Therefore A's original controls can be recovered
    // before that predecessor is erased. Mask recovery is affine and leaves the decoder endpoint unchanged.
    if !mcp_break(2) {
        if !mcp_break(3) { mcs_mask_from_end(b, ld, seg, j); }
        b.cx(prev, s);
        b.and_u(ld.sc.f, s, a);
        b.cx(prev, s);
        if !mcp_break(3) { mcs_mask_from_end(b, ld, seg, j); }
    }
}
