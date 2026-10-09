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
use crate::circuit::QubitId;

/// A toggle source: entering ladder lane l (lo <= l < hi) toggles f iff v == a + d*l. `pre` = prefix ancillas
/// (len >= v.len() - 1), disjoint from any other source whose window overlaps this one.
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
        self.a + self.d * l as isize
    }
    /// interval of matched values over the window: [min, max]
    fn span(&self) -> (isize, isize) {
        let x = self.tv(self.lo);
        let y = self.tv(self.hi - 1);
        (x.min(y), x.max(y))
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
}

fn masked(ld: &Lad, l: usize) -> bool {
    ld.srcs.iter().any(|s| l >= s.lo && l < s.hi)
}

/// Wire holding c_l (carry into ladder lane l).
fn carry_wire(ld: &Lad, l: usize) -> QubitId {
    let mut w = ld.c0;
    for m in 0..l {
        if !masked(ld, m) {
            w = ld.s[m];
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
                let o = decs[si].goto(b, j as usize);
                if s.late && pre {
                    b.cx(o, ld.t[l]);
                } else {
                    b.cx(o, ld.sc.f);
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
    let l_n = ld.t.len();
    assert_eq!(ld.s.len(), l_n);
    b.begin();
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: None }).collect();
    if ld.f0 {
        b.x(ld.sc.f);
    }
    for l in 0..l_n {
        let x = carry_wire(ld, l);
        toggles(b, ld, &mut decs, l, true);
        if masked(ld, l) {
            masked_up_cell(b, ld, l, x);
        } else {
            b.cx(ld.s[l], ld.t[l]);
            b.cx(ld.s[l], x);
            b.ccx(x, ld.t[l], ld.s[l]);
        }
        toggles(b, ld, &mut decs, l, false);
        clear_ended(b, ld, &mut decs, l, true);
    }
    f_end(b, ld);
    b.end()
}

/// Return pass. `g = Some(q)`: write the (masked) sum where q = 1, restore elsewhere; None: exact inverse of `mup`.
pub fn mdown(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    let l_n = ld.t.len();
    assert!(g.is_none() || ld.srcs.iter().all(|s| !s.late), "late sources only in compare passes");
    b.begin();
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec { v: &s.v, pre: &s.pre, cur: None }).collect();
    f_end(b, ld); // f = value after the last lane
    for l in (0..l_n).rev() {
        let x = carry_wire(ld, l);
        // undo lane l's late toggles so that f = the mask lane l's cell saw
        toggles(b, ld, &mut decs, l, false);
        if masked(ld, l) {
            masked_down_cell(b, ld, l, x, g);
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
    b.and_c(t, s, ld.sc.t);
    b.ccx(ld.sc.f, ld.sc.t, x);
    b.and_u(t, s, ld.sc.t);
    if let Some(gq) = g {
        b.and_c(gq, ld.sc.f, ld.sc.gf);
        b.ccx(ld.sc.gf, s, t);
        b.and_u(gq, ld.sc.f, ld.sc.gf);
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
