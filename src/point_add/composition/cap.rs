//! capfront: gate-for-gate Rust port of the hs2 capped front rows (hybridwalk/hs2/front.cjs, variant V1, on the
//! public generator gen.cjs = centered-point.cjs) for a uniform quotient cap B, streaming the physical op sequence.
//!
//! Every function below is a transcription of one JavaScript function; the comment above each names it as
//! file:line of the frozen copies in hr1/js/ (identical to hs2/, see hr1/js/SHA256SUMS.txt).  Sequences that the JS
//! writes as `stepList(seq, back, fn => fn(back))` are written as `run(t, n, back, |t, i| match i { .. })` with the
//! same items in the same order.
//!
//! Wire numbering: logical wires of the 634-wire layout (front.cjs:23 makeLayout(5, 243)): big 0..257, bank
//! 257..385, F 385..390, passenger 390..633, g = 633 = the fixed one (folded away, gen.cjs:867 FoldTape).  Physical
//! wire = logical (all wires < g).  The sink receives physical wires passed through the caller's lane map.

use std::cell::Cell;

pub type W = u32;
/// gen.cjs:38 omitted-control sentinel
pub const NONE: W = 1023;

/// One op of the stream.  `cond = Some(bit)`: the op is applied only if classical bit `bit` (an earlier HMR outcome)
/// is 1 (gen.cjs:888 MeasuredNct.out / 905 z under `current`).  CondBegin / CondEnd bracket every conditional block
/// exactly as gen.cjs `cond(ms, fn)` does (the ops inside also carry `cond`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    X { t: u32, cond: Option<u32> },
    Cx { c: u32, t: u32, cond: Option<u32> },
    /// controls in the generator's order (a, b): the order enters the signature
    Ccx { a: u32, b: u32, t: u32, cond: Option<u32> },
    /// X-basis measure-and-reset of wire q into classical bit `bit` (gen.cjs:897 MeasuredNct.hmr)
    Hmr { q: u32, bit: u32 },
    /// phase flip on wire q (only ever emitted inside a conditional block)
    Z { q: u32, cond: Option<u32> },
    CondBegin { bit: u32 },
    CondEnd,
}

// ------------------------------------------------------------------------------------------------ big constants
/// little-endian u64 limbs (only used for public constants: p, p+1, (p+1)/2, small integers)
#[derive(Clone, Debug)]
pub struct Limbs(pub Vec<u64>);
impl Limbs {
    pub fn small(x: u64) -> Limbs { Limbs(vec![x]) }
    pub fn bit(&self, i: usize) -> bool { let w = i / 64; w < self.0.len() && (self.0[w] >> (i % 64)) & 1 == 1 }
    pub fn is_zero(&self) -> bool { self.0.iter().all(|&x| x == 0) }
    /// self >= 2^n
    pub fn ge_pow2(&self, n: usize) -> bool { (n..64 * self.0.len()).any(|i| self.bit(i)) }
    pub fn add_small(&self, x: u64) -> Limbs {
        let mut v = self.0.clone(); v.push(0); let mut c = x as u128;
        for l in v.iter_mut() { let s = *l as u128 + c; *l = s as u64; c = s >> 64; }
        Limbs(v)
    }
    pub fn shr1(&self) -> Limbs {
        let n = self.0.len(); let mut v = vec![0u64; n];
        for i in 0..n { v[i] = (self.0[i] >> 1) | if i + 1 < n { self.0[i + 1] << 63 } else { 0 }; }
        Limbs(v)
    }
}
/// p = 2^256 - 2^32 - 977
pub fn prime() -> Limbs { Limbs(vec![0xFFFF_FFFE_FFFF_FC2F, u64::MAX, u64::MAX, u64::MAX]) }
const M: usize = 256;
const HALF: usize = 128;
/// delta = 2^32 + 977; reflect uses the set bits of delta - 1
const DELTA_M1: u64 = (1u64 << 32) + 976;

fn cat(parts: &[&[W]]) -> Vec<W> { let mut v = Vec::with_capacity(parts.iter().map(|p| p.len()).sum()); for p in parts { v.extend_from_slice(p); } v }
fn range(lo: usize, hi: usize) -> Vec<W> { (lo as W..hi as W).collect() }
/// JS Array.prototype.slice(a, b) for 0 <= a (clamped to the length, empty when b <= a)
fn js_slice(v: &[W], a: usize, b: usize) -> &[W] { let a = a.min(v.len()); let b = b.min(v.len()); if b <= a { &[] } else { &v[a..b] } }
/// stepList(seq, back, fn => fn(..)) over n items
#[inline]
fn run<T: ?Sized>(t: &mut T, n: usize, back: bool, mut f: impl FnMut(&mut T, usize)) {
    if back { for i in (0..n).rev() { f(t, i) } } else { for i in 0..n { f(t, i) } }
}
fn floor_log2(x: usize) -> usize { (usize::BITS - 1 - x.leading_zeros()) as usize }

// ------------------------------------------------------------------------------------------------ tape
/// gen.cjs:909 MeasuredFold (FoldTape over MeasuredNct) as a stream: the arithmetic below calls out/mc/loan/add on the
/// logical tape exactly as the JS does; the physical op goes to the sink.
pub struct Tape<'s> {
    one: W,
    nids: W,
    excl: Option<(W, W)>,
    map: &'s [u32],
    sink: &'s mut dyn FnMut(Op),
    current: Option<u32>,
    next_bit: u32,
    /// round discipline (run_front.cjs:176 tape.hist): row k -> classical bit of its witness HMR
    hist: Option<Vec<Option<u32>>>,
    pub hmr_count: u32,
}

#[derive(Clone, Copy)]
enum Call { Cx(W, W), Cc(W, W, W), Last(W, W) }

impl<'s> Tape<'s> {
    fn emit(&mut self, op: Op) { (self.sink)(op) }
    fn cv(&self, x: W) -> W { if x == NONE { NONE } else if x > self.one { x - 1 } else { x } }
    fn mp(&self, x: W) -> u32 { self.map[x as usize] }
    // gen.cjs:871 FoldTape.out
    pub fn out(&mut self, a: W, b: W, t: W) {
        let g = self.one;
        if t == g { panic!("write to fixed enable"); }
        let mut a = if a == g { NONE } else { a };
        let mut b = if b == g { NONE } else { b };
        if b == NONE && a != NONE { b = a; a = NONE; }
        let (a, b, t) = (self.cv(a), self.cv(b), self.cv(t));
        // gen.cjs:46 / 890 alias check
        if t == a || t == b || (a != NONE && a == b) { panic!("gate aliases {a} {b} {t}"); }
        let cond = self.current;
        let op = if a != NONE { Op::Ccx { a: self.mp(a), b: self.mp(b), t: self.mp(t), cond } }
            else if b != NONE { Op::Cx { c: self.mp(b), t: self.mp(t), cond } }
            else { Op::X { t: self.mp(t), cond } };
        self.emit(op);
    }
    // gen.cjs:876 FoldTape.mc (drops the fixed one) -> gen.cjs:56 Tape.mc
    pub fn mc(&mut self, cs: &[W], t: W, dirty: &[W]) {
        let one = self.one;
        if cs.contains(&one) { let f: Vec<W> = cs.iter().copied().filter(|&q| q != one).collect(); self.mc_raw(&f, t, dirty) } else { self.mc_raw(cs, t, dirty) }
    }
    fn mc_raw(&mut self, cs: &[W], t: W, dirty: &[W]) {
        let n = cs.len();
        if n == 0 { self.out(NONE, NONE, t); return; }
        if n == 1 { self.out(NONE, cs[0], t); return; }
        if n == 2 { self.out(cs[0], cs[1], t); return; }
        if dirty.len() >= n - 2 {
            let d = dirty;
            for i in 0..n - 2 { self.out(if i == 0 { cs[0] } else { d[i - 1] }, cs[i + 1], d[i]); }
            self.out(d[n - 3], cs[n - 1], t);
            for i in (0..=n - 3).rev() { self.out(if i == 0 { cs[0] } else { d[i - 1] }, cs[i + 1], d[i]); }
            for i in 1..n - 2 { self.out(d[i - 1], cs[i + 1], d[i]); }
            self.out(d[n - 3], cs[n - 1], t);
            for i in (1..=n - 3).rev() { self.out(d[i - 1], cs[i + 1], d[i]); }
            return;
        }
        let cut = (n + 1) / 2; let (a, b) = (&cs[..cut], &cs[cut..]);
        let x = *dirty.first().expect("missing dirty control"); let pool = &dirty[1..];
        if cs.contains(&x) || x == t { panic!("missing dirty control"); }
        let xb = cat(&[&[x], b]);
        self.mc(a, x, pool); self.mc(&xb, t, pool); self.mc(a, x, pool); self.mc(&xb, t, pool);
    }
    // gen.cjs:77 Tape.loan (ids 0..logical, guard = the fixed one)
    pub fn loan(&self, used: &[W], limit: usize) -> Vec<W> {
        if limit == 0 { return vec![]; }
        let mut bad = [0u64; 16];
        for q in 347..=352 {bad[q/64]|=1<<(q%64);}
        for &q in used { if (q as usize) < 1024 { bad[q as usize / 64] |= 1 << (q % 64); } }
        bad[self.one as usize / 64] |= 1 << (self.one % 64);
        let mut out = Vec::with_capacity(limit);
        for q in 0..self.nids { if (bad[q as usize / 64] >> (q % 64)) & 1 == 0 { out.push(q); if out.len() == limit { break; } } }
        if out.len() < limit { panic!("loan capacity"); }
        if let Some((x, sub)) = self.excl {
            if let Some(i) = out.iter().position(|&q| q == x) {
                if used.contains(&sub) || out.contains(&sub) || sub == self.one { panic!("loan substitute {sub} unavailable"); }
                out[i] = sub;
            }
        }
        out
    }
    fn exec_calls(&mut self, calls: &[Call], controls: &[W], rev: bool, loans: &[W]) {
        let mut cs: Vec<W> = Vec::with_capacity(controls.len() + 1);
        let one = |s: &mut Self, c: &Call, cs: &mut Vec<W>| match *c {
            Call::Cx(x, y) => s.mc(&[x], y, loans),
            Call::Cc(x, y, z) => s.mc(&[x, y], z, loans),
            Call::Last(x, y) => { cs.clear(); cs.extend_from_slice(controls); cs.push(x); s.mc(cs, y, loans) }
        };
        if rev { for c in calls.iter().rev() { one(self, c, &mut cs) } } else { for c in calls { one(self, c, &mut cs) } }
    }
    // gen.cjs:85 Tape.equal
    fn equal(&mut self, a: &[W], b: &[W], controls: &[W], inverse: bool, loans: &[W]) {
        let n = b.len();
        if a.len() != n || n == 0 { panic!("unequal ripple"); }
        let mut calls = Vec::with_capacity(6 * n);
        for i in 1..n { calls.push(Call::Cx(a[i], b[i])); }
        for i in (1..n.saturating_sub(1)).rev() { calls.push(Call::Cx(a[i], a[i + 1])); }
        for i in 0..n - 1 { calls.push(Call::Cc(a[i], b[i], a[i + 1])); }
        for i in (1..n).rev() { calls.push(Call::Last(a[i], b[i])); calls.push(Call::Cc(a[i - 1], b[i - 1], a[i])); }
        for i in 1..n.saturating_sub(1) { calls.push(Call::Cx(a[i], a[i + 1])); }
        calls.push(Call::Last(a[0], b[0]));
        for i in 1..n { calls.push(Call::Cx(a[i], b[i])); }
        self.exec_calls(&calls, controls, inverse, loans);
    }
    // gen.cjs:101 Tape.increment
    fn increment(&mut self, b: &[W], controls: &[W], dword: &[W], loans: &[W], inverse: bool) {
        let rv = !inverse;
        run(self, 4, rv, |s, i| match i {
            0 | 2 => s.equal(dword, b, controls, rv, loans),
            _ => { for &q in dword { s.out(NONE, NONE, q) } }
        });
    }
    // gen.cjs:112 Tape.add (the conditional controls c are always an array in the front)
    pub fn add(&mut self, src: &[W], dest: &[W], base: &[W], carry: W, inverse: bool) {
        if src.is_empty() || dest.is_empty() { return; }
        let k = src.len().min(dest.len()); let (a, b, hi) = (&src[..k], &dest[..k], &dest[k..]);
        let used = cat(&[a, dest, base, &[carry]]);
        let pool = self.loan(&used, hi.len() + 4); let (dword, loans) = (&pool[..hi.len()], &pool[hi.len()..]);
        if hi.is_empty() { self.equal(a, b, base, inverse, loans); return; }
        let mut before = Vec::new(); let mut after = Vec::new();
        if k > 1 { before.push(Call::Cx(a[k - 1], carry)); }
        for i in 1..k { before.push(Call::Cx(a[i], b[i])); }
        for i in (1..k.saturating_sub(1)).rev() { before.push(Call::Cx(a[i], a[i + 1])); }
        for i in 0..k - 1 { before.push(Call::Cc(a[i], b[i], a[i + 1])); }
        before.push(Call::Cc(a[k - 1], b[k - 1], carry));
        after.push(Call::Cc(a[k - 1], b[k - 1], carry));
        for i in (1..k).rev() { after.push(Call::Last(a[i], b[i])); after.push(Call::Cc(a[i - 1], b[i - 1], a[i])); }
        for i in 1..k.saturating_sub(1) { after.push(Call::Cx(a[i], a[i + 1])); }
        after.push(Call::Last(a[0], b[0]));
        for i in 1..k { after.push(Call::Cx(a[i], b[i])); }
        if k > 1 { after.push(Call::Cx(a[k - 1], carry)); }
        let ctrl2 = cat(&[base, &[carry]]);
        run(self, 3, inverse, |s, i| match i {
            0 => s.exec_calls(&before, base, inverse, loans),
            1 => s.increment(hi, &ctrl2, dword, loans, inverse),
            _ => s.exec_calls(&after, base, inverse, loans),
        });
    }
    // gen.cjs:912-914 MeasuredFold.hmr / z / cond -> gen.cjs:897 / 905 / 906 MeasuredNct
    pub fn hmr(&mut self, q: W) -> u32 {
        if q == self.one { panic!("fixed measurement"); }
        if self.current.is_some() { panic!("nested HMR"); }
        let bit = self.next_bit; self.next_bit += 1; self.hmr_count += 1;
        let q = self.mp(self.cv(q));
        self.emit(Op::Hmr { q, bit }); bit
    }
    pub fn z(&mut self, q: W) {
        if q == self.one { panic!("fixed measurement"); }
        let q = self.mp(self.cv(q)); let cond = self.current; self.emit(Op::Z { q, cond });
    }
    pub fn cond(&mut self, bit: u32, f: impl FnOnce(&mut Self)) {
        if self.current.is_some() { panic!("nested classical replay"); }
        self.current = Some(bit); self.emit(Op::CondBegin { bit }); f(self); self.emit(Op::CondEnd); self.current = None;
    }
}

// ------------------------------------------------------------------------------------------------ arithmetic
/// the two helper wires MixedArithmetic.digit reads from `this` (pick, carry)
#[derive(Clone, Copy)]
struct Ar { pick: W, carry: W }

// gen.cjs:153 WordArithmetic.toggle
fn toggle(t: &mut Tape, positive: &[W], negative: &[W], target: W) {
    let controls = cat(&[positive, negative]);
    let mut seen = [0u64; 16];
    for &c in &controls { if c == target || (seen[c as usize / 64] >> (c % 64)) & 1 == 1 { panic!("toggle aliases"); } seen[c as usize / 64] |= 1 << (c % 64); }
    for &i in negative { t.out(NONE, NONE, i); }
    let loans = t.loan(&cat(&[&controls, &[target]]), controls.len().saturating_sub(2));
    t.mc(&controls, target, &loans);
    for &i in negative.iter().rev() { t.out(NONE, NONE, i); }
}
// gen.cjs:161 cnotList
fn cnot_list(t: &mut Tape, controls: &[W], word: &[W]) {
    let loans = t.loan(&cat(&[controls, word]), controls.len().saturating_sub(1));
    for &q in word { t.mc(controls, q, &loans); }
}
// gen.cjs:165 inc
fn inc(t: &mut Tape, word: &[W], controls: &[W], back: bool) {
    if word.is_empty() { return; }
    let loans = t.loan(&cat(&[word, controls]), word.len() + 6);
    t.increment(word, controls, &loans[..word.len()], &loans[word.len()..], back);
}
// gen.cjs:170 reflect (fieldBits = 256, delta = 2^32 + 977)
fn reflect(t: &mut Tape, word: &[W], controls: &[W], back: bool) {
    // items: 0 = cnotList, 1 = inc(word[256..], r), 2+i = inc(word[i..], !r)
    let mut items: Vec<usize> = vec![0];
    if M < word.len() { items.push(1); }
    let mut i = 0; while DELTA_M1 >> i != 0 { if (DELTA_M1 >> i) & 1 == 1 { items.push(2 + i); } i += 1; }
    run(t, items.len(), back, |t, j| match items[j] {
        0 => cnot_list(t, controls, word),
        1 => inc(t, &word[M..], controls, back),
        x => inc(t, &word[x - 2..], controls, !back),
    });
}
// gen.cjs:180 gatedSwap
fn gated_swap(t: &mut Tape, x: W, y: W, controls: &[W], loans: &[W]) {
    t.out(NONE, x, y);
    let cs = cat(&[controls, &[y]]); t.mc(&cs, x, loans);
    t.out(NONE, x, y);
}
// gen.cjs:185 permute
fn permute(t: &mut Tape, word: &[W], origins: &[W], controls: &[W], back: bool) {
    let mut at = word.to_vec();
    let mut wh = vec![usize::MAX; 1024];
    for (i, &w) in at.iter().enumerate() { wh[w as usize] = i; }
    let mut swaps: Vec<(W, W)> = Vec::new();
    for to in 0..at.len() {
        let from = wh[origins[to] as usize];
        if from == usize::MAX { panic!("permutation origin"); }
        if from == to { continue; }
        let (take, mv) = (at[from], at[to]); at[to] = take; at[from] = mv;
        wh[take as usize] = to; wh[mv as usize] = from; swaps.push((word[to], word[from]));
    }
    let pool = t.loan(&cat(&[word, controls]), controls.len().saturating_sub(1));
    run(t, swaps.len(), back, |t, i| { let (x, y) = swaps[i]; gated_swap(t, x, y, controls, &pool) });
}
// gen.cjs:213 digit (fused comparison and subtraction)
fn digit(ar: Ar, t: &mut Tape, z: &[W], v: &[W], controls: &[W], back: bool) {
    let n = v.len(); let bb = &z[..n]; let h = z[n]; let tt = ar.pick;
    let e = if controls.len() == 1 { controls[0] } else { ar.carry };
    let multi = controls.len() > 1; let enabled = !controls.is_empty();
    let mut ops: Vec<[W; 3]> = Vec::with_capacity(8 * n + 8);
    macro_rules! x { ($a:expr) => { ops.push([NONE, NONE, $a]) } }
    macro_rules! cx { ($a:expr, $b:expr) => { ops.push([NONE, $a, $b]) } }
    macro_rules! cc { ($a:expr, $b:expr, $c:expr) => { ops.push([$a, $b, $c]) } }
    if multi { toggle(t, controls, &[], e); }
    if n == 1 {
        if enabled { x!(bb[0]); cc!(e, v[0], tt); cc!(tt, bb[0], h); x!(bb[0]); cx!(e, h); cc!(tt, h, bb[0]); cc!(e, v[0], tt); }
        else { x!(bb[0]); cc!(bb[0], v[0], h); x!(bb[0]); x!(h); cc!(h, v[0], bb[0]); }
    } else {
        for &b in bb { x!(b); }
        for i in 1..n { cx!(v[i], bb[i]); }
        if enabled { cc!(e, v[n - 1], h); } else { cx!(v[n - 1], h); }
        for i in (1..n - 1).rev() { cx!(v[i], v[i + 1]); }
        for i in 0..n - 1 { cc!(bb[i], v[i], v[i + 1]); }
        if enabled { cc!(e, v[n - 1], tt); cc!(tt, bb[n - 1], h); cc!(e, v[n - 1], tt); cx!(e, h); cc!(e, h, tt); }
        else { cc!(bb[n - 1], v[n - 1], h); x!(h); }
        let pred = if enabled { tt } else { h };
        cc!(pred, v[n - 1], bb[n - 1]);
        for i in (0..n - 1).rev() { cc!(bb[i], v[i], v[i + 1]); cc!(pred, v[i], bb[i]); }
        if enabled { cc!(e, h, tt); }
        for i in 1..n - 1 { cx!(v[i], v[i + 1]); }
        for i in 1..n { cx!(v[i], bb[i]); }
        for &b in bb { x!(b); }
    }
    run(t, ops.len(), back, |t, i| { let [a, b, c] = ops[i]; t.out(a, b, c) });
    if multi { toggle(t, controls, &[], e); }
}
// gen.cjs:241 nrAdder
fn nr_adder(t: &mut Tape, a: &[W], b: &[W], hh: Option<W>, p: Option<W>, back: bool) {
    let n = a.len(); let mut ops: Vec<[W; 3]> = Vec::with_capacity(6 * n + 4);
    macro_rules! cx { ($a:expr, $b:expr) => { ops.push([NONE, $a, $b]) } }
    macro_rules! cc { ($a:expr, $b:expr, $c:expr) => { ops.push([$a, $b, $c]) } }
    macro_rules! put { ($x:expr, $y:expr) => { match p { None => cx!($x, $y), Some(pp) => cc!(pp, $x, $y) } } }
    if n == 1 { if let Some(h) = hh { cc!(b[0], a[0], h); } put!(a[0], b[0]); }
    else {
        for i in 1..n { cx!(a[i], b[i]); }
        if let Some(h) = hh { cx!(a[n - 1], h); }
        for i in (1..n - 1).rev() { cx!(a[i], a[i + 1]); }
        for i in 0..n - 1 { cc!(b[i], a[i], a[i + 1]); }
        if let Some(h) = hh { cc!(b[n - 1], a[n - 1], h); }
        put!(a[n - 1], b[n - 1]);
        for i in (0..n - 1).rev() { cc!(b[i], a[i], a[i + 1]); put!(a[i], b[i]); }
        for i in 1..n - 1 { cx!(a[i], a[i + 1]); }
        for i in 1..n { cx!(a[i], b[i]); }
    }
    run(t, ops.len(), back, |t, i| { let [x, y, z] = ops[i]; t.out(x, y, z) });
}
// gen.cjs:255 unguardedMixed
fn unguarded_mixed(t: &mut Tape, q: &[W], v: &[W], rem: &[W], back: bool) {
    let jj = cat(&[q, rem]); let n = v.len(); let k = q.len();
    #[derive(Clone, Copy)] enum U { Flip(usize), Nr(usize), NrLast, Xs, Perm }
    let mut ops: Vec<U> = Vec::with_capacity(3 * k + 3);
    for j in (0..k).rev() { ops.push(U::Flip(j)); ops.push(U::Nr(j)); ops.push(U::Flip(j)); }
    ops.push(U::NrLast); ops.push(U::Xs); ops.push(U::Perm);
    let rv = !back;
    run(t, ops.len(), rv, |t, i| match ops[i] {
        U::Flip(j) => {
            let old = if j == k - 1 { None } else { Some(jj[j + n + 1]) };
            if let Some(o) = old { t.out(NONE, NONE, o); }
            for &x in jj[j..j + n].iter().chain(std::iter::once(&jj[j + n])) { t.out(NONE, old.unwrap_or(NONE), x); }
            if let Some(o) = old { t.out(NONE, NONE, o); }
        }
        U::Nr(j) => nr_adder(t, v, &jj[j..j + n], Some(jj[j + n]), None, rv),
        U::NrLast => nr_adder(t, v, &jj[..n], None, Some(jj[n]), rv),
        U::Xs => { for &b in &jj[n..] { t.out(NONE, NONE, b) } }
        U::Perm => { let o = cat(&[&jj[n..], &jj[..n]]); permute(t, &jj, &o, &[], rv) }
    });
}
// gen.cjs:270 mixed
fn mixed(ar: Ar, t: &mut Tape, q: &[W], v: &[W], rem: &[W], controls: &[W], back: bool) {
    if controls.is_empty() { unguarded_mixed(t, q, v, rem, back); return; }
    if v.len() != rem.len() { panic!("mixed coefficient width"); }
    let mut moving = rem.to_vec(); let mut done: Vec<W> = Vec::new(); let mut zs: Vec<Vec<W>> = Vec::with_capacity(q.len());
    for &bit in q {
        let mut z = moving.clone(); z.push(bit); zs.push(z);
        done.push(moving[0]);
        moving.remove(0); moving.push(bit);
    }
    let physical = cat(&[q, rem]); let origins = cat(&[&done, &moving]);
    let nq = q.len();
    run(t, nq + 1, back, |t, i| {
        if i < nq { digit(ar, t, &zs[i], v, controls, !back) } else { permute(t, &physical, &origins, controls, back) }
    });
}
// gen.cjs:284 constBelow: targets ^= controls AND [word < limit]
fn const_below(t: &mut Tape, word: &[W], limit: &Limbs, controls: &[W], targets: &[W]) {
    if targets.is_empty() || limit.is_zero() { return; }
    let n = word.len();
    if limit.ge_pow2(n) { cnot_list(t, controls, targets); return; }
    let bits: Vec<bool> = (0..n).map(|i| limit.bit(i)).collect();
    let d = t.loan(&cat(&[word, controls, targets]), n + 1);
    let more = t.loan(&cat(&[word, controls, targets, &d]), controls.len().saturating_sub(2));
    let mut coeff = vec![false; n + 1];
    for i in 0..n { if bits[i] { coeff[i] ^= true; coeff[i + 1] ^= true; } }
    let deposits: Vec<usize> = (0..=n).filter(|&i| coeff[i]).collect();
    for i in 0..n { if !bits[i] { t.out(NONE, NONE, word[i]); } }
    for _echo in 0..2 {
        t.mc(controls, d[n], &more);
        for i in (0..n).rev() { t.out(word[i], d[i + 1], d[i]); }
        for &i in &deposits { for &tg in targets { t.out(NONE, d[i], tg); } }
        for i in 0..n { t.out(word[i], d[i + 1], d[i]); }
    }
    for i in 0..n { if !bits[i] { t.out(NONE, NONE, word[i]); } }
}

// ------------------------------------------------------------------------------------------------ configuration
/// front.cjs:23 makeLayout(5, 243) + front.cjs:31 schedule(K, () => B) + V1 options (front.cjs:38)
#[derive(Clone, Debug)]
pub struct Config {
    pub k_rows: usize,
    pub cap: usize,
    pub caps: Vec<usize>,
    pub zf: Vec<usize>,
    pub big: Vec<W>,
    pub bank: Vec<W>,
    pub flags: Vec<W>,
    pub passenger: Vec<W>,
    pub g: W,
    pub logical: W,
    /// rows631: (X, S): wherever `Tape::loan` would lend wire X it lends wire S instead, every other loan unchanged (default None = reference rows byte for byte)
    pub excl: Option<(W, W)>,
}
impl Config {
    pub fn new(k_rows: usize, cap: usize) -> Config {
        let (mut caps, mut zf) = (vec![], vec![]); let mut z = 1usize;
        for k in 0..=k_rows { zf.push(z); if k < k_rows { caps.push(cap); z = z.max(k + 1 + cap).max(k + 2); } }
        let (nf, np) = (5usize, 243usize);
        Config { k_rows, cap, caps, zf, big: range(0, 257), bank: range(257, 385), flags: range(385, 385 + nf),
            passenger: range(385 + nf, 385 + nf + np), g: (385 + nf + np) as W, logical: (385 + nf + np + 1) as W, excl: None }
    }
    /// physical width (the folded one removed) = 633
    pub fn physical(&self) -> usize { self.logical as usize - 1 }
    // front.cjs:43 supplyOf (V1: narrow -> bank top first, then F1..F4)
    fn supply(&self, lo: usize) -> Vec<W> { let mut s: Vec<W> = self.bank[lo.min(128)..].iter().rev().copied().collect(); s.extend_from_slice(&self.flags[1..]); s }
}

#[derive(Clone, Debug)]
struct Layout { lo: usize, hi: usize, w: usize, tt: Vec<W>, d: Vec<W>, hh: Vec<W>, d0: W }

// ------------------------------------------------------------------------------------------------ general row
/// front.cjs:48 FrontGeneral (constructor chain gen.cjs:398 UniversalGeneral -> 732 OddEstimateGeneral -> front.cjs:49)
pub struct General {
    k: usize, h: usize, bcap: usize,
    r: Vec<W>, u: Vec<W>, bank: Vec<W>, v: Vec<W>, n: Vec<W>, borrow: W,
    zword: Vec<W>, g: W, sig: W, max_shift: usize,
    qc: Vec<W>, ac: Vec<W>,
    take: W, dv: [W; 2], pick: W, carry: W, tags: Vec<W>, ctrl: Vec<W>,
    zf: usize, zf_next: usize,
    sign_low: Vec<W>, sign_pool: Vec<W>, aff_w: usize, aff_z: Vec<W>,
    layouts: Vec<Layout>, p: Limbs,
    mt: Cell<Option<W>>,
    pub hosted: Vec<W>,
}

impl General {
    pub fn new(k: usize, cfg: &Config) -> Result<General, String> {
        let h = k + 1; let bcap = cfg.caps[k];
        // gen.cjs:400-413 ports (r, u, bank fixed by position; the rest is overridden by front.cjs)
        let r = range(0, M - k); let u = range(M - k, M + 1); let bank = range(M + 1, M + 1 + HALF);
        let n = range(0, M); let borrow = M as W; let v = bank[..h].to_vec();
        if h > M / 2 { return Err("universal width".into()); }
        let kc = (HALF - h).min(bcap);
        let q = js_slice(&bank, h, h + kc + 2).to_vec();
        if q.len() < bcap + 2 { return Err(format!("row {k}: q register {} < B+2", q.len())); }
        let qc = q[..bcap + 1].to_vec(); let ac = cat(&[&qc, &u]);
        let lo = (h + kc + 2).max(cfg.zf[k]);
        let supply = cfg.supply(lo);
        let tn = if kc > 0 { floor_log2(kc) + 1 } else { 0 };
        if supply.len() < 5 + tn { return Err(format!("row {k}: trial needs {} hosted lanes, supply {}", 5 + tn, supply.len())); }
        let (take, f1, f2, pick, carry) = (supply[0], supply[1], supply[2], supply[3], supply[4]);
        let tags = supply[5..5 + tn].to_vec();
        let ctrl = vec![take];
        let others: Vec<W> = supply.iter().copied().filter(|&x| x != take && x != f1).collect();
        let sign_low = vec![bank[k]];
        let sign_pool = cat(&[&q[bcap + 1..], &others]);
        let need_sign = (k + bcap + 2) - k - sign_low.len();
        if sign_pool.len() < need_sign { return Err(format!("row {k}: sign pool")); }
        let aff_w = k + bcap + 1;
        let aff_z = cat(&[&q[bcap + 1..], &[u[k]], &supply.iter().copied().filter(|&x| x != take && x != f1 && x != pick).collect::<Vec<W>>()]);
        let need_aff = aff_w - h;
        if aff_z.len() < need_aff { return Err(format!("row {k}: affine pool")); }
        let mut hosted: Vec<W> = vec![take, f1, f2, pick, carry]; hosted.extend(&tags);
        hosted.extend(&sign_pool[..need_sign]); hosted.extend(&aff_z[..need_aff]);
        hosted.retain(|x| supply.contains(x)); hosted.sort(); hosted.dedup();
        let mut row = General { k, h, bcap, r, u, bank, v, n, borrow, zword: cfg.passenger.clone(), g: cfg.g, sig: cfg.flags[0],
            max_shift: kc, qc, ac, take, dv: [f1, f2], pick, carry, tags, ctrl, zf: cfg.zf[k], zf_next: cfg.zf[k + 1],
            sign_low, sign_pool, aff_w, aff_z, layouts: vec![], p: prime(), mt: Cell::new(None), hosted };
        row.layouts = row.make_layouts(&q).ok_or_else(|| format!("row {k}: trial layout"))?;
        Ok(row)
    }
    fn ar(&self) -> Ar { Ar { pick: self.pick, carry: self.carry } }
    // gen.cjs:737 OddEstimateGeneral.layouts (spareWork = [] in front.cjs:53)
    fn make_layouts(&self, q: &[W]) -> Option<Vec<Layout>> {
        let kk = self.max_shift; let mut out = vec![];
        for (lo, hi) in [(0usize, 7usize.min(kk)), (8, kk)] {
            if lo > hi { continue; }
            let w = hi + 6; let ww = w + 1; if w - 1 > M { return None; }
            let mut spare: Vec<W> = self.n[..lo].to_vec();
            let take = (ww + 1).saturating_sub(q.len()).min(spare.len());
            let spliced: Vec<W> = spare.drain(..take).collect();
            let tt: Vec<W> = cat(&[q, &spliced]).into_iter().take(ww + 1).collect();
            let free = cat(&[js_slice(q, ww + 1, q.len()), &spare]);
            if tt.len() != ww + 1 || free.len() < 2 { return None; }
            let hh = cat(&[&self.n[M - w + 1..], &[free[1]]]); let d = cat(&[&[free[0]], &hh]);
            let mut all = cat(&[&tt, &d]); all.sort(); all.dedup(); if all.len() != tt.len() + d.len() { return None; }
            out.push(Layout { lo, hi, w, tt, d, hh, d0: free[0] });
        }
        Some(out)
    }
    fn retire(&self, t: &mut Tape, wire: W, emit: impl FnOnce(&mut Tape)) {
        // gen.cjs:702 retirePredicate
        let bit = t.hmr(wire);
        t.cond(bit, |t| { self.mt.set(Some(wire)); emit(t); self.mt.set(None); });
    }
    fn phase_deposit(&self, t: &mut Tape, wire: W, write: impl Fn(&mut Tape)) {
        // gen.cjs:701 phaseDeposit
        write(t); if self.mt.get() == Some(wire) { t.z(wire); write(t); }
    }
    // front.cjs:82 select
    fn select(&self, t: &mut Tape) {
        let high = &self.bank[self.h..self.h.max(self.zf)]; let g = [self.g, self.bank[self.k]];
        toggle(t, &g, high, self.take);
        toggle(t, &g, &cat(&[high, &self.r[HALF..]]), self.take);
    }
    // front.cjs:87 emit
    pub fn emit(&self, t: &mut Tape, back: bool) {
        run(t, 4, back, |t, i| match i {
            0 => self.select(t),
            1 => self.core(t, back),
            2 => toggle(t, &self.ctrl, &[], self.sig),
            _ => {
                let mark = [self.g, self.u[self.k]];
                toggle(t, &mark, &[], self.take);
                if self.k > 0 && self.k < HALF - 1 { toggle(t, &mark, &self.bank[self.h..self.h.max(self.zf_next)], self.take); }
            }
        });
    }
    // front.cjs:98 core
    fn core(&self, t: &mut Tape, back: bool) {
        let ar = self.ar(); let (v, q, g, flag) = (&self.v, &self.qc, &self.ctrl, self.dv[0]);
        let coef = |t: &mut Tape, rv: bool| mixed(ar, t, q, v, &self.u, g, rv);
        let gf = cat(&[g, &[flag]]);
        run(t, 9, back, |t, i| {
            let rv = back;
            match i {
                0 => self.trial(t, false, rv),
                1 => coef(t, rv),
                2 => { if rv { self.retire(t, flag, |t| self.front_sign(t, flag)) } else { self.front_sign(t, flag) } }
                3 => t.add(v, &self.ac, &gf, self.carry, !rv),
                4 => coef(t, !rv),
                5 => {
                    if t.hist.is_none() {
                        if !rv { self.retire(t, flag, |t| self.trial(t, true, rv)) } else { self.trial(t, true, rv) }
                    } else if !rv {
                        if t.hist.as_ref().unwrap()[self.k].is_some() { panic!("history collision"); }
                        let bit = t.hmr(flag); t.hist.as_mut().unwrap()[self.k] = Some(bit);
                    } else {
                        self.trial(t, true, rv);
                        let bit = t.hist.as_ref().unwrap()[self.k].expect("missing history");
                        t.cond(bit, |t| t.z(flag)); t.hist.as_mut().unwrap()[self.k] = None;
                    }
                }
                6 => coef(t, rv),
                7 => self.front_affine(t, rv),
                _ => permute(t, &cat(&[&self.bank[..self.h + self.bcap + 1], &self.u]), &cat(&[&self.ac, v]), g, rv),
            }
        });
    }
    // front.cjs:114 frontSign
    fn front_sign(&self, t: &mut Tape, target: W) {
        let k = self.k; let s = &self.ac; let w = s.len(); let low = &self.sign_low;
        let dp = cat(&[&self.zword[..k], low, &self.sign_pool[..w - k - low.len()]]);
        let word = cat(&[&self.r, &dp]);
        let nl = low.len(); let carry = self.carry;
        let seq = |t: &mut Tape, back: bool| run(t, nl + 4, back, |t, i| {
            let rv = back;
            if i < nl { t.out(NONE, self.take, low[i]); return; }
            match i - nl {
                0 => inc(t, &self.r, &[], !rv),
                1 => cnot_list(t, &[], &dp),
                2 => t.add(s, &dp, &[], carry, rv),
                _ => unguarded_mixed(t, &self.r, s, &dp, rv),
            }
        });
        seq(t, false);
        self.phase_deposit(t, target, |t| { toggle(t, &self.ctrl, &[], target); const_below(t, &word, &self.p, &self.ctrl, &[target]); });
        seq(t, true);
    }
    // front.cjs:125 frontAffine
    fn front_affine(&self, t: &mut Tape, back: bool) {
        let ar = self.ar(); let (h, r, v) = (self.h, &self.r, &self.v);
        let a = &self.ac[..self.aff_w]; let w = a.len(); let d = &self.zword[..h];
        let dp = cat(&[d, &self.aff_z[..w - h]]); let word = cat(&[r, &dp]); let g = &self.ctrl;
        let dz = cat(&[d, &[self.dv[0]]]);
        let canon = |t: &mut Tape, rv: bool| digit(ar, t, &dz, v, &[], rv);
        run(t, 9, back, |t, i| {
            let rv = back;
            match i {
                0 => canon(t, rv),
                1 => mixed(ar, t, r, a, &dp, g, rv),
                2 => reflect(t, &word, g, rv),
                3 => inc(t, &word, g, !rv),
                4 => mixed(ar, t, r, v, d, g, !rv),
                5 => cnot_list(t, g, d),
                6 => t.add(v, d, g, self.carry, rv),
                7 => inc(t, r, g, rv),
                _ => canon(t, !rv),
            }
        });
    }
    // gen.cjs:823 trial
    fn trial(&self, t: &mut Tape, witness: bool, back: bool) {
        let nb = self.layouts.len();
        run(t, 6 + nb, back, |t, i| {
            let rv = back;
            if i == 0 || i == 5 + nb { self.direction(t); }
            else if i == 1 { self.pack_number(t, rv); }
            else if i == 2 { self.normalize(t, rv); }
            else if i < 3 + nb { let lay = &self.layouts[i - 3]; if witness { self.odd_witness(t, lay, rv) } else { self.odd_quotient(t, lay, rv) } }
            else if i == 3 + nb { self.normalize(t, !rv); }
            else { self.pack_number(t, !rv); }
        });
    }
    // gen.cjs:422 packNumber
    fn pack_number(&self, t: &mut Tape, back: bool) { mixed(self.ar(), t, &self.r, &self.v, &self.u, &[], back); }
    // gen.cjs:414 normalize
    fn normalize(&self, t: &mut Tape, back: bool) {
        let n = &self.n; let nt = self.tags.len();
        run(t, nt, back, |t, jj| {
            let j = nt - 1 - jj; // js = [0..tag.length).reverse()
            let s = 1usize << j; let tg = self.tags[j];
            let origins = cat(&[&n[M - s..], &n[..M - s]]);
            run(t, 2, back, |t, i| if i == 0 { toggle(t, &[], &n[M - s..], tg) } else { permute(t, n, &origins, &[tg], back) });
        });
    }
    // gen.cjs:751 direction
    fn direction(&self, t: &mut Tape) {
        let x = cat(&[&self.v[1..], &[self.pick]]); let y = &self.u; let n = x.len(); let last = n - 1; let bit = self.dv[1];
        cnot_list(t, &[], &x);
        if n > 1 { toggle(t, &cat(&[&self.ctrl, &[y[last]]]), &[], bit); }
        let mut ops: Vec<[W; 3]> = vec![];
        for i in 1..n { ops.push([NONE, y[i], x[i]]); }
        for i in (1..n.saturating_sub(1)).rev() { ops.push([NONE, y[i], y[i + 1]]); }
        for i in 0..n - 1 { ops.push([x[i], y[i], y[i + 1]]); }
        for o in &ops { t.out(o[0], o[1], o[2]); }
        toggle(t, &cat(&[&self.ctrl, &[y[last], x[last]]]), &[], bit);
        for o in ops.iter().rev() { t.out(o[0], o[1], o[2]); }
        cnot_list(t, &[], &x);
    }
    // gen.cjs:496 TruncatedGeneral.indicator; kind 0 = eq, 1 = gt, 2 = le
    fn indicator(&self, t: &mut Tape, j: usize, kind: u8, controls: &[W], target: W) {
        if kind == 0 {
            let mut yes = controls.to_vec(); let mut no = vec![];
            for i in 0..self.tags.len() { if (j >> i) & 1 == 1 { yes.push(self.tags[i]) } else { no.push(self.tags[i]) } }
            toggle(t, &yes, &no, target);
        } else {
            if kind == 1 { toggle(t, controls, &[], target); }
            const_below(t, &self.tags, &Limbs::small(j as u64 + 1), controls, &[target]);
        }
    }
    // gen.cjs:763 bandMark
    fn band_mark(&self, t: &mut Tape, lay: &Layout) {
        if self.max_shift < 8 { toggle(t, &self.ctrl, &[], self.borrow) } else { self.indicator(t, 7, if lay.lo != 0 { 1 } else { 2 }, &self.ctrl, self.borrow) }
    }
    // gen.cjs:767 roundedDivisor
    fn rounded_divisor(&self, t: &mut Tape, lay: &Layout, back: bool) {
        run(t, 3, back, |t, i| match i {
            0 => t.out(NONE, NONE, lay.d0),
            1 => inc(t, &lay.hh, &[], !back),
            _ => inc(t, &lay.hh[1..], &[self.dv[1]], back),
        });
    }
    // gen.cjs:771 withDivisor
    fn with_divisor(&self, t: &mut Tape, lay: &Layout, back: bool, f: impl FnOnce(&mut Tape, &[W], bool)) {
        self.band_mark(t, lay); self.rounded_divisor(t, lay, false);
        f(t, &[self.g, self.take, self.borrow], back);
        self.rounded_divisor(t, lay, true); self.band_mark(t, lay);
    }
    // gen.cjs:776 onesBlock
    fn ones_block(&self, t: &mut Tape, rr: &[W], d: &[W], n: usize, extra: &[W], ctrl: &[W], back: bool) {
        let tc = self.carry; let origin = cat(&[rr, &[self.dv[0]]]); let active = cat(&[ctrl, extra]);
        toggle(t, &active, &[], tc);
        let mut remain = rr.to_vec(); let mut spare = self.dv[0];
        let mut items: Vec<(W, Vec<W>, W)> = Vec::with_capacity(n); // (input, z, high)
        for _ in 0..n {
            let input = spare; let z = cat(&[&[input], &remain]); let high = *z.last().unwrap();
            remain = z[..z.len() - 1].to_vec(); spare = high; items.push((input, z, high));
        }
        let fin = cat(&[&remain, &[spare]]);
        run(t, 3 * n + 1, back, |t, i| {
            if i == 3 * n { permute(t, &origin, &fin, &[tc], back); return; }
            let (input, ref z, high) = items[i / 3];
            match i % 3 {
                0 => t.out(NONE, tc, input),
                1 => digit(self.ar(), t, z, d, &[tc], back),
                _ => toggle(t, &[tc], &[input], high),
            }
        });
        toggle(t, &active, &[], tc);
    }
    // gen.cjs:788 lowReflect
    fn low_reflect(&self, t: &mut Tape, tt: &[W], w: usize, ctrl: &[W], back: bool) {
        let mut js: Vec<usize> = vec![];
        for j in 0..tt.len().saturating_sub(w) { if j <= self.max_shift { js.push(j); } }
        run(t, 1 + js.len(), back, |t, i| {
            if i == 0 { cnot_list(t, ctrl, tt); return; }
            let j = js[i - 1];
            self.indicator(t, j, 0, ctrl, self.carry);
            inc(t, &tt[w + j..], &[self.carry], back);
            self.indicator(t, j, 0, ctrl, self.carry);
        });
    }
    // gen.cjs:797 oddProduct
    fn odd_product(&self, t: &mut Tape, tt: &[W], d: &[W], ctrl: &[W], back: bool) {
        let m = tt.len() - 1; // split(0, T.length-1).reverse()
        run(t, m, back, |t, ii| {
            let i = m - 1 - ii;
            let on = cat(&[ctrl, &[tt[i]]]);
            toggle(t, &on, &[], self.carry);
            t.add(js_slice(d, 1, tt.len() - i), &tt[i + 1..], &[self.carry], self.pick, back);
            toggle(t, &on, &[], self.carry);
        });
    }
    // gen.cjs:805 oddQuotient
    fn odd_quotient(&self, t: &mut Tape, lay: &Layout, back: bool) {
        self.with_divisor(t, lay, back, |t, ctrl, rv| {
            let tt = &lay.tt[..lay.w + 1]; let d = &lay.d; let w = lay.w;
            let mut js: Vec<usize> = vec![]; let mut j = 0; while j < self.tags.len() && (1usize << j) <= lay.hi { js.push(j); j += 1; }
            let nj = js.len();
            run(t, 4 + nj, rv, |t, i| {
                if i == 0 { cnot_list(t, ctrl, &tt[..w - 2]); }
                else if i == 1 { self.ones_block(t, tt, d, 2, &[], ctrl, rv); }
                else if i < 2 + nj { let j = js[i - 2]; self.ones_block(t, tt, d, 1 << j, &[self.tags[j]], ctrl, rv); }
                else if i == 2 + nj { self.low_reflect(t, tt, w, ctrl, rv); }
                else { self.odd_product(t, tt, d, ctrl, !rv); }
            });
        });
    }
    // gen.cjs:814 oddWitness
    fn odd_witness(&self, t: &mut Tape, lay: &Layout, back: bool) {
        self.with_divisor(t, lay, back, |t, ctrl, _rv| {
            let tt = &lay.tt; let d = &lay.d;
            let pre = |t: &mut Tape, s: bool| run(t, 3, s, |t, i| match i {
                0 => inc(t, tt, &[], s),
                1 => self.odd_product(t, tt, d, &[], s),
                _ => self.low_reflect(t, tt, lay.w, &[], s),
            });
            pre(t, false);
            self.phase_deposit(t, self.dv[0], |t| toggle(t, ctrl, &[*tt.last().unwrap()], self.dv[0]));
            pre(t, true);
        });
    }
    /// run_front.cjs:131 R_k: relabel permute of [r.at(-1), ...u]
    pub fn relabel(&self, t: &mut Tape, back: bool) {
        let rl = *self.r.last().unwrap();
        permute(t, &cat(&[&[rl], &self.u]), &cat(&[&self.u, &[rl]]), &[self.g], back);
    }
    /// run_front.cjs:121-123 the pre-step (sign classification, reflection, V = 1), emitted with row 0's object
    pub fn pre(&self, t: &mut Tape, back: bool) {
        let g = [self.g];
        let p1 = self.p.add_small(1); let half = p1.shr1();
        run(t, 3, back, |t, i| match i {
            0 => { toggle(t, &g, &[], self.sig); const_below(t, &self.r, &half, &g, &[self.sig]); }
            1 => reflect(t, &self.r, &[self.g, self.sig], back),
            _ => toggle(t, &g, &[], self.bank[0]),
        });
    }
}

// ------------------------------------------------------------------------------------------------ unit row
/// front.cjs:137 FrontUnit (constructor chain gen.cjs:370 UnitPreparation -> front.cjs:138)
pub struct Unit {
    k: usize, r: Vec<W>, u: Vec<W>, bank: Vec<W>, v: Vec<W>, a: Vec<W>, full_v: Vec<W>, dirty: Vec<W>,
    g: W, sign: W, shape: W, fired: W, qual: W, pick: W, carry: W, norm: W, zf: usize,
    prime1: Limbs, mt: Cell<Option<W>>,
    pub hosted: Vec<W>,
}
impl Unit {
    pub fn new(k: usize, cfg: &Config) -> Result<Unit, String> {
        if k == 0 || k >= M / 2 - 1 { return Err("bad unit-preparation control width".into()); }
        let r = range(0, M - k); let u = range(M - k, M + 1); let bank = range(M + 1, M + 1 + HALF);
        let lo = (k + 2).max(cfg.zf[k]); let supply = cfg.supply(lo);
        if supply.len() < 7 { return Err(format!("unit row {k}: needs 7 hosted lanes, supply {}", supply.len())); }
        let (shape, fired, qual, pick, carry, norm, spare) = (supply[0], supply[1], supply[2], supply[3], supply[4], supply[5], supply[6]);
        let v = bank[..k + 1].to_vec(); let full_v = bank[..k + 2].to_vec(); let a = cat(&[&u, &[spare]]);
        Ok(Unit { k, r, u, bank, v, a, full_v, dirty: cfg.passenger.clone(), g: cfg.g, sign: cfg.flags[0], shape, fired, qual, pick,
            carry, norm, zf: cfg.zf[k], prime1: prime().add_small(1), mt: Cell::new(None),
            hosted: vec![pick, carry, norm, spare, shape, qual, fired] })
    }
    fn ar(&self) -> Ar { Ar { pick: self.pick, carry: self.carry } }
    // gen.cjs:382 UnitPreparation.unit
    fn unit(&self, t: &mut Tape, ctrl: &[W], back: bool) {
        let ar = self.ar(); let (v, a, r) = (&self.v, &self.a, &self.r);
        let d = &self.dirty[..v.len()]; let wide = cat(&[d, &[self.bank[v.len()]]]); let word = cat(&[r, &wide]);
        let dn = cat(&[d, &[self.norm]]);
        let canon = |t: &mut Tape, rv: bool| digit(ar, t, &dn, v, ctrl, rv);
        let tmp = cat(&[a, &self.full_v]); let swap = cat(&[&self.full_v, a]);
        run(t, 11, back, |t, i| {
            let rv = back;
            match i {
                0 => t.add(v, a, ctrl, self.carry, rv),
                1 => canon(t, rv),
                2 => mixed(ar, t, r, a, &wide, ctrl, rv),
                3 => reflect(t, &word, ctrl, rv),
                4 => inc(t, &word, ctrl, !rv),
                5 => mixed(ar, t, r, v, d, ctrl, !rv),
                6 => cnot_list(t, ctrl, d),
                7 => t.add(v, d, ctrl, self.carry, rv),
                8 => canon(t, !rv),
                9 => inc(t, r, ctrl, rv),
                _ => permute(t, &tmp, &swap, ctrl, rv),
            }
        });
    }
    // front.cjs:149 FrontUnit.emit
    pub fn emit(&self, t: &mut Tape, back: bool) {
        let ar = self.ar(); let (r, v, a, c) = (&self.r, &self.v, &self.a, &self.full_v);
        let sel = [self.g, self.shape]; let active = [self.g, self.qual];
        let rc = cat(&[r, c]);
        let shape = |t: &mut Tape| {
            let hi = &self.bank[self.k + 1..(self.k + 1).max(self.zf)]; let pos = [self.g, self.bank[self.k]];
            toggle(t, &pos, hi, self.shape); toggle(t, &pos, &cat(&[hi, &r[M / 2..]]), self.shape);
        };
        let qual = |t: &mut Tape| toggle(t, &sel, &[*a.last().unwrap()], self.qual);
        let mark = |t: &mut Tape| {
            // gen.cjs:701 phaseDeposit
            let write = |t: &mut Tape| { toggle(t, &active, &[], self.fired); const_below(t, &rc, &self.prime1, &active, &[self.fired]); };
            write(t); if self.mt.get() == Some(self.fired) { t.z(self.fired); write(t); }
        };
        let pre = |t: &mut Tape, rv: bool| run(t, 13, rv, |t, i| match i {
            0 | 12 => shape(t),
            1 | 3 => t.add(v, a, &[], self.carry, rv),
            2 | 10 => qual(t),
            4 => inc(t, c, &[], !rv),
            5 => mixed(ar, t, r, a, c, &[], rv),
            6 => mark(t),
            7 => mixed(ar, t, r, a, c, &[], !rv),
            8 => inc(t, c, &[], rv),
            _ => t.add(v, a, &[], self.carry, !rv), // 9, 11
        });
        let gf = [self.g, self.fired];
        run(t, 4, back, |t, i| {
            let rv = back;
            match i {
                0 => {
                    if rv {
                        // gen.cjs:702 retirePredicate
                        let bit = t.hmr(self.fired);
                        t.cond(bit, |t| { self.mt.set(Some(self.fired)); pre(t, rv); self.mt.set(None); });
                    } else { pre(t, rv) }
                }
                1 => self.unit(t, &gf, rv),
                2 => toggle(t, &gf, &[], self.sign),
                _ => toggle(t, &[self.g, self.u[self.k]], &[], self.fired),
            }
        });
    }
}

// ------------------------------------------------------------------------------------------------ driver
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir { Fwd, Rev }

/// Emission parameters.
pub struct Params<'a> {
    /// physical lane (0..633) -> output lane id
    pub map: &'a [u32],
    /// classical bit index of the first HMR this call emits (later HMRs: +1 each, in stream order)
    pub cbit_base: u32,
    /// round discipline, reverse only: classical bit of the FORWARD witness HMR of row k is hist_base + (k - k_lo)
    /// (the forward front of the same rows emits exactly one HMR per row, in row order, starting at its cbit_base)
    pub hist_base: u32,
    /// true = production "round" discipline (run_front.cjs mode round: forward retires the witness flag by a bare HMR,
    /// the reverse applies the deferred phase); false = run_front.cjs fwd / rev standalone discipline
    pub round: bool,
    /// emit the pre-step (sign classification + reflection + V = 1) before row k_lo (forward) / after it (reverse);
    /// run_front.cjs emits it with row 0
    pub include_pre: bool,
}

#[derive(Clone, Debug, Default)]
pub struct FrontStats { pub hmr: u32, pub next_bit: u32, pub rows: Vec<usize> }

/// Stream the ops of rows k_lo..=k_hi (forward: pre?, then per row U_k, G_k, R_k ascending; reverse: the exact
/// inverse order, per row R_k, G_k, U_k descending, then pre?) to `sink`.
pub fn front(cfg: &Config, k_lo: usize, k_hi: usize, dir: Dir, prm: &Params, sink: &mut dyn FnMut(Op)) -> Result<FrontStats, String> {
    if k_hi >= cfg.k_rows || k_lo > k_hi { return Err("row range".into()); }
    if prm.map.len() < cfg.physical() { return Err("lane map shorter than the physical width".into()); }
    let back = dir == Dir::Rev;
    let mut hist = None;
    if prm.round {
        let mut h = vec![None; HALF];
        if back { for k in k_lo..=k_hi { h[k] = Some(prm.hist_base + (k - k_lo) as u32); } }
        hist = Some(h);
    }
    let mut t = Tape { one: cfg.g, nids: cfg.logical, excl: cfg.excl, map: prm.map, sink, current: None, next_bit: prm.cbit_base, hist, hmr_count: 0 };
    let row0 = if prm.include_pre { Some(General::new(0, cfg)?) } else { None };
    let mut rows: Vec<usize> = (k_lo..=k_hi).collect();
    if back { rows.reverse(); }
    if !back { if let Some(r0) = &row0 { r0.pre(&mut t, false); } }
    for &k in &rows {
        let g = General::new(k, cfg)?;
        let u = if k > 0 && k < HALF - 1 { Some(Unit::new(k, cfg)?) } else { None };
        if !back {
            if let Some(u) = &u { u.emit(&mut t, false); }
            g.emit(&mut t, false); g.relabel(&mut t, false);
        } else {
            g.relabel(&mut t, true); g.emit(&mut t, true);
            if let Some(u) = &u { u.emit(&mut t, true); }
        }
    }
    if back { if let Some(r0) = &row0 { r0.pre(&mut t, true); } }
    if let Some(h) = &t.hist { if back && h.iter().any(|x| x.is_some()) { return Err("unfinished deferred phases".into()); } }
    Ok(FrontStats { hmr: t.hmr_count, next_bit: t.next_bit, rows })
}

/// identity lane map for the 633 physical lanes
pub fn identity_map(cfg: &Config) -> Vec<u32> { (0..cfg.physical() as u32).collect() }

// ------------------------------------------------------------------------------------------------ stream digest
/// gen.cjs:34 codeGate on physical ids (identity map), 1023 = absent control
pub fn code_gate(a: u32, b: u32, t: u32) -> u32 { (a * 1024 + b) * 1024 + t }

/// Running signature and counts exactly as gen.cjs MeasuredNct keeps them (sig: gen.cjs:49 Tape.out / 903 MeasuredNct.hmr).
#[derive(Clone, Debug)]
pub struct Digest { pub sig: u32, pub count: [u64; 3], pub controlled: [u64; 3], pub measured: u64, pub z: u64, pub ops: u64 }
impl Default for Digest { fn default() -> Self { Digest { sig: 0x811c9dc5, count: [0; 3], controlled: [0; 3], measured: 0, z: 0, ops: 0 } } }
impl Digest {
    pub fn add(&mut self, op: &Op) {
        self.ops += 1;
        let (code, kind, cond) = match *op {
            Op::X { t, cond } => (code_gate(NONE, NONE, t), 0, cond),
            Op::Cx { c, t, cond } => (code_gate(NONE, c, t), 1, cond),
            Op::Ccx { a, b, t, cond } => (code_gate(a, b, t), 2, cond),
            Op::Hmr { q, .. } => { self.measured += 1; self.sig = (self.sig ^ (0xffe00000u32.wrapping_add(q))).wrapping_mul(0x01000193); return; }
            Op::Z { .. } => { self.z += 1; return; }
            Op::CondBegin { .. } | Op::CondEnd => return,
        };
        self.count[kind] += 1; if cond.is_some() { self.controlled[kind] += 1; }
        self.sig = (self.sig ^ code).wrapping_mul(0x01000193);
    }
}

/// The op in the dump encoding of hr1/js/dump.cjs (1 or 2 u32 words), physical ids.
pub fn encode(op: &Op, out: &mut Vec<u32>) {
    match *op {
        Op::X { t, cond } => out.push(code_gate(NONE, NONE, t) | if cond.is_some() { 1 << 30 } else { 0 }),
        Op::Cx { c, t, cond } => out.push(code_gate(NONE, c, t) | if cond.is_some() { 1 << 30 } else { 0 }),
        Op::Ccx { a, b, t, cond } => out.push(code_gate(a, b, t) | if cond.is_some() { 1 << 30 } else { 0 }),
        Op::Hmr { q, bit } => { out.push(0x8100_0000 | q); out.push(bit); }
        Op::Z { q, .. } => out.push(0x8200_0000 | q),
        Op::CondBegin { bit } => { out.push(0x8300_0000); out.push(bit); }
        Op::CondEnd => out.push(0x8400_0000),
    }
}

// ------------------------------------------------------------------------------------------------ hi1 addition
// Everything above is hr1/capfront/src/lib.rs byte for byte (sha256 e2d4c67b...).  Added by hi1 (hybrid splice of the
// 633 package): the JOIN item order of hj1 (hybridwalk/hj1/emit.cjs), which differs from `front` only at the ends:
//   forward  R0, U1, G1, R1, ..., U(k_hi), G(k_hi)            (R0 first, R(k_hi) omitted: his P_K = before the relabel)
//   reverse  inverse of U1, G1, R1, ..., U(k_hi), G(k_hi), R(k_hi)  (= `front(cfg, 1, k_hi, Rev, ..)`, delegated)
// Round discipline only; HMR bits as in `front` (forward: cbit_base + (k - 1) for row k).
pub fn front_join(cfg: &Config, k_hi: usize, dir: Dir, prm: &Params, sink: &mut dyn FnMut(Op)) -> Result<FrontStats, String> {
    if !prm.round || prm.include_pre { return Err("front_join: round discipline without pre-step only".into()); }
    if dir == Dir::Rev { return front(cfg, 1, k_hi, Dir::Rev, prm, sink); }
    if k_hi >= cfg.k_rows || k_hi < 1 || k_hi >= HALF - 1 { return Err("row range".into()); }
    if prm.map.len() < cfg.physical() { return Err("lane map shorter than the physical width".into()); }
    let hist = Some(vec![None; HALF]);
    let mut t = Tape { one: cfg.g, nids: cfg.logical, excl: cfg.excl, map: prm.map, sink, current: None, next_bit: prm.cbit_base, hist, hmr_count: 0 };
    General::new(0, cfg)?.relabel(&mut t, false);
    for k in 1..=k_hi {
        let g = General::new(k, cfg)?;
        Unit::new(k, cfg)?.emit(&mut t, false);
        g.emit(&mut t, false);
        if k < k_hi { g.relabel(&mut t, false); }
    }
    Ok(FrontStats { hmr: t.hmr_count, next_bit: t.next_bit, rows: (1..=k_hi).collect() })
}

// ------------------------------------------------------------------------------------------------ pre3 addition
// pre3 (2026-11-25, local research): his column 1 replaced by our generator.  MEASURED (pre3eq fwd1, walk 1, 8192 random shots, 0 differing
// lanes at his P_2): his walk starts from a DIRTY entry state: lane Z20 (wire 276) = carry c16 of Y[0..16) + 977 = [Y[0..16) >= 0xFC2F]
// (algebraic identity at 48 random points, pre3eq alg1), which his column 1 cleans; and his P_2 has Y0 (wire 390) and H1 (wire 387) flipped
// relative to the generator's state after G0 (his next two records are X Y0, X H1).  So
//   forward block = Cl, pre-step, G0 (no R0: the old region 0 / 2 block starts with R0), X Y0, X H1
//   reverse block = R0^-1, X H1, X Y0, G0^-1, pre-step^-1, Cl
// Round discipline: row 0's witness HMR goes to classical bit `cbit_base` (forward) / is read from `hist_base` (reverse).
const Y0: W = 390; const H1: W = 387; const H0: W = 386; const Z20: W = 276; const ANC0: W = 356;
/// ladder: out ^= ctrl & AND(ys) with fresh zero ancillas anc[..ys.len()-1] (computed and uncomputed; out keeps the result)
fn ladder(t: &mut Tape, ctrl: W, ys: &[W], out: W, anc: &[W]) {
    let n = ys.len(); let mut prev = ctrl;
    for i in 0..n - 1 { t.out(prev, ys[i], anc[i]); prev = anc[i]; }
    t.out(prev, ys[n - 1], out);
    for i in (0..n - 1).rev() { let p = if i == 0 { ctrl } else { anc[i - 1] }; t.out(p, ys[i], anc[i]); }
}
/// The dirty carries of his walk entry: Z20 + j (lane ids 532..) = carry of Y + (2^32 + 977) into bit 16 (j = 0), 32, 48, 64, 80, ...
/// (polynomial identities, pre3eq alg1: c16 = AND(Y10..Y15) & [Y0..Y9 >= 47]; c32 = c16 & AND(Y16..Y31); c33 = Y32 | c32; c48 = c33 & AND(Y33..Y47);
/// c(16k) = c(16(k-1)) & AND(Y(16(k-1))..Y(16k-1)) for k >= 4).  Cleaned for Z20..Z24 (c16, c32, c48, c64, c80: probabilities 1.5e-2, 2^-22, 2^-16, 2^-32, 2^-48);
/// Z25.. (c96 and above, <= 2^-64 per shot) are left.  All ancillas are the clean bank wires Z100.. (computed and uncomputed).
/// out ^= c16 = AND(Y10..Y15) & [Y0..Y9 >= 47] (ancillas a(1..14) = Z101.. computed and uncomputed)
fn c16_xor(t: &mut Tape, out: W) {
    let y = |i: W| Y0 + i; let a = |j: W| ANC0 + j;
    let x = |t: &mut Tape, w: W| t.out(NONE, NONE, w);
    let ce = |t: &mut Tape, c1: W, c2: W, tg: W| t.out(c1, c2, tg);
    let seq: Vec<(W, W, W)> = vec![(y(10), y(11), a(1)), (a(1), y(12), a(2)), (a(2), y(13), a(3)), (a(3), y(14), a(4)), (a(4), y(15), a(5))];
    for &(c1, c2, tg) in seq.iter() { ce(t, c1, c2, tg); }
    for i in 6..10 { x(t, y(i)); }
    ce(t, y(6), y(7), a(6)); ce(t, a(6), y(8), a(7)); ce(t, a(7), y(9), a(8));
    for i in 6..10 { x(t, y(i)); }
    ce(t, y(0), y(1), a(9)); ce(t, a(9), y(2), a(10)); ce(t, a(10), y(3), a(11));
    x(t, y(4)); x(t, a(11)); ce(t, y(4), a(11), a(12)); x(t, y(4)); x(t, a(11));
    x(t, a(12)); ce(t, y(5), a(12), a(13)); x(t, a(12));
    x(t, a(13)); ce(t, a(8), a(13), a(14)); x(t, a(13));
    x(t, a(14)); ce(t, a(5), a(14), out); x(t, a(14));
    x(t, a(13)); ce(t, a(8), a(13), a(14)); x(t, a(13));
    x(t, a(12)); ce(t, y(5), a(12), a(13)); x(t, a(12));
    x(t, y(4)); x(t, a(11)); ce(t, y(4), a(11), a(12)); x(t, y(4)); x(t, a(11));
    ce(t, a(10), y(3), a(11)); ce(t, a(9), y(2), a(10)); ce(t, y(0), y(1), a(9));
    for i in 6..10 { x(t, y(i)); }
    ce(t, a(7), y(9), a(8)); ce(t, a(6), y(8), a(7)); ce(t, y(6), y(7), a(6));
    for i in 6..10 { x(t, y(i)); }
    for &(c1, c2, tg) in seq.iter().rev() { ce(t, c1, c2, tg); }
}
pub fn clean_z20(t: &mut Tape) {
    let y = |i: W| Y0 + i; let a = |j: W| ANC0 + j;
    let x = |t: &mut Tape, w: W| t.out(NONE, NONE, w);
    let ce = |t: &mut Tape, c1: W, c2: W, tg: W| t.out(c1, c2, tg);
    let (f16, c33, f32, f48, f64, f80) = (a(0), a(15), a(16), a(17), a(18), a(19));
    let lw: Vec<W> = (0..15).map(|j| 316 + j).collect();   // Z60..Z74: ladder ancillas (clean at entry)
    let ys = |lo: W, hi: W| -> Vec<W> { (lo..hi).map(|i| y(i)).collect() };
    c16_xor(t, f16);
    ce(t, NONE, f16, Z20);
    ladder(t, f16, &ys(16, 32), f32, &lw);  ce(t, NONE, f32, Z20 + 1);
    x(t, y(32)); x(t, f32); ce(t, y(32), f32, c33); x(t, y(32)); x(t, f32); x(t, c33);   // c33 = Y32 | c32
    ladder(t, c33, &ys(33, 48), f48, &lw);  ce(t, NONE, f48, Z20 + 2);
    ladder(t, f48, &ys(48, 64), f64, &lw);  ce(t, NONE, f64, Z20 + 3);
    ladder(t, f64, &ys(64, 80), f80, &lw);  ce(t, NONE, f80, Z20 + 4);
    ladder(t, f64, &ys(64, 80), f80, &lw);
    ladder(t, f48, &ys(48, 64), f64, &lw);
    ladder(t, c33, &ys(33, 48), f48, &lw);
    x(t, c33); x(t, y(32)); x(t, f32); ce(t, y(32), f32, c33); x(t, y(32)); x(t, f32);
    ladder(t, f16, &ys(16, 32), f32, &lw);
    c16_xor(t, f16);
}
/// pre5: set by hybrid::gen_x_i for walk 3 (clean entry at its seam)
pub static X_NOCLEAN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
pub fn front_x(cfg: &Config, prm: &Params, rev: bool, sink: &mut dyn FnMut(Op)) -> Result<FrontStats, String> {
    if !prm.round { return Err("front_x: round discipline only".into()); }
    if prm.map.len() < cfg.physical() { return Err("lane map shorter than the physical width".into()); }
    let mut hist = vec![None; HALF]; if rev { hist[0] = Some(prm.hist_base); }
    // pre4 (2026-11-25): the FORWARD block is self-contained: row 0's witness flag is retired inside the block (bare HMR + conditioned
    // recompute with the phase deposit, his own column-1 discipline: hist = None) instead of deferring the phase fix to a reverse block that
    // walk 2 does not have while its column 1 is still his.  PRE4_OLD=1 restores the pre3 behaviour (A/B tests only).
    let selfc = !rev && Err::<String, ()>(()).is_err();
    let mut t = Tape { one: cfg.g, nids: cfg.logical, excl: cfg.excl, map: prm.map, sink, current: None, next_bit: prm.cbit_base, hist: if selfc { None } else { Some(hist) }, hmr_count: 0 };
    let g = General::new(0, cfg)?;
    if !rev {
        if Err::<String, ()>(()).is_err() && !X_NOCLEAN.load(std::sync::atomic::Ordering::SeqCst) { clean_z20(&mut t); } if Err::<String, ()>(()).is_ok() { t.out(NONE, NONE, 255); } if Err::<String, ()>(()).is_err() { g.pre(&mut t, false); } g.emit(&mut t, false); t.out(NONE, NONE, Y0); t.out(NONE, NONE, H1);
    } else {
        g.relabel(&mut t, true); g.emit(&mut t, true); g.pre(&mut t, true); clean_z20(&mut t);
    }
    Ok(FrontStats { hmr: t.hmr_count, next_bit: t.next_bit, rows: vec![0] })
}

/// test hook: the cleaning circuit alone
pub fn clean_only(cfg: &Config, prm: &Params, sink: &mut dyn FnMut(Op)) {
    let mut t = Tape { one: cfg.g, nids: cfg.logical, excl: cfg.excl, map: prm.map, sink, current: None, next_bit: prm.cbit_base, hist: Some(vec![None; HALF]), hmr_count: 0 };
    clean_z20(&mut t);
}

pub fn generate(which:usize,capped:bool)->Vec<[u16;4]>{
let tag=if capped{"cap"}else if which==0{"col1"}else{"col3"};let mut output=Vec::new();
    let cfg=Config::new(64,24);
    let map=identity_map(&cfg);
    let prm=Params{map:&map,cbit_base:if tag=="cap"{65401}else{65400},hist_base:0,round:true,include_pre:false};
    X_NOCLEAN.store(tag=="col3",std::sync::atomic::Ordering::SeqCst);
let mut sink=|op:Op|{
        let none=u16::MAX;
        let row=match op{
            Op::X{t,..}=>[6,t as u16,none,none],Op::Cx{c,t,..}=>[8,c as u16,t as u16,none],
            Op::Ccx{a,b,t,..}=>[13,a as u16,b as u16,t as u16], Op::Z{q,..}=>[7,q as u16,none,none],
            Op::Hmr{q,bit}=>[12,q as u16,bit as u16,none],Op::CondBegin{bit}=>[15,bit as u16,none,none],
            Op::CondEnd=>[16,none,none,none]
        };
output.push(row);};
    if tag=="cap"{
        front_join(&cfg,63,Dir::Fwd,&prm,&mut sink).unwrap();
        for i in 1..=63{sink(Op::X{t:390+i,cond:None});}
    }else{
        front_x(&cfg,&prm,false,&mut sink).unwrap();
        // hybrid::Conv retires the row-0 classical condition after the scope pop.
        let row=[4u16,65400,u16::MAX,u16::MAX];
output.push(row);
}
output
}
