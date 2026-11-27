// q631 / i10 copy of r3walkgen.rs (R3: base633 walkgen.rs + SHIFT_CAP): + block labels (LOG) for the anatomy tools and the
// flag-free enable variant (see i10walkplan.rs); with LOG off and the variant off the output is r3walkgen's byte for byte
//! Rust port of the divide-walk emitters used for the replacement inner / reverse walks of the two divide blocks
//! (the public D2Canonical / D2Reduced / SectorReduced walk classes of the Q651 generator, with the D14 "walk-small" edits
//! rot2 + zeroPair + select and nasqret's graded relay, driven by explicit physical wire lists).
//! Output: records [kind, a, b, c] (X = [6,t,NONE,NONE], CX = [8,c,t,NONE], CCX = [13,a,b,t]) in the generator's own wire numbering.
//! The module mirrors the JS code block for block (plan = list of blocks; a block is a closure that appends gates to `W::g`).
use std::rc::Rc;
pub type V = Vec<i32>;
type Wr = Rc<V>;
const NONE16: u16 = u16::MAX;
/// R3: largest shift served by the relay sectors (usize::MAX = the stock generator)
pub static SHIFT_CAP: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(usize::MAX);
thread_local! {
    /// i10: when Some, run() appends (first output record, end, label) per block
    pub static LOG: std::cell::RefCell<Option<Vec<(usize, usize, u64)>>> = std::cell::RefCell::new(None);
}
/// i10 label: typ | k << 8 | base << 16 | kind << 24 | i << 32 | sector << 40
pub fn lab(typ: u64, k: usize, base: usize, kind: usize, i: usize, sec: usize) -> u64 { typ | (k as u64) << 8 | (base as u64 & 255) << 16 | (kind as u64) << 24 | (i as u64 & 255) << 32 | (sec as u64) << 40 }

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Kind {
    /// D2Canonical inner walk, graded relay with `real` clean tags
    Inner { real: usize },
    /// D2ReducedImpl (reverse "R4s"): walk-small rot + pair + select
    RevImpl,
    /// SectorReduced (reverse "R5s": aux based): walk-small rot only
    RevSector,
}

pub struct Cfg {
    pub n: usize,
    pub kind: Kind,
    /// number of tags kept on the walk object before the relay adapts it (4 for inner, 4/5 for reverse)
    pub tags: usize,
    pub l: V,
    pub r: V,
    pub loan: V,
    pub ws_tag: V,
    pub sign: i32,
    pub fire: i32,
    pub tst: i32,
    pub aux: i32,
}

struct W {
    n: usize,
    l: V,
    r: V,
    y: V,
    tag: V,
    sign: i32,
    fire: i32,
    tst: i32,
    aux: i32,
    cin: i32,
    g: Vec<u32>,
    rot2: bool,
    canon_op: bool,
    aux_restore: bool,
    mark: Vec<u32>,
    stamp: u32,
}
type F = Box<dyn Fn(&mut W)>;
struct Block {
    lab: u64,
    f: F,
    rev: bool,
    top: Option<i32>,
    ports: Vec<Option<i32>>,
    pre: bool,
    tag: Option<V>,
}

fn cat(a: &[i32], b: &[i32]) -> V {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    v
}
fn cat1(a: &[i32], x: i32) -> V {
    let mut v = a.to_vec();
    v.push(x);
    v
}
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

impl W {
    fn new(n: usize, ntag_slice: usize) -> W {
        let l: V = (0..n as i32 + 2).collect();
        let r: V = l.iter().map(|i| i + n as i32 + 2).collect();
        let data = (2 * (n + 2) + (n + 1) + 2 * n) as i32;
        let y: V = (0..2 * n as i32).map(|i| 3 * n as i32 + 5 + i).collect();
        let mut nt = 0;
        while (1usize << nt) < n {
            nt += 1;
        }
        let mut tag: V = (0..nt as i32).map(|i| data + 2 + i).collect();
        let fire = *tag.last().unwrap() + 1;
        let tst = fire + 1;
        let aux = fire + 2;
        tag.truncate(ntag_slice.min(tag.len()));
        let cin = r[n + 1];
        W { n, l, r, y, tag, sign: data + 1, fire, tst, aux, cin, g: Vec::new(), rot2: false, canon_op: false, aux_restore: false, mark: vec![0; 1024], stamp: 0 }
    }
    #[inline]
    fn raw(&mut self, a: i32, b: i32, z: i32) {
        self.g.push((((if a < 0 { 1023 } else { a }) as u32) << 20) | (((if b < 0 { 1023 } else { b }) as u32) << 10) | z as u32);
    }
    fn x(&mut self, z: i32) {
        self.raw(-1, -1, z);
    }
    fn xs(&mut self, a: &[i32]) {
        for &z in a {
            self.raw(-1, -1, z);
        }
    }
    /// op(c, z): multi-controlled NOT with borrowed (dirty) loans from `y`
    fn op(&mut self, c: &[i32], z: i32) {
        if c.len() <= 2 {
            self.raw(if c.is_empty() { -1 } else { c[0] }, if c.len() == 2 { c[1] } else { -1 }, z);
            return;
        }
        let n = c.len();
        let need = n - 2;
        let mut b: Vec<i32> = Vec::with_capacity(need);
        if self.canon_op {
            self.stamp += 1;
            let st = self.stamp;
            for &q in c {
                self.mark[q as usize] = st;
            }
            for &q in &self.y {
                if q != z && self.mark[q as usize] != st {
                    b.push(q);
                    if b.len() == need {
                        break;
                    }
                }
            }
        } else {
            for &q in self.y.iter().take(need) {
                b.push(q);
            }
        }
        if need > b.len() {
            panic!("borrow");
        }
        for s in 0..2 {
            if s == 0 {
                self.raw(c[0], c[1], b[0]);
            }
            for i in 1..n - 2 {
                self.raw(c[i + 1], b[i - 1], b[i]);
            }
            self.raw(c[n - 1], b[n - 3], z);
            for i in (1..=n - 3).rev() {
                self.raw(c[i + 1], b[i - 1], b[i]);
            }
            if s == 0 {
                self.raw(c[0], c[1], b[0]);
            }
        }
    }
    fn swap(&mut self, c: &[i32], a: i32, b: i32) {
        if a == b {
            return;
        }
        self.raw(a, -1, b);
        self.op(&cat1(c, b), a);
        self.raw(a, -1, b);
    }
    fn rot_old(&mut self, c: &[i32], a: &[i32], s: i64) {
        let n = a.len() as i64;
        let s = ((s % n) + n) % n;
        if s == 0 {
            return;
        }
        let mut seen = vec![false; n as usize];
        for k in 0..n {
            if seen[k as usize] {
                continue;
            }
            seen[k as usize] = true;
            let mut j = (k + s) % n;
            while j != k {
                self.swap(c, a[k as usize], a[j as usize]);
                seen[j as usize] = true;
                j = (j + s) % n;
            }
        }
    }
    fn rot(&mut self, c: &[i32], a: &[i32], s: i64) {
        if !self.rot2 {
            return self.rot_old(c, a, s);
        }
        let n = a.len() as i64;
        let s = ((s % n) + n) % n;
        if s == 0 {
            return;
        }
        let refl = |a0: i64| -> Vec<(i32, i32)> {
            let mut q = Vec::new();
            for i in 0..n {
                let j = (((a0 - i) % n) + n) % n;
                if i < j {
                    q.push((a[i as usize], a[j as usize]));
                }
            }
            q
        };
        let v1 = refl(0);
        let v2 = refl(s);
        let pairs = (v1.len() + v2.len()) as i64;
        if c.len() != 2 || 4 * pairs + 2 >= 6 * (n - gcd(n as usize, s as usize) as i64) {
            return self.rot_old(c, a, s);
        }
        let d = *self.y.iter().find(|q| !c.contains(q) && !a.contains(q)).expect("rotation loan");
        for v in [&v1, &v2] {
            for &(p, q) in v.iter() {
                self.raw(p, -1, q);
            }
            for &(p, q) in v.iter() {
                self.raw(d, q, p);
            }
            self.raw(c[0], c[1], d);
            for &(p, q) in v.iter() {
                self.raw(d, q, p);
            }
            for &(p, q) in v.iter() {
                self.raw(p, -1, q);
            }
        }
    }
    fn zer(&mut self, c: &[i32], arr: &[i32], z: i32) {
        self.xs(arr);
        self.op(&cat(c, arr), z);
        self.xs(arr);
    }
    fn zero_pair(&mut self, c: &[i32], small: &[i32], large: &[i32], z: i32) {
        assert!(small.iter().all(|q| large.contains(q)), "not nested");
        let mut cs = cat(c, small);
        for &q in large {
            if !small.contains(&q) {
                cs.push(q);
            }
        }
        let k = c.len() + small.len();
        let n = cs.len();
        if k < 3 || k >= n {
            self.zer(c, small, z);
            self.zer(c, large, z);
            return;
        }
        let loan: V = self.y.iter().cloned().filter(|&q| q != z && !cs.contains(&q)).collect();
        assert!(loan.len() >= n - 2, "pair loan");
        self.xs(large);
        for _ in 0..2 {
            self.raw(cs[0], cs[1], loan[0]);
            if k == 3 {
                self.raw(cs[2], loan[0], z);
            }
            for j in 2..=n - 2 {
                self.raw(cs[j], loan[j - 2], loan[j - 1]);
                if j + 2 == k {
                    self.raw(cs[k - 1], loan[k - 3], z);
                }
            }
            self.raw(cs[n - 1], loan[n - 3], z);
            for j in (2..=n - 2).rev() {
                self.raw(cs[j], loan[j - 2], loan[j - 1]);
            }
        }
        self.xs(large);
    }
    fn reverse<G: FnOnce(&mut W)>(&mut self, f: G) {
        let p = self.g.len();
        f(self);
        self.g[p..].reverse();
    }
    /// UnitWalk.add (h = None: no carry out)
    fn add(&mut self, c: &[i32], a: &[i32], b: &[i32], h: Option<i32>) {
        let n = a.len();
        let k = n - 1;
        if n == 1 {
            if let Some(h) = h {
                self.op(&cat(c, &[a[0], b[0]]), h);
            }
            self.op(&cat1(c, a[0]), b[0]);
            return;
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        if let Some(h) = h {
            self.op(&cat1(c, a[k]), h);
        }
        for i in (1..=n - 2).rev() {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 0..n - 1 {
            self.raw(b[i], a[i], a[i + 1]);
        }
        if let Some(h) = h {
            self.op(&cat(c, &[b[k], a[k]]), h);
        }
        self.op(&cat1(c, a[k]), b[k]);
        for i in (0..=n - 2).rev() {
            self.raw(b[i], a[i], a[i + 1]);
            self.op(&cat1(c, a[i]), b[i]);
        }
        for i in 1..n - 1 {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
    }
    fn lt(&mut self, c: &[i32], a: &[i32], b: &[i32], h: i32) {
        let n = a.len();
        let k = n - 1;
        self.xs(b);
        if n == 1 {
            self.op(&cat(c, &[a[0], b[0]]), h);
            self.raw(-1, -1, b[0]);
            return;
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.op(&cat1(c, a[k]), h);
        for i in (1..=n - 2).rev() {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 0..n - 1 {
            self.raw(b[i], a[i], a[i + 1]);
        }
        self.op(&cat(c, &[b[k], a[k]]), h);
        for i in (0..=n - 2).rev() {
            self.raw(b[i], a[i], a[i + 1]);
        }
        for i in 1..n - 1 {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.xs(b);
    }
    /// dirtyDigit (the loan is a single dirty lane)
    fn dirty_digit(&mut self, a: &[i32], b: &[i32], h: i32, e: i32, loan: i32) {
        let n = a.len();
        let last = n - 1;
        macro_rules! three {
            ($s:ident, $a:expr, $b:expr, $c:expr, $d:expr) => {{
                $s.raw($a, $b, loan);
                $s.raw(loan, $c, $d);
                $s.raw($a, $b, loan);
                $s.raw(loan, $c, $d);
            }};
        }
        if n == 1 {
            self.x(b[0]);
            three!(self, e, a[0], b[0], h);
            self.x(b[0]);
            self.raw(e, -1, h);
            three!(self, e, h, a[0], b[0]);
            return;
        }
        self.xs(b);
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.raw(e, a[last], h);
        for i in (1..=n - 2).rev() {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 0..n - 1 {
            self.raw(b[i], a[i], a[i + 1]);
        }
        three!(self, e, a[last], b[last], h);
        self.raw(e, -1, h);
        three!(self, e, h, a[last], b[last]);
        for i in (0..=n - 2).rev() {
            self.raw(b[i], a[i], a[i + 1]);
            three!(self, e, h, a[i], b[i]);
        }
        for i in 1..n - 1 {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.xs(b);
    }
    /// digit(n,A,B,h,e,t) of emit109-reverse-digits (e and t given)
    fn digit(&mut self, a: &[i32], b: &[i32], h: i32, e: i32, t: i32) {
        let n = a.len();
        let end = n - 1;
        if n == 1 {
            self.x(b[0]);
            self.raw(e, a[0], t);
            self.raw(t, b[0], h);
            self.x(b[0]);
            self.raw(e, -1, h);
            self.raw(t, h, b[0]);
            self.raw(e, a[0], t);
            return;
        }
        self.xs(b);
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.raw(e, a[end], h);
        for i in (1..=n - 2).rev() {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 0..n - 1 {
            self.raw(b[i], a[i], a[i + 1]);
        }
        self.raw(e, a[end], t);
        self.raw(t, b[end], h);
        self.raw(e, a[end], t);
        self.raw(e, -1, h);
        self.raw(e, h, t);
        let p = t;
        self.raw(p, a[end], b[end]);
        for i in (0..=n - 2).rev() {
            self.raw(b[i], a[i], a[i + 1]);
            self.raw(p, a[i], b[i]);
        }
        self.raw(e, h, t);
        for i in 1..n - 1 {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.xs(b);
    }
    /// UnitWalk.restore
    fn restore(&mut self, c: &[i32], a: &[i32], b: &[i32], h: i32) {
        assert!(c.len() == 1, "single control");
        if !self.aux_restore {
            let y0 = self.y[0];
            return self.dirty_digit(a, b, h, c[0], y0);
        }
        let e = c[0];
        let n = a.len();
        let k = n - 1;
        let aux = self.aux;
        if h != aux && e != aux {
            return self.digit(a, b, h, e, aux);
        }
        self.xs(b);
        if n == 1 {
            self.op(&[e, a[0], b[0]], h);
            self.raw(-1, -1, b[0]);
            self.raw(e, -1, h);
            self.raw(h, a[0], b[0]);
            return;
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.raw(e, a[k], h);
        for i in (1..=n - 2).rev() {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 0..n - 1 {
            self.raw(b[i], a[i], a[i + 1]);
        }
        self.op(&[e, a[k], b[k]], h);
        self.raw(e, -1, h);
        self.raw(h, a[k], b[k]);
        for i in (0..=n - 2).rev() {
            self.raw(b[i], a[i], a[i + 1]);
            self.raw(h, a[i], b[i]);
        }
        for i in 1..n - 1 {
            self.raw(a[i], -1, a[i + 1]);
        }
        for i in 1..n {
            self.raw(a[i], -1, b[i]);
        }
        self.xs(b);
    }
    fn multag(&mut self, c: &[i32], q: usize, hi: &[i32], z: i32) {
        let mut neg: V = Vec::new();
        for j in 0..self.tag.len() {
            if q & (1 << j) == 0 {
                neg.push(self.tag[j]);
            }
        }
        neg.extend_from_slice(hi);
        self.xs(&neg);
        let t = self.tag.clone();
        let mut cc = cat(c, &t);
        cc.extend_from_slice(hi);
        self.op(&cc, z);
        self.xs(&neg);
    }
    fn bias(&mut self, c: &[i32], v: usize) {
        let tl = self.tag.len();
        for j in 0..tl {
            if v & (1 << j) == 0 {
                continue;
            }
            for i in (j..tl).rev() {
                let t = self.tag.clone();
                self.op(&cat(c, &t[j..i]), t[i]);
            }
        }
    }
}

// ---------------------------------------------------------------- plan-time state shared by the three plans
struct Pl {
    lab: u64,
    blocks: Vec<Block>,
    top: Option<i32>,
    ports: Vec<Option<i32>>,
    tagv: V,
    sector_none: bool,
    relay: bool,
}
impl Pl {
    fn new(relay: bool) -> Pl {
        Pl { lab: 0, blocks: Vec::new(), top: None, ports: Vec::new(), tagv: Vec::new(), sector_none: false, relay }
    }
    fn one(&mut self, f: F) {
        self.one_r(f, false)
    }
    fn one_r(&mut self, f: F, rev: bool) {
        let b = Block {
            lab: self.lab,
            f,
            rev,
            top: self.top,
            ports: if self.relay { self.ports.clone() } else { Vec::new() },
            pre: self.sector_none && self.top.is_some(),
            tag: if self.relay { Some(self.tagv.clone()) } else { None },
        };
        self.blocks.push(b);
    }
}
fn sl(a: &[i32], lo: usize, hi: usize) -> V {
    a[lo..hi].to_vec()
}
fn co(a: &[i32], n: usize, t: usize) -> V {
    (0..t).map(|i| a[n - i]).collect()
}
fn rc(a: &[i32]) -> Wr {
    Rc::new(a.to_vec())
}
/// the list `a` as built by norm()/val() is a separate block vector (for cat(.., inv=true))
fn cat_inv(p: &mut Pl, other: Vec<Block>) {
    for b in other.into_iter().rev() {
        p.blocks.push(Block { rev: !b.rev, ..b });
    }
}

/// the three prelude blocks of UnitWalk.plan
fn prelude(p: &mut Pl, l: &[i32], r: &[i32], n: usize) {
    let (w, s) = (Rc::new(sl(l, 0, n)), Rc::new(sl(r, 0, n)));
    {
        let (w, s) = (w.clone(), s.clone());
        p.one(Box::new(move |g| {
            let high = s[n - 1];
            let sg = g.sign;
            g.op(&[high], sg);
            g.x(high);
            g.lt(&[high], &s[..n - 1], &w[1..], sg);
            g.x(high);
        }));
    }
    {
        let (w, s) = (w.clone(), s.clone());
        p.one(Box::new(move |g| {
            let cc = [g.sign];
            g.xs(&w);
            g.add(&cc, &w, &s, None);
            g.xs(&w);
            for &z in s.iter() {
                g.op(&cc, z);
            }
        }));
    }
    let rn = r[n];
    p.one(Box::new(move |g| g.x(rn)));
}
/// rot helper: blocks for the controlled rotations by 2^j (and `base`)
fn rot_blocks(p: &mut Pl, tg: &[i32], w: &Wr, controls: &Wr, dir: i64, base: usize) {
    if base > 0 {
        let (w, c) = (w.clone(), controls.clone());
        p.one(Box::new(move |g| g.rot(&c, &w, dir * base as i64)));
    }
    for j in 0..tg.len() {
        let s = 1usize << j;
        if s >= w.len() {
            break;
        }
        let (w, c, t) = (w.clone(), controls.clone(), tg[j]);
        p.one(Box::new(move |g| g.rot(&cat1(&c, t), &w, dir * s as i64)));
    }
}
fn norm_blocks(p: &mut Pl, tg: &[i32], w: &Wr, controls: &Wr, base: usize, dual: bool) {
    if base > 0 {
        let (w, c) = (w.clone(), controls.clone());
        p.one(Box::new(move |g| g.rot(&c, &w, base as i64)));
    }
    for j in (0..tg.len()).rev() {
        let s = 1usize << j;
        if s >= w.len() {
            continue;
        }
        let (w, c, t) = (w.clone(), controls.clone(), tg[j]);
        p.one(Box::new(move |g| {
            g.zer(&c, &w[w.len() - s..], t);
            if dual {
                g.rot(&cat1(&c, t), &w[base..], s as i64)
            } else {
                g.rot(&cat1(&c, t), &w, s as i64)
            }
        }));
    }
}
/// select(z, guard): large() = zer([], word, tst) + X(tst); large(); lt([tst, guard], A, r, z); reverse(large)
fn select(g: &mut W, a: &[i32], r: &[i32], z: i32, guard: &[i32], reduced: bool) {
    let tst = g.tst;
    let word: V = if reduced { r.to_vec() } else { a[1..].to_vec() };
    g.zer(&[], &word, tst);
    g.x(tst);
    let ctl = guard_first(tst, guard);
    g.lt(&ctl, a, r, z);
    g.reverse(|g| {
        g.zer(&[], &word, tst);
        g.x(tst);
    });
}
fn guard_first(tst: i32, guard: &[i32]) -> V {
    let mut v = vec![tst];
    v.extend_from_slice(guard);
    v
}

include!("i10walkplan.rs");
