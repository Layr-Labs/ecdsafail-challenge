//! Bit-exact classical model of the skycof_mm constructions (lazy fold semantics), plus the
//! true modular reference. Values are n-bit strings in a U512.
use ruint::Uint;

pub type U512 = Uint<512, 8>;

#[derive(Clone, Copy, Debug)]
pub struct M {
    pub n: usize,
    pub c: U512,
    pub w: usize,
    pub ww: usize,
}

pub fn one() -> U512 {
    U512::from(1u64)
}

pub fn mask(k: usize) -> U512 {
    (one() << k) - one()
}

impl M {
    pub fn new(f: super::Field, cfg: super::Cfg) -> Self {
        M { n: f.n, c: U512::from(f.c), w: cfg.fold_w, ww: cfg.cmp_w }
    }
    pub fn p(&self) -> U512 {
        (one() << self.n) - self.c
    }
    fn add_w(&self, y: U512, k: U512) -> U512 {
        let mw = mask(self.w);
        (y & !mw) | (y.wrapping_add(k) & mw)
    }
    fn sub_w(&self, y: U512, k: U512) -> U512 {
        let mw = mask(self.w);
        (y & !mw) | (y.wrapping_sub(k & mw).wrapping_add(one() << self.w) & mw)
    }
    pub fn dbl(&self, x: U512) -> U512 {
        let t = x.bit(self.n - 1);
        let y = (x << 1) & mask(self.n);
        if t { self.add_w(y, self.c) } else { y }
    }
    pub fn hlv(&self, y: U512) -> U512 {
        let h = y.bit(0);
        let y = if h { self.sub_w(y, self.c) } else { y };
        let mut x = y >> 1;
        if h {
            x |= one() << (self.n - 1);
        }
        x
    }
    fn top(&self, v: U512) -> U512 {
        v >> (self.n - self.ww)
    }
    /// (out + e*a mod p (lazy), erase event)
    pub fn madd(&self, out: U512, a: U512, e: bool) -> (U512, bool) {
        if !e {
            return (out, false);
        }
        let zz = out + a;
        let t2 = zz.bit(self.n);
        let mut low = zz & mask(self.n);
        if t2 {
            low = self.add_w(low, self.c);
        }
        let pred = self.top(low) < self.top(a);
        (low, t2 != pred)
    }
    /// inverse of madd: (value, garbage event)
    pub fn msub(&self, out: U512, a: U512, e: bool) -> (U512, bool) {
        let t2 = e && self.top(out) < self.top(a);
        let y = if t2 { self.sub_w(out, self.c) } else { out };
        let ea = if e { a } else { U512::ZERO };
        let kappa = ea > y;
        let res = y.wrapping_add(one() << self.n).wrapping_sub(ea) & mask(self.n);
        (res, t2 != kappa)
    }
    pub fn cneg(&self, x: U512, s: bool) -> U512 {
        if !s {
            return x;
        }
        let y = !x & mask(self.n);
        self.sub_w(y, self.c - one())
    }
    pub fn mul_fwd(&self, a: U512, b: U512, k: usize, s: bool) -> (U512, u32) {
        let n = self.n;
        let (lsb, xh, xd) = super::schedule(n, k);
        let mut ev = 0;
        let mut out;
        if lsb {
            out = if b.bit(0) { a } else { U512::ZERO };
            out = self.hlv(out);
            for i in 1..n {
                let (o, e) = self.madd(out, a, b.bit(i));
                ev += e as u32;
                out = self.hlv(o);
            }
        } else {
            out = if b.bit(n - 1) { a } else { U512::ZERO };
            for i in (0..n - 1).rev() {
                out = self.dbl(out);
                let (o, e) = self.madd(out, a, b.bit(i));
                ev += e as u32;
                out = o;
            }
        }
        for _ in 0..xh {
            out = self.hlv(out);
        }
        for _ in 0..xd {
            out = self.dbl(out);
        }
        (self.cneg(out, s), ev)
    }
    /// True iff some intermediate value of mul_fwd leaves [0, p) (the lazy window).
    pub fn lazy_touched(&self, a: U512, b: U512, k: usize, s: bool) -> bool {
        let n = self.n;
        let p = self.p();
        let (lsb, xh, xd) = super::schedule(n, k);
        let mut hit = a >= p || b >= p;
        let mut out;
        if lsb {
            out = self.hlv(if b.bit(0) { a } else { U512::ZERO });
            hit |= out >= p;
            for i in 1..n {
                out = self.madd(out, a, b.bit(i)).0;
                hit |= out >= p;
                out = self.hlv(out);
                hit |= out >= p;
            }
        } else {
            out = if b.bit(n - 1) { a } else { U512::ZERO };
            for i in (0..n - 1).rev() {
                out = self.dbl(out);
                hit |= out >= p;
                out = self.madd(out, a, b.bit(i)).0;
                hit |= out >= p;
            }
        }
        for _ in 0..xh {
            out = self.hlv(out);
            hit |= out >= p;
        }
        for _ in 0..xd {
            out = self.dbl(out);
            hit |= out >= p;
        }
        hit | (self.cneg(out, s) >= p)
    }
    pub fn mul_inv(&self, a: U512, b: U512, k: usize, s: bool, out: U512) -> (U512, u32) {
        let n = self.n;
        let (lsb, xh, xd) = super::schedule(n, k);
        let mut ev = 0;
        let mut out = self.cneg(out, s);
        for _ in 0..xd {
            out = self.hlv(out);
        }
        for _ in 0..xh {
            out = self.dbl(out);
        }
        if lsb {
            for i in (1..n).rev() {
                out = self.dbl(out);
                let (o, e) = self.msub(out, a, b.bit(i));
                ev += e as u32;
                out = o;
            }
            out = self.dbl(out);
            if b.bit(0) {
                out ^= a;
            }
        } else {
            for i in 0..n - 1 {
                let (o, e) = self.msub(out, a, b.bit(i));
                ev += e as u32;
                out = self.hlv(o);
            }
            if b.bit(n - 1) {
                out ^= a;
            }
        }
        (out, ev)
    }
    /// X (n+1 bits, X even when fl) -> fold under fl.
    pub fn park_fold(&self, x: U512, fl: bool) -> U512 {
        if !fl {
            return x;
        }
        let t = x.bit(self.n);
        let low = x & mask(self.n);
        if t { self.add_w(low, self.c) } else { low }
    }
    pub fn park_unfold(&self, x: U512, fl: bool) -> U512 {
        if !fl {
            return x;
        }
        let h = x.bit(0);
        let low = x & mask(self.n);
        if h { self.sub_w(low, self.c) | (one() << self.n) } else { low }
    }
    /// True value a*b*2^-k*(-1)^s mod p (canonical).
    pub fn truth(&self, a: U512, b: U512, k: usize, s: bool) -> U512 {
        let p = self.p();
        let inv2: U512 = (p + one()) >> 1usize;
        let pk = inv2.pow_mod(U512::from(k as u64), p);
        let v = a.mul_mod(b, p).mul_mod(pk, p);
        if s && !v.is_zero() { p - v } else { v }
    }
}
