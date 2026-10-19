//! lowq_mm (route lowq-cofactor-v1): out-of-place modular products over secp256k1 p = 2^256 - c, c = 2^32 + 977,
//! written against a minimal circuit trait so the same source runs in `mu_probe` and, through an adapter, in a
//! benchmark tree. See `mu_probe.rs` for the algorithms; hand-written research code, not generated from a schedule.
#![allow(dead_code)]

use crate::circuit::{BitId, QubitId};
use ruint::aliases::U256;

pub type Q = QubitId;
pub const N: usize = 256;
/// c = 2^256 - p = 2^32 + 977.
pub const C_LOW: u64 = 0x1_0000_03D1;

/// The gate vocabulary the products need. Every scored Toffoli goes through `ccx`.
pub trait Circ {
    fn q(&mut self) -> Q;
    fn qs(&mut self, n: usize) -> Vec<Q> {
        (0..n).map(|_| self.q()).collect()
    }
    /// Return a wire the caller has left in |0>.
    fn free(&mut self, q: Q);
    fn bit(&mut self) -> BitId;
    fn free_bit(&mut self, b: BitId);
    fn x(&mut self, t: Q);
    fn xs(&mut self, v: &[Q]) {
        for &q in v {
            self.x(q);
        }
    }
    fn z(&mut self, t: Q);
    fn cx(&mut self, c: Q, t: Q);
    fn ccx(&mut self, a: Q, b: Q, t: Q);
    fn cz(&mut self, a: Q, b: Q);
    fn cz_if(&mut self, a: Q, b: Q, m: BitId);
    fn hmr(&mut self, t: Q, m: BitId);
    fn push(&mut self, m: BitId);
    fn pop(&mut self);
    fn cx_if(&mut self, c: Q, t: Q, m: BitId) {
        self.push(m);
        self.cx(c, t);
        self.pop();
    }
    /// Book-keeping label only.
    fn phase(&mut self, _p: &'static str) {}
    /// X-measure `q`, free it, and run `fix` under the outcome.
    fn mbu(&mut self, q: Q, fix: impl FnOnce(&mut Self)) where Self: Sized {
        let m = self.bit();
        self.hmr(q, m);
        self.free(q);
        self.push(m);
        fix(self);
        self.pop();
        self.free_bit(m);
    }
}

#[derive(Clone, Copy)]
pub struct P {
    pub g: usize,
    pub cw: usize,
    pub room: usize,
}

impl P {
    pub fn sw(&self) -> usize {
        34 + self.g
    }
    pub fn sh(&self) -> usize {
        32 + self.g
    }
    /// Most carries one main-add chunk may hold (the rest of the room covers overflow, flags and boundaries).
    pub fn maxc(&self) -> usize {
        self.room.saturating_sub(8).max(self.cw + 2)
    }
}

/// One addend bit: zero, a wire, or the XOR of mutually exclusive flag wires (folded into the first one only while
/// that position is processed, then restored).
#[derive(Clone)]
pub enum Ad {
    Z,
    W(Q),
    X(Vec<Q>),
}

impl Ad {
    fn open<C: Circ>(&self, b: &mut C) -> Option<Q> {
        match self {
            Ad::Z => None,
            Ad::W(q) => Some(*q),
            Ad::X(v) => {
                for &f in &v[1..] {
                    b.cx(f, v[0]);
                }
                Some(v[0])
            }
        }
    }
    fn close<C: Circ>(&self, b: &mut C) {
        if let Ad::X(v) = self {
            for &f in &v[1..] {
                b.cx(f, v[0]);
            }
        }
    }
    fn wire(&self) -> Q {
        match self {
            Ad::W(q) => *q,
            _ => panic!("chunk boundary compare needs wire addends"),
        }
    }
}

pub fn wires(v: &[Q]) -> Vec<Ad> {
    v.iter().map(|&q| Ad::W(q)).collect()
}

/// One unchunked ripple: acc += add (+ cin). One Toffoli per produced carry, every carry uncomputed by X-measurement
/// with a CZ repair. The addend is restored immediately at each position, so shared flag wires are allowed.
/// With `cout` the carry off the top lands there; without it the top carry is dropped (wrapped).
pub fn ripple_plain<C: Circ>(b: &mut C, add: &[Ad], acc: &[Q], cin: Option<Q>, cout: Option<Q>) {
    let n = acc.len();
    assert_eq!(add.len(), n);
    let last = if cout.is_some() { n } else { n - 1 };
    let mut car: Vec<Option<Q>> = Vec::with_capacity(n);
    for i in 0..last {
        let prev = if i == 0 { cin } else { car[i - 1] };
        let a = add[i].open(b);
        let c = match (a, prev) {
            (None, None) => None,
            _ => Some(if i == n - 1 { cout.unwrap() } else { b.q() }),
        };
        match (a, prev, c) {
            (Some(a), Some(p), Some(c)) => {
                b.cx(p, a);
                b.cx(p, acc[i]);
                b.ccx(a, acc[i], c);
                b.cx(p, c);
                b.cx(p, a);
            }
            (Some(a), None, Some(c)) => b.ccx(a, acc[i], c),
            (None, Some(p), Some(c)) => b.ccx(p, acc[i], c),
            _ => {}
        }
        add[i].close(b);
        car.push(c);
    }
    // Top position's sum bit (acc holds acc ^ prev only where both an addend and a carry-in were present).
    let i = n - 1;
    let prev = if i == 0 { cin } else { car[i - 1] };
    let a = add[i].open(b);
    match (cout.is_some(), a, prev) {
        (true, Some(a), _) => b.cx(a, acc[i]),
        (true, None, Some(p)) => b.cx(p, acc[i]),
        (false, a, p) => {
            if let Some(a) = a {
                b.cx(a, acc[i]);
            }
            if let Some(p) = p {
                b.cx(p, acc[i]);
            }
        }
        _ => {}
    }
    add[i].close(b);
    for i in (0..n - 1).rev() {
        let prev = if i == 0 { cin } else { car[i - 1] };
        let Some(c) = car[i] else { continue };
        let a = add[i].open(b);
        match (a, prev) {
            (Some(a), Some(p)) => {
                b.cx(p, c);
                let m = b.bit();
                b.hmr(c, m);
                b.cx(p, a);
                b.cz_if(a, acc[i], m);
                b.cx(p, a);
                b.cx(a, acc[i]);
                b.free_bit(m);
            }
            (Some(a), None) => {
                let m = b.bit();
                b.hmr(c, m);
                b.cz_if(a, acc[i], m);
                b.cx(a, acc[i]);
                b.free_bit(m);
            }
            (None, Some(p)) => {
                let m = b.bit();
                b.hmr(c, m);
                b.cz_if(p, acc[i], m);
                b.cx(p, acc[i]);
                b.free_bit(m);
            }
            (None, None) => unreachable!(),
        }
        b.free(c);
        add[i].close(b);
    }
}

/// acc += add (+ cin), split into chunks of at most `p.maxc()` carries. Each chunk's top carry is kept as the next
/// chunk's carry-in; afterwards every boundary carry (the carry out of positions [0, e)) is X-measured and its phase
/// repaired on outcome 1 by a `cw`-bit windowed compare [add > acc] on positions [e - cw, e). A tie in the window
/// leaves the carry into the window undecided; `tie_cin` picks the guess. Forward adds (acc was the running value,
/// whose structured case is acc = 0, carry 0) pass false. Undo adds (acc was a complemented sum, whose structured case
/// is all ones, carry = cin) pass true, and the compare becomes [add + cin > acc].
pub fn ripple<C: Circ>(b: &mut C, p: &P, add: &[Ad], acc: &[Q], cin: Option<Q>, cout: Option<Q>, tie_cin: bool) {
    let n = acc.len();
    let maxc = p.maxc();
    let ncarry = if cout.is_some() { n } else { n - 1 };
    if ncarry <= maxc {
        ripple_plain(b, add, acc, cin, cout);
        return;
    }
    let nch = ncarry.div_ceil(maxc);
    let size = n.div_ceil(nch);
    let mut bounds: Vec<(usize, Q)> = Vec::new();
    let mut ci = cin;
    let mut a = 0;
    while a < n {
        let e = (a + size).min(n);
        if e == n {
            ripple_plain(b, &add[a..e], &acc[a..e], ci, cout);
        } else {
            let co = b.q();
            ripple_plain(b, &add[a..e], &acc[a..e], ci, Some(co));
            bounds.push((e, co));
            ci = Some(co);
        }
        a = e;
    }
    let cw = p.cw;
    for (e, q) in bounds.into_iter().rev() {
        assert!(e >= cw);
        let aw: Vec<Q> = add[e - cw..e].iter().map(Ad::wire).collect();
        let rw: Vec<Q> = acc[e - cw..e].to_vec();
        let tie = if tie_cin { cin } else { None };
        b.mbu(q, |b| with_gt_cin(b, &aw, &rw, tie, |b, c| b.z(c)));
    }
}

/// Compute [a > r] over these bits (carry off the top of a + ~r), run `body` with that wire, then unwind it.
/// `a` and `r` are restored. `a.len()` Toffoli; the unwind is measured.
pub fn with_gt<C: Circ>(b: &mut C, a: &[Q], r: &[Q], body: impl FnOnce(&mut C, Q)) {
    with_gt_cin(b, a, r, None, body)
}

/// As [`with_gt`], with a carry-in: [a + cin > r], i.e. ties resolve to `cin`.
pub fn with_gt_cin<C: Circ>(b: &mut C, a: &[Q], r: &[Q], cin: Option<Q>, body: impl FnOnce(&mut C, Q)) {
    let n = a.len();
    b.xs(r);
    let mut car: Vec<Q> = Vec::with_capacity(n);
    let prev_of = |car: &Vec<Q>, i: usize| if i == 0 { cin } else { Some(car[i - 1]) };
    for i in 0..n {
        let c = b.q();
        if let Some(p) = prev_of(&car, i) {
            b.cx(p, a[i]);
            b.cx(p, r[i]);
            b.ccx(a[i], r[i], c);
            b.cx(p, c);
        } else {
            b.ccx(a[i], r[i], c);
        }
        car.push(c);
    }
    body(b, car[n - 1]);
    for i in (0..n).rev() {
        let c = car[i];
        let prev = prev_of(&car, i);
        if let Some(p) = prev {
            b.cx(p, c);
        }
        let m = b.bit();
        b.hmr(c, m);
        b.cz_if(a[i], r[i], m);
        b.free_bit(m);
        b.free(c);
        if let Some(p) = prev {
            b.cx(p, a[i]);
            b.cx(p, r[i]);
        }
    }
    b.xs(r);
}

pub fn mask(s: usize) -> U256 {
    (U256::from(1u64) << s) - U256::from(1u64)
}

pub fn negm(v: U256, s: usize) -> U256 {
    U256::ZERO.wrapping_sub(v) & mask(s)
}

pub fn cc() -> U256 {
    U256::from(C_LOW)
}

/// acc[0..s) += sum of flag * pattern (mod 2^s); flags mutually exclusive; the carry off the window is dropped.
pub fn add_patterns<C: Circ>(b: &mut C, acc: &[Q], terms: &[(Q, U256)]) {
    let s = acc.len();
    let add: Vec<Ad> = (0..s)
        .map(|i| {
            let fs: Vec<Q> = terms.iter().filter(|(_, p)| p.bit(i)).map(|(f, _)| *f).collect();
            match fs.len() {
                0 => Ad::Z,
                1 => Ad::W(fs[0]),
                _ => Ad::X(fs),
            }
        })
        .collect();
    ripple_plain(b, &add, acc, None, None);
}

/// x <- x XOR ctl^n.
pub fn sandwich<C: Circ>(b: &mut C, x: &[Q], ctl: Q) {
    for &q in x {
        b.cx(ctl, q);
    }
}

// ─── MSB-first doubling step (mu) ──────────────────────────────────────────────────────────────────────────────────

/// k = H - (1 - b_j) as exclusive flags (k = -1, 1, 2) from h0, h1 (never both 1) and b_j. Four Toffoli.
pub fn msb_flags<C: Circ>(b: &mut C, h0: Q, h1: Q, bj: Q) -> [Q; 3] {
    let e2 = b.q();
    b.ccx(h1, bj, e2);
    let e1 = b.q();
    b.ccx(h0, bj, e1);
    b.x(bj);
    b.ccx(h1, bj, e1);
    b.x(bj);
    let em1 = b.q();
    b.cx(h0, h1);
    b.x(h1);
    b.x(bj);
    b.ccx(h1, bj, em1);
    b.x(bj);
    b.x(h1);
    b.cx(h0, h1);
    [em1, e1, e2]
}

pub fn msb_unflags<C: Circ>(b: &mut C, h0: Q, h1: Q, bj: Q, f: [Q; 3]) {
    let [em1, e1, e2] = f;
    b.mbu(em1, |b| {
        b.cx(h0, h1);
        b.x(h1);
        b.x(bj);
        b.cz(h1, bj);
        b.x(bj);
        b.x(h1);
        b.cx(h0, h1);
    });
    b.mbu(e1, |b| {
        b.cz(h0, bj);
        b.x(bj);
        b.cz(h1, bj);
        b.x(bj);
    });
    b.mbu(e2, |b| b.cz(h1, bj));
}

/// z <- 2z + d_j x (mod p), d_j = 2 b_j - 1.
pub fn msb_step<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>, x: &[Q], bj: Q) {
    let sw = p.sw();
    let cw = p.cw;
    b.phase("fwd.add");
    let fresh = b.q();
    let h1 = b.q();
    let mut acc = vec![fresh];
    acc.extend_from_slice(z);
    b.x(bj); // bj = NOT b_j: complement control and carry-in (adds ~x + 1 = 2^256 - x when b_j = 0)
    sandwich(b, x, bj);
    let mut add = wires(x);
    add.push(Ad::Z);
    ripple(b, p, &add, &acc, Some(bj), Some(h1), false);
    b.x(bj);
    let h0 = acc[N];
    let r: Vec<Q> = acc[..N].to_vec();
    b.phase("fwd.flags");
    let f = msb_flags(b, h0, h1, bj);
    b.phase("fwd.fold");
    let c = cc();
    add_patterns(b, &r[..sw], &[(f[0], negm(c, sw)), (f[1], c & mask(sw)), (f[2], (c << 1) & mask(sw))]);
    b.phase("fwd.flags");
    msb_unflags(b, h0, h1, bj, f);
    b.phase("fwd.erase");
    // h1 = NOT h0 AND [r < A'].
    b.mbu(h1, |b| {
        with_gt(b, &x[N - cw..], &r[N - cw..], |b, cmp| {
            b.x(h0);
            b.cz(cmp, h0);
            b.x(h0);
        })
    });
    // h0 = r_0 XOR A'_0.
    b.cx(r[0], h0);
    b.cx(x[0], h0);
    b.free(h0);
    b.x(bj);
    sandwich(b, x, bj);
    b.x(bj);
    *z = r;
}

pub fn msb_inv<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>, x: &[Q], bj: Q) {
    let sw = p.sw();
    let cw = p.cw;
    let r = z.clone();
    b.phase("inv.erase");
    b.x(bj);
    sandwich(b, x, bj);
    b.x(bj);
    let h0 = b.q();
    b.cx(r[0], h0);
    b.cx(x[0], h0);
    let h1 = b.q();
    with_gt(b, &x[N - cw..], &r[N - cw..], |b, cmp| {
        b.x(h0);
        b.ccx(cmp, h0, h1);
        b.x(h0);
    });
    b.phase("inv.flags");
    let f = msb_flags(b, h0, h1, bj);
    b.phase("inv.fold");
    let c = cc();
    add_patterns(b, &r[..sw], &[(f[0], c & mask(sw)), (f[1], negm(c, sw)), (f[2], negm(c << 1, sw))]);
    b.phase("inv.flags");
    msb_unflags(b, h0, h1, bj, f);
    b.phase("inv.add");
    let mut acc = r.clone();
    acc.push(h0);
    acc.push(h1);
    b.xs(&acc);
    let mut add = wires(x);
    add.push(Ad::Z);
    add.push(Ad::Z);
    b.x(bj);
    ripple(b, p, &add, &acc, Some(bj), None, true);
    b.xs(&acc);
    b.free(acc[0]);
    b.free(acc[N + 1]);
    sandwich(b, x, bj);
    b.x(bj);
    *z = acc[1..N + 1].to_vec();
}

// ─── LSB-first halving step (muc) ──────────────────────────────────────────────────────────────────────────────────

/// k' = H - ctl - q in {-2, -1, 0, 1} as exclusive flags [k' = -2, k' = -1, k' = 1], plus the two helpers
/// [H AND NOT ctl, NOT H AND ctl]. Six Toffoli.
pub fn lsb_flags<C: Circ>(b: &mut C, h: Q, ctl: Q, q: Q) -> [Q; 5] {
    let k1 = b.q();
    b.x(ctl);
    b.ccx(h, ctl, k1);
    b.x(ctl);
    let km1 = b.q();
    b.x(h);
    b.ccx(h, ctl, km1);
    b.x(h);
    let e1 = b.q();
    b.x(q);
    b.ccx(k1, q, e1);
    b.x(q);
    let em2 = b.q();
    b.ccx(km1, q, em2);
    let em1 = b.q();
    b.x(q);
    b.ccx(km1, q, em1);
    b.x(q);
    b.cx(km1, k1);
    b.x(k1);
    b.ccx(k1, q, em1);
    b.x(k1);
    b.cx(km1, k1);
    [em2, em1, e1, k1, km1]
}

pub fn lsb_unflags<C: Circ>(b: &mut C, h: Q, ctl: Q, q: Q, f: [Q; 5]) {
    let [em2, em1, e1, k1, km1] = f;
    b.mbu(em1, |b| {
        b.x(q);
        b.cz(km1, q);
        b.x(q);
        b.cx(km1, k1);
        b.x(k1);
        b.cz(k1, q);
        b.x(k1);
        b.cx(km1, k1);
    });
    b.mbu(em2, |b| b.cz(km1, q));
    b.mbu(e1, |b| {
        b.x(q);
        b.cz(k1, q);
        b.x(q);
    });
    b.mbu(km1, |b| {
        b.x(h);
        b.cz(h, ctl);
        b.x(h);
    });
    b.mbu(k1, |b| {
        b.x(ctl);
        b.cz(h, ctl);
        b.x(ctl);
    });
}

/// z <- (z + d_j x) / 2 (mod p), d_j = 1 - 2 b_j (complement x when b_j = 1).
pub fn lsb_step<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>, x: &[Q], bj: Q) {
    let sw = p.sw();
    let cw = p.cw;
    b.phase("fwd.add");
    sandwich(b, x, bj);
    let h = b.q();
    ripple(b, p, &wires(x), z, Some(bj), Some(h), false); // s = z + x' + b_j; h = carry off bit 255
    let q = b.q(); // parity of s + k c: s_0 ^ h ^ b_j
    b.cx(z[0], q);
    b.cx(h, q);
    b.cx(bj, q);
    b.phase("fwd.flags");
    let f = lsb_flags(b, h, bj, q);
    b.phase("fwd.fold");
    let c = cc();
    add_patterns(b, &z[..sw], &[(f[0], negm(c << 1, sw)), (f[1], negm(c, sw)), (f[2], c & mask(sw))]);
    b.phase("fwd.flags");
    lsb_unflags(b, h, bj, q, f);
    b.phase("fwd.erase");
    // h = [s < A'] on the top window.
    b.mbu(h, |b| with_gt(b, &x[N - cw..], &z[N - cw..], |b, cmp| b.z(cmp)));
    sandwich(b, x, bj);
    b.free(z[0]); // zero after the fold
    let mut nz = z[1..].to_vec();
    nz.push(q); // the top bit of (s + k' p) / 2 is q
    *z = nz;
}

pub fn lsb_inv<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>, x: &[Q], bj: Q) {
    let sw = p.sw();
    let cw = p.cw;
    b.phase("inv.erase");
    sandwich(b, x, bj);
    let q = z[N - 1];
    let fresh = b.q();
    let mut s = vec![fresh];
    s.extend_from_slice(&z[..N - 1]);
    let h = b.q();
    with_gt(b, &x[N - cw..], &s[N - cw..], |b, cmp| b.cx(cmp, h));
    b.phase("inv.flags");
    let f = lsb_flags(b, h, bj, q);
    b.phase("inv.fold");
    let c = cc();
    add_patterns(b, &s[..sw], &[(f[0], (c << 1) & mask(sw)), (f[1], c & mask(sw)), (f[2], negm(c, sw))]);
    b.phase("inv.flags");
    lsb_unflags(b, h, bj, q, f);
    b.phase("inv.add");
    b.cx(s[0], q);
    b.cx(h, q);
    b.cx(bj, q);
    b.free(q);
    let mut acc = s.clone();
    acc.push(h);
    b.xs(&acc);
    let mut add = wires(x);
    add.push(Ad::Z);
    ripple(b, p, &add, &acc, Some(bj), None, true);
    b.xs(&acc);
    b.free(h);
    sandwich(b, x, bj);
    *z = s;
}

// ─── tails: subtract x, halvings ───────────────────────────────────────────────────────────────────────────────────

/// z <- z - x (mod p).
pub fn sub_x<C: Circ>(b: &mut C, p: &P, z: &[Q], x: &[Q]) {
    let sw = p.sw();
    b.xs(x);
    let one = b.q();
    b.x(one);
    let h = b.q();
    ripple(b, p, &wires(x), z, Some(one), Some(h), false); // s = z + ~x + 1; h = 1 when no borrow
    b.x(one);
    b.free(one);
    b.x(h);
    add_patterns(b, &z[..sw], &[(h, negm(cc(), sw))]); // k = h - 1
    b.x(h);
    b.mbu(h, |b| with_gt(b, &x[N - p.cw..], &z[N - p.cw..], |b, cmp| b.z(cmp))); // h = [r < ~x]
    b.xs(x);
}

/// Exact inverse of [`sub_x`]: z <- z + x.
pub fn unsub_x<C: Circ>(b: &mut C, p: &P, z: &[Q], x: &[Q]) {
    let sw = p.sw();
    b.xs(x);
    let h = b.q();
    with_gt(b, &x[N - p.cw..], &z[N - p.cw..], |b, cmp| b.cx(cmp, h));
    b.x(h);
    add_patterns(b, &z[..sw], &[(h, cc() & mask(sw))]);
    b.x(h);
    let mut acc = z.to_vec();
    acc.push(h);
    b.xs(&acc);
    let one = b.q();
    b.x(one);
    let mut add = wires(x);
    add.push(Ad::Z);
    ripple(b, p, &add, &acc, Some(one), None, true);
    b.x(one);
    b.free(one);
    b.xs(&acc);
    b.free(h);
    b.xs(x);
}

/// z <- z / 2 (mod p): rotate right, then subtract z_0 * (c - 1)/2.
pub fn half1<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>) {
    let sh = p.sh();
    let mut rz = z[1..].to_vec();
    rz.push(z[0]);
    add_patterns(b, &rz[..sh], &[(rz[N - 1], negm(U256::from(C_LOW >> 1), sh))]);
    *z = rz;
}

pub fn unhalf1<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>) {
    let sh = p.sh();
    add_patterns(b, &z[..sh], &[(z[N - 1], U256::from(C_LOW >> 1) & mask(sh))]);
    let mut lz = vec![z[N - 1]];
    lz.extend_from_slice(&z[..N - 1]);
    *z = lz;
}

/// t = 61 q (10 wires) from a 4-wire q, as 65 q - 4 q; returns the temps. 7 Toffoli.
pub fn times61<C: Circ>(b: &mut C, p: &P, q: &[Q]) -> Vec<Q> {
    let t = b.qs(10);
    for i in 0..4 {
        b.cx(q[i], t[i]);
        b.cx(q[i], t[6 + i]);
    }
    b.xs(&t[2..]);
    let mut add = wires(q);
    add.extend([Ad::Z, Ad::Z, Ad::Z, Ad::Z]);
    ripple(b, p, &add, &t[2..], None, None, false);
    b.xs(&t[2..]);
    t
}

pub fn untimes61<C: Circ>(b: &mut C, p: &P, q: &[Q], t: Vec<Q>) {
    let mut add = wires(q);
    add.extend([Ad::Z, Ad::Z, Ad::Z, Ad::Z]);
    ripple(b, p, &add, &t[2..], None, None, false);
    for i in 0..4 {
        b.cx(q[i], t[i]);
        b.cx(q[i], t[6 + i]);
    }
    for w in t {
        b.free(w);
    }
}

/// z <- z / 16 (mod p). With c = 1 mod 16 the Montgomery quotient is q = z mod 16 itself:
/// (z + q p)/16 = z_hi - q (2^28 + 61) + q 2^252, so q moves to the top and z_hi pays a windowed subtract.
pub fn half4<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>) {
    let sh = p.sh();
    let q: Vec<Q> = z[..4].to_vec();
    let hi: Vec<Q> = z[4..].to_vec();
    let t = times61(b, p, &q);
    let add: Vec<Ad> = (0..sh)
        .map(|i| match i {
            0..=9 => Ad::W(t[i]),
            28..=31 => Ad::W(q[i - 28]),
            _ => Ad::Z,
        })
        .collect();
    b.xs(&hi[..sh]);
    ripple_plain(b, &add, &hi[..sh], None, None);
    b.xs(&hi[..sh]);
    untimes61(b, p, &q, t);
    let mut nz = hi;
    nz.extend(q);
    *z = nz;
}

pub fn unhalf4<C: Circ>(b: &mut C, p: &P, z: &mut Vec<Q>) {
    let sh = p.sh();
    let hi: Vec<Q> = z[..N - 4].to_vec();
    let q: Vec<Q> = z[N - 4..].to_vec();
    let t = times61(b, p, &q);
    let add: Vec<Ad> = (0..sh)
        .map(|i| match i {
            0..=9 => Ad::W(t[i]),
            28..=31 => Ad::W(q[i - 28]),
            _ => Ad::Z,
        })
        .collect();
    ripple_plain(b, &add, &hi[..sh], None, None);
    untimes61(b, p, &q, t);
    let mut nz = q;
    nz.extend(hi);
    *z = nz;
}

// ─── whole products ────────────────────────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq)]
pub enum Kind {
    Mu,
    MuC,
}

pub const MUC_K: usize = 404;

pub fn product_fwd<C: Circ>(b: &mut C, p: &P, kind: Kind, x: &[Q], m: &[Q]) -> Vec<Q> {
    b.phase("fwd.copy");
    let mut z = b.qs(N);
    if kind == Kind::Mu {
        for i in 0..N {
            b.cx(x[i], z[i]);
        }
    }
    match kind {
        Kind::Mu => {
            for j in (0..N).rev() {
                msb_step(b, p, &mut z, x, m[j]);
            }
            b.phase("fwd.tail");
            sub_x(b, p, &z, x);
            half1(b, p, &mut z);
        }
        Kind::MuC => {
            // Step 0 from z = x is z = (x + d_0 x)/2 = (1 - b_0) x: a copy of x under NOT b_0. 256 Toffoli.
            b.x(m[0]);
            for i in 0..N {
                b.ccx(m[0], x[i], z[i]);
            }
            b.x(m[0]);
            for j in 1..N {
                lsb_step(b, p, &mut z, x, m[j]);
            }
            b.phase("fwd.tail");
            sub_x(b, p, &z, x);
            let extra = MUC_K - (N - 1);
            for _ in 0..extra / 4 {
                half4(b, p, &mut z);
            }
            for _ in 0..extra % 4 {
                half1(b, p, &mut z);
            }
        }
    }
    z
}

pub fn product_inv<C: Circ>(b: &mut C, p: &P, kind: Kind, x: &[Q], m: &[Q], mut z: Vec<Q>) {
    match kind {
        Kind::Mu => {
            b.phase("inv.tail");
            unhalf1(b, p, &mut z);
            unsub_x(b, p, &z, x);
            for j in 0..N {
                msb_inv(b, p, &mut z, x, m[j]);
            }
        }
        Kind::MuC => {
            b.phase("inv.tail");
            let extra = MUC_K - (N - 1);
            for _ in 0..extra % 4 {
                unhalf1(b, p, &mut z);
            }
            for _ in 0..extra / 4 {
                unhalf4(b, p, &mut z);
            }
            unsub_x(b, p, &z, x);
            for j in (1..N).rev() {
                lsb_inv(b, p, &mut z, x, m[j]);
            }
            // z = (1 - b_0) x: X-measure it; the phase (-1)^(m.z) = (-1)^((1 - b_0)(m.x)) is a parity times a bit.
            b.phase("inv.uncopy");
            let par = b.q();
            let ms: Vec<BitId> = (0..N).map(|_| b.bit()).collect();
            for i in 0..N {
                b.hmr(z[i], ms[i]);
                b.free(z[i]);
            }
            for i in 0..N {
                b.cx_if(x[i], par, ms[i]);
            }
            b.x(m[0]);
            b.cz(par, m[0]);
            b.x(m[0]);
            for i in 0..N {
                b.cx_if(x[i], par, ms[i]);
            }
            b.free(par);
            for bit in ms {
                b.free_bit(bit);
            }
            return;
        }
    }
    b.phase("inv.uncopy");
    for i in 0..N {
        b.cx(x[i], z[i]);
    }
    for q in z {
        b.free(q);
    }
}

