//! Classical layer: run-time classical values (functions of the second point) as little-endian vectors of classical bit ids,
//! computed with the benchmark's classical ops (BitInvert / BitStore0 / BitStore1 with an optional condition bit, Push / Pop
//! condition).  Every routine only EMITS records; `Cl` is the bit allocator of one region.  The calls are driven by the scan
//! trace, so the order of allocations and ops is fixed.
use super::Row;
use std::collections::VecDeque;
const NONE: u16 = u16::MAX;
pub type V = Vec<u16>;
// ---- small unsigned big integers (64-bit limbs, little-endian) for the build-time constants
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Big(pub Vec<u64>);
impl Big {
    pub fn from_u64(x: u64) -> Big { Big(vec![x]) }
    pub fn from_le_bytes(b: &[u8]) -> Big { let mut v = vec![0u64; (b.len() + 7) / 8 + 1]; for (i, &x) in b.iter().enumerate() { v[i / 8] |= (x as u64) << (8 * (i % 8)); } Big(v) }
    pub fn bit(&self, i: usize) -> bool { let w = i / 64; w < self.0.len() && (self.0[w] >> (i % 64)) & 1 == 1 }
    pub fn bitlen(&self) -> usize { for w in (0..self.0.len()).rev() { if self.0[w] != 0 { return 64 * w + 64 - self.0[w].leading_zeros() as usize; } } 0 }
    pub fn is_zero(&self) -> bool { self.0.iter().all(|&x| x == 0) }
    pub fn pow2(n: usize) -> Big { let mut v = vec![0u64; n / 64 + 1]; v[n / 64] = 1 << (n % 64); Big(v) }
    pub fn add(&self, o: &Big) -> Big { let n = self.0.len().max(o.0.len()) + 1; let mut v = vec![0u64; n]; let mut c = 0u128; for i in 0..n { let s = *self.0.get(i).unwrap_or(&0) as u128 + *o.0.get(i).unwrap_or(&0) as u128 + c; v[i] = s as u64; c = s >> 64; } Big(v) }
    /// self - o (self >= o)
    pub fn sub(&self, o: &Big) -> Big { let n = self.0.len().max(o.0.len()); let mut v = vec![0u64; n]; let mut br = 0i128; for i in 0..n { let d = *self.0.get(i).unwrap_or(&0) as i128 - *o.0.get(i).unwrap_or(&0) as i128 - br; if d < 0 { v[i] = (d + (1i128 << 64)) as u64; br = 1; } else { v[i] = d as u64; br = 0; } } assert!(br == 0, "big subtraction"); Big(v) }
    pub fn shl(&self, k: usize) -> Big { let mut v = vec![0u64; self.0.len() + k / 64 + 1]; for (i, &x) in self.0.iter().enumerate() { v[i + k / 64] |= x << (k % 64); if k % 64 != 0 { v[i + k / 64 + 1] |= x >> (64 - k % 64); } } Big(v) }
    pub fn lt(&self, o: &Big) -> bool { let n = self.0.len().max(o.0.len()); for i in (0..n).rev() { let a = *self.0.get(i).unwrap_or(&0); let b = *o.0.get(i).unwrap_or(&0); if a != b { return a < b; } } false }
    pub fn to_u64(&self) -> u64 { assert!(self.bitlen() <= 64, "constant too large"); self.0[0] }
}
/// p = 2^256 - 2^32 - 977 and c = 2^32 + 977
pub fn p256() -> Big { Big::pow2(256).sub(&Big::from_u64((1u64 << 32) + 977)) }
fn cp() -> Big { Big::from_u64((1u64 << 32) + 977) }

pub struct Cl { pub next: usize, limit: usize, depth: usize, carry: V }
impl Cl {
    pub fn new(first: usize, limit: usize) -> Cl { let mut c = Cl { next: first, limit, depth: 0, carry: Vec::new() }; c.carry = c.vec(1400); c }
    // ---- primitives
    #[inline] fn xor(&mut self, e: &mut dyn FnMut(Row), t: u16, a: u16) { e([3, t, a, NONE]); }
    #[inline] fn not(&mut self, e: &mut dyn FnMut(Row), t: u16) { e([3, t, NONE, NONE]); }
    #[inline] fn clr(&mut self, e: &mut dyn FnMut(Row), t: u16) { e([4, t, NONE, NONE]); }
    #[inline] fn set(&mut self, e: &mut dyn FnMut(Row), t: u16) { e([5, t, NONE, NONE]); }
    #[inline] fn push(&mut self, e: &mut dyn FnMut(Row), c: u16) { self.depth += 1; e([15, c, NONE, NONE]); }
    #[inline] fn pop(&mut self, e: &mut dyn FnMut(Row)) { self.depth -= 1; e([16, NONE, NONE, NONE]); }
    fn bit(&mut self) -> u16 { assert!(self.next < self.limit, "classical bits exhausted"); self.next += 1; (self.next - 1) as u16 }
    pub fn vec(&mut self, n: usize) -> V { (0..n).map(|_| self.bit()).collect() }
    pub fn release(&mut self, e: &mut dyn FnMut(Row), m: usize) { assert!(self.depth == 0, "release inside a conditional block"); for t in (m..self.next).rev() { e([4, t as u16, NONE, NONE]); } self.next = m; }
    pub fn keep(&mut self, e: &mut dyn FnMut(Row), m: usize, v: &[u16]) -> V {
        if v.iter().enumerate().any(|(i, &t)| (t as usize) < m + v.len() && t as usize != m + i) { let c = self.vec(v.len()); for i in 0..v.len() { self.xor(e, c[i], v[i]); } return self.keep(e, m, &c); }
        for i in 0..v.len() { if v[i] as usize != m + i { self.clr(e, (m + i) as u16); self.xor(e, (m + i) as u16, v[i]); } }
        for t in (m + v.len()..self.next).rev() { e([4, t as u16, NONE, NONE]); } self.next = m + v.len(); (m..m + v.len()).map(|x| x as u16).collect() }
    // ---- values
    fn const_vec(&mut self, e: &mut dyn FnMut(Row), k: &Big, n: usize) -> V { let v = self.vec(n); for i in 0..n { if k.bit(i) { self.set(e, v[i]); } } v }
    fn copy(&mut self, e: &mut dyn FnMut(Row), a: &[u16]) -> V { let v = self.vec(a.len()); for i in 0..a.len() { self.xor(e, v[i], a[i]); } v }
    fn copy_into(&mut self, e: &mut dyn FnMut(Row), t: &[u16], a: &[u16]) { for i in 0..t.len() { self.clr(e, t[i]); if i < a.len() { self.xor(e, t[i], a[i]); } } }
    /// B += A (+ cin) mod 2^|B|; returns the last carry bit (or NONE)
    pub fn add(&mut self, e: &mut dyn FnMut(Row), b: &[u16], a: &[u16], cin: u16, cout: u16) -> u16 { let n = b.len(); let mut c = cin;
        for i in 0..n { let bb = b[i]; let c2 = self.carry[i]; self.clr(e, c2);
            if i < a.len() { let aa = a[i]; self.xor(e, bb, aa); self.xor(e, c2, aa); self.push(e, bb); self.xor(e, c2, aa); if c != NONE { self.xor(e, c2, c); } self.pop(e); if c != NONE { self.xor(e, bb, c); } }
            else if c != NONE { self.push(e, bb); self.xor(e, c2, c); self.pop(e); self.xor(e, bb, c); }
            else { break; }
            c = c2; }
        if cout != NONE && c != NONE { self.xor(e, cout, c); } c }
    /// B += k mod 2^|B| (k >= 0, taken mod 2^|B|)
    pub fn add_const(&mut self, e: &mut dyn FnMut(Row), b: &[u16], k: &Big, cout: u16) -> u16 { let n = b.len(); let mut c = NONE;
        for i in 0..n { let bb = b[i]; let c2 = self.carry[i];
            if k.bit(i) { self.not(e, bb);
                if c != NONE { self.clr(e, c2); self.set(e, c2); self.xor(e, c2, bb); self.push(e, bb); self.xor(e, c2, c); self.pop(e); self.xor(e, bb, c); c = c2; }
                else { self.clr(e, c2); self.set(e, c2); self.xor(e, c2, bb); c = c2; } }
            else if c != NONE { self.clr(e, c2); self.push(e, bb); self.xor(e, c2, c); self.pop(e); self.xor(e, bb, c); c = c2; } }
        if cout != NONE && c != NONE { self.xor(e, cout, c); } c }
    fn neg(&mut self, e: &mut dyn FnMut(Row), b: &[u16]) { for &x in b { self.not(e, x); } self.add_const(e, b, &Big::from_u64(1), NONE); }
    fn sub(&mut self, e: &mut dyn FnMut(Row), b: &[u16], a: &[u16]) { for &x in b { self.not(e, x); } self.add(e, b, a, NONE, NONE); for &x in b { self.not(e, x); } }
    /// t ^= [A >= k]
    fn ge_const(&mut self, e: &mut dyn FnMut(Row), a: &[u16], k: &Big, t: u16) { let n = a.len(); if k.is_zero() { self.not(e, t); return; } if !k.lt(&Big::pow2(n)) { return; }
        let add = Big::pow2(n).sub(k); let mut c = NONE;
        for i in 0..n { let aa = a[i]; let c2 = self.carry[i];
            if add.bit(i) { self.clr(e, c2); if c != NONE { self.set(e, c2); self.not(e, aa); self.xor(e, c2, aa); self.push(e, aa); self.xor(e, c2, c); self.pop(e); self.not(e, aa); } else { self.xor(e, c2, aa); } c = c2; }
            else if c != NONE { self.clr(e, c2); self.push(e, aa); self.xor(e, c2, c); self.pop(e); c = c2; } }
        if c != NONE { self.xor(e, t, c); } }
    fn assign_if(&mut self, e: &mut dyn FnMut(Row), sel: u16, t: &[u16], a: &[u16]) { self.push(e, sel); for i in 0..t.len() { self.clr(e, t[i]); self.xor(e, t[i], a[i]); } self.pop(e); }
    // ---- arithmetic mod p
    fn canon(&mut self, e: &mut dyn FnMut(Row), v: &[u16]) -> V { let cur: V = v.to_vec(); let p = p256();
        for _ in 0..(if v.len() > 256 { 2 } else { 1 }) { let n = cur.len(); let t = self.copy(e, &cur); let f = self.bit();
            if n > 256 { self.add_const(e, &t, &Big::pow2(256).add(&cp()), NONE); } else { self.add_const(e, &t, &cp(), NONE); }      // + c - 2^256 mod 2^n
            self.ge_const(e, &cur, &p, f); self.assign_if(e, f, &cur, &t); }
        cur[..256].to_vec() }
    pub fn addp(&mut self, e: &mut dyn FnMut(Row), a: &[u16], b: &[u16]) -> V { let s = self.vec(257); for i in 0..256 { self.xor(e, s[i], a[i]); } self.add(e, &s, b, NONE, NONE); self.canon(e, &s) }
    pub fn negp(&mut self, e: &mut dyn FnMut(Row), a: &[u16]) -> V { let t = self.vec(256); for i in 0..256 { self.xor(e, t[i], a[i]); self.not(e, t[i]); } self.add_const(e, &t, &p256().add(&Big::from_u64(1)), NONE); self.canon(e, &t) }
    pub fn add_constp(&mut self, e: &mut dyn FnMut(Row), a: &[u16], k: &Big) -> V { assert!(k.lt(&p256()), "constant not reduced"); let t = self.vec(257); for i in 0..256 { self.xor(e, t[i], a[i]); } self.add_const(e, &t, k, NONE); self.canon(e, &t) }
    pub fn mul_small(&mut self, e: &mut dyn FnMut(Row), a: &[u16], k: &Big) -> V { let kb = k.bitlen().max(1); let acc = self.vec(a.len() + kb + 1); let mut first = true;
        for i in 0..kb { if k.bit(i) { if first { for j in 0..a.len() { self.xor(e, acc[i + j], a[j]); } first = false; } else { self.add(e, &acc[i..], a, NONE, NONE); } } }
        self.reduce(e, &acc) }
    fn reduce(&mut self, e: &mut dyn FnMut(Row), v: &[u16]) -> V { let mut cur: V = v.to_vec();
        while cur.len() > 257 { let hi: V = cur[256..].to_vec(); let acc = self.vec(257.max(hi.len() + 34));
            for i in 0..256 { self.xor(e, acc[i], cur[i]); }
            for sh in [32usize, 9, 8, 7, 6, 4, 0] { self.add(e, &acc[sh..], &hi, NONE, NONE); }
            cur = acc; }
        if cur.len() < 257 { let ext = self.vec(257 - cur.len()); cur.extend(ext); }
        self.canon(e, &cur) }
    pub fn mulp(&mut self, e: &mut dyn FnMut(Row), a: &[u16], b: &[u16]) -> V { let acc = self.vec(a.len() + b.len() + 1);
        for i in 0..b.len() { self.push(e, b[i]); let hi = acc.len().min(i + a.len() + 2); self.add(e, &acc[i..hi], a, NONE, NONE); self.pop(e); }
        self.reduce(e, &acc) }
    pub fn mul_constp(&mut self, e: &mut dyn FnMut(Row), a: &[u16], k: &Big) -> V { assert!(k.lt(&p256()), "constant not reduced"); let kb = k.bitlen().max(1); let acc = self.vec(a.len() + kb + 1); let mut any = false;
        for i in 0..kb { if k.bit(i) { if !any { for j in 0..a.len() { self.xor(e, acc[i + j], a[j]); } any = true; } else { let hi = acc.len().min(i + a.len() + 2 + 8); self.add(e, &acc[i..hi], a, NONE, NONE); } } }
        self.reduce(e, &acc) }
    /// n bits of the binary expansion of C / p
    pub fn expansion(&mut self, e: &mut dyn FnMut(Row), c: &[u16], n: usize) -> V { let q = self.vec(n + 1); let mut r: V = c.to_vec(); let mut j = 0i64; let n_i = n as i64;
        loop { let sh = n_i - 256 * (j + 1); if r.len() as i64 + sh <= 0 { break; }
            let src: &[u16] = if sh >= 0 { &r } else { &r[(-sh) as usize..] }; let off = sh.max(0) as usize;
            if j == 0 { let mut i = 0; while i < src.len() && off + i < q.len() { self.xor(e, q[off + i], src[i]); i += 1; } } else { let take = src.len().min(q.len() - off); let s2: V = src[..take].to_vec(); self.add(e, &q[off..], &s2, NONE, NONE); }
            j += 1; if r.len() as i64 + n_i - 256 * (j + 1) + 33 <= 0 { break; }
            let nx = self.vec(r.len() + 33); for i in 0..r.len() { self.xor(e, nx[32 + i], r[i]); }
            for s2 in [9usize, 8, 7, 6, 4, 0] { self.add(e, &nx[s2..], &r, NONE, NONE); } r = nx; }
        q[..n].to_vec() }
    /// inverse mod p: 512 iterations of the binary extended Euclid with signed cofactors
    pub fn inverse(&mut self, e: &mut dyn FnMut(Row), x: &[u16]) -> V { const W: usize = 260; let p = p256();
        let a = self.copy(e, x); let b = self.const_vec(e, &p, 256); let d = self.vec(256); let lt = self.bit(); let sw = self.bit(); let odd = self.bit();
        let mut u = self.const_vec(e, &Big::from_u64(1), W); let v = self.vec(W); let mut av = a.clone();
        for _ in 0..512 { self.clr(e, odd); self.xor(e, odd, av[0]);
            self.copy_into(e, &d, &av); for &t in &d { self.not(e, t); } self.clr(e, lt); self.add(e, &d, &b, NONE, lt); for &t in &d { self.not(e, t); }
            self.clr(e, sw); self.push(e, odd); self.xor(e, sw, lt); self.pop(e);
            self.assign_if(e, sw, &b, &av); self.assign_if(e, odd, &av, &d); self.push(e, sw); self.neg(e, &av); self.pop(e);
            self.push(e, sw); for i in 0..W { self.xor(e, u[i], v[i]); self.xor(e, v[i], u[i]); self.xor(e, u[i], v[i]); } self.pop(e);
            self.push(e, odd); self.sub(e, &u, &v); self.pop(e);
            self.push(e, u[0]); self.add_const(e, &u, &p, NONE); self.pop(e);
            av.rotate_left(1);
            let lo = u[0]; u.rotate_left(1); self.xor(e, lo, u[W - 2]); }
        self.add_const(e, &v, &p.shl(2), NONE); self.reduce(e, &v) }
    // ---- small moduli
    fn sum_columns(&mut self, e: &mut dyn FnMut(Row), cols: &mut Vec<VecDeque<u16>>) -> V { let mut out = Vec::new(); let mut w = 0;
        while w < cols.len() {
            while cols[w].len() >= 3 { let x = cols[w].pop_back().unwrap(); let y = cols[w].pop_back().unwrap(); let z = cols[w].pop_back().unwrap(); let s2 = self.bit(); let c = self.bit();
                self.xor(e, s2, x); self.xor(e, s2, y); self.xor(e, c, x); self.push(e, s2); self.xor(e, c, x); self.xor(e, c, z); self.pop(e); self.xor(e, s2, z);
                cols[w].push_front(s2); if w + 1 >= cols.len() { cols.push(VecDeque::new()); } cols[w + 1].push_back(c); }
            if cols[w].len() == 2 { let x = cols[w].pop_back().unwrap(); let y = cols[w].pop_back().unwrap(); let s2 = self.bit(); let c = self.bit(); self.xor(e, s2, x); self.xor(e, s2, y); self.push(e, x); self.xor(e, c, y); self.pop(e);
                cols[w].push_back(s2); if w + 1 >= cols.len() { cols.push(VecDeque::new()); } cols[w + 1].push_back(c); }
            let o = if cols[w].is_empty() { self.bit() } else { cols[w][0] }; out.push(o); w += 1; }
        out }
    /// V (< bound) -> V mod l: restoring division from the top; returns the low k bits
    pub fn reduce_small(&mut self, e: &mut dyn FnMut(Row), v: &[u16], l: u64, k: usize, bound: u64) -> V { let f = self.bit(); let neg = Big::from_u64((1u64 << (k + 1)) - l); let mut jmax = 0usize; while (l << (jmax + 1)) < bound { jmax += 1; }
        let mut v: V = v[..v.len().min(jmax + k + 1)].to_vec(); while v.len() < jmax + k + 1 { let b = self.bit(); v.push(b); }
        let lb = Big::from_u64(l);
        for j in (0..=jmax).rev() { let win: V = v[j..j + k + 1].to_vec(); self.clr(e, f); self.ge_const(e, &win, &lb, f); self.push(e, f); self.add_const(e, &win, &neg, NONE); self.pop(e); }
        v[..k].to_vec() }
    pub fn residue(&mut self, e: &mut dyn FnMut(Row), x: &[u16], l: u64, k: usize) -> V { const G: usize = 3; let m = self.next; let mut cols: Vec<VecDeque<u16>> = (0..k + G).map(|_| VecDeque::new()).collect();
        let mut c = 1 % l; let mut bound = 0u64;
        for i in 0..x.len() { let mut best = c; let mut bp = c.count_ones(); let mut v = c + l; while v < (1u64 << (k + G)) { let q = v.count_ones(); if q < bp { best = v; bp = q; } v += l; }
            for j in 0..k + G { if (best >> j) & 1 == 1 { cols[j].push_back(x[i]); } } bound += best; c = (2 * c) % l; }
        let w = self.sum_columns(e, &mut cols); let r = self.reduce_small(e, &w, l, k, bound + 1); self.keep(e, m, &r) }
    pub fn mul_const_small(&mut self, e: &mut dyn FnMut(Row), r: &[u16], kc: u64, l: u64, k: usize) -> V { let m = self.next; let mut cols: Vec<VecDeque<u16>> = (0..2 * k).map(|_| VecDeque::new()).collect(); let kc = kc % l;
        for i in 0..k { if (kc >> i) & 1 == 1 { for j in 0..r.len() { cols[i + j].push_back(r[j]); } } }
        let w = self.sum_columns(e, &mut cols); let o = self.reduce_small(e, &w, l, k, l * l); self.keep(e, m, &o) }
    pub fn expansion_small(&mut self, e: &mut dyn FnMut(Row), r: &[u16], l: u64, k: usize, n: usize) -> V { let m = self.next; let out = self.vec(n); let mut v = self.vec(k + 1); let neg = Big::from_u64((1u64 << (k + 1)) - l); let lb = Big::from_u64(l);
        for i in 0..k { self.xor(e, v[i + 1], r[i]); }
        for t in 0..n { let q = out[n - 1 - t]; self.ge_const(e, &v, &lb, q); self.push(e, q); self.add_const(e, &v, &neg, NONE); self.pop(e); v.rotate_right(1); }
        self.keep(e, m, &out) }
    pub fn xor_pub(&mut self, e: &mut dyn FnMut(Row), t: u16, a: u16) { self.xor(e, t, a); }
}
