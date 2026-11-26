//! Code-only fixed upper-walk generator. No gate assets or input values.
//! Small lane lists and bounded temporary captures replace JS capture/reverse.
//! Port of forward631_opt_20261119/{forward,discovery,core}.cjs, revision4.
//! All63 columns match the JS ops8 records and SHA3, not just gate counts.
//! Stop: first r<2^129. Public columns65..127;24-bit cap below105.
//! 385 data +2 row flags +parity; a separate dispatch flag;242 passengers.
//! No filesystem access, gate assets, input-dependent emission or lookup tables.
//! Captures are computed at runtime and limited to2M words each; the fixed
//! schedule's measured largest capture is311,720 words, independent of inputs.
use crate::circuit::{BitId, Op, OperationType as K, QubitId as Q};
use std::collections::BTreeSet;
const A: usize = 385;
const B: usize = 386;
const PAR: usize = 387;
const E: usize = 630;
fn range(a: usize, b: usize) -> Vec<usize> {
    (a..b).collect()
}
fn cat(a: &[&[usize]]) -> Vec<usize> {
    a.iter().flat_map(|x| x.iter().copied()).collect()
}
fn unique(a: &[usize]) -> Vec<usize> {
    let mut r = Vec::new();
    for &q in a {
        if !r.contains(&q) {
            r.push(q);
        }
    }
    r
}
#[derive(Clone, Copy, Debug, Default)]
pub struct Cost {
    pub gates: u64,
    pub toffolis: u64,
    pub max_capture_words: usize,
}
pub struct Frame {
    pub own: [Q; 631],
}
impl Frame {
    pub fn new(walk: [Q; 389], passenger: [Q; 242]) -> Self {
        let own = std::array::from_fn(|i| {
            if i < 388 {
                walk[i]
            } else if i < 630 {
                passenger[i - 388]
            } else {
                walk[388]
            }
        });
        assert_eq!(own.iter().map(|q| q.0).collect::<BTreeSet<_>>().len(), 631);
        Self { own }
    }
}
pub struct Ports {
    pub c: usize,
    pub r: Vec<usize>,
    pub u: Vec<usize>,
}
impl Ports {
    pub fn handover() -> Self {
        Self {
            c: 65,
            r: range(0, 192),
            u: cat(&[&range(193, 256), &[256, 192]]),
        }
    }
    pub fn advance(&mut self) {
        assert!((65..128).contains(&self.c));
        self.u.push(self.r.pop().unwrap());
        self.c += 1;
    }
    pub fn canonical_map(&self) -> [usize; 631] {
        let mut a = std::array::from_fn(|i| i);
        assert_eq!(self.r.len(), 257 - self.c);
        assert_eq!(self.u.len(), self.c);
        for (i, &q) in self.r.iter().enumerate() {
            a[i] = q;
        }
        for (i, &q) in self.u.iter().enumerate() {
            a[257 - self.c + i] = q;
        }
        a
    }
}
struct Gen<'a> {
    sink: &'a mut dyn FnMut(u32),
    caps: Vec<Vec<u32>>,
    pool: Vec<usize>,
    cost: Cost,
}
impl<'a> Gen<'a> {
    fn new(sink: &'a mut dyn FnMut(u32)) -> Self {
        Self {
            sink,
            caps: Vec::new(),
            pool: cat(&[&range(0, 385), &range(388, 630)]),
            cost: Cost::default(),
        }
    }
    fn word(&mut self, w: u32) {
        if let Some(b) = self.caps.last_mut() {
            b.push(w);
            assert!(b.len() <= 2_000_000, "bounded capture");
        } else {
            self.cost.gates += 1;
            if w >> 20 & 1023 != 1023 {
                self.cost.toffolis += 1;
            }
            (self.sink)(w);
        }
    }
    fn x(&mut self, t: usize) {
        assert!(t < 631);
        self.word((1023 << 20) | (1023 << 10) | t as u32);
    }
    fn cx(&mut self, c: usize, t: usize) {
        assert!(c < 631 && t < 631 && c != t);
        self.word((1023 << 20) | ((c as u32) << 10) | t as u32);
    }
    fn ccx(&mut self, a: usize, b: usize, t: usize) {
        assert!(a < 631 && b < 631 && t < 631 && a != b && a != t && b != t);
        self.word(((a as u32) << 20) | ((b as u32) << 10) | t as u32);
    }
    fn xs(&mut self, a: &[usize]) {
        for &q in a {
            self.x(q);
        }
    }
    fn swap(&mut self, a: usize, b: usize) {
        self.cx(a, b);
        self.cx(b, a);
        self.cx(a, b);
    }
    fn cswap(&mut self, e: usize, a: usize, b: usize) {
        self.cx(b, a);
        self.ccx(e, a, b);
        self.cx(b, a);
    }
    fn capture(&mut self, f: impl FnOnce(&mut Self)) -> Vec<u32> {
        self.caps.push(Vec::new());
        f(self);
        let b = self.caps.pop().unwrap();
        self.cost.max_capture_words = self.cost.max_capture_words.max(b.len());
        b
    }
    fn play(&mut self, b: &[u32], back: bool) {
        if back {
            for &w in b.iter().rev() {
                self.word(w);
            }
        } else {
            for &w in b {
                self.word(w);
            }
        }
    }
    fn reverse(&mut self, f: impl FnOnce(&mut Self)) {
        let b = self.capture(f);
        self.play(&b, true);
    }
    fn borrow(&self, n: usize, exclude: &[&[usize]]) -> Vec<usize> {
        let mut marked = [false; 631];
        for a in exclude {
            for &q in *a {
                marked[q] = true;
            }
        }
        let v: Vec<_> = self
            .pool
            .iter()
            .copied()
            .filter(|&q| !marked[q])
            .take(n)
            .collect();
        assert_eq!(v.len(), n, "dirty loan");
        v
    }
    fn maj(&mut self, x: usize, y: usize, z: usize) {
        self.cx(z, y);
        self.cx(z, x);
        self.ccx(x, y, z);
    }
    fn uma(&mut self, x: usize, y: usize, z: usize, e: Option<usize>) {
        if let Some(e) = e {
            self.ccx(x, y, z);
            self.cx(z, x);
            self.cx(z, y);
            self.ccx(e, z, y);
            self.ccx(e, x, y);
        } else {
            self.ccx(x, y, z);
            self.cx(z, x);
            self.cx(x, y);
        }
    }
    fn add(&mut self, a: &[usize], b: &[usize], c0: usize, e: Option<usize>, out: Option<usize>) {
        let n = a.len();
        assert!(n > 0 && n == b.len());
        self.maj(c0, b[0], a[0]);
        for i in 1..n {
            self.maj(a[i - 1], b[i], a[i]);
        }
        if let Some(t) = out {
            if let Some(e) = e {
                self.ccx(e, a[n - 1], t);
            } else {
                self.cx(a[n - 1], t);
            }
        }
        for i in (1..n).rev() {
            self.uma(a[i - 1], b[i], a[i], e);
        }
        self.uma(c0, b[0], a[0], e);
    }
    fn sub(&mut self, a: &[usize], b: &[usize], c0: usize, e: Option<usize>) {
        self.reverse(|g| g.add(a, b, c0, e, None));
    }
    fn gt(&mut self, a: &[usize], b: &[usize], c0: usize, t: usize, e: Option<usize>) {
        let n = a.len();
        self.xs(b);
        self.maj(c0, b[0], a[0]);
        for i in 1..n {
            self.maj(a[i - 1], b[i], a[i]);
        }
        if let Some(e) = e {
            self.ccx(e, a[n - 1], t);
        } else {
            self.cx(a[n - 1], t);
        }
        for i in (1..n).rev() {
            self.ccx(a[i - 1], b[i], a[i]);
            self.cx(a[i], a[i - 1]);
            self.cx(a[i], b[i]);
        }
        self.ccx(c0, b[0], a[0]);
        self.cx(a[0], c0);
        self.cx(a[0], b[0]);
        self.xs(b);
    }
    fn inc(&mut self, b: &[usize], c0: usize, avoid: &[&[usize]]) {
        let c0s = [c0];
        let mut ex = vec![b, &c0s[..]];
        ex.extend_from_slice(avoid);
        let d = self.borrow(b.len(), &ex);
        self.sub(&d, b, c0, None);
        self.xs(&d);
        self.sub(&d, b, c0, None);
        self.xs(&d);
    }
    fn cinc(&mut self, e: usize, b: &[usize], c0: usize, avoid: &[&[usize]]) {
        self.inc(&cat(&[&[e], b]), c0, avoid);
        self.x(e);
    }
    fn rot1(&mut self, a: &[usize]) {
        for i in (1..a.len()).rev() {
            self.swap(a[i], a[i - 1]);
        }
    }
    fn rot_up(&mut self, a: &[usize], d: isize, e: usize) {
        let n = a.len();
        let d = d.rem_euclid(n as isize) as usize;
        if d == 0 {
            return;
        }
        let mut seen = vec![false; n];
        for k in 0..n {
            if seen[k] {
                continue;
            }
            seen[k] = true;
            let mut j = (k + d) % n;
            while j != k {
                self.cswap(e, a[k], a[j]);
                seen[j] = true;
                j = (j + d) % n;
            }
        }
    }
}
fn nr_adder(g: &mut Gen<'_>, a: &[usize], b: &[usize], out: Option<usize>, e: Option<usize>) {
    let n = a.len();
    assert!(n > 0 && n == b.len());
    assert!(out.is_none() || e.is_none());
    let put = |g: &mut Gen<'_>, c, t| {
        if let Some(e) = e {
            g.ccx(e, c, t)
        } else {
            g.cx(c, t)
        }
    };
    if n == 1 {
        if let Some(t) = out {
            g.ccx(b[0], a[0], t);
        }
        put(g, a[0], b[0]);
        return;
    }
    for i in 1..n {
        g.cx(a[i], b[i]);
    }
    if let Some(t) = out {
        g.cx(a[n - 1], t);
    }
    for i in (1..n - 1).rev() {
        g.cx(a[i], a[i + 1]);
    }
    for i in 0..n - 1 {
        g.ccx(b[i], a[i], a[i + 1]);
    }
    if let Some(t) = out {
        g.ccx(b[n - 1], a[n - 1], t);
    }
    put(g, a[n - 1], b[n - 1]);
    for i in (0..n - 1).rev() {
        g.ccx(b[i], a[i], a[i + 1]);
        put(g, a[i], b[i]);
    }
    for i in 1..n - 1 {
        g.cx(a[i], a[i + 1]);
    }
    for i in 1..n {
        g.cx(a[i], b[i]);
    }
}
fn inc_t(g: &mut Gen<'_>, b: &[usize]) {
    if b.is_empty() {
        return;
    }
    if b.len() == 1 {
        g.x(b[0]);
        return;
    }
    let d = g.borrow(b.len(), &[b]);
    g.reverse(|g| nr_adder(g, &d, b, None, None));
    g.xs(&d);
    g.reverse(|g| nr_adder(g, &d, b, None, None));
    g.xs(&d);
}
fn dec_t(g: &mut Gen<'_>, b: &[usize]) {
    if b.is_empty() {
        return;
    }
    if b.len() == 1 {
        g.x(b[0]);
        return;
    }
    let d = g.borrow(b.len(), &[b]);
    nr_adder(g, &d, b, None, None);
    g.xs(&d);
    nr_adder(g, &d, b, None, None);
    g.xs(&d);
}
fn cinc_t(g: &mut Gen<'_>, e: usize, b: &[usize]) {
    inc_t(g, &cat(&[&[e], b]));
    g.x(e);
}
fn cdec_t(g: &mut Gen<'_>, e: usize, b: &[usize]) {
    g.x(e);
    dec_t(g, &cat(&[&[e], b]));
}
fn mcx(g: &mut Gen<'_>, pos: &[usize], neg: &[usize], t: usize) {
    g.xs(neg);
    let a = unique(&cat(&[pos, neg]));
    match a.len() {
        0 => g.x(t),
        1 => g.cx(a[0], t),
        2 => g.ccx(a[0], a[1], t),
        n => {
            let d = g.borrow(n - 2, &[&a, &[t]]);
            g.ccx(a[0], a[1], d[0]);
            for i in 1..d.len() {
                g.ccx(a[i + 1], d[i - 1], d[i]);
            }
            g.ccx(a[n - 1], d[d.len() - 1], t);
            for i in (1..d.len()).rev() {
                g.ccx(a[i + 1], d[i - 1], d[i]);
            }
            g.ccx(a[0], a[1], d[0]);
            for i in 1..d.len() {
                g.ccx(a[i + 1], d[i - 1], d[i]);
            }
            g.ccx(a[n - 1], d[d.len() - 1], t);
            for i in (1..d.len()).rev() {
                g.ccx(a[i + 1], d[i - 1], d[i]);
            }
        }
    }
    for &q in neg.iter().rev() {
        g.x(q);
    }
}
fn const_below(g: &mut Gen<'_>, a: &[usize], limit: u64, t: usize, avoid: &[&[usize]]) {
    let n = a.len();
    if limit == 0 {
        return;
    }
    if (limit as u128) >= (1u128 << n) {
        g.x(t);
        return;
    }
    let ts = [t];
    let mut ex = vec![a, &ts[..]];
    ex.extend_from_slice(avoid);
    let d = g.borrow(n + 1, &ex);
    let bits: Vec<_> = (0..n).map(|i| limit >> i & 1 != 0).collect();
    let mut coeff = vec![false; n + 1];
    for i in 0..n {
        if bits[i] {
            coeff[i] ^= true;
            coeff[i + 1] ^= true;
        }
    }
    for i in 0..n {
        if !bits[i] {
            g.x(a[i]);
        }
    }
    for _ in 0..2 {
        g.x(d[n]);
        for i in (0..n).rev() {
            g.ccx(a[i], d[i + 1], d[i]);
        }
        for i in 0..=n {
            if coeff[i] {
                g.cx(d[i], t);
            }
        }
        for i in 0..n {
            g.ccx(a[i], d[i + 1], d[i]);
        }
    }
    for i in 0..n {
        if !bits[i] {
            g.x(a[i]);
        }
    }
}
// Fused non-restoring digits share a difference-encoded divisor.
fn mixed_div(g: &mut Gen<'_>, jword: &[usize], v: &[usize], k: usize) {
    let n = v.len();
    assert!(n >= 2 && k >= 1 && jword.len() >= n + k);
    fn flip(g: &mut Gen<'_>, e: Option<usize>, w: &[usize]) {
        if let Some(e) = e {
            g.x(e);
            for &q in w {
                g.cx(e, q);
            }
            g.x(e);
        } else {
            g.xs(w);
        }
    }
    let j = k - 1;
    flip(g, None, &jword[j..j + n + 1]);
    for i in 1..n {
        g.cx(v[i], jword[j + i]);
    }
    g.cx(v[n - 1], jword[j + n]);
    for i in (1..n - 1).rev() {
        g.cx(v[i], v[i + 1]);
    }
    for j in (0..k).rev() {
        let b = &jword[j..j + n];
        let h = jword[j + n];
        for i in 0..n - 1 {
            g.ccx(b[i], v[i], v[i + 1]);
        }
        g.ccx(b[n - 1], v[n - 1], h);
        g.cx(v[n - 1], b[n - 1]);
        for i in (0..n - 1).rev() {
            g.ccx(b[i], v[i], v[i + 1]);
            g.cx(v[i], b[i]);
        }
        if j == 0 {
            break;
        }
        let old = if j == k - 1 {
            None
        } else {
            Some(jword[j + n + 1])
        };
        flip(g, Some(h), &jword[j..j + n]);
        flip(g, old, &[h]);
        flip(g, Some(h), &[jword[j - 1]]);
        for i in 0..n - 1 {
            g.cx(v[i + 1], jword[j + i]);
        }
    }
    for i in 1..n - 1 {
        g.cx(v[i], v[i + 1]);
    }
    for i in 1..n {
        g.cx(v[i], jword[i]);
    }
    flip(
        g,
        if k == 1 { None } else { Some(jword[n + 1]) },
        &jword[..n + 1],
    );
    nr_adder(g, v, &jword[..n], None, Some(jword[n]));
    g.xs(&jword[n..n + k]);
}
fn mixed_mul(g: &mut Gen<'_>, j: &[usize], v: &[usize], k: usize) {
    g.reverse(|g| mixed_div(g, j, v, k));
}
fn odd_mul(g: &mut Gen<'_>, x: &[usize], hi: &[usize], c0: usize) {
    for j in (0..x.len() - 1).rev() {
        let b = &x[j + 1..];
        let m = hi.len().min(b.len());
        let a = &hi[..m];
        if m == b.len() {
            nr_adder(g, a, b, None, Some(x[j]));
        } else if m + 1 == b.len() {
            g.add(a, &b[..m], c0, Some(x[j]), Some(b[m]));
        } else {
            panic!("unfunded oddMul width");
        }
    }
}
fn reflect(g: &mut Gen<'_>, j: &[usize], e: Option<usize>) {
    for &q in j {
        if let Some(e) = e {
            g.cx(e, q);
        } else {
            g.x(q);
        }
    }
    let mut x = (1u64 << 32) + 977;
    let mut i = 0;
    while x != 0 {
        if x & 1 != 0 {
            let d = 2 - (x % 4) as i64;
            if let Some(e) = e {
                if d > 0 {
                    cdec_t(g, e, &j[i..]);
                } else {
                    cinc_t(g, e, &j[i..]);
                }
            } else if d > 0 {
                dec_t(g, &j[i..]);
            } else {
                inc_t(g, &j[i..]);
            }
            x = if d > 0 { x - 1 } else { x + 1 };
        }
        x /= 2;
        i += 1;
    }
    if let Some(e) = e {
        cinc_t(g, e, &j[256..]);
    } else {
        inc_t(g, &j[256..]);
    }
}
struct Layout {
    c: usize,
    b: usize,
    s: usize,
    r: Vec<usize>,
    u: Vec<usize>,
    v: Vec<usize>,
    q: Vec<usize>,
    n: Vec<usize>,
    bank: Vec<usize>,
    cap: bool,
}
impl Layout {
    fn new(c: usize) -> Self {
        let r = range(0, 257 - c);
        let u = range(257 - c, 257);
        let n = cat(&[&u, &r]);
        Self {
            c,
            b: 128 - c,
            s: (127 - c).min(if c < 105 { 24 } else { 127 - c }),
            r,
            u,
            v: range(257, 257 + c),
            q: range(257 + c, 385),
            n,
            bank: range(257, 385),
            cap: c < 105,
        }
    }
    fn vt(&self) -> usize {
        self.v[self.c - 1]
    }
}
fn direction(g: &mut Gen<'_>, l: &Layout) {
    let t = l.u[l.c - 1];
    g.cx(t, B);
    g.x(t);
    g.gt(&l.u[..l.c - 1], &l.v[1..], A, B, Some(t));
    g.x(t);
}
fn carry_xor(g: &mut Gen<'_>, a: &[usize], b: &[usize], t: usize, ctrl: &[usize]) {
    let code = g.capture(|g| nr_adder(g, a, b, Some(t), None));
    for w in code {
        let (c1, c2, out) = (
            (w >> 20 & 1023) as usize,
            (w >> 10 & 1023) as usize,
            (w & 1023) as usize,
        );
        if out != t || ctrl.is_empty() {
            g.word(w);
        } else {
            let x = if c1 == 1023 { vec![c2] } else { vec![c1, c2] };
            mcx(g, &cat(&[ctrl, &x]), &[], out);
        }
    }
    g.reverse(|g| nr_adder(g, a, b, None, None));
}
fn direction_no_carry(g: &mut Gen<'_>, l: &Layout) {
    let top = l.u[l.c - 1];
    let a = &l.u[..l.c - 1];
    let b = &l.v[1..];
    g.cx(top, B);
    g.x(top);
    g.xs(b);
    carry_xor_small(g, a, b, B, top);
    g.xs(b);
    g.x(top);
}
// Preserve the source helper's CCX control order for byte equality.
fn carry_xor_small(g: &mut Gen<'_>, a: &[usize], b: &[usize], t: usize, e: usize) {
    let code = g.capture(|g| nr_adder(g, a, b, Some(t), None));
    for w in code {
        let (c1, c2, out) = (
            (w >> 20 & 1023) as usize,
            (w >> 10 & 1023) as usize,
            (w & 1023) as usize,
        );
        if out != t {
            g.word(w);
        } else if c1 == 1023 {
            g.ccx(e, c2, t);
        } else {
            let d = g.borrow(1, &[&[e, c1, c2, t]])[0];
            g.ccx(e, c1, d);
            g.ccx(d, c2, t);
            g.ccx(e, c1, d);
            g.ccx(d, c2, t);
        }
    }
    g.reverse(|g| nr_adder(g, a, b, None, None));
}
fn sub_wide(g: &mut Gen<'_>, v: &[usize], w: &[usize], e: usize, carry: usize) {
    let low = &w[..v.len()];
    let high = &w[v.len()..];
    g.xs(low);
    carry_xor(g, v, low, carry, &[e]);
    g.xs(low);
    g.reverse(|g| nr_adder(g, v, low, None, Some(e)));
    cdec_t(g, carry, high);
    carry_xor(g, v, low, carry, &[e]);
}
fn reciprocal_digit(g: &mut Gen<'_>, z: &[usize], d: &[usize]) {
    let n = d.len();
    let b = &z[..n];
    let h = z[n];
    g.xs(b);
    for i in 1..n {
        g.cx(d[i], b[i]);
    }
    g.cx(d[n - 1], h);
    for i in (1..n - 1).rev() {
        g.cx(d[i], d[i + 1]);
    }
    for i in 0..n - 1 {
        g.ccx(b[i], d[i], d[i + 1]);
    }
    g.ccx(b[n - 1], d[n - 1], h);
    g.x(h);
    g.ccx(h, d[n - 1], b[n - 1]);
    for i in (0..n - 1).rev() {
        g.ccx(b[i], d[i], d[i + 1]);
        g.ccx(h, d[i], b[i]);
    }
    for i in 1..n - 1 {
        g.cx(d[i], d[i + 1]);
    }
    for i in 1..n {
        g.cx(d[i], b[i]);
    }
    g.xs(b);
}
fn quotient_value(j: usize, d: usize, h: usize, max: u64) -> u64 {
    let t = j + 5;
    let hi = (1usize << (t - 1)) - 1;
    if h == hi {
        return (1u64 << j).min(max);
    }
    let den = 2 * h as u64 + if d == 1 { 3 } else { 0 };
    let den = if d == 0 { den - 1 } else { den };
    (((1u64 << (t + j)) - 1) / den).min(max)
}
fn table(g: &mut Gen<'_>, l: &Layout, j: usize) {
    let n = &l.n[..256];
    let t = j + 5;
    let head = &n[256 - j - (t - 1)..256 - j];
    let positive = [n[255 - j]];
    let negative = &n[256 - j..];
    let low = 1usize << (t - 2);
    let high = (1usize << (t - 1)) - 1;
    let max = (1u64 << l.b) - 1;
    for d in 0..2 {
        let controls = cat(&[&positive, &[E], if d == 1 { &[B] } else { &[] }]);
        let neg = cat(&[negative, if d == 0 { &[B] } else { &[] }]);
        let mut prev = 0;
        for h in low..=high {
            let f = quotient_value(j, d, h, max);
            let delta = f ^ prev;
            if delta == 0 {
                continue;
            }
            if h != low {
                const_below(g, head, h as u64, A, &[&controls, &neg, &l.q]);
            }
            let ns = if h == low {
                neg.clone()
            } else {
                cat(&[&neg, &[A]])
            };
            for k in 0..l.b {
                if delta >> k & 1 != 0 {
                    mcx(g, &controls, &ns, l.q[k]);
                }
            }
            if h != low {
                const_below(g, head, h as u64, A, &[&controls, &neg, &l.q]);
            }
            prev = f;
        }
    }
}
fn reciprocal_body(g: &mut Gen<'_>, l: &Layout, j: usize) {
    let t = j + 5;
    let n = &l.n[..256];
    let b = &n[256 - (t - 1)..];
    let pool = cat(&[&l.q, &n[..j]]);
    let word = &pool[..t + 1];
    let d0 = pool[t + 1];
    let d = cat(&[&[d0], b]);
    let carry = l.vt();
    g.x(d0);
    dec_t(g, b);
    g.cinc(B, &b[1..], carry, &[]);
    g.xs(&word[..t - 2]);
    for _ in 0..j + 2 {
        g.rot1(word);
        g.x(word[0]);
        reciprocal_digit(g, word, &d);
        g.cx(word[0], word[t]);
        g.x(word[t]);
    }
    g.xs(word);
    if j == 0 {
        g.x(word[t]);
    }
    g.reverse(|g| odd_mul(g, word, b, carry));
    g.reverse(|g| g.cinc(B, &b[1..], carry, &[]));
    inc_t(g, b);
    g.x(d0);
    if j == l.s && l.b == l.s + 1 {
        g.cx(word[l.b], carry);
        for &q in &word[..l.b + 1] {
            g.cx(carry, q);
        }
        mcx(
            g,
            &[b[b.len() - 1]],
            &cat(&[&[B], &b[..b.len() - 1]]),
            carry,
        );
    }
}
fn controlled(g: &mut Gen<'_>, code: &[u32], enable: usize) {
    for &w in code {
        let (a, b, t) = (
            (w >> 20 & 1023) as usize,
            (w >> 10 & 1023) as usize,
            (w & 1023) as usize,
        );
        let c = if a != 1023 {
            vec![enable, a, b]
        } else if b != 1023 {
            vec![enable, b]
        } else {
            vec![enable]
        };
        assert!(!c.contains(&t));
        mcx(g, &c, &[], t);
    }
}
fn estimate(g: &mut Gen<'_>, l: &Layout) {
    if l.c == 127 {
        g.cx(E, l.q[0]);
        return;
    }
    let n = &l.n[..256];
    direction(g, l);
    mixed_mul(g, &l.n, &l.v, l.r.len());
    g.x(l.vt());
    for j in 0..=l.s {
        if l.s < 6 {
            table(g, l, j);
            continue;
        }
        let t = j + 5;
        let head = &n[256 - j - (t - 1)..256 - j];
        let hi = &n[256 - j..];
        let lead = n[255 - j];
        mcx(g, &cat(&[&[E], head]), hi, l.q[j]);
        let choose = |g: &mut Gen<'_>| {
            mcx(g, &[E, lead], hi, A);
            mcx(g, &cat(&[&[E], head]), hi, A);
        };
        choose(g);
        if j != 0 {
            g.rot_up(n, j as isize, A);
        }
        let body = g.capture(|g| reciprocal_body(g, l, j));
        controlled(g, &body, A);
        if j != 0 {
            g.rot_up(n, -(j as isize), A);
        }
        choose(g);
    }
    g.x(l.vt());
    mixed_div(g, &l.n, &l.v, l.r.len());
    direction(g, l);
}
fn small_parity(g: &mut Gen<'_>, l: &Layout, target: usize) {
    direction_no_carry(g, l);
    mixed_mul(g, &l.n, &l.v, l.r.len());
    let n = &l.n[..256];
    for j in 0..=l.s {
        let t = j + 5;
        let head = &n[256 - j - (t - 1)..256 - j];
        let hi = &n[256 - j..];
        let lead = n[255 - j];
        for d in 0..2 {
            for h in (1usize << (t - 2))..(1usize << (t - 1)) {
                let f = quotient_value(j, d, h, (1u64 << l.b) - 1);
                if f & 1 == 0 {
                    continue;
                }
                let mut pos = vec![lead];
                let mut neg = hi.to_vec();
                if d == 1 {
                    pos.push(B);
                } else {
                    neg.push(B);
                }
                for (k, &q) in head.iter().enumerate() {
                    if h >> k & 1 != 0 {
                        pos.push(q);
                    } else {
                        neg.push(q);
                    }
                }
                mcx(g, &unique(&pos), &unique(&neg), target);
            }
        }
    }
    mixed_div(g, &l.n, &l.v, l.r.len());
    direction_no_carry(g, l);
}
// Compute/uncompute arithmetic is unconditional. Only output writes need
// the rank control, and neither the output nor selector can be a dirty loan.
fn reciprocal_witness(g: &mut Gen<'_>, l: &Layout, target: usize) {
    let carry = l.vt();
    let sel = l.n[256];
    let n = &l.n[..256];
    let old = g.pool.clone();
    g.pool.retain(|&q| q != sel);
    direction_no_carry(g, l);
    mixed_mul(g, &l.n, &l.v, l.r.len());
    g.x(carry);
    for j in 0..=l.s {
        let t = j + 5;
        let head = &n[256 - j - (t - 1)..256 - j];
        let hi = &n[256 - j..];
        let lead = n[255 - j];
        let satpos = [lead];
        let satneg = cat(&[hi, &[B], &head[..head.len() - 1]]);
        mcx(g, &cat(&[head, &[l.q[0]]]), hi, target);
        if j == 0 {
            mcx(g, head, hi, target);
        }
        if j == l.s && l.b == l.s + 1 {
            mcx(g, &[lead, l.q[0]], &satneg, target);
            mcx(g, &satpos, &satneg, target);
        }
        let choose = |g: &mut Gen<'_>| {
            mcx(g, &[lead], hi, sel);
            mcx(g, head, hi, sel);
            if j == l.s && l.b == l.s + 1 {
                mcx(g, &satpos, &satneg, sel);
            }
        };
        choose(g);
        if j != 0 {
            g.rot_up(n, j as isize, sel);
        }
        let body = g.capture(|g| {
            let b = &n[256 - (t - 1)..];
            let pool = cat(&[&l.q, &n[..j]]);
            let word = &pool[..t + 1];
            let p = g.capture(|g| {
                dec_t(g, b);
                g.cinc(B, &b[1..], carry, &[]);
                inc_t(g, word);
                odd_mul(g, word, b, carry);
                g.xs(word);
                if j == 0 {
                    g.x(word[t]);
                }
            });
            g.play(&p, false);
            g.x(target);
            g.cx(word[t], target);
            g.play(&p, true);
        });
        for w in body {
            let (a, b, out) = (
                (w >> 20 & 1023) as usize,
                (w >> 10 & 1023) as usize,
                (w & 1023) as usize,
            );
            if out != target {
                g.word(w);
            } else {
                let c = if a != 1023 {
                    vec![sel, a, b]
                } else if b != 1023 {
                    vec![sel, b]
                } else {
                    vec![sel]
                };
                mcx(g, &c, &[], out);
            }
        }
        if j != 0 {
            g.rot_up(n, -(j as isize), sel);
        }
        choose(g);
    }
    g.x(carry);
    mixed_div(g, &l.n, &l.v, l.r.len());
    direction_no_carry(g, l);
    g.pool = old;
}
fn witness(g: &mut Gen<'_>, l: &Layout, target: usize) {
    if l.c >= 123 {
        small_parity(g, l, target);
        g.cx(l.q[0], target);
    } else {
        reciprocal_witness(g, l, target);
    }
}
fn guard_output(g: &mut Gen<'_>, l: &Layout, target: usize, e: usize) {
    let code = g.capture(|g| witness(g, l, target));
    for w in code {
        let (a, b, t) = (
            (w >> 20 & 1023) as usize,
            (w >> 10 & 1023) as usize,
            (w & 1023) as usize,
        );
        assert!(a != target && b != target, "oracle reads output");
        if t != target {
            g.word(w);
        } else {
            let c = if a != 1023 {
                vec![e, a, b]
            } else if b != 1023 {
                vec![e, b]
            } else {
                vec![e]
            };
            mcx(g, &c, &[], t);
        }
    }
}
// Adjacent digits cancel overlapping X scaffolds; pre/post select endpoints.
fn digit(g: &mut Gen<'_>, z: &[usize], v: &[usize], e: usize, t: usize, pre: bool, post: bool) {
    let n = v.len();
    let d = &z[..n];
    let h = z[n];
    if pre {
        g.xs(d);
    } else {
        g.x(d[0]);
    }
    for i in 1..n {
        g.cx(v[i], d[i]);
    }
    g.ccx(e, v[n - 1], h);
    for i in (1..n - 1).rev() {
        g.cx(v[i], v[i + 1]);
    }
    for i in 0..n - 1 {
        g.ccx(d[i], v[i], v[i + 1]);
    }
    g.ccx(e, v[n - 1], t);
    g.ccx(t, d[n - 1], h);
    g.ccx(e, v[n - 1], t);
    g.cx(e, h);
    g.ccx(e, h, t);
    g.ccx(t, v[n - 1], d[n - 1]);
    for i in (0..n - 1).rev() {
        g.ccx(d[i], v[i], v[i + 1]);
        g.ccx(t, v[i], d[i]);
    }
    g.ccx(e, h, t);
    for i in 1..n - 1 {
        g.cx(v[i], v[i + 1]);
    }
    for i in 1..n {
        g.cx(v[i], d[i]);
    }
    if post {
        g.xs(d);
    } else {
        g.x(d[n - 1]);
    }
}
fn div(g: &mut Gen<'_>, jword: &[usize], v: &[usize], k: usize, e: usize, pick: usize, back: bool) {
    let code = g.capture(|g| {
        for j in (0..k).rev() {
            digit(
                g,
                &jword[j..j + v.len() + 1],
                v,
                e,
                pick,
                j == k - 1,
                j == 0,
            );
        }
    });
    g.play(&code, back);
}
fn permute(g: &mut Gen<'_>, src: &[usize], dst: &[usize], e: usize) {
    let mut src = src.to_vec();
    assert_eq!(src.len(), dst.len());
    for i in 0..src.len() {
        if src[i] != dst[i] {
            let j = src.iter().position(|&q| q == dst[i]).unwrap();
            g.cswap(e, src[i], src[j]);
            src.swap(i, j);
        }
    }
}
fn correction_mark(g: &mut Gen<'_>, l: &Layout, low: usize, high: usize, e: usize) {
    mcx(
        g,
        &[e],
        &cat(&[&[l.vt()], &l.r[(130 + high).min(l.r.len())..]]),
        A,
    );
    if low != 0 {
        mcx(
            g,
            &[e],
            &cat(&[&[l.vt()], &l.r[(129 + low).min(l.r.len())..]]),
            A,
        );
    }
}
// Product/remainder widths trade clean top cells in public rank bands.
fn correction_probe(g: &mut Gen<'_>, l: &Layout, e: usize) {
    let w = cat(&[&l.u, &l.q]);
    let lo = &w[..127];
    let out = w[127];
    let candidate = if l.cap { 127.min(l.c + 25) } else { 127 };
    let mut low = 0;
    while low < l.b {
        let n = 127.min(128 - low).min(candidate);
        let high = (l.b - 1).min(255 - 2 * n);
        let cap = l.r.len().min(130 + high);
        let need = n - (l.c - 1);
        let pool = cat(&[&[B], &l.r[cap..], &lo[n..], &[l.vt()]]);
        let zeros = &pool[..need];
        assert!(high >= low);
        let j = cat(&[&range(388, 388 + l.c - 1), zeros, &l.r[..cap]]);
        let v = &lo[..n];
        correction_mark(g, l, low, high, e);
        mixed_mul(g, &j, v, cap);
        let f = g.capture(|g| reflect(g, &j, None));
        g.play(&f, false);
        g.ccx(A, j[j.len() - 1], out);
        g.play(&f, true);
        mixed_div(g, &j, v, cap);
        correction_mark(g, l, low, high, e);
        low = high + 1;
    }
}
fn exact_quotient(g: &mut Gen<'_>, l: &Layout, e: usize) {
    let w = cat(&[&l.u, &l.q]);
    let lo = &w[..127];
    let top = w[127];
    let vt = l.vt();
    estimate(g, l);
    div(g, &w, &l.v, l.b, e, A, true);
    sub_wide(g, &l.v, lo, top, A);
    g.cx(e, vt);
    g.cswap(e, top, vt);
    correction_probe(g, l, e);
    g.cswap(e, vt, A);
    g.cx(e, vt);
    sub_wide(g, &l.v, lo, top, B);
    g.cx(top, A);
    g.cx(A, top);
    carry_xor(g, &l.v, &lo[..l.c], top, &cat(&[&[A], &lo[l.c..]]));
    div(g, &w, &l.v, l.b, e, B, false);
    guard_output(g, l, A, e);
}
fn update_mark(g: &mut Gen<'_>, l: &Layout, low: usize, high: usize, e: usize) {
    let w = cat(&[&l.u, &l.q]);
    mcx(g, &[e], &w[l.c + high..], A);
    mcx(g, &[e], &w[l.c + low - 1..], A);
}
fn update(g: &mut Gen<'_>, l: &Layout, e: usize) {
    let w = cat(&[&l.u, &l.q]);
    div(g, &w, &l.v, l.b, e, A, true);
    let maxoff = (l.b - 1).min(if l.cap { 24 } else { 127 });
    let mut low = 0;
    while low <= maxoff {
        let high = maxoff.min((l.b + low - 1) / 2);
        let n = l.c + high;
        let cap = l.r.len() - low;
        let tail = &l.r[cap..];
        let loan = &w[n..127][..high - low];
        let zeros = cat(&[&[B], tail, loan]);
        assert_eq!(zeros.len(), n - l.c + 1);
        let j = cat(&[&range(388, 388 + l.c - 1), &zeros, &l.r[..cap]]);
        let src = &w[..n];
        update_mark(g, l, low, high, e);
        div(g, &j, src, cap, A, w[127], true);
        reflect(g, &j, Some(A));
        div(g, &j, &l.v, j.len() - l.c, A, w[127], false);
        let rem = &j[..l.c];
        let q = &j[l.c..];
        for &p in rem {
            g.cx(A, p);
        }
        nr_adder(g, &l.v, rem, None, Some(A));
        cinc_t(g, A, q);
        permute(g, q, &cat(&[&l.r, loan]), A);
        update_mark(g, l, low, high, e);
        low = high + 1;
    }
}
fn row(g: &mut Gen<'_>, l: &Layout, e: usize) {
    exact_quotient(g, l, e);
    update(g, l, e);
    for i in 0..l.c {
        g.cswap(e, l.u[i], l.v[i]);
    }
    g.cx(e, PAR);
}
fn shape(g: &mut Gen<'_>, l: &Layout, t: usize) {
    mcx(g, &[l.vt()], &l.q, t);
    mcx(g, &[l.vt()], &cat(&[&l.q, &l.r[129..]]), t);
}
fn qualify_two(g: &mut Gen<'_>, l: &Layout) {
    let src = cat(&[&l.u, &l.q[..2]]);
    let vt = l.vt();
    let rt = *l.r.last().unwrap();
    nr_adder(g, &l.v, &src[1..1 + l.c], Some(src[l.c + 1]), None);
    g.cx(E, vt);
    for high in [false, true] {
        let pos = if high { vec![E, rt] } else { vec![E] };
        let neg = if high { vec![] } else { vec![rt] };
        mcx(g, &pos, &neg, B);
        g.cx(B, E);
        let n = l.c + if high { 1 } else { 2 };
        let cap = l.r.len() - if high { 0 } else { 1 };
        let zeros = if high { vec![vt, E] } else { vec![vt, rt, E] };
        let j = cat(&[&range(388, 388 + l.c - 1), &zeros, &l.r[..cap]]);
        assert_eq!(j.len(), 258);
        mixed_mul(g, &j, &src[..n], cap);
        let f = g.capture(|g| reflect(g, &j, None));
        g.play(&f, false);
        g.cx(B, A);
        g.ccx(B, j[j.len() - 1], A);
        g.play(&f, true);
        mixed_div(g, &j, &src[..n], cap);
        g.cx(B, E);
        mcx(g, &pos, &neg, B);
    }
    g.cx(E, vt);
    g.reverse(|g| nr_adder(g, &l.v, &src[1..1 + l.c], Some(src[l.c + 1]), None));
    g.cx(A, E);
    shape(g, l, A);
    g.cx(E, A);
}
// One259-bit trial product; Q[2] is a guarded output, excluded from loans.
// On inactive/ahead inputs it may be dirty and is restored exactly.
fn qualify_one(g: &mut Gen<'_>, l: &Layout) {
    if l.c == 126 {
        qualify_two(g, l);
        return;
    }
    assert!(l.c <= 125);
    let src = cat(&[&l.u, &l.q[..2]]);
    let vt = l.vt();
    let out = l.q[2];
    let old = g.pool.clone();
    g.cx(E, B);
    g.cx(B, E);
    nr_adder(g, &l.v, &src[1..1 + l.c], Some(src[l.c + 1]), None);
    g.cx(B, vt);
    let j = cat(&[&range(388, 388 + l.c - 1), &[A, E, vt], &l.r]);
    assert_eq!(j.len(), 259);
    g.pool.retain(|&q| q != out);
    mixed_mul(g, &j, &src, l.r.len());
    let f = g.capture(|g| reflect(g, &j, None));
    g.play(&f, false);
    g.ccx(B, j[j.len() - 1], out);
    g.play(&f, true);
    mixed_div(g, &j, &src, l.r.len());
    g.pool = old;
    g.ccx(B, out, E);
    g.cx(E, out);
    g.cx(B, vt);
    g.reverse(|g| nr_adder(g, &l.v, &src[1..1 + l.c], Some(src[l.c + 1]), None));
    shape(g, l, B);
}
fn unit(g: &mut Gen<'_>, l: &Layout) {
    let w = cat(&[&l.u, &l.q[..1]]);
    let j = cat(&[&range(388, 388 + l.c - 1), &[A, B], &l.r]);
    let pick = l.bank[127];
    g.add(&l.v, &l.u, A, Some(E), Some(l.q[0]));
    div(g, &j, &w, l.r.len(), E, pick, true);
    reflect(g, &j, Some(E));
    div(g, &j, &l.v, j.len() - l.c, E, pick, false);
    let rem = &j[..l.c];
    let q = &j[l.c..];
    for &p in rem {
        g.cx(E, p);
    }
    nr_adder(g, &l.v, rem, None, Some(E));
    cinc_t(g, E, q);
    permute(g, q, &cat(&[&l.r, &[B]]), E);
    for i in 0..l.c {
        g.cswap(E, l.u[i], l.v[i]);
    }
    g.cx(E, PAR);
    g.cx(l.u[l.c - 1], E);
}
fn forced127(g: &mut Gen<'_>, l: &Layout) {
    nr_adder(g, &l.v, &l.u, None, Some(E));
    let j = cat(&[&range(388, 514), &[A], &l.r]);
    div(g, &j, &l.u, 130, E, B, true);
    reflect(g, &j, Some(E));
    div(g, &j, &l.v, 130, E, B, false);
    let rem = &j[..127];
    for &p in rem {
        g.cx(E, p);
    }
    nr_adder(g, &l.v, rem, None, Some(E));
    cinc_t(g, E, &l.r);
    for i in 0..127 {
        g.cswap(E, l.u[i], l.v[i]);
    }
    g.cx(E, PAR);
    g.cx(l.u[126], E);
}
fn clear_general(g: &mut Gen<'_>, l: &Layout) {
    let w = &l.bank;
    mixed_div(g, w, &l.u, l.b);
    g.cx(l.u[l.c - 1], E);
    mcx(g, &[l.u[l.c - 1]], &cat(&[&[w[l.c - 1]], &w[l.c + 1..]]), E);
    mixed_mul(g, w, &l.u, l.b);
}
fn column_body(g: &mut Gen<'_>, l: &Layout) {
    shape(g, l, E);
    if l.c == 127 {
        forced127(g, l);
        return;
    }
    qualify_one(g, l);
    unit(g, l);
    shape(g, l, E);
    row(g, l, E);
    clear_general(g, l);
}
fn decode(w: u32, map: &[usize; 631], frame: &Frame) -> Op {
    let (a, b, t) = (
        (w >> 20 & 1023) as usize,
        (w >> 10 & 1023) as usize,
        (w & 1023) as usize,
    );
    let mut o = Op::empty();
    o.q_target = frame.own[map[t]];
    if a != 1023 {
        o.kind = K::CCX;
        o.q_control1 = frame.own[map[a]];
        o.q_control2 = frame.own[map[b]];
    } else if b != 1023 {
        o.kind = K::CX;
        o.q_control1 = frame.own[map[b]];
    } else {
        o.kind = K::X;
    }
    o
}
/// Canonical packed NCT callback, used for exhaustive JS word equivalence.
pub fn canonical_column(c: usize, mut emit: impl FnMut(u32)) -> Cost {
    assert!((65..128).contains(&c));
    let l = Layout::new(c);
    let mut g = Gen::new(&mut emit);
    column_body(&mut g, &l);
    g.cost
}
pub fn column(frame: &Frame, ports: &Ports, mut emit: impl FnMut(Op)) -> Cost {
    let map = ports.canonical_map();
    canonical_column(ports.c, |w| emit(decode(w, &map, frame)))
}
fn one(k: K, q: Q) -> Op {
    let mut o = Op::empty();
    o.kind = k;
    o.q_target = q;
    o
}
pub fn prefix(frame: &Frame, mut emit: impl FnMut(Op)) -> Cost {
    emit(one(K::X, frame.own[A]));
    Cost {
        gates: 1,
        ..Cost::default()
    }
}
pub fn terminal(frame: &Frame, ports: &Ports, record: BitId, mut emit: impl FnMut(Op)) -> Cost {
    assert_eq!(ports.c, 128);
    assert_eq!(ports.r, range(0, 129));
    assert_eq!(ports.u.len(), 128);
    assert_eq!(ports.u[127], 129);
    for (i, &q) in ports.u[..127].iter().enumerate() {
        let mut o = one(K::Hmr, frame.own[q]);
        o.c_target = BitId(record.0 + i as u64);
        emit(o);
    }
    for i in 388..452 {
        emit(one(K::X, frame.own[i]));
    }
    Cost {
        gates: 191,
        ..Cost::default()
    }
}
pub fn forward(frame: &Frame, record: BitId, mut emit: impl FnMut(Op)) -> Cost {
    let mut cost = prefix(frame, &mut emit);
    let mut p = Ports::handover();
    for _ in 65..128 {
        let x = column(frame, &p, &mut emit);
        cost.gates += x.gates;
        cost.toffolis += x.toffolis;
        cost.max_capture_words = cost.max_capture_words.max(x.max_capture_words);
        p.advance();
    }
    cost.gates += terminal(frame, &p, record, &mut emit).gates;
    cost
}
