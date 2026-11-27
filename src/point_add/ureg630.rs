//! Regenerate U across the rank-119 mixed-radix carrier.
use super::{post_pass::{run_chunk, Step}, Row};
use std::collections::{BTreeSet, HashMap};

const NIL: u16 = u16::MAX;
const N: usize = 127;
const MIN: usize = 119;
const PREFIX: usize = 18;

fn x(g: &mut Vec<Row>, t: u16) {
    g.push([6, t, NIL, NIL]);
}

fn cx(g: &mut Vec<Row>, a: u16, t: u16) {
    g.push([8, a, t, NIL]);
}

fn ccx(g: &mut Vec<Row>, a: u16, b: u16, t: u16) {
    g.push([13, a, b, t]);
}

fn flip(g: &mut Vec<Row>, word: &[u16]) {
    for &q in word { x(g, q); }
}

fn append(g: &mut Vec<Row>, gates: &[Row], inverse: bool) {
    if inverse {
        g.extend(gates.iter().rev());
    } else {
        g.extend_from_slice(gates);
    }
}

pub(super) fn multi(g: &mut Vec<Row>, c: &[u16], t: u16, start: u16, pin: u16) {
    match c {
        [] => x(g, t),
        [a] => cx(g, *a, t),
        [a, b] => ccx(g, *a, *b, t),
        _ => {
            let ds: Vec<_> = (start..631).chain(0..start)
                .filter(|&q| q != t && q != pin && !c.contains(&q))
                .take(c.len() - 2).collect();
            assert_eq!(ds.len(), c.len() - 2);
            for _ in 0..2 {
                ccx(g, *c.last().unwrap(), *ds.last().unwrap(), t);
                for j in (1..ds.len()).rev() {
                    ccx(g, c[j + 1], ds[j - 1], ds[j]);
                }
                ccx(g, c[0], c[1], ds[0]);
                for j in 1..ds.len() {
                    ccx(g, c[j + 1], ds[j - 1], ds[j]);
                }
            }
        }
    }
}

fn maj(g: &mut Vec<Row>, a: u16, b: u16, c: u16) {
    cx(g, a, b);
    cx(g, a, c);
    ccx(g, c, b, a);
}

fn unmaj(g: &mut Vec<Row>, a: u16, b: u16, c: u16) {
    ccx(g, c, b, a);
    cx(g, a, c);
    cx(g, a, b);
}

fn fold(ports: &[i16], select: u16, carry: u16, inverse: bool) -> Vec<Row> {
    let v: Vec<_> = ports.iter().map(|&q| if q < 0 { (-1 - q) as u16 } else { q as u16 }).collect();
    let negative: Vec<_> = ports.iter().zip(&v).filter_map(|(&q, &port)| (q < 0).then_some(port)).collect();
    let w: Vec<u16> = (129..256).chain([127, 128, 512]).collect();
    assert_eq!(v.len(), N);
    let mut g = Vec::new();
    flip(&mut g, &negative);
    for width in 108..=N {
        let mut mark = Vec::new();
        flip(&mut mark, &v[width..]);
        multi(&mut mark, &v[width - 1..], select, 256, NIL);
        flip(&mut mark, &v[width..]);
        g.extend_from_slice(&mark);
        for off in 0..w.len() - width {
            let flag = w[off + width];
            let z = |i: usize| if i == 0 { carry } else { v[i - 1] };
            for i in 0..width { maj(&mut g, v[i], w[off + i], z(i)); }
            for i in (0..width).rev() {
                let y = w[off + i];
                unmaj(&mut g, v[i], y, z(i));
                cx(&mut g, v[i], z(i));
                multi(&mut g, &[select, flag, z(i)], y, 256, NIL);
                cx(&mut g, v[i], z(i));
            }
            flip(&mut g, &w[off..off + width]);
            for i in 0..width { maj(&mut g, v[i], w[off + i], z(i)); }
            cx(&mut g, select, flag);
            ccx(&mut g, select, v[width - 1], flag);
            for i in (0..width).rev() { unmaj(&mut g, v[i], w[off + i], z(i)); }
            flip(&mut g, &w[off..off + width]);
        }
        g.extend_from_slice(&mark);
    }
    flip(&mut g, &negative);
    cx(&mut g, 130, 512);
    cx(&mut g, 512, 130);
    cx(&mut g, 130, 512);
    if inverse { g.reverse(); }
    g
}

struct Recovery {
    v: Vec<u16>,
    pin: u16,
    result: u16,
    guard: u16,
    saved: u16,
    f: u16,
    carry: u16,
}

impl Recovery {
    fn multi(&self, g: &mut Vec<Row>, c: &[u16], t: u16) {
        multi(g, c, t, 385, self.pin);
    }

    fn swap(&self, g: &mut Vec<Row>, c: &[u16], a: u16, b: u16) {
        cx(g, a, b);
        let mut controls = c.to_vec();
        controls.push(b);
        self.multi(g, &controls, a);
        cx(g, a, b);
    }

    fn add(&self, a: &[u16], b: &[u16], ctrl: Option<u16>) -> Vec<Row> {
        assert_eq!(a.len(), b.len());
        let mut g = Vec::with_capacity(a.len() * 9);
        let z = |i: usize| if i == 0 { self.carry } else { a[i - 1] };
        for i in 0..a.len() { maj(&mut g, a[i], b[i], z(i)); }
        for i in (0..a.len()).rev() {
            let c = z(i);
            unmaj(&mut g, a[i], b[i], c);
            if let Some(control) = ctrl {
                cx(&mut g, a[i], c);
                ccx(&mut g, control, c, b[i]);
                cx(&mut g, a[i], c);
            } else {
                cx(&mut g, a[i], b[i]);
                cx(&mut g, c, b[i]);
            }
        }
        g
    }

    fn greater(&self, g: &mut Vec<Row>, a: &[u16], b: &[u16], t: u16, ctrl: Option<u16>) {
        assert_eq!(a.len(), b.len());
        let mut half = Vec::with_capacity(a.len() * 4);
        flip(&mut half, b);
        for i in 0..a.len() {
            maj(&mut half, a[i], b[i], if i == 0 { self.carry } else { a[i - 1] });
        }
        g.extend_from_slice(&half);
        if let Some(control) = ctrl {
            ccx(g, control, a[a.len() - 1], t);
        } else {
            cx(g, a[a.len() - 1], t);
        }
        append(g, &half, true);
    }

    fn half_mod(&self, d: &[u16]) -> Vec<Row> {
        let mut g = Vec::new();
        let mut m = self.v.clone();
        m.rotate_left(1);
        cx(&mut g, d[0], self.f);
        for pair in d.windows(2) { self.swap(&mut g, &[], pair[0], pair[1]); }
        cx(&mut g, self.f, d[N - 1]);
        flip(&mut g, &m[..N - 1]);
        append(&mut g, &self.add(&m, d, Some(self.f)), true);
        flip(&mut g, &m[..N - 1]);
        x(&mut g, self.v[0]);
        self.greater(&mut g, d, &m, self.f, None);
        x(&mut g, self.v[0]);
        g
    }

    fn mod_add(&self, d: &[u16], u: &[u16], ctrl: u16) -> Vec<Row> {
        let mut g = Vec::new();
        let vu = self.add(u, &self.v, None);
        append(&mut g, &vu, true);
        cx(&mut g, ctrl, self.f);
        self.greater(&mut g, &self.v, d, self.f, Some(ctrl));
        g.extend(vu);
        append(&mut g, &self.add(&self.v, d, Some(self.f)), true);
        g.extend(self.add(u, d, Some(ctrl)));
        self.greater(&mut g, u, d, self.f, Some(ctrl));
        g
    }

    fn increment(&self, d: &[u16]) -> Vec<Row> {
        let mut g = Vec::new();
        for i in (0..N).rev() { self.multi(&mut g, &d[..i], d[i]); }
        for (&v, &target) in self.v.iter().zip(d) { cx(&mut g, v, target); }
        flip(&mut g, d);
        self.multi(&mut g, d, self.f);
        flip(&mut g, d);
        for (&v, &target) in self.v.iter().zip(d) { cx(&mut g, v, target); }
        for (&v, &target) in self.v.iter().zip(d) { ccx(&mut g, self.f, v, target); }
        flip(&mut g, d);
        self.multi(&mut g, d, self.f);
        flip(&mut g, d);
        g
    }

    fn high_swap(&self, g: &mut Vec<Row>, i: usize, a: u16, b: u16) {
        let high = &self.v[i..];
        flip(g, high);
        self.swap(g, high, a, b);
        flip(g, high);
    }

    fn fingerprint(&self, g: &mut Vec<Row>, r: &[u16], d: &[u16]) {
        cx(g, d[0], r[127]);
        let mut mask = Vec::new();
        for (i, &q) in r.iter().enumerate().take(N).skip(1) { ccx(&mut mask, r[0], self.v[i], q); }
        g.extend_from_slice(&mask);
        for i in 1..N {
            let mut controls = r[1..=i].to_vec();
            controls.push(d[i]);
            self.multi(g, &controls, r[128]);
            x(g, r[i]);
        }
        flip(g, &r[1..N]);
        append(g, &mask, true);
    }

    fn quotient_bit(&self, k: usize) -> Vec<Row> {
        let mut sum = vec![0u32; (1 << PREFIX) + 1];
        let shift = N - PREFIX;
        for i in (1 << (MIN - shift))..(1 << PREFIX) {
            let quotient = (1 << (129 - shift)) / i;
            sum[i + 1] = sum[i] + ((quotient >> k) & 1) as u32;
        }
        fn visit(rec: &Recovery, g: &mut Vec<Row>, sums: &[u32], a: usize, b: usize, depth: usize) {
            let n = (sums[b] - sums[a]) as usize;
            if n == 0 { return; }
            if n == b - a {
                let controls: Vec<_> = rec.v.iter().rev().take(depth).copied().collect();
                let negative: Vec<_> = controls.iter().enumerate().filter_map(|(i, &q)|
                    ((a >> (PREFIX - 1 - i)) & 1 == 0).then_some(q)).collect();
                flip(g, &negative);
                rec.multi(g, &controls, rec.guard);
                flip(g, &negative);
                return;
            }
            let mid = (a + b) / 2;
            visit(rec, g, sums, a, mid, depth + 1);
            visit(rec, g, sums, mid, b, depth + 1);
        }
        let mut g = Vec::new();
        visit(self, &mut g, &sum, 0, 1 << PREFIX, 0);
        g
    }

    fn plus_shift(&self, dst: &[u16], k: usize, ctrl: u16) -> Vec<Row> {
        let mut g = Vec::new();
        let m = N.min(dst.len() - k);
        let (a, b) = (&self.v[..m], &dst[k..k + m]);
        if k + m < dst.len() {
            let mut half = Vec::new();
            for i in 0..m {
                maj(&mut half, a[i], b[i], if i == 0 { self.carry } else { a[i - 1] });
            }
            g.extend_from_slice(&half);
            for i in (k + m..dst.len()).rev() {
                let mut controls = vec![ctrl, a[m - 1]];
                controls.extend_from_slice(&dst[k + m..i]);
                self.multi(&mut g, &controls, dst[i]);
            }
            append(&mut g, &half, true);
        }
        g.extend(self.add(a, b, Some(ctrl)));
        g
    }

    fn supported(&self, g: &mut Vec<Row>, target: u16, extra: &[u16]) {
        let mut controls = extra.to_vec();
        controls.push(self.v[0]);
        self.multi(g, &controls, target);
        let high = &self.v[MIN..];
        flip(g, high);
        controls.extend_from_slice(high);
        self.multi(g, &controls, target);
        flip(g, high);
    }

    fn eligibility(&self, g: &mut Vec<Row>, r: &[u16]) {
        self.greater(g, &self.v, &r[..N], self.f, None);
        x(g, r[127]);
        x(g, r[128]);
        self.supported(g, self.guard, &[self.f, r[127], r[128]]);
        x(g, r[128]);
        x(g, r[127]);
        self.greater(g, &self.v, &r[..N], self.f, None);
    }

    fn selected(&self, g: &mut Vec<Row>, k: usize, r: &[u16], u: &[u16], conditional: bool, reverse: bool) {
        let sel = self.quotient_bit(k);
        g.extend_from_slice(&sel);
        let active = if conditional {
            ccx(g, self.guard, self.result, self.f);
            self.f
        } else { self.guard };
        append(g, &self.plus_shift(r, k, active), reverse);
        append(g, &self.plus_shift(u, k, active), !reverse);
        if conditional { ccx(g, self.guard, self.result, self.f); }
        append(g, &sel, true);
    }

    fn kernel(&self) -> Vec<Row> {
        let mut r: Vec<u16> = (0..129).collect();
        let mut u: Vec<u16> = (129..256).collect();
        let d: Vec<u16> = (256..383).collect();
        let mut g = Vec::new();
        let mut oracle = Vec::new();
        self.eligibility(&mut g, &r);
        for i in MIN + 1..N { self.high_swap(&mut oracle, i, r[i], d[i]); }
        for (i, &q) in d.iter().enumerate().skip(MIN) {
            let high = &self.v[i + 1..];
            flip(&mut oracle, high);
            let mut controls = high.to_vec();
            controls.push(self.v[i]);
            self.swap(&mut oracle, &controls, q, self.saved);
            flip(&mut oracle, high);
        }
        self.fingerprint(&mut oracle, &r, &d);
        let half = self.half_mod(&d);
        let increment = self.increment(&d);
        for _ in 0..N { oracle.extend_from_slice(&half); }
        append(&mut oracle, &increment, true);
        for i in (0..256).rev() {
            append(&mut oracle, &half, true);
            if i < N {
                if i > MIN { self.high_swap(&mut oracle, i, r[i], d[i]); }
                oracle.extend(self.mod_add(&d, &u, r[i]));
                if i > MIN { self.high_swap(&mut oracle, i, r[i], d[i]); }
            }
            if i == 32 || (i < 10 && (977 >> i) & 1 != 0) { oracle.extend_from_slice(&increment); }
        }
        for _ in 0..129 { oracle.extend_from_slice(&half); }
        self.fingerprint(&mut oracle, &r, &d);
        g.extend_from_slice(&oracle);
        cx(&mut g, self.guard, self.result);
        x(&mut g, r[127]);
        x(&mut g, r[128]);
        self.multi(&mut g, &[self.guard, r[127], r[128]], self.result);
        x(&mut g, r[128]);
        x(&mut g, r[127]);
        append(&mut g, &oracle, true);
        self.eligibility(&mut g, &r);
        g.push([7, self.result, 64000, NIL]);
        for k in 0..=129 - MIN { self.selected(&mut g, k, &r, &u, true, false); }
        r.push(self.saved);
        u.push(self.f);
        let mut marker = Vec::new();
        for k in 0..=129 - MIN { self.selected(&mut marker, k, &r, &u, false, true); }
        g.extend_from_slice(&marker);
        x(&mut g, self.saved);
        x(&mut g, self.f);
        self.supported(&mut g, self.result, &[self.saved, self.f]);
        x(&mut g, self.f);
        x(&mut g, self.saved);
        append(&mut g, &marker, true);
        g.push([4, 64000, NIL, NIL]);
        g
    }
}

fn arity(kind: u16) -> usize {
    match kind { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 }
}

fn cancel(rows: &mut Vec<Row>) {
    loop {
        let mut write = [-1isize; 631];
        let mut read = [-1isize; 631];
        let mut last = HashMap::new();
        let mut removed = false;
        for i in 0..rows.len() {
            let [k, p, q, _] = rows[i];
            let n = arity(k);
            let t = rows[i][n] as usize;
            let (a, b) = (if n > 1 { p } else { 1023 }, if n > 2 { q } else { 1023 });
            let key = ((t as u32) << 20) | (u32::from(a.min(b)) << 10) | u32::from(a.max(b));
            let mut limit = read[t];
            for &c in &rows[i][1..n] { limit = limit.max(write[c as usize]); }
            if let Some(&previous) = last.get(&key) {
                if previous >= limit {
                    rows[previous as usize][0] = 0;
                    rows[i][0] = 0;
                    last.remove(&key);
                    removed = true;
                    continue;
                }
            }
            last.insert(key, i as isize);
            write[t] = i as isize;
            for &c in &rows[i][1..n] { read[c as usize] = i as isize; }
        }
        if !removed { break; }
        rows.retain(|r| r[0] != 0);
    }
}

fn optimize(rows: &[Row], run_donor: bool) -> Vec<Row> {
    let mut out = Vec::with_capacity(rows.len());
    let mut start = 0;
    for end in rows.iter().enumerate().filter_map(|(i, r)|
        (!matches!(r[0], 6 | 8 | 13)).then_some(i)).chain([rows.len()])
    {
        if end > start {
            let unitary = &rows[start..end];
            let mut rewritten = if run_donor { donor(unitary) } else { unitary.to_vec() };
            cancel(&mut rewritten);
            out.extend(rewritten);
        }
        if end < rows.len() { out.push(rows[end]); }
        start = end + 1;
    }
    out
}

pub(super) fn donor(rows: &[Row]) -> Vec<Row> {
    let mut out = Vec::with_capacity(rows.len());
    let mut allowed = [false; 631];
    for chunk in rows.chunks(750_000) {
        for r in chunk {
            for &q in &r[1..=arity(r[0])] { allowed[q as usize] = true; }
        }
        let ops = run_chunk(chunk.to_vec(), &[Step::Rgp, Step::Schn, Step::Swp, Step::Gm, Step::Q23]);
        if ops.iter().any(|r| r[1..=arity(r[0])].iter().any(|&q| !allowed[q as usize])) {
            return rows.to_vec();
        }
        out.extend(ops);
    }
    out
}

fn remap(g: &mut Vec<Row>, input: &[Row], routes: &str) {
    let mut data = routes.split_whitespace().map(|t| t.parse::<usize>().unwrap());
    let pin = data.next().unwrap();
    let mut state = Frame::new(pin);
    let mut next = data.next();
    for (pos, &r) in input.iter().enumerate() {
        if next == Some(pos) {
            let to = data.next().unwrap();
            let predictor = data.next().unwrap();
            let inverted = data.next().unwrap() == 1;
            state.change(g, to, predictor, inverted);
            next = data.next();
        }
        state.row(g, r);
    }
    assert!(next.is_none() && state.spoiled.is_empty());
    state.close(g);
}

pub(super) struct Frame {
    pin: usize,
    pub(super) hole: usize,
    predictor: usize,
    inverted: bool,
    pub(super) place: [u16; 631],
    scopes: Vec<u16>,
    spoiled: BTreeSet<u16>,
}

impl Frame {
    pub(super) fn new(pin: usize) -> Self {
        Self { pin, hole: pin, predictor: 631, inverted: false,
               place: std::array::from_fn(|q| q as u16),
               scopes: vec![768], spoiled: BTreeSet::new() }
    }

    fn pause(&self, g: &mut Vec<Row>) {
        g.extend(std::iter::repeat([16, NIL, NIL, NIL]).take(self.scopes.len()));
    }

    fn resume(&self, g: &mut Vec<Row>) {
        g.extend(self.scopes.iter().map(|&bit| [15, bit, NIL, NIL]));
    }

    pub(super) fn change(&mut self, g: &mut Vec<Row>, to: usize, predictor: usize, inverted: bool) {
        assert!(to != self.hole && self.place[self.hole] as usize == self.pin);
        let mut toggles = Vec::new();
        if self.inverted != inverted { toggles.push(NIL); }
        if predictor != self.predictor {
            if predictor < 631 {
                assert!(predictor != self.hole && predictor != to);
                toggles.push(self.place[predictor]);
            }
            if self.predictor < 631 && self.predictor != to {
                toggles.push(self.place[self.predictor]);
            }
        }
        if !toggles.is_empty() {
            assert!(self.spoiled.is_empty());
            self.pause(g);
            for a in toggles {
                if a == NIL { x(g, self.place[to]); }
                else { cx(g, a, self.place[to]); }
            }
            self.resume(g);
        }
        self.place.swap(self.hole, to);
        self.hole = to;
        self.predictor = predictor;
        self.inverted = inverted;
    }

    pub(super) fn row(&mut self, g: &mut Vec<Row>, mut r: Row) {
        match r[0] {
            15 => self.scopes.push(r[1]),
            16 => {
                let bit = self.scopes.pop().unwrap();
                if !self.scopes.contains(&bit) { self.spoiled.remove(&bit); }
            }
            3..=5 | 12 => {
                let bit = r[if r[0] == 12 { 2 } else { 1 }];
                if self.scopes.contains(&bit) { self.spoiled.insert(bit); }
            }
            2 => panic!("register inside U stage"),
            _ => {}
        }
        let n = arity(r[0]);
        for q in &mut r[1..1 + n] {
            assert!(usize::from(*q) != self.hole && usize::from(*q) != self.predictor);
            *q = self.place[*q as usize];
        }
        g.push(r);
    }

    pub(super) fn close(mut self, g: &mut Vec<Row>) {
        assert!(self.spoiled.is_empty());
        if self.hole != self.pin { self.change(g, self.pin, 631, false); }
        self.pause(g);
        for q in 0..631u16 {
            while self.place[q as usize] != q {
                let a = self.place[q as usize];
                assert!(a as usize != self.pin && q as usize != self.pin);
                cx(g, a, q);
                cx(g, q, a);
                cx(g, a, q);
                let i = self.place.iter().position(|p| *p == q).unwrap();
                self.place.swap(i, q as usize);
            }
        }
        self.resume(g);
    }

    pub(super) fn emit_unscoped(&self, g: &mut Vec<Row>, rows: &[Row]) {
        assert!(self.spoiled.is_empty());
        self.pause(g);
        g.extend_from_slice(rows);
        self.resume(g);
    }
}

#[path = "ureg630_data.rs"]
mod ureg630_data;

fn extract_flag(port: i16) -> Vec<Row> {
    let q = if port < 0 { (-1 - port) as u16 } else { port as u16 };
    let mut gates = Vec::with_capacity(7);
    if port >= 0 { x(&mut gates, q); }
    x(&mut gates, 129);
    cx(&mut gates, 130, 129);
    ccx(&mut gates, q, 129, 130);
    cx(&mut gates, 130, 129);
    x(&mut gates, 129);
    if port >= 0 { x(&mut gates, q); }
    gates
}

fn kernel(ports: &[u16], zeros: [u16; 6]) -> Vec<Row> {
    let [pin, result, guard, saved, f, carry] = zeros;
    let recovery = Recovery { v: ports.to_vec(), pin, result, guard, saved, f, carry };
    recovery.kernel()
}

pub fn check_kernel(name: &str, compact: bool) -> Vec<Row> {
    let (_, _, _, _, ports, zeros, _, _, _) = ureg630_data::config(name);
    let rows = kernel(ports, zeros);
    if compact { optimize(&rows, true) } else { rows }
}

pub fn generate(name: &str, parent: Vec<Row>) -> Vec<Row> {
    let (lo, hi, en, ex, ports, zeros, v, w, routes) = ureg630_data::config(name);
    let mut input = Vec::with_capacity(parent.len() + 6_000_000);
    input.extend_from_slice(&parent[..lo]);
    input.extend(optimize(&fold(v, en[0], en[1], false), true));
    input.extend(extract_flag(v[0]));
    input.push([12, 130, 64000, NIL]);
    input.extend_from_slice(&parent[lo..hi]);
    input.extend(extract_flag(w[0]).into_iter().rev());
    input.extend(optimize(&fold(w, ex[0], ex[1], true), true));
    input.extend_from_slice(&parent[hi..]);
    drop(parent);
    input.extend(optimize(&kernel(ports, zeros), true));
    let mut routed = Vec::with_capacity(input.len() + 4096);
    remap(&mut routed, &input, routes);
    drop(input);
    optimize(&routed, false)
}
