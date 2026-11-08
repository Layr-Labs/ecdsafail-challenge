//! Resynthesize bounded six-wire quadratic Boolean permutations. The
//! nonlinear output forms must have a basis of at most three single
//! products and a verified order of reversible shears. Every emitted
//! replacement independently replays its entire basis truth table.
//! No quantum/classical inputs, measurements or phases are added.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
const MAX: usize = 6;
fn mobius(mut w: u64) -> u64 {
    for (s, m) in [
        (1, 0x5555555555555555),
        (2, 0x3333333333333333),
        (4, 0x0f0f0f0f0f0f0f0f),
        (8, 0x00ff00ff00ff00ff),
        (16, 0x0000ffff0000ffff),
        (32, 0x00000000ffffffff),
    ] {
        w ^= (w & m) << s;
    }
    w
}
const fn degree(d: u32) -> u64 {
    let mut m = 0;
    let mut i = 0u32;
    while i < 64 {
        if i.count_ones() == d {
            m |= 1u64 << i;
        }
        i += 1;
    }
    m
}
const LO: u64 = degree(0) | degree(1);
const QUAD: u64 = degree(2);
#[derive(Clone)]
struct Chart {
    wires: [QubitId; MAX],
    value: [u64; MAX],
    n: usize,
}
impl Chart {
    fn new() -> Self {
        Self {
            wires: [NO_QUBIT; MAX],
            value: [0; MAX],
            n: 0,
        }
    }
    fn idx(&mut self, w: QubitId) -> Option<usize> {
        if let Some(k) = self.wires[..self.n].iter().position(|&q| q == w) {
            return Some(k);
        }
        if self.n == MAX {
            return None;
        }
        let k = self.n;
        self.n += 1;
        self.wires[k] = w;
        self.value[k] = [
            0xaaaaaaaaaaaaaaaa,
            0xcccccccccccccccc,
            0xf0f0f0f0f0f0f0f0,
            0xff00ff00ff00ff00,
            0xffff0000ffff0000,
            0xffffffff00000000,
        ][k];
        Some(k)
    }
    fn step(&mut self, op: Op) -> Option<()> {
        if !matches!(op.kind, K::X | K::CX | K::CCX | K::Swap) || op.c_condition != NO_BIT {
            return None;
        }
        let t = self.idx(op.q_target)?;
        match op.kind {
            K::X => self.value[t] ^= u64::MAX,
            K::CX => {
                let a = self.idx(op.q_control1)?;
                self.value[t] ^= self.value[a];
            }
            K::CCX => {
                let a = self.idx(op.q_control1)?;
                let b = self.idx(op.q_control2)?;
                self.value[t] ^= self.value[a] & self.value[b];
            }
            K::Swap => {
                let a = self.idx(op.q_control1)?;
                self.value.swap(a, t);
            }
            _ => unreachable!(),
        }
        Some(())
    }
}
fn reduce(a: &mut [u64; MAX], n: usize) -> usize {
    let mut rank = 0;
    for i in 0..n {
        let mut v = a[i];
        for j in 0..rank {
            v = v.min(v ^ a[j]);
        }
        if v != 0 {
            a[rank] = v;
            rank += 1;
        }
    }
    rank
}
fn coordinates(v: u64, b: &[u64]) -> Option<u8> {
    for mask in 0usize..1 << b.len() {
        let mut w = 0;
        for (k, &p) in b.iter().enumerate() {
            if mask >> k & 1 != 0 {
                w ^= p
            }
        }
        if w == v {
            return Some(mask as u8);
        }
    }
    None
}
#[derive(Clone, Copy, Default)]
struct Product {
    f: u8,
    g: u8,
    d: u8,
}
fn factor(q: u64, n: usize) -> Option<Product> {
    if q == 0 {
        return None;
    }
    let mon = q.trailing_zeros() as usize;
    let (a, b) = (
        mon.trailing_zeros() as usize,
        (mon & (mon - 1)).trailing_zeros() as usize,
    );
    let read = |i: usize, j: usize| -> u8 {
        if i == j {
            0
        } else {
            ((q >> ((1 << i) | (1 << j))) & 1) as u8
        }
    };
    let (mut f, mut g) = (0u8, 0u8);
    for i in 0..n {
        f |= read(b, i) << i;
        g |= read(a, i) << i;
    }
    for i in 0..n {
        for j in i + 1..n {
            if ((f >> i & g >> j) ^ (f >> j & g >> i)) & 1 != read(i, j) {
                return None;
            }
        }
    }
    Some(Product { f, g, d: 0 })
}
fn inverse(mut rows: [u8; MAX], n: usize) -> Option<[u8; MAX]> {
    let mut out = [0; MAX];
    for i in 0..n {
        out[i] = 1 << i
    }
    for k in 0..n {
        let p = (k..n).find(|&v| rows[v] >> k & 1 != 0)?;
        rows.swap(k, p);
        out.swap(k, p);
        for h in 0..n {
            if h != k && rows[h] >> k & 1 != 0 {
                rows[h] ^= rows[k];
                out[h] ^= out[k];
            }
        }
    }
    Some(out)
}
fn parity(v: u8) -> bool {
    v.count_ones() & 1 != 0
}
#[derive(Clone, Copy)]
struct Plan {
    products: [Product; 3],
    count: usize,
    rows: [u8; MAX],
    constant: u8,
}
fn possible(
    span: &[u64],
    quads: &[u64; MAX],
    base: [u8; MAX],
    constant: u8,
    n: usize,
    forms: &[u64],
    facts: &[Product],
) -> Option<Plan> {
    let k = span.len();
    let mut rows = base;
    let mut prods = [Product::default(); 3];
    for x in 0..k {
        prods[x] = facts[x];
    }
    for i in 0..n {
        let alpha = coordinates(quads[i], forms)?;
        for j in 0..k {
            if alpha >> j & 1 != 0 {
                prods[j].d |= 1 << i;
                rows[i] ^= prods[j].f & prods[j].g;
            }
        }
    }
    let reverse = inverse(rows, n)?;
    for p in &mut prods[..k] {
        let mut direction = 0;
        for i in 0..n {
            if parity(reverse[i] & p.d) {
                direction |= 1 << i;
            }
        }
        p.d = direction;
        if direction == 0 || parity(direction & p.f) || parity(direction & p.g) {
            return None;
        }
    }
    let mut visited = 0;
    let mut order = [Product::default(); 3];
    for j in 0..k {
        let mut found = false;
        for i in 0..k {
            if visited & (1 << i) != 0 {
                continue;
            }
            let p = prods[i];
            let can = (0..k).all(|h| {
                h == i
                    || visited & (1 << h) != 0
                    || (!parity(prods[h].f & p.d) && !parity(prods[h].g & p.d))
            });
            if can {
                visited |= 1 << i;
                order[j] = p;
                found = true;
                break;
            }
        }
        if !found {
            return None;
        }
    }
    Some(Plan {
        products: order,
        count: k,
        rows,
        constant,
    })
}
fn classify(chart: &Chart, charged: usize) -> Option<Plan> {
    let n = chart.n;
    let mut q = [0; MAX];
    let mut base = [0u8; MAX];
    let mut c = 0u8;
    let mut pure = true;
    for i in 0..n {
        let w = mobius(chart.value[i]);
        q[i] = w & !LO;
        pure &= q[i] & !QUAD == 0;
        c |= ((w & 1) as u8) << i;
        for j in 0..n {
            base[i] |= (((w >> (1 << j)) & 1) as u8) << j;
        }
    }
    let mut basis = q;
    let rank = reduce(&mut basis, n);
    if rank >= charged {
        return None;
    }
    if !pure || rank > 3 {
        return None;
    }
    if rank == 0 {
        return if inverse(base, n).is_some() {
            Some(Plan {
                products: [Product::default(); 3],
                count: 0,
                rows: base,
                constant: c,
            })
        } else {
            None
        };
    }
    let span = &basis[..rank];
    let mut qs = [0u64; 7];
    let mut fs = [Product::default(); 7];
    let mut count = 0;
    for subset in 1..1 << rank {
        let mut w = 0;
        for (i, &z) in span.iter().enumerate() {
            if subset >> i & 1 != 0 {
                w ^= z
            }
        }
        if let Some(f) = factor(w, n) {
            qs[count] = w;
            fs[count] = f;
            count += 1;
        }
    }
    if count < rank {
        return None;
    }
    for i in 0..count {
        if rank == 1 {
            if let Some(p) = possible(span, &q, base, c, n, &[qs[i]], &[fs[i]]) {
                return Some(p);
            }
        } else {
            for j in i + 1..count {
                if rank == 2 {
                    if let Some(p) =
                        possible(span, &q, base, c, n, &[qs[i], qs[j]], &[fs[i], fs[j]])
                    {
                        return Some(p);
                    }
                } else {
                    for l in j + 1..count {
                        if qs[i] ^ qs[j] == qs[l] {
                            continue;
                        }
                        if let Some(p) = possible(
                            span,
                            &q,
                            base,
                            c,
                            n,
                            &[qs[i], qs[j], qs[l]],
                            &[fs[i], fs[j], fs[l]],
                        ) {
                            return Some(p);
                        }
                    }
                }
            }
        }
    }
    None
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Small {
    X(u8),
    CX(u8, u8),
    Swap(u8, u8),
    CCX(u8, u8, u8),
}
fn instructions_for(rows: [u8; MAX], constant: u8, n: usize, out: &mut Vec<Small>) {
    let mut r = rows;
    let start = out.len();
    for i in 0..n {
        let j = (i..n)
            .find(|&j| r[j] >> i & 1 != 0)
            .expect("nonsingular linear layer");
        if j != i {
            r.swap(i, j);
            out.push(Small::Swap(i as u8, j as u8));
        }
        for j in 0..n {
            if j != i && r[j] >> i & 1 != 0 {
                r[j] ^= r[i];
                out.push(Small::CX(i as u8, j as u8));
            }
        }
    }
    out[start..].reverse();
    for i in 0..n {
        if constant >> i & 1 != 0 {
            out.push(Small::X(i as u8));
        }
    }
}
fn basis_pair(g: Product, k: usize, n: usize) -> Option<(usize, usize, u8, u8)> {
    let f = g.f & !(1 << k);
    let h = g.g & !(1 << k);
    let mut best = None;
    let mut score = usize::MAX;
    for i in 0..n {
        for j in 0..n {
            if i == j || i == k || j == k {
                continue;
            }
            let a = (f >> i & 1) | ((f >> j & 1) << 1);
            let b = (h >> i & 1) | ((h >> j & 1) << 1);
            if a == 0 || b == 0 || a == b {
                continue;
            }
            let core = match (a, b) {
                (1, 2) => 0,
                (2, 1) | (1, 3) | (3, 2) => 1,
                _ => 2,
            };
            let external = (f & !((1 << i) | (1 << j))).count_ones()
                + (h & !((1 << i) | (1 << j))).count_ones();
            let cost = core + external as usize;
            if cost < score {
                score = cost;
                best = Some((i, j, a, b));
            }
        }
    }
    best
}
fn product(p: Product, n: usize, out: &mut Vec<Small>) {
    let k = p.d.trailing_zeros() as usize;
    assert!(k < n);
    let start = out.len();
    for i in 0..n {
        if i != k && p.d >> i & 1 != 0 {
            out.push(Small::CX(k as u8, i as u8));
        }
    }
    let (i, j, a, b) = basis_pair(p, k, n).expect("two independent controls");
    let (ui, uj) = (i as u8, j as u8);
    match (a, b) {
        (1, 2) => {}
        (2, 1) => out.push(Small::Swap(ui, uj)),
        (1, 3) => out.push(Small::CX(ui, uj)),
        (3, 2) => out.push(Small::CX(uj, ui)),
        (2, 3) => out.extend_from_slice(&[Small::Swap(ui, uj), Small::CX(ui, uj)]),
        (3, 1) => out.extend_from_slice(&[Small::Swap(ui, uj), Small::CX(uj, ui)]),
        _ => unreachable!(),
    }
    for h in 0..n {
        if h == i || h == j || h == k {
            continue;
        }
        if p.f >> h & 1 != 0 {
            out.push(Small::CX(h as u8, ui));
        }
        if p.g >> h & 1 != 0 {
            out.push(Small::CX(h as u8, uj));
        }
    }
    let end = out.len();
    out.push(Small::CCX(ui, uj, k as u8));
    for j in (start..end).rev() {
        out.push(out[j]);
    }
}
fn simplify_linear(src: &[Small], n: usize, scratch: &mut Vec<Small>, out: &mut Vec<Small>) {
    let mut i = 0;
    while i < src.len() {
        if let Small::CCX(_, _, _) = src[i] {
            out.push(src[i]);
            i += 1;
            continue;
        }
        let begin = i;
        let mut rows = [0u8; MAX];
        for i in 0..n {
            rows[i] = 1 << i;
        }
        let mut offsets = 0u8;
        while i < src.len() {
            match src[i] {
                Small::X(t) => offsets ^= 1 << t,
                Small::CX(a, b) => {
                    rows[b as usize] ^= rows[a as usize];
                    offsets ^= ((offsets >> a) & 1) << b;
                }
                Small::Swap(a, b) => {
                    rows.swap(a as usize, b as usize);
                    let d = (offsets >> a ^ offsets >> b) & 1;
                    offsets ^= (d << a) | (d << b);
                }
                Small::CCX(_, _, _) => break,
            }
            i += 1;
        }
        scratch.clear();
        instructions_for(rows, offsets, n, scratch);
        if scratch.len() <= i - begin {
            out.extend_from_slice(scratch);
        } else {
            out.extend_from_slice(&src[begin..i]);
        }
    }
}
fn native(g: Small, w: &[QubitId; MAX]) -> Op {
    match g {
        Small::X(t) => Op {
            kind: K::X,
            q_target: w[t as usize],
            ..Op::empty()
        },
        Small::CX(a, t) => Op {
            kind: K::CX,
            q_control1: w[a as usize],
            q_target: w[t as usize],
            ..Op::empty()
        },
        Small::Swap(a, t) => Op {
            kind: K::Swap,
            q_control1: w[a as usize],
            q_target: w[t as usize],
            ..Op::empty()
        },
        Small::CCX(a, b, t) => Op {
            kind: K::CCX,
            q_control1: w[a as usize],
            q_control2: w[b as usize],
            q_target: w[t as usize],
            ..Op::empty()
        },
    }
}
struct Synthesis {
    raw: Vec<Small>,
    simple: Vec<Small>,
    scratch: Vec<Small>,
    native: Vec<Op>,
    best: Vec<Op>,
}
impl Synthesis {
    fn new() -> Self {
        Self {
            raw: Vec::with_capacity(150),
            simple: Vec::with_capacity(150),
            scratch: Vec::with_capacity(64),
            native: Vec::with_capacity(150),
            best: Vec::with_capacity(150),
        }
    }
    fn realize(&mut self, chart: &Chart, p: &Plan) {
        self.raw.clear();
        for &g in &p.products[..p.count] {
            product(g, chart.n, &mut self.raw);
        }
        instructions_for(p.rows, p.constant, chart.n, &mut self.raw);
        self.simple.clear();
        simplify_linear(&self.raw, chart.n, &mut self.scratch, &mut self.simple);
        self.native.clear();
        for &small in &self.simple {
            self.native.push(native(small, &chart.wires));
        }
        // Independent complete truth-table re-simulation for every proposed
        // physical replacement. Each six-variable truth table fits one word.
        let mut proof = Chart::new();
        for &w in &chart.wires[..chart.n] {
            proof.idx(w).unwrap();
        }
        for &g in &self.native {
            proof
                .step(g)
                .expect("native replacement outside local wires");
        }
        assert!(
            proof.value[..proof.n] == chart.value[..chart.n],
            "multi-output replacement disagrees with original truth table"
        );
    }
}

#[path = "cubic_branch.rs"]
mod cubic_branch;

pub(super) fn apply_joint(ops: &mut Vec<Op>) -> cubic_branch::Joint {
    cubic_branch::joint(ops)
}
