//! Share a Toffoli across an invertible affine circuit, without allocating wires.
pub type Row = [u16; 4];
const NONE: u16 = u16::MAX;
const GAP: usize = 12;
const SITES: usize = 2 * GAP + 6;
fn cx(a: u16, b: u16) -> Row {
    [8, a, b, NONE]
}
fn x(t: u16) -> Row {
    [6, t, NONE, NONE]
}
fn ccx(a: u16, b: u16, t: u16) -> Row {
    [13, a, b, t]
}

#[derive(Default)]
pub struct Metrics {
    pub pairs: u64,
    pub cancelled: u64,
    pub factored: u64,
    pub distributed: u64,
}

struct Sites {
    names: [u16; SITES],
    count: usize,
}
impl Sites {
    fn new() -> Self {
        Self {
            names: [0; SITES],
            count: 0,
        }
    }
    fn mask(&mut self, name: u16) -> u32 {
        for i in 0..self.count {
            if self.names[i] == name {
                return 1 << i;
            }
        }
        self.names[self.count] = name;
        self.count += 1;
        1 << (self.count - 1)
    }
    fn name(&self, bit: u32) -> u16 {
        self.names[bit.trailing_zeros() as usize]
    }
}

fn bits(mut mask: u32, mut call: impl FnMut(u32)) {
    while mask != 0 {
        let bit = mask & mask.wrapping_neg();
        call(bit);
        mask ^= bit;
    }
}

fn affine_update(
    s: &Sites,
    destinations: u32,
    controls: u32,
    flip: bool,
    emit: &mut impl FnMut(Row),
) {
    debug_assert_eq!(destinations & controls, 0);
    bits(destinations, |dst| {
        if flip {
            emit(x(s.name(dst)));
        }
        bits(controls, |src| emit(cx(s.name(src), s.name(dst))));
    });
}

fn parity_product(
    s: &Sites,
    mut a: u32,
    mut b: u32,
    dst: u32,
    mut linear: u32,
    emit: &mut impl FnMut(Row),
) {
    debug_assert_eq!((a | b | linear) & dst, 0);
    if a == b {
        linear ^= a;
        b = 0;
    }
    if a != 0 && b != 0 {
        // When one support contains the other, adding the smaller form to the
        // larger gives exclusive pivots. A*A=A compensates the changed product.
        if a & !b == 0 {
            linear ^= a;
            b ^= a;
        } else if b & !a == 0 {
            linear ^= b;
            a ^= b;
        }
        let p = 1 << (a & !b).trailing_zeros();
        let q = 1 << (b & !a).trailing_zeros();
        let prepare = |o: &mut dyn FnMut(Row)| {
            bits(a ^ p, |r| o(cx(s.name(r), s.name(p))));
            bits(b ^ q, |r| o(cx(s.name(r), s.name(q))));
        };
        prepare(emit);
        emit(ccx(s.name(p), s.name(q), s.name(dst)));
        prepare(emit); // All preparatory CNOTs commute.
    }
    affine_update(s, dst, linear, false, emit);
}

fn distribute(s: &Sites, dst: u32, a: u32, b: u32, emit: &mut impl FnMut(Row)) {
    if dst == 0 {
        return;
    }
    debug_assert_eq!(dst & (a | b), 0);
    let pivot = dst & dst.wrapping_neg();
    let fan = |o: &mut dyn FnMut(Row)| bits(dst ^ pivot, |d| o(cx(s.name(pivot), s.name(d))));
    fan(emit);
    emit(ccx(s.name(a), s.name(b), s.name(pivot)));
    fan(emit);
}

// On crossing the affine gates the first CCX becomes x += d*(u.x+f)*(v.x+g).
// The second is x += t*(a.x)*(b.x), where a,b,t are distinct unit vectors.
fn combine(
    first: Row,
    gap: &[Row],
    second: Row,
    metrics: &mut Metrics,
    output: &mut Vec<Row>,
) -> bool {
    let mut sites = Sites::new();
    let mut u = sites.mask(first[1]);
    let mut v = sites.mask(first[2]);
    let mut d = sites.mask(first[3]);
    let a = sites.mask(second[1]);
    let b = sites.mask(second[2]);
    let t = sites.mask(second[3]);
    let mut f = false;
    let mut g = false;
    for &[kind, src, dst, _] in gap {
        let c = sites.mask(src);
        if kind == 6 {
            f ^= u & c != 0;
            g ^= v & c != 0;
        } else {
            let z = sites.mask(dst);
            if u & z != 0 {
                u ^= c;
            }
            if v & z != 0 {
                v ^= c;
            }
            if d & c != 0 {
                d ^= z;
            }
        }
    }
    let from = [u, v, u ^ v];
    let to = [a, b, a ^ b];
    let same_plane = to.contains(&u) && to.contains(&v);
    // Linear part of the Boolean product after reducing x_i*x_i to x_i.
    let linear = (u & v) ^ (if f { v } else { 0 }) ^ (if g { u } else { 0 });
    let constant = f && g;
    output.clear();
    if same_plane {
        affine_update(&sites, d, linear, constant, &mut |row| output.push(row));
        distribute(&sites, d ^ t, a, b, &mut |row| output.push(row));
        metrics.distributed += u64::from(d != t);
        metrics.cancelled += u64::from(d == t);
    } else if d == t {
        let Some(s) = from.iter().copied().find(|w| to.contains(w)) else {
            return false;
        };
        let h = (if s == u { v } else { u }) ^ (if s == a { b } else { a });
        if constant {
            output.push(x(sites.name(t)));
        }
        parity_product(&sites, s, h, t, linear ^ (s & h), &mut |row| {
            output.push(row)
        });
        metrics.factored += 1;
    } else {
        return false;
    }
    metrics.pairs += 1;
    true
}

pub struct Affine {
    first: Option<Row>,
    gap: Vec<Row>,
    replacement: Vec<Row>,
    pub metrics: Metrics,
}
impl Affine {
    pub fn new() -> Self {
        Self {
            first: None,
            gap: Vec::with_capacity(GAP),
            replacement: Vec::with_capacity(32),
            metrics: Metrics::default(),
        }
    }
    pub fn flush(&mut self, mut emit: impl FnMut(Row)) {
        if let Some(first) = self.first.take() {
            emit(first);
        }
        for r in self.gap.drain(..) {
            emit(r);
        }
    }
    pub fn push(&mut self, row: Row, mut emit: impl FnMut(Row)) {
        if row[0] == 13 {
            if let Some(first) = self.first {
                if combine(
                    first,
                    &self.gap,
                    row,
                    &mut self.metrics,
                    &mut self.replacement,
                ) {
                    for r in self.gap.drain(..) {
                        emit(r);
                    }
                    for &r in &self.replacement {
                        emit(r);
                    }
                    self.first = None;
                    return;
                }
                self.flush(&mut emit);
            }
            self.first = Some(row);
        } else if self.first.is_some()
            && self.gap.len() < GAP
            && (row[0] == 6 && row[2] == NONE || row[0] == 8 && row[3] == NONE)
        {
            self.gap.push(row);
        } else {
            self.flush(&mut emit);
            emit(row);
        }
    }
}
