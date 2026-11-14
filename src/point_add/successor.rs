//! Replace quantum controls whose values equal live classical bits, then share remaining products.
use super::values::Values;
use super::{affine::Affine, mirror::Mirror};
use std::collections::HashMap;
pub type Row = [u16; 4];
const NONE: u16 = u16::MAX;
const WIDTH: usize = 646;
pub const BLOCK: usize = 8192;
const ALIAS_SLOTS: usize = 1 << 16;

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct Counts {
    pub classical_products: u64,
    pub classical_controls: u64,
    pub quantum_copies: u64,
    pub constant_products: u64,
    pub trivial_controls: u64,
    pub mirror_saved: u64,
    pub affine_saved: u64,
}
struct Classical {
    values: Values,
    // Each entry is advisory. Check the current bit's full ID before using it.
    classical: Vec<u16>,
    quantum: Vec<u16>,
    started: bool,
    active: HashMap<u64, usize>,
    masks: Vec<u64>,
    maximum_bit: usize,
}
impl Classical {
    fn new(maximum_bit: usize) -> Self {
        assert!(maximum_bit < NONE as usize - WIDTH);
        Self {
            values: Values::new(WIDTH + maximum_bit + 1),
            classical: vec![NONE; ALIAS_SLOTS],
            quantum: vec![NONE; ALIAS_SLOTS],
            started: false,
            active: HashMap::new(),
            masks: Vec::new(),
            maximum_bit,
        }
    }
    fn bit(&self, b: u16) -> u64 {
        if b == NONE {
            1
        } else {
            assert!(usize::from(b) <= self.maximum_bit);
            self.values.wire[WIDTH + usize::from(b)]
        }
    }
    fn slot(v: u64) -> usize {
        ((v >> 1) as usize) & (ALIAS_SLOTS - 1)
    }
    fn write(&mut self, q: usize, v: u64) {
        self.values.set(q, v);
        if v >= 2 {
            if q >= WIDTH {
                self.classical[Self::slot(v)] = (q - WIDTH) as u16;
            } else {
                self.quantum[Self::slot(v)] = q as u16;
            }
        }
    }
    fn unknown(&mut self, q: usize) {
        self.values.unknown(q);
        self.write(q, self.values.wire[q]);
    }
    fn alias(&self, v: u64, classical: bool) -> Option<(u16, bool)> {
        if v < 2 {
            return None;
        }
        let q = if classical {
            self.classical[Self::slot(v)]
        } else {
            self.quantum[Self::slot(v)]
        };
        if q == NONE {
            return None;
        }
        let difference = v ^ self.values.wire[usize::from(q) + if classical { WIDTH } else { 0 }];
        (difference <= 1).then_some((q, difference != 0))
    }
    fn known(&self, id: u64) -> u64 {
        if id >= 2 {
            if self.active.contains_key(&id) {
                return 1;
            }
            if self.active.contains_key(&(id ^ 1)) {
                return 0;
            }
        }
        id
    }
    fn conditional(&self, b: u16) -> u64 {
        self.known(self.bit(b))
    }
    fn gate(&mut self, row: Row, counts: &mut Counts, emit: &mut impl FnMut(Row)) {
        let [k, a, b, c] = row;
        let (x, y, t) = (usize::from(a), usize::from(b), usize::from(c));
        if !matches!(k, 1 | 2 | 18) {
            self.started = true;
        }
        match k {
            1 => {}
            2 => {
                assert!(!self.started && y < WIDTH);
                self.unknown(y);
            }
            18 => {
                assert!(!self.started && y <= self.maximum_bit);
                self.unknown(WIDTH + y);
            }
            15 => {
                let id = self.bit(a);
                self.values.enter();
                self.masks.push(id);
                *self.active.entry(id).or_default() += 1;
            }
            16 => {
                let id = self.masks.pop().expect("unmatched condition pop");
                let n = self.active.get_mut(&id).unwrap();
                *n -= 1;
                if *n == 0 {
                    self.active.remove(&id);
                }
                self.values.leave();
            }
            3..=5 => {
                assert!(x <= self.maximum_bit);
                let p = self.conditional(b);
                let previous = self.values.wire[WIDTH + x];
                let toggled = match k {
                    3 => p,
                    4 => self.values.product(p, previous),
                    5 => self.values.product(p, previous ^ 1),
                    _ => unreachable!(),
                };
                let out = self.values.sum(previous, toggled);
                self.write(WIDTH + x, out);
            }
            6 => {
                assert!(x < WIDTH);
                let p = self.conditional(b);
                let out = self.values.sum(self.values.wire[x], p);
                self.write(x, out);
            }
            8 => {
                assert!(x < WIDTH && y < WIDTH && x != y);
                let p = self.conditional(c);
                let source = self.known(self.values.wire[x]);
                let toggle = self.values.product(source, p);
                let out = self.values.sum(self.values.wire[y], toggle);
                self.write(y, out);
            }
            12 => {
                assert!(x < WIDTH);
                self.write(x, 0);
                if b != NONE {
                    assert!(y <= self.maximum_bit);
                    self.unknown(WIDTH + y);
                }
            }
            7 | 9 => {}
            13 => {
                assert!(x < WIDTH && y < WIDTH && t < WIDTH && x != y && y != t && x != t);
                let left = self.known(self.values.wire[x]);
                let right = self.known(self.values.wire[y]);
                let g = self.values.product(left, right);
                let next = self.values.sum(g, self.values.wire[t]);
                let xgate = |q| [6, c, q, NONE];
                let cx = |q, bit| [8, q, c, bit];
                if g < 2 {
                    if g == 1 {
                        emit(xgate(NONE));
                    }
                    counts.constant_products += 1;
                } else if g == left || g == right {
                    emit(cx(if g == left { a } else { b }, NONE));
                    counts.trivial_controls += 1;
                } else if let Some((q, inv)) = self.alias(g, true) {
                    emit(xgate(q));
                    if inv {
                        emit(xgate(NONE));
                    }
                    counts.classical_products += 1;
                } else if let Some((q, inv)) = self.alias(g, false).filter(|&(q, _)| q != c) {
                    emit(cx(q, NONE));
                    if inv {
                        emit(xgate(NONE));
                    }
                    counts.quantum_copies += 1;
                } else if let Some(((q, inv), other)) = self
                    .alias(left, true)
                    .map(|v| (v, b))
                    .or_else(|| self.alias(right, true).map(|v| (v, a)))
                {
                    if inv {
                        emit(cx(other, NONE));
                    }
                    emit(cx(other, q));
                    counts.classical_controls += 1;
                } else {
                    emit(row);
                }
                self.write(t, next);
                return;
            }
            _ => panic!("unsupported native row {k}"),
        }
        emit(row);
    }
}
// Fixed mini-blocks belong to the successor alone and ignore donor chunk boundaries.
pub struct Successor {
    rules: Classical,
    backwards: Mirror,
    affine: Affine,
    pending: Vec<Row>,
    mirrored: Vec<Row>,
    pub counts: Counts,
}
impl Successor {
    pub fn new() -> Self {
        Self {
            rules: Classical::new(10861),
            backwards: Mirror::new(WIDTH),
            affine: Affine::new(),
            pending: Vec::with_capacity(BLOCK),
            mirrored: Vec::with_capacity(BLOCK + 32),
            counts: Counts::default(),
        }
    }
    pub fn push(&mut self, r: Row, emit: &mut impl FnMut(Row)) {
        self.rules.gate(r, &mut self.counts, &mut |r| {
            self.pending.push(r);
            if self.pending.len() == BLOCK {
                self.backwards.chunk(&self.pending, &mut self.mirrored);
                self.pending.clear();
                for &r in &self.mirrored {
                    self.affine.push(r, &mut *emit);
                }
            }
        });
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        self.rules.values.finish();
        assert!(self.rules.masks.is_empty() && self.rules.active.is_empty());
        self.backwards.chunk(&self.pending, &mut self.mirrored);
        self.pending.clear();
        for &r in &self.mirrored {
            self.affine.push(r, &mut *emit);
        }
        self.affine.flush(emit);
        self.counts.mirror_saved = self.backwards.saved();
        self.counts.affine_saved = self.affine.metrics.pairs + self.affine.metrics.cancelled;
    }
}
