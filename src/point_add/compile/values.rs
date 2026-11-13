//! Conservative equality of basis values. An evicted equation only loses a rewrite.
const SLOTS: usize = 1 << 16;
const NO_WIRE: u16 = u16::MAX;

#[derive(Clone, Copy, Default)]
struct Equation {
    left: u64,
    right: u64,
    result: u64,
}

struct Table(Vec<Equation>);
impl Table {
    fn new() -> Self {
        Self(vec![Equation::default(); SLOTS])
    }
    fn index(a: u64, b: u64) -> usize {
        let h = a.wrapping_mul(0x9e3779b97f4a7c15) ^ b.wrapping_mul(0xc2b2ae3d27d4eb4f);
        (h >> 48) as usize
    }
    fn get(&self, a: u64, b: u64) -> Option<u64> {
        let (l, r) = (a.min(b), a.max(b));
        let v = self.0[Self::index(l, r)];
        (v.left == l && v.right == r).then_some(v.result)
    }
    fn put(&mut self, a: u64, b: u64, result: u64) {
        let (left, right) = (a.min(b), a.max(b));
        self.0[Self::index(left, right)] = Equation {
            left,
            right,
            result,
        };
    }
}

struct Undo {
    q: usize,
    prior: u64,
    mark: u64,
}
pub struct Values {
    pub wire: Vec<u64>,
    pub zero: Vec<u64>,
    live: Vec<u16>,
    xor: Table,
    and: Table,
    next: u64,
    frame_id: u64,
    frames: Vec<(u64, usize)>,
    undo: Vec<Undo>,
    marks: Vec<u64>,
    join: Vec<usize>,
}

impl Values {
    pub fn new(width: usize) -> Self {
        let mut zero = vec![u64::MAX; width.div_ceil(64)];
        if width % 64 != 0 {
            *zero.last_mut().unwrap() = (1u64 << (width % 64)) - 1;
        }
        Self {
            wire: vec![0; width],
            zero,
            live: vec![NO_WIRE; SLOTS],
            xor: Table::new(),
            and: Table::new(),
            next: 2,
            frame_id: 0,
            frames: Vec::new(),
            undo: Vec::new(),
            marks: vec![0; width],
            join: Vec::new(),
        }
    }
    fn fresh(&mut self) -> u64 {
        let v = self.next;
        self.next += 2;
        v
    }
    pub fn product(&mut self, a: u64, b: u64) -> u64 {
        if a == 0 || b == 0 || a ^ b == 1 {
            return 0;
        }
        if a == 1 || a == b {
            return b;
        }
        if b == 1 {
            return a;
        }
        if let Some(value) = self.and.get(a, b) {
            return value;
        }
        let value = self.fresh();
        self.and.put(a, b, value);
        value
    }
    pub fn sum(&mut self, a: u64, b: u64) -> u64 {
        let parity = (a ^ b) & 1;
        let (a, b) = (a & !1, b & !1);
        if a == b {
            return parity;
        }
        if a == 0 || b == 0 {
            return (a | b) ^ parity;
        }
        let value = if let Some(value) = self.xor.get(a, b) {
            value
        } else {
            let value = self.fresh();
            self.xor.put(a, b, value);
            self.xor.put(a, value, b);
            self.xor.put(b, value, a);
            value
        };
        value ^ parity
    }
    pub fn alias(&self, id: u64, except: u16) -> Option<(u16, bool)> {
        if id < 2 {
            return None;
        }
        let q = self.live[(id as usize >> 1) & (SLOTS - 1)];
        if q == NO_WIRE || q == except {
            return None;
        }
        let difference = id ^ self.wire[q as usize];
        (difference <= 1).then_some((q, difference != 0))
    }
    fn assign(&mut self, q: usize, id: u64) {
        let old = self.wire[q];
        if old == id {
            return;
        }
        if old == 0 || id == 0 {
            self.zero[q / 64] ^= 1 << (q % 64);
        }
        self.wire[q] = id;
        if id > 1 {
            self.live[(id as usize >> 1) & (SLOTS - 1)] = q as u16;
        }
    }
    pub fn set(&mut self, q: usize, id: u64) {
        if self.wire[q] == id {
            return;
        }
        if let Some(&(frame, _)) = self.frames.last() {
            if self.marks[q] != frame {
                self.undo.push(Undo {
                    q,
                    prior: self.wire[q],
                    mark: self.marks[q],
                });
                self.marks[q] = frame;
            }
        }
        self.assign(q, id);
    }
    pub fn unknown(&mut self, q: usize) {
        let id = self.fresh();
        self.set(q, id);
    }
    pub fn enter(&mut self) {
        self.frame_id += 1;
        self.frames.push((self.frame_id, self.undo.len()));
    }
    pub fn leave(&mut self) {
        let (_, start) = self.frames.pop().expect("unmatched condition pop");
        while self.undo.len() > start {
            let u = self.undo.pop().unwrap();
            self.marks[u.q] = u.mark;
            if self.wire[u.q] != u.prior {
                self.assign(u.q, u.prior);
                self.join.push(u.q);
            }
        }
        while let Some(q) = self.join.pop() {
            self.unknown(q);
        }
    }
    pub fn finish(&self) {
        assert!(self.frames.is_empty() && self.undo.is_empty());
    }
}
