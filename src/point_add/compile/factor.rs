//! Streaming Rust counterpart of factor.hh, usable directly after the stock Cache emitter.
pub type Row = [u16; 4];
const NONE: u16 = u16::MAX;
const MIX_GAP: usize = 48;
const TABLE_BITS: u32 = 18;

#[derive(Default, Clone, Copy)]
struct Seen {
    time: u64,
    key: u32,
    parity: u8,
}
struct Table(Vec<Seen>);
impl Table {
    fn new() -> Self {
        Self(vec![Seen::default(); 1 << TABLE_BITS])
    }
    fn slot(a: u16, b: u16) -> (u32, usize) {
        let key = (u32::from(a) << 16) | u32::from(b);
        (
            key,
            (key.wrapping_mul(2_654_435_761) >> (32 - TABLE_BITS)) as usize,
        )
    }
    fn get(&self, a: u16, b: u16) -> Seen {
        let (key, at) = Self::slot(a, b);
        let seen = self.0[at];
        if seen.key == key {
            seen
        } else {
            Seen::default()
        }
    }
    fn put(&mut self, a: u16, b: u16, time: u64, parity: u8) {
        let (key, at) = Self::slot(a, b);
        self.0[at] = Seen { key, time, parity };
    }
}

#[derive(Clone, Copy, Default)]
struct Wire {
    read: u64,
    write: u64,
    hard: u64,
    cx_from: u16,
    parity: u8,
}
#[derive(Clone, Copy)]
enum Plan {
    Keep,
    Drop,
    Pair(u16, u16, u16, u8),
    Factor(u16, u16, u16, u8),
}

pub struct Factor {
    block: usize,
    wire: Vec<Wire>,
    pending: Vec<Row>,
    plan: Vec<Plan>,
    pairs: Table,
    shared: Table,
    time: u64,
    pub saved: u64,
}

impl Factor {
    pub fn new(width: usize, block: usize) -> Self {
        assert!((1..=usize::from(NONE)).contains(&width) && (1..=1 << 20).contains(&block));
        Self {
            block,
            wire: vec![Wire::default(); width],
            pending: Vec::with_capacity(block),
            plan: Vec::with_capacity(block),
            pairs: Table::new(),
            shared: Table::new(),
            time: 0,
            saved: 0,
        }
    }
    fn valid(&self, [k, a, b, c]: Row) -> bool {
        let q = |i: u16| usize::from(i) < self.wire.len();
        match k {
            1 | 15 => a != NONE && b == NONE && c == NONE,
            2 => a != NONE && q(b) && c == NONE,
            18 => a != NONE && b != NONE && c == NONE,
            3..=5 => a != NONE && c == NONE,
            6 | 7 => q(a) && c == NONE,
            8 | 9 => q(a) && q(b) && a != b,
            12 => q(a) && b != NONE && c == NONE,
            13 => q(a) && q(b) && q(c) && a != b && a != c && b != c,
            16 => a == NONE && b == NONE && c == NONE,
            _ => false,
        }
    }
    fn hard_write(&mut self, q: u16) {
        let w = &mut self.wire[usize::from(q)];
        w.hard = self.time;
        w.write = self.time;
    }
    fn parity(&self, x: u16, y: u16) -> u8 {
        self.wire[usize::from(x)].parity | (self.wire[usize::from(y)].parity << 1)
    }
    fn difference(&self, gap: &[Row], x: u16, y: u16, seen: Seen) -> Option<u8> {
        let wx = self.wire[usize::from(x)];
        let wy = self.wire[usize::from(y)];
        if wx.hard > seen.time || wy.hard > seen.time {
            return None;
        }
        if wx.write <= seen.time && wy.write <= seen.time {
            let d = self.parity(x, y) ^ seen.parity;
            return Some(u8::from(d == 3) | (d & 2) | ((d & 1) << 2));
        }
        if gap.len() > MIX_GAP
            || (wx.write > seen.time && wx.cx_from != y)
            || (wy.write > seen.time && wy.cx_from != x)
        {
            return None;
        }
        let (mut u, mut v) = (10u8, 12u8);
        for &[k, a, b, c] in gap {
            if k == 6 && (a == x || a == y) {
                if b != NONE {
                    return None;
                }
                if a == x {
                    u ^= 15;
                } else {
                    v ^= 15;
                }
            } else if k == 8 && (b == x || b == y) {
                if c != NONE || a != (if b == x { y } else { x }) {
                    return None;
                }
                if b == x {
                    u ^= v;
                } else {
                    v ^= u;
                }
            }
        }
        let d = (u & v) ^ 8;
        let c = d & 1;
        let a = ((d >> 1) & 1) ^ c;
        let b = ((d >> 2) & 1) ^ c;
        (((d >> 3) & 1) == (a ^ b ^ c)).then_some(c | (a << 1) | (b << 2))
    }
    fn run_block(&mut self, emit: &mut impl FnMut(Row)) {
        let rows = std::mem::take(&mut self.pending);
        assert!(
            rows.iter().copied().all(|r| self.valid(r)),
            "invalid compact gate record"
        );
        self.plan.clear();
        self.plan.resize(rows.len(), Plan::Keep);
        let base = self.time;
        let mut boundary = base;
        let index = |at: u64| rows.len() - (at - base) as usize;
        for (i, &[k, a, b, t]) in rows.iter().enumerate().rev() {
            self.time += 1;
            match k {
                13 => {
                    let (lo, hi) = (a.min(b), a.max(b));
                    let attempt = |seen: Seen, x: u16, y: u16, factor: bool| {
                        if seen.time <= boundary {
                            return None;
                        }
                        let j = index(seen.time);
                        let dst = rows[j][3];
                        if self.wire[usize::from(dst)].read > seen.time {
                            return None;
                        }
                        let lin = self.difference(&rows[i + 1..j], x, y, seen)?;
                        let plan = if factor {
                            Plan::Factor(x, y, dst, lin)
                        } else {
                            Plan::Pair(x, y, dst, lin)
                        };
                        Some((j, plan, 1 + u64::from(!factor && t == dst)))
                    };
                    let mut selected = attempt(self.pairs.get(lo, hi), lo, hi, false);
                    for (common, earlier) in [(lo, hi), (hi, lo)] {
                        if selected.is_some() {
                            break;
                        }
                        let seen = self.shared.get(common, t);
                        if seen.time <= boundary {
                            continue;
                        }
                        let later = rows[index(seen.time)];
                        let y = if later[1] == common {
                            later[2]
                        } else {
                            later[1]
                        };
                        if y != earlier {
                            selected = attempt(seen, common, y, true);
                        }
                    }
                    if let Some((j, p, saved)) = selected {
                        self.plan[i] = p;
                        self.plan[j] = Plan::Drop;
                        self.saved += saved;
                        boundary = self.time;
                    }
                    self.pairs.put(lo, hi, self.time, self.parity(lo, hi));
                    self.shared.put(lo, t, self.time, self.parity(lo, hi));
                    self.shared.put(hi, t, self.time, self.parity(hi, lo));
                    self.wire[usize::from(a)].read = self.time;
                    self.wire[usize::from(b)].read = self.time;
                    self.hard_write(t);
                }
                6 if b == NONE => self.wire[usize::from(a)].parity ^= 1,
                6 => self.hard_write(a),
                8 => {
                    self.wire[usize::from(a)].read = self.time;
                    if t == NONE {
                        self.wire[usize::from(b)].write = self.time;
                        self.wire[usize::from(b)].cx_from = a;
                    } else {
                        self.hard_write(b);
                    }
                }
                7 | 9 => {
                    self.wire[usize::from(a)].read = self.time;
                    if k == 9 {
                        self.wire[usize::from(b)].read = self.time;
                    }
                }
                12 => {
                    self.wire[usize::from(a)].read = self.time;
                    self.hard_write(a);
                }
                1 | 2 | 18 | 15 | 16 => boundary = self.time,
                _ => {}
            }
        }
        let cx = |a, b| [8, a, b, NONE];
        for (&row, &p) in rows.iter().zip(&self.plan) {
            let [_, a, b, t] = row;
            let (x, y, dst, lin) = match p {
                Plan::Keep => {
                    emit(row);
                    continue;
                }
                Plan::Drop => continue,
                Plan::Factor(x, y, dst, lin) => {
                    let u = if a == x { b } else { a };
                    emit(cx(y, u));
                    emit([13, x, u, t]);
                    emit(cx(y, u));
                    (x, y, dst, lin)
                }
                Plan::Pair(x, y, dst, lin) => {
                    if dst != t {
                        emit(cx(t, dst));
                        emit(row);
                        emit(cx(t, dst));
                    }
                    (x, y, dst, lin)
                }
            };
            if lin & 2 != 0 {
                emit(cx(x, dst));
            }
            if lin & 4 != 0 {
                emit(cx(y, dst));
            }
            if lin & 1 != 0 {
                emit([6, dst, NONE, NONE]);
            }
        }
        self.pending = rows;
        self.pending.clear();
    }
    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        self.pending.push(row);
        if self.pending.len() == self.block {
            self.run_block(emit);
        }
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        if !self.pending.is_empty() {
            self.run_block(emit);
        }
    }
}
