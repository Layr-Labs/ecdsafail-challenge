//! Reuse an exact product through a clean idle wire and erase it by measurement.
use super::values::Values;
pub type Row = [u16; 4];
pub const NONE: u16 = u16::MAX;
pub const BLOCK: usize = 8192;

#[derive(Clone, Copy, Default)]
struct Prior {
    at: u64,
    x: u64,
    y: u64,
}
#[derive(Clone, Copy)]
enum Action {
    Original,
    Drop,
    X,
    Copy(u16, bool),
    Erase(u16, bool),
    Open(u16),
    Hit(u16, u8),
    Close(u16, u8),
}

#[derive(Default)]
pub struct Metrics {
    pub constants: u64,
    pub copies: u64,
    pub erasures: u64,
    pub opened: u64,
    pub hits: u64,
    pub internal_hits: u64,
    pub hmr_added: u64,
    pub input_t: u64,
    pub output_ops: u64,
    pub input_ops: u64,
}
pub struct Cache {
    width: usize,
    scratch: u16,
    facts: Values,
    prior: Vec<Prior>,
    touched: Vec<u64>,
    occupied: Vec<u64>,
    actions: Vec<Action>,
    barrier: u64,
    declarations_closed: bool,
    pub metrics: Metrics,
}

impl Cache {
    pub fn new(width: usize, extra: usize, scratch: u16) -> Self {
        assert!(width > 0 && width < NONE as usize && extra < NONE as usize - width);
        assert_ne!(scratch, NONE, "missing classical scratch bit");
        Self {
            width,
            scratch,
            facts: Values::new(width + extra),
            prior: vec![Prior::default(); width * width],
            touched: vec![0; width + extra],
            occupied: vec![0; width + extra],
            actions: Vec::new(),
            barrier: 0,
            declarations_closed: false,
            metrics: Metrics::default(),
        }
    }
    fn free(&self, start: u64, c: u16) -> Option<u16> {
        for (i, &word) in self.facts.zero.iter().enumerate().rev() {
            let mut bits = word;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                let q = i * 64 + bit;
                if q != c as usize && self.touched[q] < start && self.occupied[q] < start {
                    return Some(q as u16);
                }
                bits &= bits - 1;
            }
        }
        None
    }
    fn nonlinear(&mut self, row: Row, base: u64, at: u64, i: usize) {
        let (a, b) = (row[1].min(row[2]), row[1].max(row[2]));
        let c = row[3];
        assert!(a != b && b != c && a != c && [b, c].iter().all(|&q| (q as usize) < self.width));
        let (x, y) = (self.facts.wire[a as usize], self.facts.wire[b as usize]);
        let g = self.facts.product(x, y);
        let next = self.facts.sum(self.facts.wire[c as usize], g);
        let action = if g < 2 {
            self.metrics.constants += 1;
            if g == 0 {
                Action::Drop
            } else {
                Action::X
            }
        } else if let Some((q, invert)) = self.facts.alias(g, c).or_else(|| {
            if (x ^ g) <= 1 {
                Some((a, x != g))
            } else if (y ^ g) <= 1 {
                Some((b, y != g))
            } else {
                None
            }
        }) {
            self.metrics.copies += 1;
            self.touched[q as usize] = at;
            Action::Copy(q, invert)
        } else if let Some((q, invert)) = if next < 2 {
            Some((NONE, next == 1))
        } else {
            self.facts.alias(next, c)
        } {
            self.metrics.erasures += 1;
            self.metrics.hmr_added += 1;
            if q != NONE {
                self.touched[q as usize] = at;
            }
            Action::Erase(q, invert)
        } else {
            let key = a as usize * self.width + b as usize;
            let previous = self.prior[key];
            self.prior[key] = Prior { at, x, y };
            let mut action = Action::Original;
            if previous.at >= base
                && previous.at > self.barrier
                && (x ^ previous.x) <= 1
                && (y ^ previous.y) <= 1
            {
                let earlier = (previous.at - base) as usize;
                let changed = ((x ^ previous.x) | ((y ^ previous.y) << 1)) as u8;
                let choice = match self.actions[earlier] {
                    Action::Original => self
                        .free(previous.at, c)
                        .map(|q| (q, changed, Action::Open(q), true)),
                    Action::Close(q, prior_flip)
                        if self.touched[q as usize] < previous.at
                            && self.occupied[q as usize] == previous.at
                            && q != c =>
                    {
                        Some((q, prior_flip ^ changed, Action::Hit(q, prior_flip), false))
                    }
                    _ => None,
                };
                if let Some((q, flip, replacement, open)) = choice {
                    self.actions[earlier] = replacement;
                    self.occupied[q as usize] = at;
                    action = Action::Close(q, flip);
                    self.metrics.hits += 1;
                    self.metrics.internal_hits += u64::from((q as usize) < self.width);
                    if open {
                        self.metrics.opened += 1;
                        self.metrics.hmr_added += 1;
                    }
                }
            }
            action
        };
        self.actions[i] = action;
        self.facts.set(c as usize, next);
        self.touched[a as usize] = at;
        self.touched[b as usize] = at;
        self.touched[c as usize] = at;
    }
    pub fn chunk(&mut self, rows: &[Row], mut emit: impl FnMut(Row)) {
        let base = self.metrics.input_ops + 1;
        self.actions.clear();
        self.actions.resize(rows.len(), Action::Original);
        for (i, &row) in rows.iter().enumerate() {
            let at = base + i as u64;
            let [k, a, b, c] = row;
            // The evaluator preloads every quantum input before it runs any gate.
            // A streaming pass must see the whole port prefix before borrowing a wire.
            if k == 2 {
                assert!(!self.declarations_closed, "quantum ports must precede computation");
                assert!((b as usize) < self.width, "input port outside the original width");
            } else if k != 1 && k != 18 {
                self.declarations_closed = true;
            }
            let collision = match k {
                18 | 6 | 7 | 12 => b == self.scratch,
                3..=5 => a == self.scratch || b == self.scratch,
                8 | 9 => c == self.scratch,
                15 => a == self.scratch,
                _ => false,
            };
            assert!(!collision, "classical scratch collision");
            match k {
                6 if b == NONE => {
                    self.facts.set(a as usize, self.facts.wire[a as usize] ^ 1);
                    self.touched[a as usize] = at;
                }
                8 if c == NONE => {
                    let v = self
                        .facts
                        .sum(self.facts.wire[a as usize], self.facts.wire[b as usize]);
                    self.facts.set(b as usize, v);
                    self.touched[a as usize] = at;
                    self.touched[b as usize] = at;
                }
                13 => {
                    self.metrics.input_t += 1;
                    self.nonlinear(row, base, at, i);
                }
                _ => {
                    self.barrier = at;
                    match k {
                        2 => self.facts.unknown(b as usize),
                        6 => self.facts.unknown(a as usize),
                        8 => self.facts.unknown(b as usize),
                        12 => self.facts.set(a as usize, 0),
                        15 => self.facts.enter(),
                        16 => self.facts.leave(),
                        1 | 3..=5 | 7 | 9 | 18 => (),
                        _ => panic!("unsupported gate {k}"),
                    }
                }
            }
        }
        self.metrics.input_ops += rows.len() as u64;
        let scratch = self.scratch;
        let mut send = |row| {
            self.metrics.output_ops += 1;
            emit(row);
        };
        for (&row, &action) in rows.iter().zip(&self.actions) {
            let [_, a, b, c] = row;
            let (x, y) = (a.min(b), a.max(b));
            let add = |q| [8, q, c, NONE];
            let toggle = |q| [6, q, NONE, NONE];
            let clear = [4, scratch, NONE, NONE];
            match action {
                Action::Original => send(row),
                Action::Drop => (),
                Action::X => send(toggle(c)),
                Action::Copy(q, invert) => {
                    send(add(q));
                    if invert {
                        send(toggle(c));
                    }
                }
                Action::Erase(q, invert) => {
                    if q != NONE {
                        send(add(q));
                    }
                    if invert {
                        send(toggle(c));
                    }
                    send([12, c, scratch, NONE]);
                    send([9, x, y, scratch]);
                    send(clear);
                    if q != NONE {
                        send(add(q));
                    }
                    if invert {
                        send(toggle(c));
                    }
                }
                Action::Open(q) => {
                    send([13, x, y, q]);
                    send(add(q));
                }
                Action::Hit(q, flip) | Action::Close(q, flip) => {
                    send(add(q));
                    if flip & 1 != 0 {
                        send(add(y));
                    }
                    if flip & 2 != 0 {
                        send(add(x));
                    }
                    if flip == 3 {
                        send(toggle(c));
                    }
                    if matches!(action, Action::Close(..)) {
                        send([12, q, scratch, NONE]);
                        if flip & 1 != 0 {
                            send(toggle(x));
                        }
                        if flip & 2 != 0 {
                            send(toggle(y));
                        }
                        send([9, x, y, scratch]);
                        if flip & 1 != 0 {
                            send(toggle(x));
                        }
                        if flip & 2 != 0 {
                            send(toggle(y));
                        }
                        send(clear);
                    }
                }
            }
        }
    }
    pub fn finish(&self) {
        self.facts.finish();
    }
}
