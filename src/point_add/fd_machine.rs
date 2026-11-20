pub type Row = [u16; 4];
pub const N: u16 = u16::MAX;
pub const ZERO: u64 = 0;
pub const ONE: u64 = 1;
const DEPTH: usize = 32;

// Physical ports at input and output are independent of the segment's id names.
#[derive(Clone)]
pub struct Frame {
    pub live: Vec<usize>,
    pub ones: Vec<usize>,
    pub bits_zero: Vec<u16>,
    pub bits_one: Vec<u16>,
    // Captured effective guards, outermost first: 0 false, 1 true, 2 opaque.
    pub guards: Vec<u8>,
    // For each captured guard, possible nonzero lanes on the bypass path.
    pub bypass: Vec<Vec<u64>>,
}
#[derive(Copy, Clone, Eq, PartialEq)]
struct Term {
    row: Row,
    left: u64,
    right: u64,
    guard: u64,
    bit: u64,
}
#[derive(Copy, Clone)]
struct Saved {
    term: Term,
    before: u64,
    opened: u64,
}
pub struct Machine {
    pub q: Vec<u64>,
    pub bits: Vec<u64>,
    pub guards: Vec<u64>,
    history: Vec<Vec<Saved>>,
    serial: u64,
    pub brackets: bool,
    live_mask: Vec<u64>,
    bypass: Vec<Vec<u64>>,
    pub opened: Option<u64>,
    step_index: u64,
}
#[derive(Copy, Clone, Debug)]
pub struct Effect {
    pub lanes: [u16; 2],
    pub reason: &'static str,
    pub noop: bool,
}
impl Effect {
    fn new(a: u16, b: u16, reason: &'static str) -> Self {
        Self {
            lanes: [a, b],
            reason,
            noop: false,
        }
    }
}
impl Machine {
    pub fn new(width: usize, f: &Frame, brackets: bool) -> Self {
        let mut m = Self {
            q: vec![0; width],
            bits: (0..65536).map(|i| i + 2).collect(),
            guards: vec![],
            history: vec![vec![]; width],
            serial: 65538,
            brackets,
            live_mask: vec![0; width.div_ceil(64)],
            bypass: vec![],
            opened: None,
            step_index: 0,
        };
        for &l in &f.live {
            m.q[l] = m.fresh();
        }
        for &l in &f.ones {
            assert!(m.q[l] != 0);
            m.q[l] = ONE;
        }
        for &b in &f.bits_zero {
            assert_ne!(b, N);
            m.bits[b as usize] = ZERO;
        }
        for &b in &f.bits_one {
            assert_ne!(b, N);
            assert_ne!(m.bits[b as usize], 0);
            m.bits[b as usize] = ONE;
        }
        m.bits[N as usize] = ONE;
        for &g in &f.guards {
            let tag = match g {
                0 | 1 => g as u64,
                2 => m.fresh(),
                _ => panic!("bad guard"),
            };
            assert!(m.base() != 0 || tag == 0);
            assert!(m.base() <= 1 || tag != 1);
            m.guards.push(tag);
        }
        for l in 0..width {
            m.update_mask(l);
        }
        m.bypass = if f.bypass.is_empty() {
            vec![vec![u64::MAX; width.div_ceil(64)]; f.guards.len()]
        } else {
            assert_eq!(f.bypass.len(), f.guards.len());
            assert!(f.bypass.iter().all(|b| b.len() == m.live_mask.len()));
            f.bypass.clone()
        };
        m
    }
    pub fn frame(&self) -> Frame {
        Frame {
            live: (0..self.q.len()).filter(|&i| self.q[i] != 0).collect(),
            ones: (0..self.q.len()).filter(|&i| self.q[i] == 1).collect(),
            bits_zero: (0..N).filter(|&i| self.bits[i as usize] == 0).collect(),
            bits_one: (0..N).filter(|&i| self.bits[i as usize] == 1).collect(),
            guards: self.guards.iter().map(|&g| g.min(2) as u8).collect(),
            bypass: self.bypass.clone(),
        }
    }
    fn fresh(&mut self) -> u64 {
        self.serial += 1;
        self.serial
    }
    pub fn base(&self) -> u64 {
        *self.guards.last().unwrap_or(&ONE)
    }
    pub fn move_runs_where_live(&self, l: usize) -> bool {
        self.base() == ONE
            || self
                .bypass
                .last()
                .is_some_and(|m| m[l / 64] & (1u64 << (l % 64)) == 0)
    }
    fn update_mask(&mut self, l: usize) {
        let bit = 1u64 << (l % 64);
        if self.q[l] == 0 {
            self.live_mask[l / 64] &= !bit;
        } else {
            self.live_mask[l / 64] |= bit;
        }
    }
    pub fn assert_zero(&mut self, l: usize) {
        assert_ne!(
            self.q[l], ONE,
            "false structural zero: annotation contradicts a known one on lane {l}"
        );
        self.q[l] = ZERO;
        self.history[l].clear();
        self.update_mask(l);
    }
    pub fn step(&mut self, r: Row) -> Effect {
        let [k, a, b, c] = r;
        let pos = self.step_index;
        self.step_index += 1;
        self.opened = None;
        let base = self.base();
        let (i, j) = (a as usize, b as usize);
        let mut e = Effect::new(N, N, "unchanged");
        match k {
            1 | 2 | 18 => {}
            15 => {
                let bit = self.bits[i];
                let g = if base == 0 || bit == 0 {
                    0
                } else if bit == 1 {
                    base
                } else if base == 1 {
                    bit
                } else {
                    self.fresh()
                };
                let outside = if g == base {
                    self.bypass
                        .last()
                        .cloned()
                        .unwrap_or_else(|| vec![0; self.live_mask.len()])
                } else {
                    self.live_mask.clone()
                };
                self.bypass.push(outside);
                self.guards.push(g);
            }
            16 => {
                self.guards
                    .pop()
                    .expect("pop requires matching frame scope");
                self.bypass.pop().unwrap();
            }
            3..=5 => {
                let bit = self.bits[j];
                if base != 0 && bit != 0 {
                    let old = self.bits[i];
                    self.bits[i] = match k {
                        4 if old == 0 || (bit == 1 && base == 1) => 0,
                        5 if old == 1 || (bit == 1 && base == 1) => 1,
                        3 if old <= 1 && bit == 1 && base == 1 => 1 - old,
                        _ => self.fresh(),
                    };
                }
            }
            6 | 8 | 13 => {
                let (t, left, right, cond) = match k {
                    6 => (a, ONE, ONE, b),
                    8 => (b, self.q[i], ONE, c),
                    _ => (c, self.q[i], self.q[j], N),
                };
                if base == 0 || self.bits[cond as usize] == 0 || left == 0 || right == 0 {
                    e.noop = true;
                    return e;
                }
                let idx = t as usize;
                let term = Term {
                    row: r,
                    left,
                    right,
                    guard: base,
                    bit: self.bits[cond as usize],
                };
                let old = self.q[idx];
                e = Effect::new(t, N, "write");
                if self.brackets && self.history[idx].last().is_some_and(|s| s.term == term) {
                    let saved = self.history[idx].pop().unwrap();
                    self.q[idx] = saved.before;
                    self.opened = Some(saved.opened);
                    e.reason = "inverse_bracket";
                } else {
                    if self.brackets {
                        if self.history[idx].len() >= DEPTH {
                            self.history[idx].clear();
                        }
                        self.history[idx].push(Saved {
                            term,
                            before: old,
                            opened: pos,
                        });
                    }
                    self.q[idx] =
                        if old <= 1 && base == 1 && term.bit == 1 && left == 1 && right == 1 {
                            1 - old
                        } else {
                            self.fresh()
                        };
                    if self.q[idx] == 0 {
                        e.reason = "constant_toggle";
                    }
                }
            }
            7 | 9 | 14 => {
                e.noop = base == 0
                    || self.q[i] == 0
                    || match k {
                        7 => self.bits[j] == 0,
                        9 => self.q[j] == 0 || self.bits[c as usize] == 0,
                        _ => self.q[j] == 0 || self.q[c as usize] == 0,
                    };
            }
            10 => {
                let bit = self.bits[c as usize];
                if base == 0 || bit == 0 || self.q[i] == self.q[j] {
                    e.noop = true;
                    return e;
                }
                self.history[i].clear();
                self.history[j].clear();
                e = Effect::new(a, b, "swap");
                if base == 1 && bit == 1 {
                    self.q.swap(i, j);
                } else {
                    self.q[i] = self.fresh();
                    self.q[j] = self.fresh();
                }
            }
            11 | 12 => {
                if k == 12 && b != N && base != 0 {
                    self.bits[j] = self.fresh();
                }
                let bcond = if k == 11 { self.bits[j] } else { ONE };
                let outside_zero = self
                    .bypass
                    .last()
                    .is_some_and(|v| v[i / 64] & (1u64 << (i % 64)) == 0);
                let erased = bcond == ONE && (base == ONE || outside_zero);
                if base != 0 && bcond != 0 {
                    self.history[i].clear();
                    if erased {
                        self.q[i] = 0;
                    } else if self.q[i] != 0 {
                        self.q[i] = self.fresh();
                    }
                }
                e = Effect::new(
                    a,
                    N,
                    if erased && base != ONE {
                        "reset_bypass_zero"
                    } else {
                        "reset"
                    },
                );
            }
            _ => panic!("unknown row kind {k}"),
        }
        for l in e.lanes {
            if l != N {
                self.update_mask(l as usize);
            }
        }
        e
    }
}
// Physical qubit fields only. Validate once per row before indexing machines.
pub fn operands(r: &Row) -> &[u16] {
    match r[0] {
        1 | 3..=5 | 15 | 16 | 18 => &[],
        2 => &r[2..3],
        6 | 7 | 11 | 12 => &r[1..2],
        8..=10 => &r[1..3],
        13 | 14 => &r[1..4],
        k => panic!("unknown kind {k}"),
    }
}
