//! Bring a later product back to an earlier gate when its target is unread in between.
use super::cache::{Row, NONE};

#[derive(Default, Clone, Copy)]
struct Prior {
    time: u64,
    parity: u8,
}
#[derive(Clone, Copy)]
enum Replacement {
    Original,
    Drop,
    Pair {
        other: u16,
        parity: u8,
    },
    Factor {
        shared: u16,
        first: u16,
        second: u16,
    },
}
pub struct Mirror {
    width: usize,
    pair: Vec<Prior>,
    shared: Vec<u64>,
    read: Vec<u64>,
    write: Vec<u64>,
    nonlinear_write: Vec<u64>,
    parity: Vec<u8>,
    plan: Vec<Replacement>,
    time: u64,
    pub cancelled: u64,
    pub shared_target: u64,
    pub distributed: u64,
}
impl Mirror {
    pub fn new(width: usize) -> Self {
        Self {
            width,
            pair: vec![Prior::default(); width * width],
            shared: vec![0; width * width],
            read: vec![0; width],
            write: vec![0; width],
            nonlinear_write: vec![0; width],
            parity: vec![0; width],
            plan: Vec::new(),
            time: 0,
            cancelled: 0,
            shared_target: 0,
            distributed: 0,
        }
    }
    pub fn saved(&self) -> u64 {
        2 * self.cancelled + self.shared_target + self.distributed
    }
    pub fn chunk(&mut self, rows: &[Row], out: &mut Vec<Row>) {
        let mut boundary = self.time;
        let base = boundary + 1;
        self.plan.clear();
        self.plan.resize(rows.len(), Replacement::Original);
        for (i, &[k, aa, bb, cc]) in rows.iter().enumerate().rev() {
            self.time += 1;
            let now = self.time;
            let (a, b, c) = (aa as usize, bb as usize, cc as usize);
            match k {
                6 if bb == NONE => {
                    self.write[a] = now;
                    self.parity[a] ^= 1;
                }
                8 if cc == NONE => {
                    self.read[a] = now;
                    self.write[b] = now;
                    self.nonlinear_write[b] = now;
                }
                13 => {
                    let (x, y) = (a.min(b), a.max(b));
                    let pair = x * self.width + y;
                    let parity = self.parity[x] | (self.parity[y] << 1);
                    let prior = self.pair[pair];
                    let at = |t: u64| rows.len() - 1 - (t - base) as usize;
                    let mut selected = None;
                    if prior.time > boundary
                        && self.nonlinear_write[x] <= prior.time
                        && self.nonlinear_write[y] <= prior.time
                    {
                        let other = rows[at(prior.time)][3];
                        if self.read[other as usize] <= prior.time {
                            selected = Some((
                                prior.time,
                                Replacement::Pair {
                                    other,
                                    parity: parity ^ prior.parity,
                                },
                            ));
                            if other == cc {
                                self.cancelled += 1;
                            } else {
                                self.distributed += 1;
                            }
                        }
                    }
                    if selected.is_none() {
                        for &(common, first) in &[(x, y), (y, x)] {
                            let last = self.shared[common * self.width + c];
                            if last <= boundary || self.read[c] > last || self.write[common] > last
                            {
                                continue;
                            }
                            let old = rows[at(last)];
                            let second = if old[1] as usize == common {
                                old[2]
                            } else {
                                old[1]
                            };
                            if second as usize == first || self.write[second as usize] > last {
                                continue;
                            }
                            selected = Some((
                                last,
                                Replacement::Factor {
                                    shared: common as u16,
                                    first: first as u16,
                                    second,
                                },
                            ));
                            self.shared_target += 1;
                            break;
                        }
                    }
                    if let Some((last, rewrite)) = selected {
                        self.plan[at(last)] = Replacement::Drop;
                        self.plan[i] = rewrite;
                        boundary = now;
                    }
                    self.pair[pair] = Prior { time: now, parity };
                    self.shared[x * self.width + c] = now;
                    self.shared[y * self.width + c] = now;
                    self.read[a] = now;
                    self.read[b] = now;
                    self.write[c] = now;
                    self.nonlinear_write[c] = now;
                }
                _ => boundary = now,
            }
        }
        out.clear();
        for (&row, &r) in rows.iter().zip(&self.plan) {
            let [_, a, b, t] = row;
            let cx = |c, d| [8, c, d, NONE];
            match r {
                Replacement::Original => out.push(row),
                Replacement::Drop => (),
                Replacement::Pair { other, parity } => {
                    if other != t {
                        out.push(cx(t, other));
                        out.push(row);
                        out.push(cx(t, other));
                    }
                    let (x, y) = (a.min(b), a.max(b));
                    if parity & 1 != 0 {
                        out.push(cx(y, other));
                    }
                    if parity & 2 != 0 {
                        out.push(cx(x, other));
                    }
                    if parity == 3 {
                        out.push([6, other, NONE, NONE]);
                    }
                }
                Replacement::Factor {
                    shared,
                    first,
                    second,
                } => {
                    out.extend_from_slice(&[
                        cx(second, first),
                        [13, shared, first, t],
                        cx(second, first),
                    ]);
                }
            }
        }
    }
}
