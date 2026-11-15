//! Share a conjunction between two multi-controlled XORs with different targets.
use super::{ccx, cost_for, cx, emit_ladder, Atom, Controls, Ladder, Row};
use std::collections::HashMap;

struct Pair {
    left: usize,
    right: usize,
    common: Vec<u16>,
    first: Option<u16>,
    second: Option<u16>,
    saved: usize,
}

fn candidate(atoms: &[Atom], j: usize, i: usize, width: usize) -> Option<Pair> {
    let (a, b) = (&atoms[j], &atoms[i]);
    let (u, v) = (a.sites(), b.sites());
    if a.target == b.target || u.contains(&b.target) || v.contains(&a.target) {
        return None;
    }
    let common: Vec<_> = u.iter().copied().filter(|q| v.contains(q)).collect();
    let k = common.len();
    if k < 2 || u.len() > k + 1 || v.len() > k + 1 || u == v {
        return None;
    }
    let first = u.iter().copied().find(|q| !v.contains(q));
    let second = v.iter().copied().find(|q| !u.contains(q));
    let remainder = usize::from(first.is_some()) + usize::from(second.is_some());
    // One echo bit plus k-2 restored dirty bits for computing the conjunction.
    if width < 2 + k + remainder + 1 + (k - 2) {
        return None;
    }
    let old = a.cost() + b.cost();
    let new = 2 * (cost_for(k) + remainder);
    (old > new).then(|| Pair {
        left: j,
        right: i,
        common,
        first,
        second,
        saved: old - new,
    })
}

fn emit_pair(p: &Pair, atoms: &[Atom], width: usize, emit: &mut impl FnMut(Row)) {
    let (a, b) = (&atoms[p.left], &atoms[p.right]);
    let mut free = (0..width as u16).filter(|q| {
        *q != a.target && *q != b.target && !a.sites().contains(q) && !b.sites().contains(q)
    });
    let d = free.next().unwrap();
    let loans: Vec<_> = free.take(p.common.len() - 2).collect();
    for _ in 0..2 {
        for (residual, target) in [(p.first, a.target), (p.second, b.target)] {
            emit(match residual {
                Some(q) => ccx(d, q, target),
                None => cx(d, target),
            });
        }
        emit_ladder(&p.common, d, &loans, emit);
    }
}

pub struct Group {
    width: usize,
    limit: usize,
    rows: Vec<Row>,
    decoder: Ladder,
    pub pairs: usize,
    pub savings: usize,
}

impl Group {
    pub fn new(width: usize, limit: usize) -> Self {
        Self {
            width,
            limit,
            rows: Vec::with_capacity(limit),
            decoder: Ladder::new(width, limit),
            pairs: 0,
            savings: 0,
        }
    }
    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        self.rows.push(row);
        if self.rows.len() == self.limit {
            self.finish(emit);
        }
    }
    pub fn macro_count(&self) -> u64 {
        self.decoder.metrics.macros
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        if self.rows.is_empty() {
            return;
        }
        if !self.rows.windows(4).any(|s| s.iter().all(|r| r[0] == 13)) {
            self.rows.drain(..).for_each(emit);
            return;
        }
        let atoms = self.decoder.lift(&self.rows);
        let mut read = vec![0; self.width];
        let mut write = vec![0; self.width];
        let mut prior = HashMap::<Vec<u16>, [Option<usize>; 2]>::new();
        let mut pairs = HashMap::new();
        let mut skip = vec![false; atoms.len()];
        let mut boundary = 0;
        for (i, node) in atoms.iter().enumerate() {
            if let Controls::Barrier = node.controls {
                boundary = i + 1;
                continue;
            }
            let sites = node.sites();
            if sites.len() >= 2 {
                let mut keys = vec![sites.to_vec()];
                if sites.len() > 2 {
                    for q in sites {
                        keys.push(sites.iter().copied().filter(|p| p != q).collect());
                    }
                }
                let mut best: Option<Pair> = None;
                for key in &keys {
                    if let Some(recent) = prior.get(key) {
                        for &j in recent.iter().flatten() {
                            if j < boundary
                                || read[usize::from(node.target)] > j + 1
                                || sites.iter().any(|&q| write[usize::from(q)] > j + 1)
                            {
                                continue;
                            }
                            if let Some(p) = candidate(&atoms, j, i, self.width) {
                                if best.as_ref().is_none_or(|old| p.saved > old.saved) {
                                    best = Some(p);
                                }
                            }
                        }
                    }
                }
                if let Some(p) = best {
                    self.pairs += 1;
                    self.savings += p.saved;
                    skip[i] = true;
                    pairs.insert(p.left, p);
                    boundary = i + 1;
                }
                for key in keys {
                    let last = prior.entry(key).or_insert([None, None]);
                    if last[0].is_some_and(|j| atoms[j].target != node.target) {
                        last[1] = last[0];
                    }
                    last[0] = Some(i);
                }
            }
            for &q in sites {
                read[usize::from(q)] = i + 1;
            }
            write[usize::from(node.target)] = i + 1;
        }
        for (i, node) in atoms.iter().enumerate() {
            if let Some(p) = pairs.get(&i) {
                emit_pair(p, &atoms, self.width, emit);
            } else if !skip[i] {
                self.rows[node.start..node.end]
                    .iter()
                    .copied()
                    .for_each(&mut *emit);
            }
        }
        self.rows.clear();
    }
}
