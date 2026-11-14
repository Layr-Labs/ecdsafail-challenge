//! Fuse multi-controlled toggles recognized from complete dirty-ancilla ladders.
//! Inputs/outputs are eight-byte compact rows; no fresh quantum/classical sites.
use std::collections::HashMap;

pub type Row = [u16; 4];
const NONE: u16 = u16::MAX;
const MAX_HALF: usize = 64;
const MAX_REPLAY: usize = 2048;
const MAX_SWEEPS: usize = 8;

fn x(q: u16) -> Row {
    [6, q, NONE, NONE]
}
fn cx(c: u16, q: u16) -> Row {
    [8, c, q, NONE]
}
fn ccx(a: u16, b: u16, q: u16) -> Row {
    [13, a, b, q]
}

enum Controls {
    X,
    Cx(u16),
    Ccx([u16; 2]),
    Ladder { sites: Vec<u16>, dirty: Vec<u16> },
    Barrier,
}
struct Atom {
    start: usize,
    end: usize,
    target: u16,
    controls: Controls,
}
impl Atom {
    fn sites(&self) -> &[u16] {
        match &self.controls {
            Controls::X | Controls::Barrier => &[],
            Controls::Cx(c) => std::slice::from_ref(c),
            Controls::Ccx(both) => both,
            Controls::Ladder { sites, .. } => sites,
        }
    }
    fn dirty(&self) -> &[u16] {
        if let Controls::Ladder { dirty, .. } = &self.controls {
            dirty
        } else {
            &[]
        }
    }
    fn cost(&self) -> usize {
        if self.sites().len() >= 2 {
            self.end - self.start
        } else {
            0
        }
    }
}

// H = A D where D walks down the ladder and returns, or H = D A.
// The second H removes every contribution from the original dirty bits.
fn decode_half(half: &[Row], reverse: bool) -> Option<(Vec<u16>, Vec<u16>, u16)> {
    let at = |i: usize| {
        if reverse {
            half[half.len() - 1 - i]
        } else {
            half[i]
        }
    };
    let a = at(0);
    if a[0] != 13 {
        return None;
    }
    let mut sites = vec![a[1], a[2]];
    let mut dirty = vec![a[3]];
    let mut last = a[3];
    for i in 1..=half.len() / 2 {
        let gate = at(i);
        if gate[0] != 13 || gate != at(half.len() - i) {
            return None;
        }
        let next = if gate[1] == last {
            gate[2]
        } else if gate[2] == last {
            gate[1]
        } else {
            return None;
        };
        let target = gate[3];
        if dirty.contains(&next) || dirty.contains(&target) || sites.contains(&target) {
            return None;
        }
        if !sites.contains(&next) {
            sites.push(next);
        }
        if i < half.len() / 2 {
            dirty.push(target);
        }
        last = target;
    }
    sites.sort_unstable();
    Some((sites, dirty, last))
}

#[derive(Default)]
pub struct Metrics {
    pub input: u64,
    pub output: u64,
    pub input_ccx: u64,
    pub output_ccx: u64,
    pub macros: u64,
    pub cancel: u64,
    pub distribute: u64,
    pub factor: u64,
    pub subset: u64,
    pub polarity: u64,
    pub swept: u64,
}
pub struct Ladder {
    width: usize,
    limit: usize,
    rows: Vec<Row>,
    pub metrics: Metrics,
}

#[derive(Clone, Copy)]
enum Rewrite {
    Same {
        polarity: u64,
    },
    Factor {
        pivot: u16,
        other: u16,
        flip: bool,
    },
    Subset {
        broad: usize,
        pivot: u16,
        flip: bool,
    },
}
#[derive(Clone, Copy)]
struct Pair {
    before: usize,
    after: usize,
    rewrite: Rewrite,
    saved: usize,
}

fn cost_for(n: usize) -> usize {
    match n {
        0 | 1 => 0,
        2 => 1,
        _ => 4 * (n - 2),
    }
}

fn emit_ladder(controls: &[u16], target: u16, dirty: &[u16], emit: &mut impl FnMut(Row)) {
    match controls {
        [] => emit(x(target)),
        [a] => emit(cx(*a, target)),
        [a, b] => emit(ccx(*a, *b, target)),
        _ => {
            let n = controls.len();
            let d = &dirty[..n - 2];
            let a = ccx(controls[0], controls[1], d[0]);
            let step = |i: usize| {
                ccx(
                    d[i - 2],
                    controls[i],
                    if i + 1 == n { target } else { d[i - 1] },
                )
            };
            for _ in 0..2 {
                emit(a);
                for i in 2..n {
                    emit(step(i));
                }
                for i in (2..n - 1).rev() {
                    emit(step(i));
                }
            }
        }
    }
}

// Pull the later all-ones test back through a reversible permutation acting
// wholly on its controls. Only one assignment passes, so inverse evaluation
// requires just one bit per site, including for internal nonlinear writes.
fn polarity(atoms: &[Atom], j: usize, i: usize, writes: &[usize]) -> Option<u64> {
    let sites = atoms[i].sites();
    if sites.iter().all(|q| writes[usize::from(*q)] <= j + 1) {
        return Some(0);
    }
    if i - j > MAX_REPLAY {
        return None;
    }
    let mut flipped = 0u64;
    for node in atoms[j + 1..i].iter().rev() {
        let Ok(t) = sites.binary_search(&node.target) else {
            continue;
        };
        let mut enabled = true;
        for q in node.sites() {
            let c = sites.binary_search(q).ok()?;
            enabled &= flipped & (1 << c) == 0;
        }
        if enabled {
            flipped ^= 1 << t;
        }
    }
    Some(flipped)
}

fn proposal(atoms: &[Atom], j: usize, i: usize, flipped: u64) -> Option<Pair> {
    let (a, b) = (&atoms[j], &atoms[i]);
    let (u, v) = (a.sites(), b.sites());
    if a.cost() == 1 && b.cost() == 1 {
        return None;
    }
    let (rewrite, replacement);
    if u == v {
        let same_target = a.target == b.target;
        replacement = if same_target { 0 } else { a.cost() }
            + if flipped == 0 {
                0
            } else {
                cost_for(v.len() - 1)
            };
        rewrite = Rewrite::Same { polarity: flipped };
    } else {
        if a.target != b.target {
            return None;
        }
        let mut before = u.iter().copied().filter(|q| v.binary_search(q).is_err());
        let mut after = v.iter().copied().filter(|q| u.binary_search(q).is_err());
        let old = before.next();
        let new = after.next();
        if before.next().is_some() || after.next().is_some() {
            return None;
        }
        match (old, new) {
            (Some(pivot), Some(other)) => {
                let bit = 1 << v.binary_search(&other).unwrap();
                if flipped & !bit != 0 {
                    return None;
                }
                rewrite = Rewrite::Factor {
                    pivot,
                    other,
                    flip: flipped != 0,
                };
                replacement = a.cost();
            }
            (None, Some(pivot)) => {
                let bit = 1 << v.binary_search(&pivot).unwrap();
                if flipped & !bit != 0 {
                    return None;
                }
                rewrite = Rewrite::Subset {
                    broad: i,
                    pivot,
                    flip: flipped == 0,
                };
                replacement = b.cost();
            }
            (Some(pivot), None) if flipped == 0 => {
                rewrite = Rewrite::Subset {
                    broad: j,
                    pivot,
                    flip: true,
                };
                replacement = a.cost();
            }
            _ => return None,
        }
    }
    let saved = a.cost() + b.cost();
    (saved > replacement).then(|| Pair {
        before: j,
        after: i,
        rewrite,
        saved: saved - replacement,
    })
}

fn emit_pair(pair: Pair, atoms: &[Atom], rows: &[Row], emit: &mut impl FnMut(Row)) {
    let a = &atoms[pair.before];
    let b = &atoms[pair.after];
    let original = |node: &Atom, output: &mut dyn FnMut(Row)| {
        for &row in &rows[node.start..node.end] {
            output(row);
        }
    };
    match pair.rewrite {
        Rewrite::Same { polarity } => {
            if a.target != b.target {
                emit(cx(a.target, b.target));
                original(a, emit);
                emit(cx(a.target, b.target));
            }
            if polarity != 0 {
                let pivot = polarity.trailing_zeros() as usize;
                let p = a.sites()[pivot];
                let controls: Vec<_> = a.sites().iter().copied().filter(|&q| q != p).collect();
                let affine: Vec<_> = a
                    .sites()
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != pivot && polarity & (1 << i) != 0)
                    .map(|(_, q)| *q)
                    .collect();
                for &q in &affine {
                    emit(cx(p, q));
                    emit(x(q));
                }
                let dirty: Vec<_> = a
                    .dirty()
                    .iter()
                    .copied()
                    .filter(|&q| q != b.target)
                    .collect();
                emit_ladder(&controls, b.target, &dirty, emit);
                for &q in affine.iter().rev() {
                    emit(x(q));
                    emit(cx(p, q));
                }
            }
        }
        Rewrite::Factor { pivot, other, flip } => {
            emit(cx(other, pivot));
            if flip {
                emit(x(pivot));
            }
            original(a, emit);
            if flip {
                emit(x(pivot));
            }
            emit(cx(other, pivot));
        }
        Rewrite::Subset { broad, pivot, flip } => {
            if flip {
                emit(x(pivot));
            }
            original(&atoms[broad], emit);
            if flip {
                emit(x(pivot));
            }
        }
    }
}

impl Ladder {
    pub fn new(width: usize, limit: usize) -> Self {
        assert!(width > 0 && width < usize::from(NONE) && limit > 0);
        Self {
            width,
            limit,
            rows: Vec::with_capacity(limit),
            metrics: Metrics::default(),
        }
    }
    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        let [k, a, b, t] = row;
        let valid = |x| usize::from(x) < self.width;
        match k {
            6 | 7 | 12 => assert!(valid(a)),
            8 | 9 => assert!(valid(a) && valid(b) && a != b),
            13 => assert!(valid(a) && valid(b) && valid(t) && a != b && a != t && b != t),
            _ => (),
        }
        self.metrics.input += 1;
        self.metrics.input_ccx += u64::from(k == 13);
        self.rows.push(row);
        if self.rows.len() == self.limit {
            self.run(emit);
        }
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        if !self.rows.is_empty() {
            self.run(emit);
        }
    }
    fn run(&mut self, emit: &mut impl FnMut(Row)) {
        let mut rows = std::mem::take(&mut self.rows);
        let mut buffer = Vec::with_capacity(rows.len());
        let mut reversed = false;
        let mut stalls = 0;
        for round in 0..MAX_SWEEPS {
            if round > 0 {
                rows.reverse();
                reversed = !reversed;
            }
            let (any, saved) = self.sweep(&rows, &mut |r| buffer.push(r));
            if saved > 0 {
                stalls = 0;
                std::mem::swap(&mut rows, &mut buffer);
            } else {
                stalls += 1;
            }
            buffer.clear();
            if !any || stalls == 2 {
                break;
            }
        }
        if reversed {
            rows.reverse();
        }
        for &r in &rows {
            self.metrics.output += 1;
            self.metrics.output_ccx += u64::from(r[0] == 13);
            emit(r);
        }
        self.rows = rows;
        self.rows.clear();
    }
    fn sweep(&mut self, rows: &[Row], emit: &mut impl FnMut(Row)) -> (bool, usize) {
        if !rows.windows(4).any(|s| s.iter().all(|r| r[0] == 13)) {
            return (false, 0);
        }
        self.metrics.swept += 1;
        let atoms = self.lift(rows);
        if !atoms.iter().any(|a| a.end - a.start > 1) {
            return (false, 0);
        }
        let mut at = vec![None; atoms.len()];
        let mut drop = vec![false; atoms.len()];
        let mut read = vec![0; self.width];
        let mut write = vec![0; self.width];
        let mut exact = HashMap::<Vec<u16>, usize>::new();
        let mut same_target = HashMap::<(u16, Vec<u16>), usize>::new();
        let mut omit_one = HashMap::<(u16, Vec<u16>), usize>::new();
        let mut boundary = 0;
        let mut saved = 0;
        for (i, node) in atoms.iter().enumerate() {
            if let Controls::Barrier = node.controls {
                boundary = i + 1;
                continue;
            }
            let t = usize::from(node.target);
            let sites = node.sites();
            if sites.len() >= 2 {
                let mut best = None;
                let mut attempt = |j: usize| {
                    if j + 1 <= boundary || read[t] > j + 1 {
                        return;
                    }
                    let Some(flips) = polarity(&atoms, j, i, &write) else {
                        return;
                    };
                    if let Some(p) = proposal(&atoms, j, i, flips) {
                        if best.is_none_or(|old: Pair| p.saved > old.saved) {
                            best = Some(p);
                        }
                    }
                };
                if let Some(&j) = exact.get(sites) {
                    attempt(j);
                }
                let full = (node.target, sites.to_vec());
                if let Some(&j) = omit_one.get(&full) {
                    attempt(j);
                }
                // Ordinary two-control gates only need to match a larger prior gate.
                // Many such gates occur in runs; only longer gates use their subsets.
                if sites.len() > 2 || node.cost() > 1 {
                    for cut in 0..sites.len() {
                        let key = (
                            node.target,
                            sites[..cut]
                                .iter()
                                .chain(&sites[cut + 1..])
                                .copied()
                                .collect(),
                        );
                        if let Some(&j) = omit_one.get(&key) {
                            attempt(j);
                        }
                        if let Some(&j) = same_target.get(&key) {
                            attempt(j);
                        }
                    }
                }
                if let Some(p) = best {
                    at[p.before] = Some(p);
                    drop[i] = true;
                    boundary = i + 1;
                    saved += p.saved;
                    match p.rewrite {
                        Rewrite::Same { polarity } => {
                            if atoms[p.before].target == node.target {
                                self.metrics.cancel += 1;
                            } else {
                                self.metrics.distribute += 1;
                            }
                            self.metrics.polarity += u64::from(polarity != 0);
                        }
                        Rewrite::Factor { .. } => self.metrics.factor += 1,
                        Rewrite::Subset { .. } => self.metrics.subset += 1,
                    }
                }
                if sites.len() > 2 || node.cost() > 1 {
                    for cut in 0..sites.len() {
                        let key = (
                            node.target,
                            sites[..cut]
                                .iter()
                                .chain(&sites[cut + 1..])
                                .copied()
                                .collect(),
                        );
                        omit_one.insert(key, i);
                    }
                    exact.insert(sites.to_vec(), i);
                }
                same_target.insert(full, i);
            }
            for q in sites {
                read[usize::from(*q)] = i + 1;
            }
            write[t] = i + 1;
        }
        if saved > 0 {
            for (i, node) in atoms.iter().enumerate() {
                if let Some(p) = at[i] {
                    emit_pair(p, &atoms, rows, emit);
                } else if !drop[i] {
                    for &row in &rows[node.start..node.end] {
                        emit(row);
                    }
                }
            }
        }
        (true, saved)
    }
}

impl Ladder { fn lift(&mut self, rows: &[Row]) -> Vec<Atom> {
        let mut normalized = rows.to_vec();
        let mut next = vec![rows.len(); rows.len()];
        let mut same = HashMap::new();
        for i in (0..rows.len()).rev() {
            let row = &mut normalized[i];
            if row[0] == 13 {
                if row[1] > row[2] {
                    row.swap(1, 2);
                }
                if let Some(j) = same.insert(*row, i) {
                    next[i] = j;
                }
            }
        }
        let mut atoms = Vec::with_capacity(rows.len());
        let mut i = 0;
        while i < rows.len() {
            let [k, a, b, c] = normalized[i];
            let mut node = Atom {
                start: i,
                end: i + 1,
                target: NONE,
                controls: Controls::Barrier,
            };
            if k == 13 {
                node.target = c;
                node.controls = Controls::Ccx([a, b]);
                let mut j = next[i];
                while j < rows.len() && j - i <= MAX_HALF && j + (j - i) <= rows.len() {
                    let length = j - i;
                    if length % 2 == 0 && normalized[i..j] == normalized[j..j + length] {
                        let h = &normalized[i..j];
                        if let Some((sites, dirty, target)) =
                            decode_half(h, false).or_else(|| decode_half(h, true))
                        {
                            node.end = j + length;
                            node.target = target;
                            node.controls = Controls::Ladder { sites, dirty };
                        }
                    }
                    j = next[j];
                }
            } else if k == 6 && b == NONE {
                node.target = a;
                node.controls = Controls::X;
            } else if k == 8 && c == NONE {
                node.target = b;
                node.controls = Controls::Cx(a);
            }
            i = node.end;
            if node.end - node.start > 1 {
                self.metrics.macros += 1;
            }
            atoms.push(node);
        }
atoms
} }
#[path="group.rs"] pub mod group;
#[path="clean.rs"] pub mod clean;
#[path="rotate.rs"] pub mod rotate;
