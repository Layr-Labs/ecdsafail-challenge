//! Pebbling plans for an AND ladder `node(j) = node(j-1) AND lit(j-1)` (node 0 is a given wire) under a
//! budget of `b` simultaneously live ladder nodes.  Placing a node costs 1 T (`AndC`); removing node j needs
//! node j-1 live and costs 0 T forward but 1 T when the block is replayed in reverse (the park detector's
//! erase sweep replays its compute part), so every plan is costed as placements + removals.
//!
//! `plan_visits(n, b)` visits nodes 1..n in ascending order (each `Visit(j)` happens while node j is live) and
//! may leave nodes live at the end (the replay removes them).  Optimal over the recursive split family
//!   VT(n, b) = n                                    if n <= b
//!            = min_m V(m, b) + VT(n - m, b - 1)     (checkpoint at m, kept to the end)
//!   V(n, b)  = 2n - 1                               if n <= b   (place 1..n, remove n-1..1)
//!            = min_m V(m, b) + V(n - m, b - 1) + R(m, b - 1)
//!   R(n, b)  = 2n - 1 if n <= b, else min_j R(j, b) + R(n - j, b - 1) + R(j, b - 1)   (place node n alone)
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    Place(usize),
    Remove(usize),
    Visit(usize),
}

const INF: u64 = u64::MAX / 4;

#[derive(Default)]
struct Dp {
    r: HashMap<(usize, usize), (u64, usize)>,
    v: HashMap<(usize, usize), (u64, usize)>,
    vt: HashMap<(usize, usize), (u64, usize)>,
}

impl Dp {
    fn r(&mut self, n: usize, b: usize) -> u64 {
        if n == 0 {
            return 0;
        }
        if b == 0 {
            return INF;
        }
        if n <= b {
            return 2 * n as u64 - 1;
        }
        if let Some(&(c, _)) = self.r.get(&(n, b)) {
            return c;
        }
        let mut best = (INF, 0);
        for j in 1..n {
            let c = self.r(j, b).saturating_add(self.r(n - j, b - 1)).saturating_add(self.r(j, b - 1));
            if c < best.0 {
                best = (c, j);
            }
        }
        self.r.insert((n, b), best);
        best.0
    }
    fn v(&mut self, n: usize, b: usize) -> u64 {
        if n == 0 {
            return 0;
        }
        if b == 0 {
            return INF;
        }
        if n <= b {
            return 2 * n as u64 - 1;
        }
        if let Some(&(c, _)) = self.v.get(&(n, b)) {
            return c;
        }
        let mut best = (INF, 0);
        for m in 1..n {
            let c = self.v(m, b).saturating_add(self.v(n - m, b - 1)).saturating_add(self.r(m, b - 1));
            if c < best.0 {
                best = (c, m);
            }
        }
        self.v.insert((n, b), best);
        best.0
    }
    fn vt(&mut self, n: usize, b: usize) -> u64 {
        if n == 0 {
            return 0;
        }
        if b == 0 {
            return INF;
        }
        if n <= b {
            return n as u64;
        }
        if let Some(&(c, _)) = self.vt.get(&(n, b)) {
            return c;
        }
        let mut best = (INF, 0);
        for m in 1..n {
            let c = self.v(m, b).saturating_add(self.vt(n - m, b - 1));
            if c < best.0 {
                best = (c, m);
            }
        }
        self.vt.insert((n, b), best);
        best.0
    }
    fn gen_r(&mut self, s: usize, e: usize, b: usize, out: &mut Vec<Step>) {
        let n = e - s;
        if n == 0 {
            return;
        }
        if n <= b {
            for j in s + 1..=e {
                out.push(Step::Place(j));
            }
            for j in (s + 1..e).rev() {
                out.push(Step::Remove(j));
            }
            return;
        }
        self.r(n, b);
        let j = self.r[&(n, b)].1;
        self.gen_r(s, s + j, b, out);
        self.gen_r(s + j, e, b - 1, out);
        self.gen_unr(s, s + j, b - 1, out);
    }
    fn gen_unr(&mut self, s: usize, e: usize, b: usize, out: &mut Vec<Step>) {
        let mut tmp = Vec::new();
        self.gen_r(s, e, b, &mut tmp);
        for st in tmp.into_iter().rev() {
            out.push(match st {
                Step::Place(j) => Step::Remove(j),
                Step::Remove(j) => Step::Place(j),
                Step::Visit(_) => continue,
            });
        }
    }
    fn gen_v(&mut self, s: usize, e: usize, b: usize, out: &mut Vec<Step>) {
        let n = e - s;
        if n == 0 {
            return;
        }
        if n <= b {
            for j in s + 1..=e {
                out.push(Step::Place(j));
                out.push(Step::Visit(j));
            }
            for j in (s + 1..e).rev() {
                out.push(Step::Remove(j));
            }
            return;
        }
        self.v(n, b);
        let m = self.v[&(n, b)].1;
        self.gen_v(s, s + m, b, out);
        self.gen_v(s + m, e, b - 1, out);
        self.gen_unr(s, s + m, b - 1, out);
    }
    fn gen_vt(&mut self, s: usize, e: usize, b: usize, out: &mut Vec<Step>) {
        let n = e - s;
        if n == 0 {
            return;
        }
        if n <= b {
            for j in s + 1..=e {
                out.push(Step::Place(j));
                out.push(Step::Visit(j));
            }
            return;
        }
        self.vt(n, b);
        let m = self.vt[&(n, b)].1;
        self.gen_v(s, s + m, b, out);
        self.gen_vt(s + m, e, b - 1, out);
    }
}

/// Plan visiting nodes 1..=n ascending with at most `b` live ladder nodes (node 0 not counted).
/// Returns (steps, cost = placements + removals).  Panics if `b` is too small for `n` (cost infinite).
pub fn plan_visits(n: usize, b: usize) -> (Vec<Step>, u64) {
    let mut dp = Dp::default();
    let c = dp.vt(n, b);
    assert!(c < INF, "pebble budget {b} too small for a ladder of {n}");
    let mut out = Vec::new();
    dp.gen_vt(0, n, b, &mut out);
    // self-check: legality, budget and cost
    let mut live = std::collections::BTreeSet::new();
    let (mut pl, mut rm) = (0u64, 0u64);
    for st in &out {
        match *st {
            Step::Place(j) => {
                assert!(j == 1 || live.contains(&(j - 1)), "place {j} without {}", j - 1);
                assert!(live.insert(j));
                assert!(live.len() <= b, "budget exceeded");
                pl += 1;
            }
            Step::Remove(j) => {
                assert!(j == 1 || live.contains(&(j - 1)), "remove {j} without {}", j - 1);
                assert!(live.remove(&j));
                rm += 1;
            }
            Step::Visit(j) => assert!(live.contains(&j)),
        }
    }
    assert_eq!(pl + rm, c);
    (out, c)
}

/// Cost only (placements + removals) of the visiting plan; `None` when the budget is too small.
pub fn visit_cost(n: usize, b: usize) -> Option<u64> {
    let mut dp = Dp::default();
    let c = dp.vt(n, b);
    (c < INF).then_some(c)
}
