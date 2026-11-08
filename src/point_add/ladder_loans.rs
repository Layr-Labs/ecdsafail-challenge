//! A constant, a signed named variable, and a signed two-variable XOR
//! correspond to signed graph edges (0,0), (0,a), and (a,b).
//! The XOR around any cycle is its signed parity. Each non-tree edge can
//! therefore be parked at zero by XORing in just its forest path. Path
//! wires are never parked, so multiple such loans can coexist.
use super::{names::Names, Ladder};
#[derive(Debug, Clone)]
pub(super) struct Loan {
    pub wire: u16,
    pub terms: Vec<u16>,
    pub sign: bool,
}
impl Loan {
    pub fn cost(&self) -> usize {
        self.terms.len() + usize::from(self.sign)
    }
}
struct Edge {
    end: usize,
    next: usize,
    q: u16,
}
const NIL: usize = usize::MAX;
pub(super) struct Forest {
    table: Vec<(u32, u32, usize)>,
    stamp: u32,
    parent: Vec<usize>,
    heads: Vec<usize>,
    degree: Vec<usize>,
    tree: Vec<Edge>,
    chords: Vec<(usize, usize, u16)>,
    dad: Vec<usize>,
    up: Vec<u16>,
    depth: Vec<usize>,
    stack: Vec<usize>,
    seen_wire: Vec<u32>,
}
impl Forest {
    pub fn new(nq: usize) -> Self {
        Self {
            table: vec![(0, 0, 0); (4 * nq + 8).next_power_of_two()],
            stamp: 0,
            parent: Vec::new(),
            heads: Vec::new(),
            degree: Vec::new(),
            tree: Vec::new(),
            chords: Vec::new(),
            dad: Vec::new(),
            up: Vec::new(),
            depth: Vec::new(),
            stack: Vec::new(),
            seen_wire: vec![0; nq],
        }
    }
    fn reset(&mut self) {
        self.stamp = self
            .stamp
            .checked_add(1)
            .expect("over four billion candidates");
        self.parent.clear();
        self.heads.clear();
        self.tree.clear();
        self.chords.clear();
        self.degree.clear();
        self.stack.clear();
    }
    fn node(&mut self, key: u32) -> usize {
        let m = self.table.len() - 1;
        let mut i = ((key.wrapping_mul(0x9e3779b9) ^ (key >> 16)) as usize) & m;
        loop {
            let (stamp, k, v) = self.table[i];
            if stamp != self.stamp {
                let ix = self.parent.len();
                self.table[i] = (self.stamp, key, ix);
                self.parent.push(ix);
                self.heads.push(NIL);
                self.degree.push(1);
                return ix;
            }
            if k == key {
                return v;
            }
            i = (i + 1) & m;
        }
    }
    fn root(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let y = self.parent[x];
            self.parent[x] = self.parent[y];
            x = y;
        }
        x
    }
    fn visit(&mut self, id: u16, n: &Names, allowed: bool) {
        let e = n.wires[id as usize];
        let a = self.node(e.form.0);
        let b = self.node(e.form.1);
        let x = self.root(a);
        let y = self.root(b);
        if x == y {
            if allowed {
                self.chords.push((a, b, id));
            }
        } else {
            if self.degree[x] >= self.degree[y] {
                self.parent[y] = x;
                self.degree[x] += self.degree[y]
            } else {
                self.parent[x] = y;
                self.degree[y] += self.degree[x]
            }
            for (from, to) in [(a, b), (b, a)] {
                let i = self.tree.len();
                self.tree.push(Edge {
                    end: to,
                    next: self.heads[from],
                    q: id,
                });
                self.heads[from] = i;
            }
        }
    }
    pub fn choices(&mut self, n: &Names, l: &Ladder, amount: usize) -> Vec<Loan> {
        self.reset();
        // Insert unchanged controls first so a fundamental-cycle chord is a
        // usable target wire whenever the same cycle has a non-control choice.
        self.seen_wire[l.target as usize] = self.stamp;
        for &q in &l.control {
            self.seen_wire[q as usize] = self.stamp;
            self.visit(q, n, false);
        }
        for q in 0..n.wires.len() {
            if self.seen_wire[q] != self.stamp {
                self.visit(q as u16, n, true);
            }
        }
        if self.chords.is_empty() {
            return Vec::new();
        }
        let nodes = self.parent.len();
        self.dad.clear();
        self.dad.resize(nodes, NIL);
        self.depth.clear();
        self.depth.resize(nodes, 0);
        self.up.clear();
        self.up.resize(nodes, 0);
        for root in 0..nodes {
            if self.dad[root] != NIL {
                continue;
            }
            self.dad[root] = root;
            self.stack.push(root);
            while let Some(x) = self.stack.pop() {
                let mut j = self.heads[x];
                while j != NIL {
                    let e = &self.tree[j];
                    if self.dad[e.end] == NIL {
                        self.dad[e.end] = x;
                        self.depth[e.end] = self.depth[x] + 1;
                        self.up[e.end] = e.q;
                        self.stack.push(e.end);
                    }
                    j = e.next;
                }
            }
        }
        let mut loans = Vec::new();
        for &(mut a, mut b, w) in &self.chords {
            let mut terms = Vec::new();
            while a != b && terms.len() <= 12 {
                if self.depth[a] >= self.depth[b] {
                    terms.push(self.up[a]);
                    a = self.dad[a];
                } else {
                    terms.push(self.up[b]);
                    b = self.dad[b];
                }
            }
            if a != b || terms.len() > 12 {
                continue;
            }
            let sign = terms.iter().fold(n.wires[w as usize].sign, |p, &q| {
                p ^ n.wires[q as usize].sign
            });
            loans.push(Loan {
                wire: w,
                terms,
                sign,
            });
        }
        loans.sort_unstable_by_key(|z| (z.cost(), z.wire));
        loans.truncate(amount);
        loans
    }
}
