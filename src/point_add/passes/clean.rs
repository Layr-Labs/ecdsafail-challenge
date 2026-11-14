//! Replace borrowed-wire MCX ladders using wires that are provably zero on this branch.
use super::{ccx, cx, emit_ladder, x, Atom, Controls, Ladder, Row, NONE};
use super::super::values::Values;

#[derive(Default)]
pub struct Counts {
    pub ladders: u64,
    pub replaced: u64,
    pub saved: u64,
}

pub struct Clean {
    facts: Values,
    decoder: Ladder,
    rows: Vec<Row>,
    size: usize,
    ports_closed: bool,
    pub counts: Counts,
}

fn dirty_cost(n: usize) -> usize {
    match n { 0 | 1 => 0, 2 => 1, _ => 4 * (n - 2) }
}

impl Clean {
    pub fn new(width: usize, size: usize) -> Self {
        Self {
            facts: Values::new(width), decoder: Ladder::new(width, size),
            rows: Vec::with_capacity(size), size, ports_closed: false, counts: Counts::default(),
        }
    }

    fn observe(&mut self, [kind,a,b,c]: Row) {
        let f = &mut self.facts;
        match kind {
            2 => f.unknown(b as usize),
            6 if b==NONE => f.set(a as usize, f.wire[a as usize]^1),
            6 => f.unknown(a as usize),
            8 if c==NONE => {
                let v = f.sum(f.wire[a as usize], f.wire[b as usize]);
                f.set(b as usize, v);
            }
            8 => f.unknown(b as usize),
            12 => f.set(a as usize, 0),
            13 => {
                let v = f.product(f.wire[a as usize], f.wire[b as usize]);
                let out = f.sum(v, f.wire[c as usize]);
                f.set(c as usize, out);
            }
            15 => f.enter(),
            16 => f.leave(),
            1|3..=5|7|9|18 => (),
            _ => panic!("unsupported compact row {kind}"),
        }
    }

    fn replace(&mut self, node: &Atom, emit: &mut impl FnMut(Row)) -> bool {
        let Controls::Ladder { sites, dirty } = &node.controls else { return false; };
        self.counts.ladders += 1;
        let n = sites.len();
        let target = node.target;
        let old = node.cost();
        let mut product = 1;
        for &q in sites { product = self.facts.product(product, self.facts.wire[q as usize]); }
        let mut saved = 0;
        if product <= 1 {
            if product==1 { emit(x(target)); }
            saved = old;
        } else {
            let mut zero = Vec::with_capacity(n.saturating_sub(2));
            if n>2 {
                'words: for (i,&word) in self.facts.zero.iter().enumerate() {
                    let mut bits = word;
                    while bits!=0 {
                        let q = (64*i+bits.trailing_zeros() as usize) as u16;
                        bits &= bits-1;
                        if q!=target && sites.binary_search(&q).is_err() {
                            zero.push(q);
                            if zero.len()==n-2 { break 'words; }
                        }
                    }
                }
            }
            let k = zero.len();
            // Make k clean prefix products, leaving n-k controls for the ordinary dirty ladder.
            let cost = 2*k+dirty_cost(n-k);
            if cost<old {
                let mut first = sites[0];
                for (i,&aux) in zero.iter().enumerate() {
                    emit(ccx(first,sites[i+1],aux));
                    first = aux;
                }
                let rest: Vec<_> = std::iter::once(first).chain(sites[k+1..].iter().copied()).collect();
                let borrowed: Vec<_> = dirty.iter().copied().filter(|q| !zero.contains(q)).collect();
                assert!(borrowed.len()>=rest.len().saturating_sub(2));
                match rest.as_slice() {
                    [a] => emit(cx(*a,target)),
                    _ => emit_ladder(&rest,target,&borrowed,emit),
                }
                for i in (0..k).rev() {
                    let a = if i==0 {sites[0]} else {zero[i-1]};
                    emit(ccx(a,sites[i+1],zero[i]));
                }
                saved = old-cost;
            }
        }
        // The decoded ladder changes only the target irrespective of the chosen implementation.
        let out = self.facts.sum(self.facts.wire[target as usize],product);
        self.facts.set(target as usize,out);
        self.counts.replaced += u64::from(saved!=0);
        self.counts.saved += saved as u64;
        saved!=0
    }

    fn flush(&mut self, emit: &mut impl FnMut(Row)) {
        if self.rows.is_empty() { return; }
        let mut rows = std::mem::take(&mut self.rows);
        for node in self.decoder.lift(&rows) {
            if let Controls::Ladder {..} = node.controls {
                if !self.replace(&node, emit) {
                    for &r in &rows[node.start..node.end] { emit(r); }
                }
            } else {
                let r = rows[node.start];
                self.observe(r);
                emit(r);
            }
        }
        rows.clear();
        self.rows=rows;
    }

    pub fn push(&mut self, r: Row, emit: &mut impl FnMut(Row)) {
        match r[0] {
            2 => assert!(!self.ports_closed, "late input declaration"),
            1 | 18 => (),
            _ => self.ports_closed = true,
        }
        self.rows.push(r);
        if self.rows.len()==self.size { self.flush(emit); }
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        self.flush(emit);
        self.facts.finish();
    }
}
