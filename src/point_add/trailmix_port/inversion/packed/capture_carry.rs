//! Fresh majority carries with measured cleanup and bounded checkpoint replay.
use crate::point_add::trailmix_port::circuit::{BorrowedQReg, Circuit, QReg};

pub(super) fn engine_room(bits: usize) -> usize {
    if std::env::var("MIDQ_ONEHOT_NOFOLD").ok().as_deref() == Some("1") { bits }
    else if bits >= 7 { 4.max(bits - 3) }
    else if bits >= 5 { 3.max(bits - 2) }
    else if bits >= 3 { bits - 1 }
    else { bits }
}

pub(super) fn plan(count: usize, available: usize) -> (usize, Vec<usize>) {
    let count_fresh = count.min(available.saturating_mul(available.saturating_add(1)) / 2);
    let chunks = crate::point_add::clean_chunk_plan::plan(count_fresh, available)
        .expect("triangular carry capacity");
    (count - count_fresh, chunks)
}

fn majority(c: &mut Circuit, a: &QReg, b: &QReg, cin: &QReg, out: &QReg) {
    c.cx(cin, a);
    c.cx(cin, b);
    c.ccx(a, b, out);
    c.cx(cin, out);
    c.cx(cin, b);
    c.cx(cin, a);
}

fn majority_phase(c: &mut Circuit, a: &QReg, b: &QReg, cin: &QReg) {
    // maj(a,b,cin) = a*b XOR a*cin XOR b*cin over F2.
    c.cz(a, b);
    c.cz(a, cin);
    c.cz(b, cin);
}

fn clear_majority(c: &mut Circuit, a: &QReg, b: &QReg, cin: &QReg, out: &QReg) {
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.with_condition(m, |c| majority_phase(c, a, b, cin));
    c.free_bit(m);
}

struct Boundary<'a> {
    wire: BorrowedQReg<'a>,
    start: usize,
    end: usize,
}

pub(super) struct Carries<'a> {
    a: &'a [&'a QReg],
    b: &'a [&'a QReg],
    initial: &'a QReg,
    sizes: Vec<usize>,
    chunk: usize,
    start: usize,
    chain: Vec<BorrowedQReg<'a>>,
    boundaries: Vec<Boundary<'a>>,
    scratch: Vec<&'a QReg>,
}

impl<'a> Carries<'a> {
    pub(super) fn new(a: &'a [&'a QReg], b: &'a [&'a QReg], initial: &'a QReg,
                      start: usize, sizes: Vec<usize>, scratch: &[&'a QReg]) -> Self {
        Self { a, b, initial, sizes, chunk: 0, start, chain: Vec::new(),
            boundaries: Vec::new(), scratch: scratch.to_vec() }
    }

    pub(super) fn current(&self) -> &QReg {
        self.chain.last().map(|q| &**q)
            .unwrap_or_else(|| self.boundaries.last().map_or(self.initial, |b| &*b.wire))
    }

    fn alloc(&mut self, c: &mut Circuit) -> BorrowedQReg<'a> {
        match self.scratch.pop() {
            Some(q) => BorrowedQReg::Borrowed(q),
            None => BorrowedQReg::Owned(c.alloc_qreg("ccmp.carry")),
        }
    }

    fn release(&mut self, c: &mut Circuit, wire: BorrowedQReg<'a>) {
        match wire {
            BorrowedQReg::Owned(q) => c.zero_and_free(q),
            BorrowedQReg::Borrowed(q) => self.scratch.push(q),
        }
    }

    pub(super) fn advance(&mut self, c: &mut Circuit, i: usize) {
        assert_eq!(i, self.start + self.chain.len());
        let next = self.alloc(c);
        majority(c, self.a[i], self.b[i], self.current(), &next);
        self.chain.push(next);
        if self.chain.len() == self.sizes[self.chunk] && self.chunk + 1 < self.sizes.len() {
            let end = i + 1;
            let wire = self.chain.pop().unwrap();
            self.clear_chain(c);
            self.boundaries.push(Boundary { wire, start: self.start, end });
            self.start = end;
            self.chunk += 1;
        }
    }

    fn clear_chain(&mut self, c: &mut Circuit) {
        while let Some(wire) = self.chain.pop() {
            let i = self.start + self.chain.len();
            clear_majority(c, self.a[i], self.b[i], self.current(), &wire);
            self.release(c, wire);
        }
    }

    pub(super) fn finish(mut self, c: &mut Circuit) {
        self.clear_chain(c);
        while let Some(boundary) = self.boundaries.pop() {
            let m = c.alloc_bit();
            c.hmr(&boundary.wire, m);
            self.release(c, boundary.wire);
            self.start = boundary.start;
            c.with_condition(m, |c| {
                for i in boundary.start..boundary.end - 1 {
                    let next = self.alloc(c);
                    majority(c, self.a[i], self.b[i], self.current(), &next);
                    self.chain.push(next);
                }
                let i = boundary.end - 1;
                majority_phase(c, self.a[i], self.b[i], self.current());
                self.clear_chain(c);
            });
            c.free_bit(m);
        }
    }
}
