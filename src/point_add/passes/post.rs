//! Run the established branch peephole on complete output blocks after dirty-ladder synthesis.
use super::base;
pub type Row = [u16; 4];

pub struct Post {
    pending: Vec<Row>,
    depth: usize,
    pub saved_ccx: u64,
}
impl Post {
    pub fn new() -> Self {
        Self { pending: Vec::with_capacity(base::CHUNK), depth: 0, saved_ccx: 0 }
    }
    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        self.pending.push(row);
        if self.pending.len() == base::CHUNK { self.flush(emit); }
    }
    fn flush(&mut self, emit: &mut impl FnMut(Row)) {
        if self.pending.is_empty() { return; }
        let input = std::mem::take(&mut self.pending);
        let leaving = base::stack_after(self.depth, &input);
        let before = input.iter().filter(|r| r[0] == 13).count();
        let (rows, _) = base::optimize(input, self.depth, leaving, 3);
        let after = rows.iter().filter(|r| r[0] == 13).count();
        assert!(after <= before);
        self.saved_ccx += (before - after) as u64;
        self.depth = leaving;
        self.pending = rows;
        for row in self.pending.drain(..) { emit(row); }
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        self.flush(emit);
        assert_eq!(self.depth, 0, "unclosed incoming scope");
    }
}
