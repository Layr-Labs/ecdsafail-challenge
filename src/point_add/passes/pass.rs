use super::base;
use super::cleanup::{Cleanup, Row};

pub struct Pass {
    pub cleanup: Cleanup,
    pub fanout_merges: u64,
    depth: usize,
    rounds: usize,
}

impl Pass {
    pub fn new(width: usize, scratch: u16, rounds: usize) -> Self {
        Self {cleanup: Cleanup::new(width, scratch), fanout_merges: 0, depth: 0, rounds}
    }
    pub fn chunk(&mut self, rows: Vec<Row>, mut emit: impl FnMut(Row)) {
        let end = base::stack_after(self.depth, &rows);
        let (rewritten, merges) = if self.rounds > 0 {
            base::optimize(rows, self.depth, end, self.rounds)
        } else { (rows, 0) };
        self.depth = end;
        self.fanout_merges += merges;
        for row in rewritten { self.cleanup.push(row, &mut emit); }
    }
    pub fn finish(&self) {
        assert_eq!(self.depth, 0);
        self.cleanup.finish();
    }
}
