//! D1 cuts (C7 = 7, C9b = 9, C9c = 10), baked by s25: shipped set hard-coded, no environment reads, off in fused columns.
pub fn on(n: usize) -> bool { !super::devsw_a::fz_blocked("") && matches!(n, 99) }
pub fn brk(_n: usize) -> u32 { 0 }
