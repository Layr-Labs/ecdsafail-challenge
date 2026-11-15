//! D2 cuts (C1 = 1, C2 = 2, C3 = 3, C4A = 4, C4B = 5, C5 = 6, C4C = 7), baked by s25: shipped set hard-coded, no environment reads, off in fused columns.
pub fn on(n: usize) -> bool { !super::devsw_a::fz_blocked("") && matches!(n, 1|2|3) }
pub fn brk(_n: usize) -> u32 { 0 }
