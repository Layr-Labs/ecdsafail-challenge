//! D1 cuts (C7 = 7, C9b = 9, C9c = 10), baked by s20: accepted set hard-coded, no environment reads.
pub fn on(n: usize) -> bool { matches!(n, 7) }
pub fn brk(_n: usize) -> u32 { 0 }
