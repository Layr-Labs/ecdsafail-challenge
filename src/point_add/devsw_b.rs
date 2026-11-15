//! s16 cuts (B_top), baked by s20 (accepted set hard-coded, no environment reads).
pub fn on(n: &str) -> bool { matches!(n, "") }
pub fn brk(_n: &str) -> u32 { 0 }
pub fn site(_n: &str, _tag: u32) -> bool { true }
