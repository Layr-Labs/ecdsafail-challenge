//! s16 cuts (B_top), baked by s25 (shipped set hard-coded, no environment reads).
pub fn on(n: &str) -> bool { !super::devsw_a::fz_blocked(n) && matches!(n, "P1R2A"|"P1R2B"|"P1R3"|"P1R4A"|"P1R4B"|"P1R6A"|"P1R6B"|"P2F1"|"P2F3A"|"P2F3B"|"P2F3C"|"P2F3D"|"P2F4A"|"P2F4C"|"P2F5A"|"P2F5B"|"P2F7A"|"P2F7B"|"P2F8"|"P2F9") }
pub fn brk(_n: &str) -> u32 { 0 }
pub fn site(_n: &str, _tag: u32) -> bool { true }
