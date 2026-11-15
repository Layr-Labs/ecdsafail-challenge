//! s15 cuts A1..A9, baked by s20 (accepted set hard-coded, no environment reads).
pub fn on(n: usize) -> bool { matches!(n, 1|2|3|4|5|6|8) }
pub fn brk(_n: usize) -> u32 { 0 }
/// A5 masked-digit sub-edit: never reached at 740 (identical stream), kept off
pub fn a5m() -> bool { false }
