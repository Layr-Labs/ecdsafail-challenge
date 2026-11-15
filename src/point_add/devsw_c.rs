//! s17 clean-scratch cuts (A10..A20), baked by s20 (accepted set hard-coded, no environment reads, no diagnostics).
pub const NC: usize = 21;
pub fn on(n: usize) -> bool { matches!(n, 10|11|12|13|14|15|17|19) }
pub fn brk(_n: usize) -> u32 { 0 }
pub fn mark() -> bool { false }
pub fn tally(_site: u32, _ladder: u64, _lanes: u64) {}
pub fn print_marks() {}
pub fn print_tally() {}
/// numeric level of a switch
pub fn lvl(n: usize) -> u32 { match n { 10 => 1, 11 => 2, 12 => 1, 13 => 1, 14 => 1, 15 => 1, 17 => 1, 19 => 1, _ => 0 } }
pub fn dbg() -> bool { false }
pub fn count_mark(_id: u32) {}
