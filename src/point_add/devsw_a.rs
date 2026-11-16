//! s15 cuts A1..A9, baked by s25 (shipped set hard-coded, no environment reads).
//! Fused-column guard (Hopsersperri): every switch of the three families reads OFF while a fused column is emitted.
thread_local! { pub static FZCOL: std::cell::Cell<bool> = std::cell::Cell::new(false); }
/// true while a fused (floor-form NICF) column is emitted
pub fn fz_blocked(_name: &str) -> bool { FZCOL.with(|c| c.get()) }
/// sets FZCOL for the lifetime of the guard (restores the previous value on drop)
pub struct FzGuard(bool);
impl FzGuard { pub fn set(v: bool) -> FzGuard { FzGuard(FZCOL.with(|c| c.replace(v))) } }
impl Drop for FzGuard { fn drop(&mut self) { FZCOL.with(|c| c.set(self.0)); } }
pub fn on(n: usize) -> bool { !fz_blocked("") && matches!(n, 1|2|4|5|6|8) }
pub fn brk(_n: usize) -> u32 { 0 }
/// A5 masked-digit sub-edit: unreached on 738 (identical stream), off
pub fn a5m() -> bool { false }
