//! C1-only actual caller: decision1 during reversed SUM, decision0 afterward.
//! No new rail. Offguard two carry halves share the same dirty extension.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub(super) fn enabled()->bool{std::env::var("Q794_T10_C1_DECISION").ok().as_deref()==Some("1")}
pub(super) fn forward(c:&mut Circuit,s:&QReg,t:&QReg,h:&QReg,m:&QReg,d:&QReg){
 c.cx(s,t);c.cx(h,s);c.ccx(m,s,d);c.ccx(d,t,h);c.ccx(m,s,d);
}
/// Leaves source in the SAME temporary SUM coordinate as the old caller;
/// special low-seam SUM comes next, then the caller restores source ^= h.
pub(super) fn reverse_sum(c:&mut Circuit,s:&QReg,t:&QReg,h:&QReg,m:&QReg,g:&QReg,d:&QReg){
 c.cx(g,d);c.ccx(m,s,d);c.ccx(d,t,h);c.cx(s,t);c.cx(h,t);c.ccx(g,d,t);c.ccx(m,s,d);c.cx(g,d);
}
