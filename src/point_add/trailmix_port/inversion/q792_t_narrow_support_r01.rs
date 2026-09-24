//! A branch-local arithmetic width must not be mistaken for the original
//! calendar bound on quotient address M=A+C. Keep that older bound explicit.
use crate::point_add::trailmix_port::circuit::Circuit;
thread_local!{static QUOTIENT:std::cell::Cell<Option<Option<(usize,usize)>>>=const{std::cell::Cell::new(None)};}
pub(super) struct Scope;
pub(super) fn enter(original:Option<(usize,usize)>)->Scope{QUOTIENT.with(|v|{assert!(v.get().is_none());v.set(Some(original));});Scope}
impl Drop for Scope{fn drop(&mut self){QUOTIENT.with(|v|{assert!(v.get().is_some());v.set(None);});}}
pub(super) fn quotient_support(c:&Circuit)->Option<(usize,usize)>{QUOTIENT.with(|v|v.get().unwrap_or(c.q797_a_support))}
