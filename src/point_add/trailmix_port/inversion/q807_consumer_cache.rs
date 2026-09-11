//! Dedicated clean g*decision cache for the numeric R01 reverse epoch.
//! Do not use the shared clean scratch or any retained equality prefix lane.
//! This module emits no measurement and does not allocate any circuit wire.
use crate::point_add::trailmix_port::circuit::QReg;
thread_local! { static CACHE: std::cell::RefCell<Option<QReg>> = const { std::cell::RefCell::new(None) }; }
pub(crate) struct Scope;
impl Scope {
    pub(crate) fn set(clean: &QReg) -> Self {
        CACHE.with(|q| { assert!(q.borrow().is_none(), "nested consumer cache"); *q.borrow_mut() = Some(clean.borrowed_alias()); });
        Self
    }
}
impl Drop for Scope { fn drop(&mut self) { CACHE.with(|q| *q.borrow_mut() = None); } }
pub(super) fn current() -> Option<QReg> { CACHE.with(|q| q.borrow().as_ref().map(QReg::borrowed_alias)) }
