//! Isolated R01 numeric-scan prototype; NOT connected to the submitted builder.
//! Own exactly k-2 clean lanes across a read-only control epoch. Every recorded
//! advance span must be reversed after its matching consumer, last first.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

pub(super) struct Prefix<'a> {
    controls: Vec<&'a QReg>, // most significant to least significant
    clean: &'a [QReg],
    last: Option<Vec<bool>>,
}

impl<'a> Prefix<'a> {
    pub(super) fn new(controls_msb_first: Vec<&'a QReg>, clean: &'a [QReg]) -> Self {
        assert!(controls_msb_first.len() >= 2);
        assert_eq!(clean.len(), controls_msb_first.len() - 2);
        let mut ids: Vec<_> = controls_msb_first.iter().map(|q| q.id())
            .chain(clean.iter().map(QReg::id)).collect();
        ids.sort_unstable();
        assert!(ids.windows(2).all(|p| p[0] != p[1]));
        Self { controls: controls_msb_first, clean, last: None }
    }

    fn cell(&self, c: &mut Circuit, values: &[bool], at: usize) {
        let right = self.controls[at + 1];
        if !values[at + 1] { c.x(right); }
        if at == 0 {
            let left = self.controls[0];
            if !values[0] { c.x(left); }
            c.ccx(left, right, &self.clean[0]);
            if !values[0] { c.x(left); }
        } else {
            c.ccx(&self.clean[at - 1], right, &self.clean[at]);
        }
        if !values[at + 1] { c.x(right); }
    }

    /// Leaves all control bits unchanged; target is arbitrary XOR output.
    /// Prefix lanes remain live, so the caller must record/reverse this span.
    /// During a consumer, physical controls may be temporarily conjugated only
    /// if restored before this method or its literal inverse next executes.
    pub(super) fn toggle(&mut self, c: &mut Circuit, values_msb_first: &[bool], target: &QReg) {
        let k = self.controls.len();
        assert_eq!(values_msb_first.len(), k);
        assert!(self.controls.iter().all(|q| q.id() != target.id()));
        assert!(self.clean.iter().all(|q| q.id() != target.id()));
        let mut first = 0;
        if let Some(old) = &self.last {
            let common = old[..k - 1].iter().zip(&values_msb_first[..k - 1])
                .take_while(|(a, b)| a == b).count();
            first = common.saturating_sub(1);
            for at in (first..self.clean.len()).rev() { self.cell(c, old, at); }
        }
        for at in first..self.clean.len() { self.cell(c, values_msb_first, at); }
        let low = self.controls[k - 1];
        if !values_msb_first[k - 1] { c.x(low); }
        if k == 2 {
            let high = self.controls[0];
            if !values_msb_first[0] { c.x(high); }
            c.ccx(high, low, target);
            if !values_msb_first[0] { c.x(high); }
        } else { c.ccx(&self.clean[k - 3], low, target); }
        if !values_msb_first[k - 1] { c.x(low); }
        self.last = Some(values_msb_first.to_vec());
    }
}

thread_local! { static POOL: std::cell::RefCell<Option<Vec<QReg>>> = const { std::cell::RefCell::new(None) }; }
pub(crate) struct Scope;
impl Scope {
    pub(crate) fn set(clean: &[QReg]) -> Self {
        assert_eq!(clean.len(), 11);
        POOL.with(|p| { assert!(p.borrow().is_none()); *p.borrow_mut() = Some(clean.iter().map(QReg::borrowed_alias).collect()); });
        Self
    }
}
impl Drop for Scope { fn drop(&mut self) { POOL.with(|p| *p.borrow_mut() = None); } }
pub(super) fn current() -> Option<Vec<QReg>> { POOL.with(|p| p.borrow().as_ref().map(|v| v.iter().map(QReg::borrowed_alias).collect())) }

