//! The three nonzero forms in a binary plane are U,V,U+V. An AND of any two
//! independent signed forms is the indicator of one point on that plane.
use super::names::{Expr, Form};
#[derive(Clone, Copy)]
pub(super) struct Plane {
    pub first: Form,
    pub second: Form,
    a: u8,
    b: u8,
    a_sign: bool,
    b_sign: bool,
}
impl Plane {
    pub(super) fn new(a: Expr, b: Expr) -> Option<Self> {
        if a.form.1 == 0 || b.form.1 == 0 || a.form == b.form {
            return None;
        }
        let (mut first, mut second) = if a.form < b.form {
            (a.form, b.form)
        } else {
            (b.form, a.form)
        };
        if let Some(third) = a.form.xor(b.form) {
            if third < first {
                second = first;
                first = third;
            } else if third < second {
                second = third;
            }
        }
        let code = |v| {
            if v == first {
                1
            } else if v == second {
                2
            } else {
                3
            }
        };
        Some(Self {
            first,
            second,
            a: code(a.form),
            b: code(b.form),
            a_sign: a.sign,
            b_sign: b.sign,
        })
    }
    pub(super) fn values(self, point: u8) -> (bool, bool) {
        let v = |tag: u8, sign: bool| ((tag & point).count_ones() % 2 != 0) ^ sign;
        (v(self.a, self.a_sign), v(self.b, self.b_sign))
    }
    pub(super) fn active_point(self) -> u8 {
        (0..4).find(|&p| self.values(p) == (true, true)).unwrap()
    }
}
