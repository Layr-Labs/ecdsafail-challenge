use super::*;

struct Field { u: i64, v: i64, sign: bool, p: i64 }
impl Kernel for Field {
    fn emit(&mut self, op: Operation, _: Lowering) {
        let signed = if self.sign { -self.u } else { self.u };
        match op {
            Operation::Add => self.v += signed,
            Operation::Sub => self.v -= signed,
            Operation::Half => self.v *= (self.p + 1) / 2,
            Operation::Double => self.v *= 2,
            Operation::HalfU => self.u *= (self.p + 1) / 2,
            Operation::DoubleU => self.u *= 2,
            Operation::Swap => std::mem::swap(&mut self.u, &mut self.v),
        }
        self.u = self.u.rem_euclid(self.p);
        self.v = self.v.rem_euclid(self.p);
    }
}

#[test]
fn inverse_reverses_order_and_inverts_each_operation() {
    let p = Program::parse("swap:direct,sub:power2,half:direct,half_u:power2").unwrap();
    let inverse = p.inverse();
    assert_eq!(inverse.instructions()[0].op, Operation::DoubleU);
    assert_eq!(inverse.instructions()[2].op, Operation::Add);
    assert_eq!(inverse.instructions()[2].lowering, Lowering::Power2);
    assert_eq!(inverse.inverse(), p);
    for u in 0..17 { for v in 0..17 { for sign in [false,true] {
        let mut f = Field { u,v,sign,p:17 };
        p.emit(&mut f, Direction::Forward);
        p.emit(&mut f, Direction::Inverse);
        assert_eq!((f.u,f.v,f.sign), (u,v,sign));
    }}}
}

#[test]
fn expanding_composition_matches_seed_and_wrong_order_has_witness() {
    let seed = Program::parse("add:direct,half:direct").unwrap();
    let expanded = Program::parse("half_u:power2,half:direct,add:power2,double_u:direct").unwrap();
    let bad = Program::parse("half:direct,add:direct").unwrap();
    let mut witness = None;
    for u in 0..17 { for v in 0..17 { for sign in [false,true] {
        let mut a = Field { u,v,sign,p:17 };
        let mut b = Field { u,v,sign,p:17 };
        let mut c = Field { u,v,sign,p:17 };
        seed.emit(&mut a, Direction::Forward);
        expanded.emit(&mut b, Direction::Forward);
        bad.emit(&mut c, Direction::Forward);
        assert_eq!((a.u,a.v), (b.u,b.v));
        if a.v != c.v { witness = Some((u,v,sign,a.v,c.v)); }
    }}}
    assert!(witness.is_some(), "the invalid order must retain a counterexample");
}

#[test]
fn syntax_rejects_unknown_types_and_keeps_semantic_proposals() {
    for text in ["", "add", "add:unknown", "unknown:direct", "add:direct,", "add:direct:extra"] {
        assert!(Program::parse(text).is_err(), "{text}");
    }
    assert!(Program::parse(&["add:direct";9].join(",")).is_err());
    assert!(Program::parse("half:direct,add:power2").is_ok());
}

#[test]
fn lowering_scope_restores_after_normal_return_and_panic() {
    assert_eq!(Lowering::current(), Lowering::Direct);
    Lowering::Power2.with_scope(|| {
        assert_eq!(Lowering::current(), Lowering::Power2);
        Lowering::Direct.with_scope(|| assert_eq!(Lowering::current(), Lowering::Direct));
        assert_eq!(Lowering::current(), Lowering::Power2);
    });
    let _ = std::panic::catch_unwind(|| Lowering::Power2.with_scope(|| panic!("test scope")));
    assert_eq!(Lowering::current(), Lowering::Direct);
}
