//! Exact short XOR names. A longer expression receives a fresh unique atom.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Form(pub u32, pub u32);
impl Form {
    fn single(id: u32) -> Self {
        Self(0, id)
    }
    pub(super) fn xor(self, other: Self) -> Option<Self> {
        if self == other {
            return Some(Self::default());
        }
        if self.1 == 0 {
            return Some(other);
        }
        if other.1 == 0 {
            return Some(self);
        }
        if self.0 == 0 && other.0 == 0 {
            return Some(Self(self.1.min(other.1), self.1.max(other.1)));
        }
        let mut atoms = [self.0, self.1, other.0, other.1];
        atoms.sort_unstable();
        let mut keep = [0u32; 2];
        let mut n = 0;
        let mut i = 0;
        while i < 4 {
            let at = atoms[i];
            i += 1;
            if i < 4 && atoms[i] == at {
                i += 1;
                continue;
            }
            if at != 0 {
                if n == 2 {
                    return None;
                }
                keep[n] = at;
                n += 1;
            }
        }
        Some(if n == 1 {
            Self::single(keep[0])
        } else {
            Self(keep[0], keep[1])
        })
    }
}
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Expr {
    pub form: Form,
    pub sign: bool,
}
impl Expr {
    pub(super) fn zero(self) -> bool {
        self.form.1 == 0 && !self.sign
    }
    fn one(self) -> bool {
        self.form.1 == 0 && self.sign
    }
}
#[derive(Clone, Copy, Default)]
struct Intern {
    a: Expr,
    b: Expr,
    name: Expr,
}
pub(super) struct Names {
    pub wires: Vec<Expr>,
    next: u32,
    products: Vec<Intern>,
}
pub(super) fn bucket(a: Form, b: Form, slots: usize) -> usize {
    let x = (a.0 as u64) << 32 | a.1 as u64;
    let y = (b.0 as u64) << 32 | b.1 as u64;
    let h = (x.wrapping_mul(0xa0761d6478bd642f) ^ y.wrapping_mul(0xe7037ed1a0b428db))
        .wrapping_mul(0x8ebc6af09c88c6e3);
    ((h ^ h >> 32) as usize) & (slots - 1)
}
impl Names {
    pub(super) fn new(inputs: &[bool]) -> Self {
        let mut s = Self {
            wires: vec![Expr::default(); inputs.len()],
            next: 0,
            products: vec![Intern::default(); 1 << 17],
        };
        for (i, &unknown) in inputs.iter().enumerate() {
            if unknown {
                s.wires[i] = s.fresh();
            }
        }
        s
    }
    fn fresh(&mut self) -> Expr {
        self.next = self.next.checked_add(1).unwrap();
        Expr {
            form: Form::single(self.next),
            sign: false,
        }
    }
    fn xor(&mut self, a: Expr, b: Expr) -> Expr {
        match a.form.xor(b.form) {
            Some(form) => Expr {
                form,
                sign: a.sign ^ b.sign,
            },
            None => self.fresh(),
        }
    }
    fn product(&mut self, a: Expr, b: Expr) -> Expr {
        if a.zero() || b.zero() {
            return Expr::default();
        }
        if a.one() {
            return b;
        }
        if b.one() {
            return a;
        }
        if a.form == b.form {
            return if a == b { a } else { Expr::default() };
        }
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        let i = bucket(a.form, b.form, self.products.len())
            ^ (a.sign as usize)
            ^ ((b.sign as usize) << 8);
        let hit = self.products[i];
        if hit.a == a && hit.b == b {
            return hit.name;
        }
        let name = self.fresh();
        self.products[i] = Intern { a, b, name };
        name
    }
    pub(super) fn observe(&mut self, x: &super::Op, unconditional: bool) {
        use super::K;
        let (q, a, b) = (
            x.q_target.0 as usize,
            x.q_control1.0 as usize,
            x.q_control2.0 as usize,
        );
        match x.kind {
            K::X if unconditional => self.wires[q].sign ^= true,
            K::X => self.wires[q] = self.fresh(),
            K::CX | K::CCX => {
                let toggle = if x.kind == K::CX {
                    self.wires[a]
                } else {
                    self.product(self.wires[a], self.wires[b])
                };
                if !toggle.zero() {
                    self.wires[q] = if unconditional {
                        self.xor(self.wires[q], toggle)
                    } else {
                        self.fresh()
                    };
                }
            }
            K::R | K::Hmr => {
                if unconditional {
                    self.wires[q] = Expr::default();
                } else if !self.wires[q].zero() {
                    self.wires[q] = self.fresh();
                }
            }
            K::Swap if unconditional => self.wires.swap(a, q),
            K::Swap if self.wires[a] != self.wires[q] => {
                self.wires[q] = self.fresh();
                self.wires[a] = self.fresh();
            }
            _ => {}
        }
    }
}
