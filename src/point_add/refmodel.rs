//! Integer reference model of the froghop-single slot machine (the gate-level traversal is tested against it).
//! Used only by tests to check the gate-level circuit slot by slot.

pub type N = ruint::Uint<384, 6>;

pub const OUT: u8 = 0;
pub const RET: u8 = 1;
pub const DIV: u8 = 2;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct St {
    pub r: N,
    pub td: N,
    pub rv: N,
    pub tv: N,
    pub pi: u32,
    pub ph: u8,
    pub stk: Vec<u8>, // stk.last() = top
    pub done: bool,
    pub cnt: u32,
    pub par: u8,
    pub f1: u8,
    pub refl: u8,
}

fn bl(x: &N) -> usize {
    x.bit_len()
}

impl St {
    /// Start state for input x in [1, p): reflection x' = min(x, p - x).
    pub fn new(x: N) -> St {
        let pp = p();
        let refl = (x > pp - x) as u8;
        let xr = if refl == 1 { pp - x } else { x };
        St { r: pp, td: N::from(1u64), rv: xr, tv: N::ZERO, pi: 1, ph: OUT, stk: Vec::new(), done: false, cnt: 0,
             par: 0, f1: 1, refl }
    }

    fn coef(&mut self, bit: u8, j: u32) {
        if bit == 1 {
            self.td += self.tv << (j as usize);
        }
        assert_eq!((self.td >= (self.tv << (j as usize))) as u8, bit, "COEF erase compare failed");
    }

    /// One slot. DONE shots only count slots and oscillate pi (+1 on even slots, -1 on odd slots).
    pub fn fwd_at(&mut self, sigma: usize) {
        if self.done {
            self.cnt += 1;
            if sigma % 2 == 0 { self.pi += 1 } else { self.pi -= 1 }
            return;
        }
        let was_done = self.done;
        self.fwd();
        if self.done && !was_done {
            // the termination slot is itself a DONE-post slot
            if sigma % 2 == 0 { self.pi += 1 } else { self.pi -= 1 }
        }
    }

    pub fn fwd(&mut self) {
        if self.done {
            self.cnt += 1;
            return;
        }
        if self.ph == OUT {
            if !self.stk.is_empty() {
                let b = self.stk.pop().unwrap();
                let pi = self.pi;
                self.coef(b, pi);
                if self.stk.is_empty() && bl(&self.td) >= 256 {
                    self.done = true;
                    return;
                }
            }
            let a = self.r >= (self.rv << (self.pi as usize));
            if !self.stk.is_empty() || a {
                self.pi += 1;
            } else {
                self.ph = RET;
                self.pi -= 1;
            }
            return;
        }
        let x = self.rv << (self.pi as usize);
        let c = (self.r >= x) as u8;
        if c == 1 {
            self.r -= x;
        }
        if self.ph == DIV || c == 1 {
            self.stk.push(c);
            self.ph = DIV;
        }
        if self.ph == DIV && self.pi == 0 {
            std::mem::swap(&mut self.r, &mut self.rv);
            std::mem::swap(&mut self.td, &mut self.tv);
            self.par ^= 1;
            self.f1 = 0;
            let b = self.stk.pop().unwrap();
            self.coef(b, 0);
            self.ph = OUT;
            self.pi = 1;
        } else {
            self.pi -= 1;
        }
    }

    /// Inverse of x read from the final state.
    pub fn result(&self) -> N {
        let pp = p();
        assert!(self.done && self.r == N::from(1u64) && self.td == pp && self.rv == N::ZERO && self.stk.is_empty());
        let inv = if self.par == 1 { self.tv } else { (pp - self.tv) % pp };
        if self.refl == 1 { (pp - inv) % pp } else { inv }
    }
}
