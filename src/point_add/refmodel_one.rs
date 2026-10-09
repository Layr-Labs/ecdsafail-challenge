//! Integer reference model of froghop-one: froghop-single's one-hop slot machine on froghop-double's exact-packed
//! registers. Used by tests (gate-level slot check) and by the window generator.
//!
//! Registers (value LSB at lane 0 growing up, cofactor LSB at lane W-1 growing down; V rotated up by pi):
//!   D = (r = r_{j-1} dividend, cd = t_{j-1} cofactor source),  V = (rv = r_j divisor, cv = cofactor target, t_{j-2}
//!   growing to t_j while the previous quotient's bits are popped on the up-ramp).
//! b: bit length of the dividend while the step is not aligned (k == 0), of the divisor once aligned (k > 0).
//! k: alignment height of the step (the pi at which r < rv << pi first held), 0 before it; cleared at the step end.

pub type N = ruint::Uint<384, 6>;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ph {
    Out,
    Ret,
    Div,
    Dn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct St {
    pub r: N,
    pub cd: N,
    pub rv: N,
    pub cv: N,
    pub pi: u32,
    pub ph: Ph,
    pub k: u32,
    pub b: u32,
    pub stk: Vec<u8>, // last = top
    pub cnt: u32,
    pub par: u8,
    pub refl: u8,
    pub f1: u8,
}

pub fn bl(x: &N) -> u32 {
    x.bit_len() as u32
}

/// What a slot did (for envelope statistics).
#[derive(Clone, Copy, Debug, Default)]
pub struct Ev {
    /// alignment found this slot: (b before, b after, pi)
    pub align: Option<(u32, u32, u32)>,
    /// step end this slot: b after
    pub step_end: Option<u32>,
    pub first_step_end: bool,
}

impl St {
    /// Start state for input x in [1, p): reflection x' = min(x, p - x) < 2^255.
    pub fn new(x: N) -> St {
        let pp = p();
        let refl = (x > pp - x) as u8;
        let xr = if refl == 1 { pp - x } else { x };
        St { r: pp, cd: N::ZERO, rv: xr, cv: N::from(1u64), pi: 1, ph: Ph::Out, k: 0, b: bl(&pp), stk: vec![],
             cnt: 0, par: 0, refl, f1: 1 }
    }

    /// The boundary B1: the value ladder works on lanes [pi, b1()], the cofactor ladders on lanes > b1().
    pub fn b1(&self) -> u32 {
        // aligned once k > 0; the last step (dividend 1, divisor 0: b == 1) climbs past b while popping the last
        // quotient and counts as aligned, which keeps V's wrapped cofactor bits (lanes < pi) out of the cofactor ladders
        if self.k > 0 || self.b == 1 { self.b + self.pi } else { self.b }
    }

    fn coef(&mut self, bit: u8, j: u32) {
        if bit == 1 {
            self.cv += self.cd << (j as usize);
        }
        assert_eq!((self.cv >= (self.cd << (j as usize))) as u8, bit, "COEF erase compare failed");
    }

    /// One slot. DONE shots only count slots and oscillate pi (+1 on even slots, -1 on odd slots); the termination
    /// slot is itself a DONE-post slot.
    pub fn fwd_at(&mut self, sigma: usize) -> Ev {
        let mut ev = Ev::default();
        let osc = |pi: &mut u32| if sigma % 2 == 0 { *pi += 1 } else { *pi -= 1 };
        match self.ph {
            Ph::Dn => {
                self.cnt += 1;
                osc(&mut self.pi);
            }
            Ph::Out => {
                if let Some(bit) = self.stk.pop() {
                    let pi = self.pi;
                    self.coef(bit, pi);
                }
                if self.stk.is_empty() && self.b == 1 && self.k == 0 {
                    self.ph = Ph::Dn;
                    osc(&mut self.pi);
                    return ev;
                }
                let a = self.r >= (self.rv << self.pi as usize);
                if self.k == 0 && !a {
                    let delta = bl(&self.r) - bl(&self.rv) - (self.pi - 1);
                    assert!(delta <= 1 && self.b == bl(&self.r));
                    let b0 = self.b;
                    self.b -= self.pi - 1 + delta;
                    assert_eq!(self.b, bl(&self.rv));
                    self.k = self.pi;
                    ev.align = Some((b0, self.b, self.pi));
                }
                if !self.stk.is_empty() || a {
                    self.pi += 1;
                } else {
                    self.ph = Ph::Ret;
                    self.pi -= 1;
                }
            }
            Ph::Ret | Ph::Div => {
                let x = self.rv << self.pi as usize;
                let c = (self.r >= x) as u8;
                if c == 1 {
                    self.r -= x;
                }
                if self.ph == Ph::Div || c == 1 {
                    self.stk.push(c);
                    self.ph = Ph::Div;
                }
                if self.ph == Ph::Div && self.pi == 0 {
                    assert_eq!(self.stk.len() as u32, self.k);
                    std::mem::swap(&mut self.r, &mut self.rv);
                    std::mem::swap(&mut self.cd, &mut self.cv);
                    self.par ^= 1;
                    ev.first_step_end = self.f1 == 1;
                    self.f1 = 0;
                    let bit = self.stk.pop().unwrap();
                    self.coef(bit, 0);
                    self.k = 0;
                    self.ph = Ph::Out;
                    self.pi = 1;
                    assert_eq!(self.b, bl(&self.r));
                    ev.step_end = Some(self.b);
                } else {
                    self.pi -= 1;
                }
            }
        }
        ev
    }

    /// Inverse of x read from the final state.
    pub fn result(&self) -> N {
        let pp = p();
        assert!(self.ph == Ph::Dn && self.r == N::from(1u64) && self.cv == pp && self.rv == N::ZERO
            && self.stk.is_empty());
        let inv = if self.par == 1 { self.cd } else { (pp - self.cd) % pp };
        if self.refl == 1 { (pp - inv) % pp } else { inv }
    }
}
