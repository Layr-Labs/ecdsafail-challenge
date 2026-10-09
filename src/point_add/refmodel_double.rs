//! Integer reference model of froghop-double: bit-serial 4-phase extended Euclid on exact-packed registers. Used by
//! tests to check the gate-level slot.

pub type N = ruint::Uint<384, 6>;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ph {
    Al,
    Dv,
    Co,
    Rt,
    Dn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct St {
    pub r: N,
    pub cd: N,
    pub rv: N,
    pub cv: N,
    pub pi: i32,
    pub ph: Ph,
    pub stk: Vec<u8>, // last = top
    pub b: u32,
    pub cnt: u32,
    pub par: u8,
    pub refl: u8,
}

fn bl(x: &N) -> u32 {
    x.bit_len() as u32
}

impl St {
    pub fn new(x: N) -> St {
        let pp = p();
        let refl = (x > pp - x) as u8;
        let xr = if refl == 1 { pp - x } else { x };
        St { r: pp, cd: N::from(1u64), rv: xr, cv: N::ZERO, pi: 1, ph: Ph::Al, stk: vec![], b: bl(&pp), cnt: 0, par: 0,
             refl }
    }

    /// DONE shots oscillate: up when pi is even, down when odd (pi stays >= 0).
    fn osc(&mut self, _sigma: usize) {
        self.pi += if self.pi % 2 == 0 { 1 } else { -1 };
    }

    pub fn fwd(&mut self, sigma: usize) {
        match self.ph {
            Ph::Dn => {
                self.cnt += 1;
                self.osc(sigma);
            }
            Ph::Al => {
                if self.r >= (self.rv << self.pi as usize) {
                    self.pi += 1;
                } else {
                    let k = self.pi as u32 - 1;
                    let delta = bl(&self.r) - bl(&self.rv) - k;
                    assert!(delta <= 1 && self.b == bl(&self.r));
                    self.b -= k + delta;
                    self.ph = Ph::Dv;
                    self.pi -= 1;
                }
            }
            Ph::Dv => {
                let x = self.rv << self.pi as usize;
                let c = (self.r >= x) as u8;
                if c == 1 {
                    self.r -= x;
                }
                if self.pi > 0 {
                    self.stk.push(c);
                    self.pi -= 1;
                } else {
                    if c == 1 {
                        self.cv += self.cd;
                    }
                    assert_eq!((self.cv >= self.cd) as u8, c);
                    self.ph = Ph::Co;
                    self.pi = 1;
                }
            }
            Ph::Co => {
                if let Some(bit) = self.stk.pop() {
                    let x = self.cd << self.pi as usize;
                    if bit == 1 {
                        self.cv += x;
                    }
                    assert_eq!((self.cv >= x) as u8, bit, "COEF erase");
                }
                if self.stk.is_empty() {
                    self.ph = Ph::Rt;
                    self.pi -= 1;
                } else {
                    self.pi += 1;
                }
            }
            Ph::Rt => {
                if self.pi > 0 {
                    self.pi -= 1;
                    return;
                }
                std::mem::swap(&mut self.r, &mut self.rv);
                std::mem::swap(&mut self.cd, &mut self.cv);
                self.par ^= 1;
                if self.b == 1 {
                    self.ph = Ph::Dn;
                    self.osc(sigma);
                } else {
                    self.ph = Ph::Al;
                    self.pi = 1;
                }
            }
        }
    }

    /// D's boundary (own frame): b in AL/CO/RT, b + pi + 1 in DV.
    pub fn bd(&self) -> u32 {
        if self.ph == Ph::Dv { self.b + self.pi as u32 + 1 } else { self.b }
    }

    pub fn result(&self) -> N {
        let pp = p();
        assert!(self.ph == Ph::Dn && self.r == N::from(1u64) && self.cd == pp && self.rv == N::ZERO && self.stk.is_empty());
        let inv = if self.par == 1 { self.cv } else { (pp - self.cv) % pp };
        if self.refl == 1 { (pp - inv) % pp } else { inv }
    }
}
