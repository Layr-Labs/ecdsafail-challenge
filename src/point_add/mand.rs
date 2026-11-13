//! MAND: measured AND uncompute on the finished stream (exact).
//!
//! Every lane carries a symbolic value: a XOR of atoms, where an atom is a fresh unknown (a register input, or a value
//! written under a condition) or the AND of two lane values. Each atom has a 128-bit id and a lane holds the XOR of its
//! atom ids, so a lane with id 0 is provably 0 and two lanes with equal ids provably hold equal values. A CCX(a, b -> t)
//! whose target id equals the id of the atom AND(a, b) clears t on every input: it is replaced by an X-basis
//! measurement of t into a bit m followed by CZ(a, b) conditioned on m (t = a & b, so the CZ cancels the measurement's
//! phase kick; 0 Toffoli). Only unconditioned CCX outside every condition block are rewritten. Ids depend only on the
//! stream, so the pass is deterministic.
use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT, NO_QUBIT};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cls {
    Other,
    /// unconditioned CCX that clears its target: rewritten
    AndU,
    /// the same inside a condition block: counted only
    AndUBlock,
    /// unconditioned CCX whose controls provably never both hold: counted only
    Dead,
    /// unconditioned CCX whose controls provably hold equal values (a CX): counted only
    EqCtl,
}

#[inline]
fn fmix(mut k: u64) -> u64 {
    k ^= k >> 33;
    k = k.wrapping_mul(0xff51afd7ed558ccd);
    k ^= k >> 33;
    k = k.wrapping_mul(0xc4ceb9fe1a85ec53);
    k ^= k >> 33;
    k
}
#[inline]
fn h128(a0: u64, a1: u64, b0: u64, b1: u64, dom: u64) -> u128 {
    let lo = fmix(a0 ^ fmix(a1 ^ fmix(b0 ^ fmix(b1 ^ fmix(dom ^ 0x9e3779b97f4a7c15)))));
    let hi = fmix(b1 ^ fmix(b0.wrapping_add(0x632be59bd9b4e019) ^ fmix(a1 ^ fmix(a0 ^ fmix(dom ^ 0x85ebca6b2f2b8bd1)))));
    ((hi as u128) << 64) | lo as u128
}
/// id of the atom AND(x, y) (unordered)
#[inline]
fn mix(x: u128, y: u128) -> u128 {
    let (a, b) = if x <= y { (x, y) } else { (y, x) };
    h128(a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64, 2)
}

pub struct Sym {
    h: Vec<u128>,
    depth: u32,
    fresh_n: u64,
    one: u128,
    pub n: [u64; 5],
}

impl Sym {
    pub fn new() -> Self {
        Sym { h: vec![0; 1024], depth: 0, fresh_n: 0, one: h128(1, 1, 1, 1, 1), n: [0; 5] }
    }
    #[inline]
    fn lane(&mut self, q: QubitId) -> usize {
        let i = q.0 as usize;
        if i >= self.h.len() {
            self.h.resize(i + 1, 0);
        }
        i
    }
    #[inline]
    fn fresh(&mut self, q: QubitId) {
        let i = self.lane(q);
        self.fresh_n += 1;
        self.h[i] = h128(self.fresh_n, 0, 0, 0, 3);
    }
    /// condition-block depth before the next op
    pub fn depth_now(&self) -> u32 {
        self.depth
    }
    /// advance the symbolic state over `op` and classify it
    pub fn step(&mut self, op: &Op) -> Cls {
        use OperationType as K;
        let cond = op.c_condition != NO_BIT || self.depth > 0;
        let mut cls = Cls::Other;
        match op.kind {
            K::PushCondition => self.depth += 1,
            K::PopCondition => self.depth = self.depth.saturating_sub(1),
            K::AppendToRegister => {
                if op.q_target != NO_QUBIT {
                    self.fresh(op.q_target);
                }
            }
            K::X => {
                if cond {
                    self.fresh(op.q_target);
                } else {
                    let t = self.lane(op.q_target);
                    self.h[t] ^= self.one;
                }
            }
            K::CX => {
                if cond {
                    self.fresh(op.q_target);
                } else {
                    let (c, t) = (self.lane(op.q_control1), self.lane(op.q_target));
                    self.h[t] ^= self.h[c];
                }
            }
            K::Swap => {
                if cond {
                    self.fresh(op.q_control1);
                    self.fresh(op.q_target);
                } else {
                    let (c, t) = (self.lane(op.q_control1), self.lane(op.q_target));
                    self.h.swap(c, t);
                }
            }
            K::CCX => {
                let (a, b, t) = (self.lane(op.q_control1), self.lane(op.q_control2), self.lane(op.q_target));
                let (ha, hb, ht) = (self.h[a], self.h[b], self.h[t]);
                let distinct = a != b && t != a && t != b;
                if distinct && ha != 0 && hb != 0 && ht != 0 && ht == mix(ha, hb) {
                    if !cond {
                        cls = Cls::AndU;
                        self.h[t] = 0;
                    } else {
                        if op.c_condition == NO_BIT {
                            cls = Cls::AndUBlock;
                        }
                        self.fresh(op.q_target);
                    }
                } else if cond || !distinct {
                    self.fresh(op.q_target);
                } else if ha == 0 || hb == 0 || ha == hb ^ self.one {
                    cls = Cls::Dead;
                } else if ha == hb {
                    cls = Cls::EqCtl;
                    self.h[t] ^= ha;
                } else {
                    self.h[t] ^= mix(ha, hb);
                }
            }
            K::Hmr | K::R => {
                let t = self.lane(op.q_target);
                if !cond {
                    self.h[t] = 0;
                } else if self.h[t] != 0 {
                    self.fresh(op.q_target);
                }
            }
            _ => {}
        }
        let k = match cls { Cls::Other => 0, Cls::AndU => 1, Cls::AndUBlock => 2, Cls::Dead => 3, Cls::EqCtl => 4 };
        self.n[k] += 1;
        cls
    }
}

/// The rewrite: every AndU CCX becomes Hmr(t -> m) + CZ(a, b) conditioned on m, with one new classical bit m
/// (written and read back to back, so one bit serves every site).
pub fn apply(ops: Vec<Op>) -> Vec<Op> {
    let mut maxb: Option<u64> = None;
    for o in &ops {
        for c in [o.c_target, o.c_condition] {
            if c != NO_BIT {
                maxb = Some(maxb.map_or(c.0, |m| m.max(c.0)));
            }
        }
    }
    let m = BitId(maxb.map_or(0, |x| x + 1));
    let mut s = Sym::new();
    let mut out = Vec::with_capacity(ops.len() + ops.len() / 16);
    let ccx0 = ops.iter().filter(|o| o.kind == OperationType::CCX).count();
    for op in ops {
        if s.step(&op) == Cls::AndU {
            let mut h = Op::empty();
            h.kind = OperationType::Hmr;
            h.q_target = op.q_target;
            h.c_target = m;
            out.push(h);
            let mut z = Op::empty();
            z.kind = OperationType::CZ;
            z.q_control1 = op.q_control1;
            z.q_target = op.q_control2;
            z.c_condition = m;
            out.push(z);
        } else {
            out.push(op);
        }
    }
    eprintln!("MAND: ccx {} -> {}; rewritten {} (in blocks {}, dead {}, equal controls {} counted only); bit {}",
              ccx0, ccx0 as u64 - s.n[1], s.n[1], s.n[2], s.n[3], s.n[4], m.0);
    out
}
