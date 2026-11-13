//! MAND: measured AND uncompute on the finished stream (exact).
//!
//! Every lane carries a symbolic value: a XOR of atoms, where an atom is a fresh unknown (a register input, or a value
//! written under a condition) or the AND of two lane values. Each atom has a 128-bit id and a lane holds the XOR of its
//! atom ids, so a lane with id 0 is provably 0 and two lanes with equal ids provably hold equal values. A CCX(a, b -> t)
//! whose target id equals the id of the atom AND(a, b) clears t on every input: it is replaced by an X-basis
//! measurement of t into a bit m followed by CZ(a, b) conditioned on m (t = a & b, so the CZ cancels the measurement's
//! phase kick; 0 Toffoli). Classical bits are tracked the same way (a measurement result is a fresh atom) and a write
//! under a condition C is t ^= C & value, so classically controlled loads and condition blocks stay exact. Only
//! unconditioned CCX outside every condition block are rewritten. Ids depend only on the stream (deterministic).
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
    /// classical bits: the same XOR-of-atoms ids (a measured bit is a fresh atom)
    hb: Vec<u128>,
    /// condition of the current block (one = always), and the stack of outer ones
    blk: u128,
    stack: Vec<u128>,
    fresh_n: u64,
    one: u128,
    pub n: [u64; 5],
}

impl Sym {
    pub fn new() -> Self {
        let one = h128(1, 1, 1, 1, 1);
        Sym { h: vec![0; 1024], hb: vec![0; 1024], blk: one, stack: vec![], fresh_n: 0, one, n: [0; 5] }
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
    fn bit(&mut self, c: BitId) -> usize {
        let i = c.0 as usize;
        if i >= self.hb.len() {
            self.hb.resize(i + 1, 0);
        }
        i
    }
    #[inline]
    fn new_atom(&mut self) -> u128 {
        self.fresh_n += 1;
        h128(self.fresh_n, 0, 0, 0, 3)
    }
    /// id of x & y for two XOR-of-atoms values (exact identities only: 0, 1, x & x, x & !x)
    #[inline]
    fn and(&self, x: u128, y: u128) -> u128 {
        if x == 0 || y == 0 || x ^ y == self.one {
            0
        } else if x == self.one || x == y {
            y
        } else if y == self.one {
            x
        } else {
            mix(x, y)
        }
    }
    /// give lane q a fresh unknown value (a lane that is not known to be clean)
    pub fn set_atom(&mut self, q: u64) {
        let i = self.lane(QubitId(q));
        self.h[i] = self.new_atom();
    }
    /// take lane q as clean (a precondition supplied by the caller)
    pub fn set_zero(&mut self, q: u64) {
        let i = self.lane(QubitId(q));
        self.h[i] = 0;
    }
    /// is the lane provably 0 now
    pub fn is_zero(&self, q: u64) -> bool {
        (q as usize) < self.h.len() && self.h[q as usize] == 0
    }
    /// condition-block depth before the next op
    pub fn depth_now(&self) -> u32 {
        self.stack.len() as u32
    }
    /// advance the symbolic state over `op` and classify it. Every write is exact: a write under condition C is
    /// t ^= C & (value), with C the AND of the block's bits and the op's own bit.
    pub fn step(&mut self, op: &Op) -> Cls {
        use OperationType as K;
        let one = self.one;
        let c = if op.c_condition != NO_BIT {
            let b = self.bit(op.c_condition);
            self.and(self.blk, self.hb[b])
        } else {
            self.blk
        };
        let plain = op.c_condition == NO_BIT && self.stack.is_empty();
        let mut cls = Cls::Other;
        match op.kind {
            K::PushCondition => {
                self.stack.push(self.blk);
                self.blk = c;
            }
            K::PopCondition => {
                if let Some(b) = self.stack.pop() {
                    self.blk = b;
                }
            }
            K::AppendToRegister => {
                if op.q_target != NO_QUBIT {
                    let t = self.lane(op.q_target);
                    self.h[t] = self.new_atom();
                }
                if op.c_target != NO_BIT {
                    let b = self.bit(op.c_target);
                    self.hb[b] = self.new_atom();
                }
            }
            K::X => {
                let t = self.lane(op.q_target);
                self.h[t] ^= c;
            }
            K::CX => {
                let (a, t) = (self.lane(op.q_control1), self.lane(op.q_target));
                let v = self.and(c, self.h[a]);
                self.h[t] ^= v;
            }
            K::Swap => {
                let (a, t) = (self.lane(op.q_control1), self.lane(op.q_target));
                let d = self.and(c, self.h[a] ^ self.h[t]);
                self.h[a] ^= d;
                self.h[t] ^= d;
            }
            K::CCX => {
                let (a, b, t) = (self.lane(op.q_control1), self.lane(op.q_control2), self.lane(op.q_target));
                let ab = self.and(self.h[a], self.h[b]);
                let distinct = a != b && t != a && t != b;
                if distinct && ab != 0 && self.h[t] == ab {
                    cls = if plain { Cls::AndU } else if op.c_condition == NO_BIT { Cls::AndUBlock } else { Cls::Other };
                } else if distinct && plain && ab == 0 {
                    cls = Cls::Dead;
                } else if distinct && plain && self.h[a] == self.h[b] {
                    cls = Cls::EqCtl;
                }
                let v = self.and(c, ab);
                self.h[t] ^= v;
            }
            K::Hmr | K::R => {
                let t = self.lane(op.q_target);
                let v = self.and(c, self.h[t]);
                self.h[t] ^= v;
                if op.kind == K::Hmr {
                    let r = self.new_atom();
                    let m = self.bit(op.c_target);
                    // m <- m ^ C & (m ^ r): exact with r a fresh atom
                    let v = self.and(c, self.hb[m] ^ r);
                    self.hb[m] ^= v;
                }
            }
            K::BitInvert => {
                let m = self.bit(op.c_target);
                self.hb[m] ^= c;
            }
            K::BitStore0 => {
                let m = self.bit(op.c_target);
                let v = self.and(c, self.hb[m]);
                self.hb[m] ^= v;
            }
            K::BitStore1 => {
                let m = self.bit(op.c_target);
                let v = self.and(c, self.hb[m] ^ one);
                self.hb[m] ^= v;
            }
            _ => {}
        }
        let k = match cls { Cls::Other => 0, Cls::AndU => 1, Cls::AndUBlock => 2, Cls::Dead => 3, Cls::EqCtl => 4 };
        self.n[k] += 1;
        cls
    }
}

/// Also rewrite the CCX whose controls provably never both hold (removed) and those whose controls provably hold equal
/// values (CX from the first control).
pub const REWRITE_DEAD: bool = true;
pub const REWRITE_EQ: bool = true;

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
    let (mut dropped, mut to_cx) = (0u64, 0u64);
    for op in ops {
        let cls = s.step(&op);
        if REWRITE_DEAD && cls == Cls::Dead {
            dropped += 1;
            continue;
        }
        if REWRITE_EQ && cls == Cls::EqCtl {
            let mut x = Op::empty();
            x.kind = OperationType::CX;
            x.q_control1 = op.q_control1;
            x.q_target = op.q_target;
            out.push(x);
            to_cx += 1;
            continue;
        }
        if cls == Cls::AndU {
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
    eprintln!("MAND: ccx {} -> {}; measured erasures {}, dead CCX removed {}, equal-control CCX -> CX {}; in blocks {} (kept); bit {}",
              ccx0, ccx0 as u64 - s.n[1] - dropped - to_cx, s.n[1], dropped, to_cx, s.n[2], m.0);
    out
}
