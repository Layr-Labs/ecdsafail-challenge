//! frogdrop tests: the 3-of-4 machine primitives, columns, traversal, product fold and end-to-end point addition.

use super::builder::B;
use super::frogdrop::*;
use super::frogdrop_sched::N;
use crate::circuit::QubitId;
use crate::circuit::{analyze_ops, Op};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

pub struct Sim {
    pub q: Vec<u64>,
    pub phase: u64,
    pub tof: u64,
}

/// Run ops on 64 shots starting from `init` qubit words; returns final words, phase word, Toffoli count.
pub fn run(ops: &[Op], nq: usize, init: &dyn Fn(&mut Vec<u64>)) -> Sim {
    let (aq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq.max(aq as usize);
    let mut h = sha3::Shake256::default();
    h.update(b"frogdrop-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq, (nb as usize).max(1), &mut xof);
    init(&mut s.qubits);
    s.apply_iter(ops.iter());
    Sim {
        q: s.qubits.clone(),
        phase: s.phase,
        tof: s.stats.toffoli_gates,
    }
}

pub struct Rng(u64);
impl Rng {
    pub fn new(s: u64) -> Rng {
        Rng(s ^ 0x9E3779B97F4A7C15)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, bits: usize) -> N {
        let mut v = N::ZERO;
        for i in 0..6 {
            v |= N::from(self.next()) << (64 * i);
        }
        if bits < 384 {
            v & ((N::from(1u64) << bits) - N::from(1u64))
        } else {
            v
        }
    }
}

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot
        } else {
            w[q.0 as usize] &= !(1 << shot)
        }
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
fn getb(w: &[u64], q: QubitId, shot: usize) -> u64 {
    (w[q.0 as usize] >> shot) & 1
}
fn mask(l: usize) -> N {
    (N::from(1u64) << l) - N::from(1u64)
}
