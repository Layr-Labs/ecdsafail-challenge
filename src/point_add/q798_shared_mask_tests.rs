//! Native-only fixed exhaustive local check of Q798's actual masked return cell.
//! No point-add input generation, schedule edits, or scientific execution by author.

use super::{masked_down_cell, Lad, Mscr};
use crate::circuit::{OperationType, QubitId};
use crate::point_add::builder::B;
use crate::sim::Simulator;
use sha3::digest::XofReader;

// q0=t, q1=s, q2=x, q3=f, q4=g, q5=clean cell temp, q6=arbitrary spectator.
const NQ: usize = 7;
const NB: usize = 3;

struct Tape {
    words: Vec<u64>,
    used: usize,
}

impl XofReader for Tape {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8, "actual Simulator Hmr/R draw width changed");
        let word = self.words[self.used];
        self.used += 1;
        out.copy_from_slice(&word.to_le_bytes());
    }
}

// Literal parent cell, retained only as an independent comparison arm.
fn parent_cell(b: &mut B) {
    let (t, s, x, f, g, h) = (
        QubitId(0), QubitId(1), QubitId(2), QubitId(3), QubitId(4), QubitId(5),
    );
    b.and_c(t, s, h);
    b.ccx(f, h, x);
    b.and_u(t, s, h);
    b.and_c(g, f, h);
    b.ccx(h, s, t);
    b.and_u(g, f, h);
    b.cx(x, t);
    b.cx(x, s);
}

fn candidate_cell(b: &mut B) {
    let t = [QubitId(0)];
    let s = [QubitId(1)];
    let sc = Mscr {
        f: QubitId(3), t: QubitId(5), gf: QubitId(5),
        chain: vec![], dirty: vec![QubitId(6)],
    };
    let ld = Lad {
        t: &t, s: &s, c0: QubitId(2), srcs: &[],
        f0: false, cmpl: false, sc: &sc, keep_f: true,
    };
    masked_down_cell(b, &ld, 0, QubitId(2), Some(QubitId(4)));
}

// mode 0=forward, 1=literal recorded inverse, 2=forward then literal inverse.
// Context false uses direct emission for forward and a single recording for inverse.
// Context true routes the whole selected word through two nested recordings.
fn build(candidate: bool, nested: bool, mode: usize) -> B {
    let mut b = B::new();
    assert_eq!(b.alloc_n(NQ), (0..NQ).map(|q| QubitId(q as u64)).collect::<Vec<_>>());
    if nested {
        b.begin();
        b.begin();
    }
    let cell = if candidate { candidate_cell } else { parent_cell };
    if mode != 1 {
        cell(&mut b);
    }
    if mode != 0 {
        b.begin();
        cell(&mut b);
        let rec = b.end();
        b.play(&rec, true);
    }
    if nested {
        let inner = b.end();
        b.play(&inner, false);
        let outer = b.end();
        b.play(&outer, false);
    }
    assert_eq!(b.width(), NQ as u64);
    assert_eq!(b.live, NQ as u64);
    assert_eq!(b.peak, NQ as u64);
    b
}

fn initial_qubits() -> Vec<u64> {
    let mut q = vec![0u64; NQ];
    // All 32 independent (t,s,x,f,g), with both values of the spectator.
    for lane in 0..64usize {
        for bit in 0..5 {
            q[bit] |= (((lane >> bit) & 1) as u64) << lane;
        }
        q[6] |= (((lane >> 5) & 1) as u64) << lane;
    }
    q
}

// Independent Boolean map, not gate replay; inverse solves the outputs in reverse order.
fn reference(input: &[u64], mode: usize) -> Vec<u64> {
    let mut q = input.to_vec();
    if mode == 2 {
        return q;
    }
    let (t, s, x, f, g) = (input[0], input[1], input[2], input[3], input[4]);
    if mode == 0 {
        let carry = x ^ (f & t & s);
        q[0] = t ^ (g & f & s) ^ carry;
        q[1] = s ^ carry;
        q[2] = carry;
    } else {
        let source = s ^ x;
        let target = t ^ x ^ (g & f & source);
        q[0] = target;
        q[1] = source;
        q[2] = x ^ (f & target & source);
    }
    q
}

#[test]
fn all_inputs_outcomes_and_recordings() {
    let initial = initial_qubits();
    let initial_bits = vec![0x8123_4567_89ab_cdef, 0x9696_a5a5_5a5a_6969, 0x1234_5678_8765_4321];
    let phases = [0, 0xa569_36c3_96a5_c33c];
    let mut packs = 0usize;
    let mut assertions = 0usize;
    let mut built_words = 0usize;
    for candidate in [false, true] {
        for nested in [false, true] {
            for mode in 0..3usize {
                let b = build(candidate, nested, mode);
                let passes = if mode == 2 { 2usize } else { 1usize };
                let draws = passes * if candidate { 1 } else { 2 };
                let ccx = passes * if candidate { 3 } else { 4 };
                let want_ops = passes * if candidate { 7 } else { 10 };
                assert_eq!(b.tof, ccx as u64);
                assert_eq!(b.ops.len(), want_ops);
                assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::Hmr).count(), draws);
                assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::CZ).count(), draws);
                assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::CX).count(), 2 * passes);
                built_words += 1;
                assertions += 8; // three allocation checks in build plus these five gate checks
                let want_q = reference(&initial, mode);
                for outcome in 0..(1usize << draws) {
                    let words: Vec<u64> = (0..draws)
                        .map(|i| if (outcome >> i) & 1 == 0 { 0 } else { u64::MAX })
                        .collect();
                    let mut want_bits = initial_bits.clone();
                    want_bits[0] = *words.last().unwrap();
                    for phase in phases {
                        let mut tape = Tape { words: words.clone(), used: 0 };
                        {
                            let mut sim = Simulator::new(NQ, NB, &mut tape);
                            sim.qubits.clone_from(&initial);
                            sim.bits.clone_from(&initial_bits);
                            sim.phase = phase;
                            // One complete original apply_iter call per arm, never fragmented.
                            sim.apply_iter(b.ops.iter());
                            assert_eq!(sim.qubits, want_q, "q candidate={candidate} nested={nested} mode={mode} tape={outcome}");
                            assert_eq!(sim.bits, want_bits, "classical scratch and spectators");
                            assert_eq!(sim.phase, phase, "phase candidate={candidate} nested={nested} mode={mode} tape={outcome}");
                            assert_eq!(sim.stats.toffoli_gates, 64 * ccx as u64);
                        }
                        assert_eq!(tape.used, draws);
                        assertions += 5;
                        packs += 1;
                    }
                }
            }
        }
    }
    assert_eq!(built_words, 12);
    assert_eq!(packs, 128);
    assert_eq!(assertions, 736);
    eprintln!("Q798_FUSED_FINITE words={built_words} packs={packs} basis_instances={} state_phase_cost_checks={assertions} failures=0", packs * 64);
}
