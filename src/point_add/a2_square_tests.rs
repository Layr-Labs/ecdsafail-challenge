use super::{tri_square_k2r,tri_square_k2r_inv,Builder};
use crate::circuit::{Op,QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;
/// Deterministic u64 stream for the simulator's R/Hmr draws (splitmix64).
struct Xof64(u64);

impl XofReader for Xof64 {
    fn read(&mut self, out: &mut [u8]) {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out.copy_from_slice(&z.to_le_bytes()[..out.len()]);
    }
}

/// (qubits, bits) needed to simulate `ops`.
fn dims(ops: &[Op]) -> (usize, usize) {
    let (mut nq, mut nb) = (0u64, 0u64);
    for op in ops {
        for q in [op.q_control1, op.q_control2, op.q_target] {
            if q.0 != u64::MAX {
                nq = nq.max(q.0 + 1);
            }
        }
        for b in [op.c_target, op.c_condition] {
            if b.0 != u64::MAX {
                nb = nb.max(b.0 + 1);
            }
        }
    }
    (nq as usize, nb as usize)
}

/// Simulate `ops` on 64 lanes at once; lane `l` gets `inputs[r][l]` in
/// register `r`. Returns (qubits, bits, phase).
fn run_ops(ops: &[Op], inputs: &[(&[QubitId], [u64; 64])], seed: u64) -> (Vec<u64>, Vec<u64>, u64) {
    let (nq, nb) = dims(ops);
    let mut xof = Xof64(seed);
    let mut sim = Simulator::new(nq.max(1), nb.max(1), &mut xof);
    for (reg, values) in inputs {
        for (lane, &v) in values.iter().enumerate() {
            for (i, &q) in reg.iter().enumerate() {
                if v >> i & 1 == 1 {
                    sim.qubits[q.0 as usize] |= 1 << lane;
                }
            }
        }
    }
    sim.apply_iter(ops.iter());
    (sim.qubits, sim.bits, sim.phase)
}

fn get_word(q: &[u64], reg: &[QubitId], lane: usize) -> u64 {
    reg.iter()
        .enumerate()
        .fold(0u64, |acc, (i, &qq)| acc | (((q[qq.0 as usize] >> lane) & 1) << i))
}


#[test]
fn a2_nested_square_value_phase_and_cleanup() {
    // Small analog of the shipping sum>=65, low>=64 policy. Set once because
    // the policy accessors use OnceLock. This binary runs this one square test.
    std::env::set_var("SQ_SPLIT_SUM_MIN","5");
    std::env::set_var("SQ_SPLIT_LOW_MIN","4");
    for cut in ["0","1"] {
        std::env::set_var("PP_CUT_SQIDENT",cut);
        for m in [8usize,9,10] {
            for inverse in [false,true] {
                let mut circ=Builder::new();
                let x=circ.alloc_qubits(m);let product=circ.alloc_qubits(2*m);
                let retained=tri_square_k2r(&mut circ,&x,&product);
                if inverse {tri_square_k2r_inv(&mut circ,&x,&product,retained);}
                let ops=circ.take_ops();
                for run in 0..(1u64<<m)/64 {
                    let mut values=[0u64;64];for (i,v) in values.iter_mut().enumerate(){*v=run*64+i as u64;}
                    for seed in [0xCAB00D1E,0x01234567,0x89ABCDEF,0xFACECAFE] {
                        let(q,_,phase)=run_ops(&ops,&[(&x,values)],seed+run);
                        assert_eq!(phase,0,"phase cut={cut} m={m} inv={inverse}");
                        for lane in 0..64 {
                            assert_eq!(get_word(&q,&product,lane),if inverse{0}else{values[lane]*values[lane]});
                            if inverse {assert_eq!(get_word(&q,&x,lane),values[lane]);}
                        }
                        if inverse {for id in 3*m..q.len(){assert_eq!(q[id],0,"dirty scratch id={id}");}}
                    }
                }
            }
        }
    }
}
