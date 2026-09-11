use super::*;
use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, QubitId, NO_BIT};
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

struct Random { mode: usize, rng: sha3::Shake256Reader }
impl XofReader for Random {
    fn read(&mut self, out: &mut [u8]) {
        match self.mode { 0 => out.fill(0), 1 => out.fill(255), 2 => out.fill(0x55), _ => self.rng.read(out) }
    }
}

fn test(n: usize, available: usize, nested: bool) -> usize {
    let Some(chunks) = crate::point_add::clean_chunk_plan::plan(n - 1, available) else { return 0; };
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let b = c.alloc_qreg_bits("test.b", n);
    let g = c.alloc_qreg("test.g");
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    let build = |c: &mut Circuit| emit(c, &g, &a.iter().collect::<Vec<_>>(), &b.iter().collect::<Vec<_>>(), &chunks);
    if nested { c.with_conditions(&[outer, inner], build); } else { build(&mut c); }
    assert!(c.b.peak_qubits as usize <= 2 * n + 1 + available);
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nb = nb.max(inner.raw() as u64 + 1);
    let ids: Vec<_> = a.iter().chain(&b).chain([&g]).map(|q| QubitId(q.id().into())).collect();
    let total = if n <= 7 { 1usize << (2 * n + 1) } else { 2048 };
    let mut checked = 0;
    for mode in 0..4 {
        let mut seed = Shake256::default(); seed.update(b"chunked-controlled-add-v1");
        let mut rng = Random { mode, rng: seed.finalize_xof() };
        let mut seed = Shake256::default(); seed.update(b"chunked-controlled-add-inputs-v1");
        let mut input_rng = seed.finalize_xof();
        for first in (0..total).step_by(64) {
            let valid = 64.min(total - first);
            let mask = u64::MAX >> (64 - valid);
            let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
            let mut initial = Vec::new();
            for (bit, &id) in ids.iter().enumerate() {
                let word = if n <= 7 {
                    (0..valid).fold(0, |v, shot| v | ((((first + shot) >> bit) & 1) as u64) << shot)
                } else {
                    let mut bytes = [0u8; 8]; input_rng.read(&mut bytes);
                    let mut v = u64::from_le_bytes(bytes) & !15;
                    if bit < n || bit == 2 * n { v |= 2; }
                    if bit == n || bit == 2 * n { v |= 4; }
                    if bit < n || bit == n || bit == 2 * n { v |= 8; }
                    v
                };
                *sim.qubit_mut(id) = word;
                initial.push(word);
            }
            let outer_mask = 0xaaaaaaaaaaaaaaaa;
            let inner_mask = 0xcccccccccccccccc;
            *sim.bit_mut(BitId(outer.raw().into())) = outer_mask;
            *sim.bit_mut(BitId(inner.raw().into())) = inner_mask;
            let enabled = initial[2 * n] & if nested { outer_mask & inner_mask } else { u64::MAX };
            let mut expected = initial.clone();
            let mut carry = 0;
            for i in 0..n {
                let (a, b) = (initial[i], initial[n + i]);
                expected[i] ^= enabled & (b ^ carry);
                carry = (a & b) | ((a ^ b) & carry);
            }
            let scratch = BitId(nb);
            let mut push = Op::empty(); push.kind = K::PushCondition; push.c_condition = scratch;
            let mut pop = Op::empty(); pop.kind = K::PopCondition;
            let mut active = u64::MAX;
            let mut stack = Vec::new();
            for op in &c.b.ops {
                match op.kind {
                    K::PushCondition => { stack.push(active); active &= sim.bit(op.c_condition); }
                    K::PopCondition => active = stack.pop().unwrap(),
                    _ => {
                        if op.kind == K::R {
                            let condition = active & if op.c_condition == NO_BIT { u64::MAX } else { sim.bit(op.c_condition) };
                            assert_eq!(sim.qubit(op.q_target) & mask & condition, 0, "dirty reset");
                        }
                        *sim.bit_mut(scratch) = active;
                        sim.apply_iter([&push, op, &pop].into_iter());
                    }
                }
            }
            assert!(stack.is_empty());
            assert_eq!(sim.phase & mask, 0, "n={n}, available={available}, nested={nested}, mode={mode}");
            for (&id, &value) in ids.iter().zip(&expected) {
                assert_eq!(sim.qubit(id) & mask, value & mask);
                *sim.qubit_mut(id) = 0;
            }
            assert!(sim.qubits.iter().all(|v| v & mask == 0));
            checked += valid;
        }
    }
    checked
}

pub(crate) fn run() {
    let mut checked = 0;
    for n in (2usize..=7).chain([16, 73, 85, 128, 256, 257]) {
        for available in [2usize, 3, 4, 8, 16, 32, 64, 100, n - 1] {
            for nested in [false, true] { checked += test(n, available, nested); }
        }
    }
    eprintln!("CHUNKED_CONTROLLED_ADD PASS: {checked} input/measurement cases, both controls, nested conditions, long carries, source restoration, phase and every reset");
}
