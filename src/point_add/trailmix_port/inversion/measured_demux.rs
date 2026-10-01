//! Exact one-hot XOR write with a measured prefix tree.
use super::*;

fn visit(c: &mut Circuit, q: &[QReg], address: &[QReg], prefix: usize, parent: &QReg) {
    if prefix >= q.len() { return; }
    let Some((bit, lower)) = address.split_last() else {
        c.cx(parent, &q[prefix]);
        return;
    };
    let right = prefix + (1usize << lower.len());
    if lower.is_empty() {
        if right < q.len() {
            // Conjugating the shared product write toggles both destinations,
            // preserving arbitrary old values in them.
            c.cx(&q[right], &q[prefix]);
            c.ccx(parent, bit, &q[right]);
            c.cx(&q[right], &q[prefix]);
            c.cx(parent, &q[prefix]);
        } else {
            c.x(bit);
            c.ccx(parent, bit, &q[prefix]);
            c.x(bit);
        }
        return;
    }
    let child = c.alloc_qreg("demux.prefix");
    if right < q.len() {
        c.ccx(parent, bit, &child);
        visit(c, q, lower, right, &child);
        c.cx(parent, &child);
        visit(c, q, lower, prefix, &child);
        c.cx(parent, &child);
        c.clear_and(&child, parent, bit);
    } else {
        c.x(bit);
        c.ccx(parent, bit, &child);
        visit(c, q, lower, prefix, &child);
        c.clear_and(&child, parent, bit);
        c.x(bit);
    }
    c.zero_and_free(child);
}

pub(super) fn apply(c: &mut Circuit, q: &[QReg], address: &[QReg], active: &QReg) -> bool {
    if std::env::var("MIDQ_MEASURED_DEMUX").ok().as_deref() != Some("1") { return false; }
    c.flush_pending_frees();
    if address.len() >= usize::BITS as usize || q.len() > 1usize << address.len() {
        return false;
    }
    let cap = env_usize("MIDQ_PREFIX_QCAP", 1019);
    if address.len().saturating_sub(1) > cap.saturating_sub(c.b.active_qubits as usize) {
        return false;
    }
    let section = c.push_section("p.demux.measured");
    visit(c, q, address, 0, active);
    c.pop_section(&section);
    true
}

pub(crate) fn selftest() {
    use crate::circuit::{analyze_ops, BitId};
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};
    struct Measurements { forced: Option<u8>, random: sha3::Shake256Reader }
    impl XofReader for Measurements {
        fn read(&mut self, bytes: &mut [u8]) {
            if let Some(value) = self.forced { bytes.fill(value); }
            else { self.random.read(bytes); }
        }
    }
    let mut checked = 0;
    for width in 0usize..=5 {
        for size in [1usize, 2, 3, 5, 9, 18, 26, 32] {
            if size > 1 << width { continue; }
            for nested in [false, true] {
                let mut c = Circuit::new();
                let address = c.alloc_qreg_bits("test.address", width);
                let q = c.alloc_qreg_bits("test.q", size);
                let active = c.alloc_qreg("test.active");
                let outer = c.alloc_input_bit();
                let inner = c.alloc_input_bit();
                if nested { c.with_conditions(&[outer, inner], |c| visit(c, &q, &address, 0, &active)); }
                else { visit(&mut c, &q, &address, 0, &active); }
                let ids: Vec<_> = address.iter().chain(&q).chain([&active])
                    .map(|q| QubitId(q.id().into())).collect();
                let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
                let nq = (nq as usize).max(ids.iter().map(|q| q.0 as usize + 1).max().unwrap());
                let nb = (nb as usize).max(inner.raw() as usize + 1);
                let mut inputs = Vec::new();
                for value in 0usize..1 << width {
                    for enabled in 0..=1usize {
                        let masks: Vec<usize> = if size <= 5 { (0..1usize << size).collect() }
                            else { vec![0, (1 << size) - 1, 0x55555555 & ((1 << size) - 1),
                                (value.wrapping_mul(0x9e3779b9)) & ((1 << size) - 1)] };
                        for mask in masks {
                            inputs.push(value | (mask << width) | (enabled << (width + size)));
                        }
                    }
                }
                for forced in [Some(0), Some(255), Some(0x55), None] {
                    let mut hash = Shake256::default(); hash.update(b"measured-demux-v1");
                    let mut rng = Measurements { forced, random: hash.finalize_xof() };
                    for batch in inputs.chunks(64) {
                        let mask = u64::MAX >> (64 - batch.len());
                        let mut sim = Simulator::new(nq, nb + 1, &mut rng);
                        let outer_mask = 0xaaaaaaaaaaaaaaaa;
                        let inner_mask = 0xcccccccccccccccc;
                        *sim.bit_mut(BitId(outer.raw().into())) = outer_mask;
                        *sim.bit_mut(BitId(inner.raw().into())) = inner_mask;
                        for (bit, &id) in ids.iter().enumerate() {
                            for (shot, &value) in batch.iter().enumerate() {
                                *sim.qubit_mut(id) |= ((value >> bit & 1) as u64) << shot;
                            }
                        }
                        predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops, mask);
                        assert_eq!(sim.phase & mask, 0);
                        for (shot, &value) in batch.iter().enumerate() {
                            let addr = value & ((1 << width) - 1);
                            let enabled = value >> (width + size) & 1 != 0;
                            let selected = !nested || (outer_mask & inner_mask) >> shot & 1 != 0;
                            let want = if addr < size && enabled && selected {
                                value ^ (1 << (width + addr))
                            } else { value };
                            for (bit, &id) in ids.iter().enumerate() {
                                assert_eq!(sim.qubit(id) >> shot & 1, (want >> bit & 1) as u64);
                            }
                        }
                        for &id in &ids { *sim.qubit_mut(id) = 0; }
                        assert!(sim.qubits.iter().all(|v| v & mask == 0));
                        checked += batch.len();
                    }
                }
            }
        }
    }
    eprintln!("MEASURED_DEMUX PASS: {checked} basis/measurement cases, arbitrary XOR targets, nested conditions, phase and pre-reset");
}
