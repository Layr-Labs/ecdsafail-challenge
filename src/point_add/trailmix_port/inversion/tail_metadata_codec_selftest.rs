use super::*;
use super::super::predicate_clear_selftest::checked_apply;
use crate::circuit::{analyze_ops, OperationType};
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut seed = Shake256::default();
        seed.update(b"tail-metadata-codec-v1");
        Self([Some(0), Some(255), Some(0x55), None][mode], seed.finalize_xof())
    }
}
impl XofReader for Measurements {
    fn read(&mut self, bytes: &mut [u8]) {
        if let Some(byte) = self.0 { bytes.fill(byte); } else { self.1.read(bytes); }
    }
}
fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}
fn raw_ids(raw: &Raw) -> [Vec<QubitId>; 4] {
    [ids(&raw.qtag), ids(&raw.ctz), ids(std::slice::from_ref(&raw.selector)), ids(std::slice::from_ref(&raw.terminal))]
}
fn write<R: XofReader>(sim: &mut Simulator<R>, reg: &[QubitId], lane: usize, value: usize) {
    for (i, &q) in reg.iter().enumerate() {
        if value >> i & 1 != 0 { *sim.qubit_mut(q) |= 1 << lane; }
    }
}
fn read<R: XofReader>(sim: &Simulator<R>, reg: &[QubitId], lane: usize) -> usize {
    reg.iter().enumerate().fold(0, |value, (i, &q)| value | (((sim.qubit(q) >> lane & 1) as usize) << i))
}
fn clean<R: XofReader>(sim: &Simulator<R>, keep: &[QubitId], mask: u64) {
    assert_eq!(sim.phase & mask, 0, "phase");
    for (i, &bits) in sim.qubits.iter().enumerate() {
        if !keep.contains(&QubitId(i as u64)) { assert_eq!(bits & mask, 0, "scratch {i}"); }
    }
}

pub(crate) fn run() {
    let mut c = Circuit::new();
    // The proposed integration boundary has about 956 live qubits including
    // metadata. Retain unrelated passengers when measuring this local peak.
    let passengers = c.alloc_qreg_bits("passengers", 942);
    let raw = Raw {
        qtag: c.alloc_qreg_bits("qtag", 5), ctz: c.alloc_qreg_bits("ctz", 7),
        selector: c.alloc_qreg("selector"), terminal: c.alloc_qreg("terminal"),
    };
    let input = raw_ids(&raw);
    let start = c.b.active_qubits;
    let packed = pack(&mut c, raw);
    let packed_ids = ids(&packed.bits);
    assert_eq!(packed_ids, input[0].iter().chain(&input[1]).copied().collect::<Vec<_>>());
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits, start - 2, "exact two-qubit persistent saving");
    let packed_peak = c.b.peak_qubits;
    let mid = c.b.ops.len();
    // Force freed IDs to be reused before reconstruction.
    let scratch = c.alloc_qreg_bits("interlude", 24);
    for bit in &scratch { c.x(bit); }
    for bit in &scratch { c.x(bit); }
    for bit in scratch { c.zero_and_free(bit); }
    let raw = unpack(&mut c, packed);
    let output = raw_ids(&raw);
    assert_eq!(input[0], output[0]);
    assert_eq!(input[1], output[1]);
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits, start);
    let all_peak = c.b.peak_qubits;
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut cases = Vec::new();
    for k in 0..=85 { for s in 0..=1 { for q in 0..=18 {
        cases.push([q, k, s, 0]);
    } } }
    cases.push([18, 0, 0, 1]);
    let mut ranks = std::collections::BTreeSet::new();
    for [q, k, s, t] in &cases { assert!(ranks.insert(q + 38*k + 19*s + 3250*t)); }
    assert_eq!(ranks, (0..=3268).collect());
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            let mask = u64::MAX >> (64 - batch.len());
            for (lane, values) in batch.iter().enumerate() {
                for (reg, &value) in input.iter().zip(values) { write(&mut sim, reg, lane, value); }
            }
            checked_apply(&mut sim, &c.b.ops[..mid], mask);
            clean(&sim, &packed_ids, mask);
            for (lane, [q, k, s, t]) in batch.iter().enumerate() {
                assert_eq!(read(&sim, &packed_ids, lane), q + 38*k + 19*s + 3250*t);
            }
            checked_apply(&mut sim, &c.b.ops[mid..], mask);
            let keep: Vec<_> = output.iter().flatten().copied().collect();
            clean(&sim, &keep, mask);
            for (lane, values) in batch.iter().enumerate() {
                for (reg, &value) in output.iter().zip(values) { assert_eq!(read(&sim, reg, lane), value); }
            }
        }
    }
    let toffoli = |ops: &[crate::circuit::Op]| ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count();
    eprintln!("TAIL_METADATA_CODEC PASS 3269 valid states x 4 measurement streams; packed/unpacked values, exact phase, pre-reset, scratch, reused IDs; live {start}->{}->{start}, pack_peak={packed_peak}, combined_peak={all_peak}, pack_T={}, unpack_T={}", start - 2, toffoli(&c.b.ops[..mid]), toffoli(&c.b.ops[mid..]));
    drop(passengers);
}
