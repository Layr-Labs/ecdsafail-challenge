//! Source-bound native tests of the new low3 bridge; no packed-layout claim.
use super::*;
use crate::{circuit::{Op, OperationType as K}, sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;
impl XofReader for Fixed { fn read(&mut self, out: &mut [u8]) { out.fill(0x69); } }
fn rnd(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
fn put(w: &mut [u64], q: usize, lane: usize, value: bool) {
    let mask = 1u64 << lane;
    w[q] = (w[q] & !mask) | if value { mask } else { 0 };
}
struct Program {
    ops: Vec<Op>, word: [usize; 12], source: Vec<usize>, target: Vec<usize>,
    decision: usize, g: usize, ha: usize, dirty: Vec<usize>, nq: usize, t: usize,
}
fn program(n: usize, shift: usize, aliases: bool) -> Program {
    let mut circ = Circuit::new(); circ.b.count_only = false; circ.b.fiat_hash = None;
    let source = circ.alloc_qreg_bits("q793.r01.source", n);
    let chart = circ.alloc_qreg_bits("q793.r01.chart", 12);
    let word: [&QReg; 12] = std::array::from_fn(|i| {
        if aliases && (6..9).contains(&i) && shift+i-6 < n { &source[shift+i-6] } else { &chart[i] }
    });
    let target = circ.alloc_qreg_bits("q793.r01.high", n-3);
    let decision = circ.alloc_qreg("q793.r01.existing_h");
    let g = circ.alloc_qreg("q793.r01.guard"); let ha = circ.alloc_qreg("q793.r01.existing_HA");
    let dirty = circ.alloc_qreg_bits("q793.r01.existing_dirty", 6);
    let nq = circ.b.next_qubit as usize;
    emit(&mut circ, word, &source, &target, &decision, &g, &ha, &dirty, shift);
    assert_eq!(circ.b.next_qubit as usize, nq);
    let ops = circ.b.ops.clone();
    for op in &ops { op.validate(); assert!(matches!(op.kind, K::X | K::CX | K::CCX)); }
    let t = ops.iter().filter(|o| o.kind == K::CCX).count();
    Program { ops, word: word.map(|q| q.id() as usize), source: source.iter().map(|q| q.id() as usize).collect(),
        target: target.iter().map(|q| q.id() as usize).collect(), decision: decision.id() as usize,
        g: g.id() as usize, ha: ha.id() as usize, dirty: dirty.iter().map(|q| q.id() as usize).collect(), nq, t }
}
fn lane(p: &Program, n: usize, shift: usize, index: usize, codes: &[usize], exhaustive: bool,
        seed: &mut u64, before: &mut [u64], after: &mut [u64], l: usize) {
    let mut z = index;
    let code = codes[z % codes.len()]; z /= codes.len();
    let mut x = vec![false; n]; let mut y = vec![false; n];
    for bit in 0..3 {
        if shift+bit < n { x[shift+bit] = code >> (6+bit) & 1 != 0; }
        y[bit] = residual(code) >> bit & 1 != 0;
    }
    for bit in (shift+3).min(n)..n {
        x[bit] = if exhaustive { let b = z & 1 != 0; z >>= 1; b } else { rnd(seed) & 1 != 0 };
    }
    for bit in 3..n {
        y[bit] = if exhaustive { let b = z & 1 != 0; z >>= 1; b } else { rnd(seed) & 1 != 0 };
    }
    let h = z & 1 != 0; z >>= 1;
    let (g, ha) = match z % 3 { 0 => (true, false), 1 => (false, false), _ => (false, true) }; z /= 3;
    let dirty = if exhaustive { (index / 6 + index / 3072) & 63 } else { (z + index) & 63 };
    if !exhaustive && (index / codes.len()) % 4 != 3 {
        let pattern = (index / codes.len()) % 4;
        for bit in (shift+3).min(n)..n { x[bit] = pattern & 1 != 0; }
        for bit in 3..n { y[bit] = pattern & 2 != 0; }
    }
    let ge = (0..n).rev().find(|&i| x[i] != y[i]).map(|i| y[i]).unwrap_or(true);
    let decision = if g { h ^ ge } else { h };
    let take = g && decision;
    let mut output = y.clone(); let mut borrow = false;
    if take { for bit in 0..n {
        output[bit] = y[bit] ^ x[bit] ^ borrow;
        borrow = (!y[bit] && (x[bit] || borrow)) || (x[bit] && borrow);
    }}
    let b = code >> 3 & 7; let q = code >> 9 & 7;
    let amount = if shift < 3 { ((code >> 6 & 7) << shift) & 7 } else { 0 };
    let b_new = if take && code & 1 == 0 { b.wrapping_sub(amount) & 7 } else { b };
    let q_new = if take && shift < 3 { (q + (1 << shift)) & 7 } else { q };
    let next = (code & (7 | (7 << 6))) | (b_new << 3) | (q_new << 9);
    assert_eq!(residual(next), output[..3].iter().enumerate().map(|(i,&b)| (b as usize) << i).sum::<usize>());
    for bit in 0..n { put(before, p.source[bit], l, x[bit]); put(after, p.source[bit], l, x[bit]); }
    for bit in 0..12 { put(before, p.word[bit], l, code >> bit & 1 != 0); put(after, p.word[bit], l, next >> bit & 1 != 0); }
    for bit in 3..n { put(before, p.target[bit-3], l, y[bit]); put(after, p.target[bit-3], l, output[bit]); }
    for (w, d) in [(&mut *before, h), (&mut *after, decision)] {
        put(w, p.decision, l, d); put(w, p.g, l, g); put(w, p.ha, l, ha);
        for (i, &q) in p.dirty.iter().enumerate() { put(w, q, l, dirty >> i & 1 != 0); }
    }
}
fn check(n: usize, shift: usize, aliases: bool) -> (usize, usize, String) {
    let p = program(n, shift, aliases);
    let v_width = n.saturating_sub(shift).min(3);
    let codes: Vec<_> = (0..4096).filter(|&c| valid(c) && (c >> 6 & 7) < (1 << v_width)).collect();
    let exhaustive = n <= 5;
    let raw_cases = if exhaustive { codes.len() * (1 << n.saturating_sub(shift+3)) * (1 << (n-3)) * 6 }
                    else { codes.len() * 6 * 4 };
    let cases = raw_cases.div_ceil(64) * 64;
    let mut random = Fixed; let mut sim = Simulator::new(p.nq, 0, &mut random);
    let mut seed = 0x793f01ab345c87d1 ^ n as u64 ^ ((shift as u64) << 32) ^ (aliases as u64);
    for first in (0..cases).step_by(64) {
        let mut before: Vec<_> = (0..p.nq).map(|_| rnd(&mut seed)).collect(); let mut expected = before.clone();
        for l in 0..64 { lane(&p, n, shift, (first+l) % raw_cases, &codes, exhaustive, &mut seed, &mut before, &mut expected, l); }
        sim.qubits.copy_from_slice(&before); sim.phase = 0; sim.apply_iter(p.ops.iter());
        assert_eq!(sim.qubits, expected, "Q793 R01 n={n} shift={shift} alias={aliases} first={first}"); assert_eq!(sim.phase, 0);
        let effect = sim.qubits[p.decision]; sim.qubits[p.dirty[0]] ^= effect; before[p.dirty[0]] ^= effect;
        sim.apply_iter(p.ops.iter().rev());
        assert_eq!(sim.qubits, before, "Q793 R01 dirty-consumer inverse n={n} shift={shift} first={first}"); assert_eq!(sim.phase, 0);
    }
    // Complete 4096 chart-code off-guard screen, both HA/h and all64 dirty
    // patterns over every code. High words are independently arbitrary.
    let off_cases = 4096 * 2 * 2 * 64;
    for first in (0..off_cases).step_by(64) {
        let mut before: Vec<_> = (0..p.nq).map(|_| rnd(&mut seed)).collect();
        for l in 0..64 {
            let z = first+l; let code = z & 4095;
            for bit in 0..12 { put(&mut before, p.word[bit], l, code >> bit & 1 != 0); }
            put(&mut before, p.g, l, false); put(&mut before, p.ha, l, z >> 12 & 1 != 0); put(&mut before, p.decision, l, z >> 13 & 1 != 0);
            for (bit, &q) in p.dirty.iter().enumerate() { put(&mut before, q, l, z >> (14+bit) & 1 != 0); }
        }
        sim.qubits.copy_from_slice(&before); sim.phase = 0; sim.apply_iter(p.ops.iter());
        assert_eq!(sim.qubits, before, "Q793 R01 off-guard n={n} shift={shift} alias={aliases} first={first}"); assert_eq!(sim.phase, 0);
        sim.apply_iter(p.ops.iter().rev()); assert_eq!(sim.qubits, before); assert_eq!(sim.phase, 0);
    }
    eprintln!("Q793_R01_FUSED_LOW_CASE_PASS n={n} shift={shift} aliases={aliases} active={cases} offguard={off_cases} Q={} T={} ops={}", p.nq, p.t, p.ops.len());
    (cases, off_cases, format!("{{\"n\":{n},\"shift\":{shift},\"v_source_aliases\":{aliases},\"active_and_guard_lanes\":{cases},\"offguard_lanes\":{off_cases},\"all_chart_high_h_guard_combinations\":{exhaustive},\"all64_dirty_patterns_offguard\":true,\"dirty_consumer_inverse\":true,\"forward_T\":{},\"ops\":{},\"extra_allocations\":0}}", p.t, p.ops.len()))
}
pub(super) fn run() {
    let mut active = 0; let mut off = 0; let mut rows = Vec::new();
    for n in [3,4,5,6,7,256] { for shift in 0..=4 { for aliases in [false,true] {
        let (a, b, row) = check(n, shift, aliases); active += a; off += b; rows.push(row);
    }}}
    println!("{{\"kind\":\"Q793 exact fused virtual low3 R01 native component\",\"active_lanes\":{active},\"offguard_lanes\":{off},\"results\":[{}],\"packed_cargo_adapter_tested\":false,\"whole_q793_proven\":false}}", rows.join(","));
}
