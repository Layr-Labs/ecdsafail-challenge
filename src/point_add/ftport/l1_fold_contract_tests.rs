//! Contract gates for nested classical conditions and recorded inverses.
//! Included as a cfg(test) child of modp_ft; no production dispatch changes.
use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Tape { first: Option<u64>, rest: u64 }
impl XofReader for Tape {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.first.take().unwrap_or(self.rest).to_le_bytes());
    }
}

fn mask(n: usize) -> u128 { (1u128 << n) - 1 }
fn input(n: usize, shot: usize) -> u128 {
    match shot {
        0 => 0,
        1 => mask(n),
        2 => 1,
        3 => mask(n) - 1,
        4 => (1u128 << (n - 1)) - 1,
        5 => 1u128 << (n - 1),
        _ => (shot as u128).wrapping_mul(0x19e3_779b_97f4_a7c1_9e37_79b9u128) & mask(n),
    }
}
fn load(qs: &mut [u64], reg: &[QubitId], shot: usize, value: u128) {
    for (i, q) in reg.iter().enumerate() {
        qs[q.0 as usize] |= (((value >> i) & 1) as u64) << shot;
    }
}
fn read(qs: &[u64], reg: &[QubitId], shot: usize) -> u128 {
    reg.iter().enumerate().fold(0, |v, (i, q)| v | (((qs[q.0 as usize] >> shot) & 1) as u128) << i)
}
fn preserved_except_target(sim: &Simulator<'_, Tape>, before: &[u64], target: &[QubitId], tag: &str) {
    for (q, (&got, &want)) in sim.qubits.iter().zip(before).enumerate() {
        if !target.iter().any(|t| t.0 as usize == q) {
            assert_eq!(got, want, "{tag} qubit {q}");
        }
    }
    assert_eq!(sim.phase, 0, "{tag} phase");
}

#[test]
fn l1_fold_nested_classical_snapshot_exact_counts() {
    let (n, p) = (58usize, 38usize);
    let (need, loan) = (n - 1, n - 1 - p);
    let mut b = B::new();
    let target = b.alloc_n(n);
    let h = b.alloc();
    let pool = b.alloc_n(p);
    let spectator = b.alloc();
    // This known-zero spectator produces the outer classical mask without
    // phase or value effects. Inner AND erases reuse bit0 after the snapshot.
    b.measure_and_push(spectator);
    const_add_recycled(&mut b, &target, h, C, &pool);
    b.pop_classical();
    for outer in [0u64, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa, 0x00ff_00ff_00ff_00ff] {
        for inner in [0u64, u64::MAX] {
            let mut tape = Tape { first: Some(outer), rest: inner };
            let mut sim = Simulator::new(b.peak as usize, 10_100, &mut tape);
            for shot in 0..64 {
                load(&mut sim.qubits, &target, shot, input(n, shot));
                load(&mut sim.qubits, &[h], shot, (shot & 1) as u128);
            }
            let before = sim.qubits.clone();
            sim.apply_iter(b.ops.iter());
            for shot in 0..64 {
                let add = if outer >> shot & 1 != 0 { (shot & 1) as u128 * C as u128 } else { 0 };
                assert_eq!(read(&sim.qubits, &target, shot), (input(n, shot) + add) & mask(n),
                    "outer={outer:016x} inner={inner:016x} shot={shot}");
            }
            preserved_except_target(&sim, &before, &target, "nested fold");
            let per_active = if super::super::l1_fold::enabled_at(1) {
                need + if inner == 0 { 0 } else { loan }
            } else { need + loan };
            assert_eq!(sim.stats.toffoli_gates, outer.count_ones() as u64 * per_active as u64,
                "outer={outer:016x} inner={inner:016x} executed Toffoli");
        }
    }
    eprintln!("L1_CONTRACT_NESTED PASS outer_masks=4 inner_masks=2 shots=64 inactive_identity all_wire_phase exact_executed_counts enabled={}",
        super::super::l1_fold::enabled_at(1));
}

fn table(n: usize, a: usize) -> u128 {
    let d = if a >= 10 { a as i128 - 16 } else { a as i128 };
    ((C as i128 * d - (a as i128 & 1)) / 2).rem_euclid(1i128 << n) as u128
}

#[test]
fn l1_fold_recorded_and_inverse_use_parent_path() {
    let n = 58;
    for kind in 0..3 {
        for inverse in [false, true] {
            let mut b = B::new();
            let target = b.alloc_n(n);
            let source = b.alloc_n(if kind == 0 { 1 } else { 4 });
            let p = if kind == 2 { 56 } else { 38 };
            let pool = b.alloc_n(p);
            let add: Vec<Option<QubitId>> = (0..n).map(|i| {
                if i % 7 == 3 { None } else { Some(source[i % source.len()]) }
            }).collect();
            b.begin();
            match kind {
                0 => const_add_recycled(&mut b, &target, source[0], C, &pool),
                1 => var_add_recycled(&mut b, &target, &add, &pool),
                2 => add_table_jit(&mut b, &pool, &target, &source, &|a| table(n, a)),
                _ => unreachable!(),
            }
            let record = b.end();
            assert!(b.ops.is_empty(), "kind {kind} leaked operations out of recording");
            b.play(&record, inverse);
            // Parent recorded construction: 57 carries plus a 19-carry
            // recycled prefix. JIT has 11 monomials, 44 remaining carries,
            // and a 13-carry recycled prefix: 11+57+13=81.
            let expected = if kind == 2 { 81u64 } else { 76u64 };
            assert_eq!(b.tof, expected, "kind={kind} inverse={inverse} parent emitted count");
            for forced in [0u64, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa] {
                let mut tape = Tape { first: None, rest: forced };
                let mut sim = Simulator::new(b.peak as usize, 10_100, &mut tape);
                for shot in 0..64 {
                    load(&mut sim.qubits, &target, shot, input(n, shot));
                    load(&mut sim.qubits, &source, shot, (shot as u128) & mask(source.len()));
                }
                let before = sim.qubits.clone();
                sim.apply_iter(b.ops.iter());
                for shot in 0..64 {
                    let a = (shot as u128) & mask(source.len());
                    let value = match kind {
                        0 => a * C as u128,
                        1 => (0..n).filter(|i| i % 7 != 3).map(|i| ((a >> (i % 4)) & 1) << i).sum(),
                        2 => table(n, a as usize),
                        _ => unreachable!(),
                    };
                    let want = if inverse { input(n, shot).wrapping_sub(value) } else { input(n, shot).wrapping_add(value) } & mask(n);
                    assert_eq!(read(&sim.qubits, &target, shot), want,
                        "kind={kind} inverse={inverse} forced={forced:016x} shot={shot}");
                }
                preserved_except_target(&sim, &before, &target, "recorded fold");
                assert_eq!(sim.stats.toffoli_gates, 64 * expected,
                    "kind={kind} inverse={inverse} forced={forced:016x} parent executed count");
            }
        }
    }
    eprintln!("L1_CONTRACT_RECORD PASS const,var,JIT directions=2 forced_masks=3 shots=64 parent_counts76,76,81 all_wire_phase");
}
