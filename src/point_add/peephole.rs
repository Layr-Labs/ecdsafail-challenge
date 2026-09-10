//! Exact cancellation of identical self-inverse quantum operations, with a configurable pass cap.
//!
//! Two identical ops A ... A cancel exactly when every op between them acts on
//! qubits disjoint from A's wires (such ops commute with A, regardless of their
//! own classical conditions), no PushCondition/PopCondition lies between them
//! (both then execute under the identical condition stack), and, when A carries
//! a direct classical condition, that bit is not rewritten between them (both
//! then execute or both skip). Only deletions are performed; surviving ops keep
//! their order. Removing one pair can expose another, so the scan repeats to a
//! fixpoint by default (PEEPHOLE_MAX_PASSES=0); a positive environment value
//! limits productive passes. Qubit 0 (the constant outer control eliminated later) is never a
//! pair member, preserving that pass's exactly-two-toggles invariant.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT};
use std::collections::HashMap;

#[derive(Clone, Copy, Default)]
pub(super) struct PeepholeStats {
    pub passes: usize,
    pub removed_ops: u64,
    pub ccx_uncond_pairs: u64,
    pub ccx_cond_pairs: u64,
    pub other_pairs: u64,
}

fn self_inverse_quantum(kind: K) -> bool {
    matches!(
        kind,
        K::X | K::Z | K::CX | K::CZ | K::Swap | K::CCX | K::CCZ
    )
}

fn wires(op: &Op) -> impl Iterator<Item = u64> {
    [op.q_control2.0, op.q_control1.0, op.q_target.0]
        .into_iter()
        .filter(|&q| q != u64::MAX)
}

fn key(op: &Op) -> (u8, u64, u64, u64, u64) {
    (
        op.kind as u8,
        op.q_control2.0,
        op.q_control1.0,
        op.q_target.0,
        op.c_condition.0,
    )
}

// Zero means no productive-pass cap. PEEPHOLE_MAX_PASSES=32 restores the old cap.
fn configured_max_passes() -> usize {
    match std::env::var("PEEPHOLE_MAX_PASSES") {
        Ok(value) => value.parse().expect("PEEPHOLE_MAX_PASSES must be a nonnegative integer"),
        Err(std::env::VarError::NotPresent) => 0,
        Err(error) => panic!("invalid PEEPHOLE_MAX_PASSES: {error}"),
    }
}

pub(super) fn cancel_identical_pairs(ops: &mut Vec<Op>) -> PeepholeStats {
    cancel_identical_pairs_with_cap(ops, configured_max_passes())
}

fn cancel_identical_pairs_with_cap(ops: &mut Vec<Op>, max_passes: usize) -> PeepholeStats {
    let mut stats = PeepholeStats::default();
    // Use compact dense lookup for the verified frame. Preserve generic
    // original behavior with the same capped algorithm outside that frame.
    let mut nq = 0usize;
    let mut nb = 0usize;
    for op in ops.iter() {
        for q in wires(op) {
            if q > 834 { return cancel_identical_pairs_hashed(ops, max_passes); }
            nq = nq.max(q as usize + 1);
        }
        if op.c_condition != NO_BIT {
            if op.c_condition.0 > 1281 { return cancel_identical_pairs_hashed(ops, max_passes); }
            nb = nb.max(op.c_condition.0 as usize + 1);
        }
        if matches!(op.kind, K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr) {
            if op.c_target == NO_BIT || op.c_target.0 > 1281 { return cancel_identical_pairs_hashed(ops, max_passes); }
            nb = nb.max(op.c_target.0 as usize + 1);
        }
    }
    let mut alive = vec![true; ops.len()];
    loop {
        let pass_started = std::time::Instant::now();
        stats.passes += 1;
        let mut last_touch = vec![-1i64; nq];
        let mut last_bit_write = vec![-1i64; nb];
        let mut last_pushpop = -1i64;
        let mut depth = 0i64;
        let mut last_op: HashMap<(u8, u64, u64, u64, u64), i64> = HashMap::new();
        let mut removed = 0u64;
        for i in 0..ops.len() {
            if !alive[i] {
                continue;
            }
            let op = ops[i];
            let idx = i as i64;
            match op.kind {
                K::PushCondition => {
                    last_pushpop = idx;
                    depth += 1;
                }
                K::PopCondition => {
                    last_pushpop = idx;
                    depth -= 1;
                }
                K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                    last_bit_write[op.c_target.0 as usize] = idx;
                }
                _ => {}
            }
            let touches_outer = wires(&op).any(|q| q == 0);
            if self_inverse_quantum(op.kind) && !touches_outer {
                let k = key(&op);
                let mut cancel = false;
                if let Some(&p) = last_op.get(&k) {
                    let gap_clean = last_pushpop < p
                        && (op.c_condition == NO_BIT
                            || last_bit_write[op.c_condition.0 as usize] < p)
                        && wires(&op).all(|w| last_touch[w as usize] == p);
                    if gap_clean {
                        cancel = true;
                        alive[p as usize] = false;
                        alive[i] = false;
                        removed += 2;
                        if matches!(op.kind, K::CCX | K::CCZ) {
                            if depth > 0 || op.c_condition != NO_BIT {
                                stats.ccx_cond_pairs += 1;
                            } else {
                                stats.ccx_uncond_pairs += 1;
                            }
                        } else {
                            stats.other_pairs += 1;
                        }
                        last_op.remove(&k);
                    }
                }
                if cancel {
                    continue;
                }
                last_op.insert(k, idx);
            }
            for w in wires(&op) {
                last_touch[w as usize] = idx;
            }
        }
        stats.removed_ops += removed;
        eprintln!("PEEPHOLE_PASS: pass={} removed_ops={} cumulative_removed_ops={} ccx_uncond_pairs={} ccx_cond_pairs={} other_pairs={} seconds={:.6} max_passes={}",
            stats.passes, removed, stats.removed_ops, stats.ccx_uncond_pairs,
            stats.ccx_cond_pairs, stats.other_pairs, pass_started.elapsed().as_secs_f64(), max_passes);
        if removed == 0 {
            stats.passes -= 1; // exclude the final pass that only observes the fixpoint
            break;
        }
        if max_passes != 0 && stats.passes == max_passes {
            break; // include every nonempty pass, including the capped last pass
        }
    }
    let mut at = 0;
    ops.retain(|_| {
        let keep = alive[at];
        at += 1;
        keep
    });
    stats
}

// The exact hashed reference is retained for IDs outside the dense frame.
fn cancel_identical_pairs_hashed(ops: &mut Vec<Op>, max_passes: usize) -> PeepholeStats {
    let mut stats = PeepholeStats::default();
    let mut alive = vec![true; ops.len()];
    loop {
        let pass_started = std::time::Instant::now();
        stats.passes += 1;
        let mut last_touch: HashMap<u64, i64> = HashMap::new();
        let mut last_bit_write: HashMap<u64, i64> = HashMap::new();
        let mut last_pushpop = -1i64;
        let mut depth = 0i64;
        let mut last_op: HashMap<(u8, u64, u64, u64, u64), i64> = HashMap::new();
        let mut removed = 0u64;
        for i in 0..ops.len() {
            if !alive[i] {
                continue;
            }
            let op = ops[i];
            let idx = i as i64;
            match op.kind {
                K::PushCondition => {
                    last_pushpop = idx;
                    depth += 1;
                }
                K::PopCondition => {
                    last_pushpop = idx;
                    depth -= 1;
                }
                K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                    last_bit_write.insert(op.c_target.0, idx);
                }
                _ => {}
            }
            let touches_outer = wires(&op).any(|q| q == 0);
            if self_inverse_quantum(op.kind) && !touches_outer {
                let k = key(&op);
                let mut cancel = false;
                if let Some(&p) = last_op.get(&k) {
                    let gap_clean = last_pushpop < p
                        && (op.c_condition == NO_BIT
                            || last_bit_write.get(&op.c_condition.0).copied().unwrap_or(-1) < p)
                        && wires(&op).all(|w| last_touch.get(&w).copied().unwrap_or(-1) == p);
                    if gap_clean {
                        cancel = true;
                        alive[p as usize] = false;
                        alive[i] = false;
                        removed += 2;
                        if matches!(op.kind, K::CCX | K::CCZ) {
                            if depth > 0 || op.c_condition != NO_BIT {
                                stats.ccx_cond_pairs += 1;
                            } else {
                                stats.ccx_uncond_pairs += 1;
                            }
                        } else {
                            stats.other_pairs += 1;
                        }
                        last_op.remove(&k);
                    }
                }
                if cancel {
                    continue;
                }
                last_op.insert(k, idx);
            }
            for w in wires(&op) {
                last_touch.insert(w, idx);
            }
        }
        stats.removed_ops += removed;
        eprintln!("PEEPHOLE_PASS: pass={} removed_ops={} cumulative_removed_ops={} ccx_uncond_pairs={} ccx_cond_pairs={} other_pairs={} seconds={:.6} max_passes={}",
            stats.passes, removed, stats.removed_ops, stats.ccx_uncond_pairs,
            stats.ccx_cond_pairs, stats.other_pairs, pass_started.elapsed().as_secs_f64(), max_passes);
        if removed == 0 {
            stats.passes -= 1; // exclude the final pass that only observes the fixpoint
            break;
        }
        if max_passes != 0 && stats.passes == max_passes {
            break; // include every nonempty pass, including the capped last pass
        }
    }
    let mut at = 0;
    ops.retain(|_| {
        let keep = alive[at];
        at += 1;
        keep
    });
    stats
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;

    fn gate(kind: K, c2: u64, c1: u64, t: u64) -> Op {
        let mut o = Op::empty();
        o.kind = kind;
        match kind {
            K::X | K::Z => o.q_target = QubitId(t),
            K::CX | K::CZ | K::Swap => {
                o.q_control1 = QubitId(c1);
                o.q_target = QubitId(t);
            }
            K::CCX | K::CCZ => {
                o.q_control2 = QubitId(c2);
                o.q_control1 = QubitId(c1);
                o.q_target = QubitId(t);
            }
            _ => {}
        }
        o.validate();
        o
    }

    #[test]
    fn nested_pairs_beyond_32_reach_dense_and_hashed_fixpoint() {
        // All gates touch wire 1: only one nested pair disappears per scan.
        let nested = |offset: u64| {
            let half: Vec<_> = (2..42).map(|q| gate(K::CX, 0, 1 + offset, q + offset)).collect();
            half.iter().chain(half.iter().rev()).copied().collect::<Vec<_>>()
        };
        for offset in [0, 1000] {
            let mut capped = nested(offset);
            let stats = cancel_identical_pairs_with_cap(&mut capped, 32);
            assert_eq!(stats.passes, 32);
            assert_eq!(stats.removed_ops, 64);
            assert_eq!(capped.len(), 16);
            let mut full = nested(offset);
            let stats = cancel_identical_pairs_with_cap(&mut full, 0);
            assert_eq!(stats.passes, 40);
            assert_eq!(stats.removed_ops, 80);
            assert!(full.is_empty());
            assert_eq!(cancel_identical_pairs_with_cap(&mut full, 0).passes, 0);
        }
    }

    #[test]
    fn adjacent_and_gap_pairs_cancel_fixpoint_stops() {
        // X(3) between the two CCX blocks cancellation until the X pair
        // cancels; the fixpoint then removes the CCX pair.
        let mut ops = vec![
            gate(K::CCX, 1, 2, 4),
            gate(K::X, 0, 0, 3),
            gate(K::CX, 0, 5, 6),
            gate(K::X, 0, 0, 3),
            gate(K::CCX, 1, 2, 4),
        ];
        let stats = cancel_identical_pairs(&mut ops);
        assert_eq!(ops.len(), 1);
        assert_eq!(ops[0].kind, K::CX);
        assert_eq!(stats.ccx_uncond_pairs, 1);
        assert_eq!(stats.other_pairs, 1);
        assert_eq!(stats.passes, 1);
    }

    #[test]
    fn wire_touch_pushpop_and_condition_writes_block() {
        // touch of a member wire between the pair blocks cancellation
        let mut a = vec![
            gate(K::CCX, 1, 2, 4),
            gate(K::CX, 0, 7, 4),
            gate(K::CCX, 1, 2, 4),
        ];
        assert_eq!(cancel_identical_pairs(&mut a).removed_ops, 0);
        assert_eq!(a.len(), 3);
        // a balanced PushCondition/PopCondition between the pair blocks it
        let mut push = Op::empty();
        push.kind = K::PushCondition;
        push.c_condition = BitId(0);
        let mut pop = Op::empty();
        pop.kind = K::PopCondition;
        let mut b = vec![
            gate(K::CCX, 1, 2, 4),
            push,
            pop,
            gate(K::CCX, 1, 2, 4),
        ];
        assert_eq!(cancel_identical_pairs(&mut b).removed_ops, 0);
        assert_eq!(b.len(), 4);
        // a write to the condition bit between conditional members blocks
        let mut c1 = gate(K::CCX, 1, 2, 4);
        c1.c_condition = BitId(0);
        let mut inv = Op::empty();
        inv.kind = K::BitInvert;
        inv.c_target = BitId(0);
        let mut c = vec![c1, inv, c1];
        assert_eq!(cancel_identical_pairs(&mut c).removed_ops, 0);
        assert_eq!(c.len(), 3);
        // no write to the condition bit: the conditional pair cancels
        let mut d1 = gate(K::CCX, 1, 2, 4);
        d1.c_condition = BitId(1);
        let mut d = vec![d1, gate(K::X, 0, 0, 9), d1];
        let st = cancel_identical_pairs(&mut d);
        assert_eq!(st.ccx_cond_pairs, 1);
        assert_eq!(d.len(), 1);
    }

    #[test]
    fn outer_control_q0_never_cancels() {
        let mut ops = vec![gate(K::X, 0, 0, 0), gate(K::X, 0, 0, 0)];
        assert_eq!(cancel_identical_pairs(&mut ops).removed_ops, 0);
        assert_eq!(ops.len(), 2);
    }

    struct Xor(u64);
    impl XofReader for Xor {
        fn read(&mut self, b: &mut [u8]) {
            for x in b.iter_mut() {
                self.0 ^= self.0 << 13;
                self.0 ^= self.0 >> 7;
                self.0 ^= self.0 << 17;
                *x = self.0 as u8;
            }
        }
    }

    #[test]
    fn random_soup_filtered_stream_is_exact() {
        let mut seed = 0x243f6a8885a308d3u64;
        let mut rand = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for round in 0..40 {
            let nq = 12;
            let mut ops = Vec::new();
            let mut depth = 0usize;
            for _ in 0..600 {
                let pick = rand() % 100;
                let mut o = Op::empty();
                match pick {
                    0..=49 => {
                        let kinds = [K::X, K::Z, K::CX, K::CZ, K::Swap, K::CCX, K::CCZ];
                        o.kind = kinds[(rand() % 7) as usize];
                        let wires: Vec<u64> = match o.kind {
                            K::X | K::Z => vec![rand() % nq],
                            K::CX | K::CZ | K::Swap => {
                                let a = rand() % nq;
                                let mut b = rand() % nq;
                                while b == a {
                                    b = rand() % nq;
                                }
                                vec![a, b]
                            }
                            _ => {
                                let mut v = vec![rand() % nq, rand() % nq, rand() % nq];
                                while v[1] == v[0] {
                                    v[1] = rand() % nq;
                                }
                                while v[2] == v[0] || v[2] == v[1] {
                                    v[2] = rand() % nq;
                                }
                                v
                            }
                        };
                        match o.kind {
                            K::X | K::Z => o.q_target = QubitId(wires[0]),
                            K::CX | K::CZ | K::Swap => {
                                o.q_control1 = QubitId(wires[0]);
                                o.q_target = QubitId(wires[1]);
                            }
                            _ => {
                                o.q_control2 = QubitId(wires[0]);
                                o.q_control1 = QubitId(wires[1]);
                                o.q_target = QubitId(wires[2]);
                            }
                        }
                        if depth == 0 && rand() % 4 == 0 {
                            o.c_condition = BitId(rand() % 2);
                        }
                    }
                    50..=59 => {
                        if depth < 2 {
                            o.kind = K::PushCondition;
                            o.c_condition = BitId(rand() % 2);
                            depth += 1;
                        } else {
                            continue;
                        }
                    }
                    60..=69 => {
                        if depth > 0 {
                            o.kind = K::PopCondition;
                            depth -= 1;
                        } else {
                            continue;
                        }
                    }
                    70..=79 => {
                        o.kind = K::Hmr;
                        o.q_target = QubitId(rand() % nq);
                        o.c_target = BitId(rand() % 2);
                    }
                    80..=89 => {
                        o.kind = K::BitInvert;
                        o.c_target = BitId(rand() % 2);
                        if depth == 0 && rand() % 2 == 0 {
                            o.c_condition = BitId(rand() % 2);
                        }
                    }
                    _ => {
                        o.kind = K::Neg;
                        if depth == 0 && rand() % 2 == 0 {
                            o.c_condition = BitId(rand() % 2);
                        }
                    }
                }
                o.validate();
                ops.push(o);
            }
            while depth > 0 {
                let mut o = Op::empty();
                o.kind = K::PopCondition;
                ops.push(o);
                depth -= 1;
            }
            let mut filtered = ops.clone();
            cancel_identical_pairs(&mut filtered);
            // debug: test each canceled pair in isolation
            if std::env::var_os("PEEPHOLE_DEBUG").is_some() {
                let mut alive2 = vec![true; ops.len()];
                let mut last_touch2: std::collections::HashMap<u64, i64> = std::collections::HashMap::new();
                let mut last_bitw2: std::collections::HashMap<u64, i64> = std::collections::HashMap::new();
                let mut last_pp2 = -1i64;
                let mut last_op2: std::collections::HashMap<(u8, u64, u64, u64, u64), i64> = std::collections::HashMap::new();
                for i in 0..ops.len() {
                    let op = ops[i];
                    let idx = i as i64;
                    match op.kind {
                        K::PushCondition | K::PopCondition => last_pp2 = idx,
                        K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                            last_bitw2.insert(op.c_target.0, idx);
                        }
                        _ => {}
                    }
                    if super::self_inverse_quantum(op.kind) && !super::wires(&op).any(|q| q == 0) {
                        let k = super::key(&op);
                        if let Some(&p) = last_op2.get(&k) {
                            let ok = last_pp2 < p
                                && (op.c_condition == NO_BIT
                                    || last_bitw2.get(&op.c_condition.0).copied().unwrap_or(-1) < p)
                                && super::wires(&op).all(|w| last_touch2.get(&w).copied().unwrap_or(-1) == p);
                            if ok {
                                let mut solo = ops.clone();
                                solo.remove(i);
                                solo.remove(p as usize);
                                let mut ra = Xor(seed ^ 7);
                                let mut rb = Xor(seed ^ 7);
                                let mut a = Simulator::new(nq as usize, 2, &mut ra);
                                let mut b = Simulator::new(nq as usize, 2, &mut rb);
                                for q in 0..nq as usize {
                                    a.qubits[q] = (7 >> (q % 3)) & 1;
                                }
                                b.qubits = a.qubits.clone();
                                a.apply_iter(ops.iter());
                                b.apply_iter(solo.iter());
                                if a.qubits != b.qubits || a.phase != b.phase || a.bits != b.bits {
                                    eprintln!(
                                        "INEXACT PAIR ({p},{i}) kind={:?} q2={} q1={} qt={} cc={} ops={:?}",
                                        op.kind, op.q_control2.0, op.q_control1.0, op.q_target.0, op.c_condition.0,
                                        &ops[p as usize..=i]
                                    );
                                }
                                alive2[p as usize] = false;
                                alive2[i] = false;
                                last_op2.remove(&k);
                                continue;
                            }
                        }
                        last_op2.insert(k, idx);
                    }
                    for w in super::wires(&op) {
                        last_touch2.insert(w, idx);
                    }
                }
            }
            for basis in 0..8 {
                let mut ra = Xor(seed ^ basis);
                let mut rb = Xor(seed ^ basis);
                let mut a = Simulator::new(nq as usize, 2, &mut ra);
                let mut b = Simulator::new(nq as usize, 2, &mut rb);
                for q in 0..nq as usize {
                    a.qubits[q] = (basis >> (q % 3)) & 1;
                }
                b.qubits = a.qubits.clone();
                a.bits = b.bits.clone();
                a.apply_iter(ops.iter());
                b.apply_iter(filtered.iter());
                assert_eq!(a.qubits, b.qubits, "round {round} basis {basis}");
                assert_eq!(a.phase, b.phase, "round {round} basis {basis}");
                assert_eq!(a.bits, b.bits, "round {round} basis {basis}");
            }
        }
    }
}
