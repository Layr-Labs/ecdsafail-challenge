//! Exact fixed-point cancellation of identical self-inverse quantum operations.
//!
//! Two identical ops A ... A cancel exactly when every op between them acts on
//! qubits disjoint from A's wires (such ops commute with A, regardless of their
//! own classical conditions), no PushCondition/PopCondition lies between them
//! (both then execute under the identical condition stack), and, when A carries
//! a direct classical condition, that bit is not rewritten between them (both
//! then execute or both skip). Only deletions are performed; surviving ops keep
//! their order. Per-qubit survivor stacks restore the previous live touches
//! when a pair dies, so cancellations exposed by deletions happen during the
//! same linear scan. Qubit 0 (the constant outer control eliminated later) is
//! never a pair member, preserving that pass's exactly-two-toggles invariant.
use crate::circuit::{Op, OperationType as K, NO_BIT};
use std::time::Instant;

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

pub(super) fn cancel_identical_pairs(ops: &mut Vec<Op>) -> PeepholeStats {
    let started = Instant::now();
    let mut stats = PeepholeStats::default();
    let mut nq = 0usize;
    let mut nb = 0usize;
    for op in ops.iter() {
        for q in wires(op) {
            let q = usize::try_from(q).expect("qubit index fits usize");
            assert!(q <= 834, "Q833 peephole qubit index exceeds 834: {q}");
            nq = nq.max(q.checked_add(1).expect("qubit extent overflow"));
        }
        if op.c_condition != NO_BIT {
            let bit = usize::try_from(op.c_condition.0).expect("bit index fits usize");
            assert!(
                bit <= 1281,
                "Q833 peephole condition bit index exceeds 1281: {bit}"
            );
            nb = nb.max(bit.checked_add(1).expect("bit extent overflow"));
        }
        if matches!(op.kind, K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr) {
            assert_ne!(op.c_target, NO_BIT, "classical write has no target");
            let bit = usize::try_from(op.c_target.0).expect("bit index fits usize");
            assert!(
                bit <= 1281,
                "Q833 peephole target bit index exceeds 1281: {bit}"
            );
            nb = nb.max(bit.checked_add(1).expect("bit extent overflow"));
        }
    }

    assert!(
        ops.len() <= u32::MAX as usize,
        "peephole survivor indices require at most u32::MAX operations"
    );

    // Each wire stack is the trace-monoid heap for that wire: its top is the
    // last live, pairable operation since the most recent permanent touch.
    // A global Push/Pop barrier advances `epoch`; stacks are cleared lazily on
    // their next access, avoiding O(number_of_qubits) work at every barrier.
    let mut wire_stacks: Vec<Vec<u32>> = (0..nq).map(|_| Vec::new()).collect();
    let mut wire_epochs = vec![0usize; nq];
    let mut epoch = 0usize;
    let mut last_bit_write = vec![usize::MAX; nb];
    let mut alive = vec![true; ops.len()];
    let mut depth = 0usize;
    let mut live_stack_entries = 0usize;
    let mut peak_live_stack_entries = 0usize;
    let mut allocated_stack_entries = 0usize;

    for i in 0..ops.len() {
        let op = ops[i];
        match op.kind {
            K::PushCondition => {
                depth = depth.checked_add(1).expect("condition depth overflow");
                epoch = epoch.checked_add(1).expect("condition epoch overflow");
            }
            K::PopCondition => {
                depth = depth.checked_sub(1).expect("unbalanced condition pop");
                epoch = epoch.checked_add(1).expect("condition epoch overflow");
            }
            K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                last_bit_write[op.c_target.0 as usize] = i;
            }
            _ => {}
        }

        // Make the lazy condition-barrier reset visible on every member wire
        // before reading or changing its survivor stack.
        for wire in wires(&op) {
            let wire = wire as usize;
            if wire_epochs[wire] != epoch {
                live_stack_entries -= wire_stacks[wire].len();
                wire_stacks[wire].clear();
                wire_epochs[wire] = epoch;
            }
        }

        let pairable = self_inverse_quantum(op.kind) && !wires(&op).any(|q| q == 0);
        if pairable {
            let first_wire = wires(&op)
                .next()
                .expect("self-inverse quantum operation has a member wire")
                as usize;
            let previous = wire_stacks[first_wire].last().copied();
            let gap_has_condition_write = previous.is_some_and(|p| {
                op.c_condition != NO_BIT
                    && last_bit_write[op.c_condition.0 as usize] != usize::MAX
                    && last_bit_write[op.c_condition.0 as usize] > p as usize
            });
            let cancel = previous.is_some_and(|p| {
                !gap_has_condition_write
                    && key(&ops[p as usize]) == key(&op)
                    && wires(&op).all(|wire| {
                        wire_stacks[wire as usize].last().copied() == Some(p)
                    })
            });

            if cancel {
                let previous = previous.expect("checked cancellation candidate");
                alive[previous as usize] = false;
                alive[i] = false;
                stats.removed_ops += 2;
                if matches!(op.kind, K::CCX | K::CCZ) {
                    if depth > 0 || op.c_condition != NO_BIT {
                        stats.ccx_cond_pairs += 1;
                    } else {
                        stats.ccx_uncond_pairs += 1;
                    }
                } else {
                    stats.other_pairs += 1;
                }
                for wire in wires(&op) {
                    assert_eq!(wire_stacks[wire as usize].pop(), Some(previous));
                    live_stack_entries -= 1;
                }
                continue;
            }

            let index = u32::try_from(i).expect("operation index fits u32");
            for wire in wires(&op) {
                let stack = &mut wire_stacks[wire as usize];
                let old_capacity = stack.capacity();
                stack.push(index);
                allocated_stack_entries += stack.capacity() - old_capacity;
                live_stack_entries += 1;
            }
            peak_live_stack_entries = peak_live_stack_entries.max(live_stack_entries);
        } else {
            // This live operation can never disappear in this pass, so it is
            // a permanent floor for every member wire. Earlier candidates on
            // those wires can no longer participate in a legal pair.
            for wire in wires(&op) {
                let stack = &mut wire_stacks[wire as usize];
                live_stack_entries -= stack.len();
                stack.clear();
            }
        }
    }

    assert_eq!(depth, 0, "unbalanced condition stack at end");
    stats.passes = usize::from(stats.removed_ops != 0);
    eprintln!(
        "PEEPHOLE_PASS pass={} removed={}",
        stats.passes, stats.removed_ops
    );
    let mut read = 0usize;
    ops.retain(|_| {
        let keep = alive[read];
        read += 1;
        keep
    });
    debug_assert_eq!(
        live_stack_entries,
        wire_stacks.iter().map(Vec::len).sum::<usize>()
    );
    debug_assert_eq!(
        allocated_stack_entries,
        wire_stacks.iter().map(Vec::capacity).sum::<usize>()
    );
    eprintln!(
        "PEEPHOLE_LINEAR: peak_live_entries={} allocated_entries={} allocated_bytes={} elapsed_s={:.3}",
        peak_live_stack_entries,
        allocated_stack_entries,
        allocated_stack_entries * std::mem::size_of::<u32>(),
        started.elapsed().as_secs_f64(),
    );
    stats
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId, QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    use std::collections::HashMap;

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
    fn rollback_exposes_shared_wire_pairs_in_one_scan() {
        let outer = gate(K::CCX, 1, 2, 4);
        let inner = gate(K::CX, 0, 4, 5);
        let mut ops = vec![outer, inner, inner, outer];
        let stats = cancel_identical_pairs(&mut ops);
        assert!(ops.is_empty());
        assert_eq!(stats.removed_ops, 4);
        assert_eq!(stats.ccx_uncond_pairs, 1);
        assert_eq!(stats.other_pairs, 1);
        assert_eq!(stats.passes, 1);
    }

    #[test]
    fn deep_shared_wire_nesting_has_no_pass_cap() {
        let mut ops = Vec::new();
        for control in 1..=300 {
            ops.push(gate(K::CX, 0, control, 400));
        }
        for control in (1..=300).rev() {
            ops.push(gate(K::CX, 0, control, 400));
        }
        let stats = cancel_identical_pairs(&mut ops);
        assert!(ops.is_empty());
        assert_eq!(stats.removed_ops, 600);
        assert_eq!(stats.other_pairs, 300);
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

        // A q0-touching operation is also a permanent touch on its other
        // wires, so it blocks an otherwise identical pair there.
        let x = gate(K::X, 0, 0, 1);
        let mut blocked = vec![x, gate(K::CX, 0, 0, 1), x];
        assert_eq!(cancel_identical_pairs(&mut blocked).removed_ops, 0);
        assert_eq!(blocked.len(), 3);
    }

    #[test]
    fn different_direct_conditions_shadow_instead_of_pairing_through() {
        let mut c0 = gate(K::CCX, 1, 2, 4);
        c0.c_condition = BitId(0);
        let mut c1 = c0;
        c1.c_condition = BitId(1);
        let mut ops = vec![c0, c1, c0, c1];
        assert_eq!(cancel_identical_pairs(&mut ops).removed_ops, 0);
        assert_eq!(ops, [c0, c1, c0, c1]);

        let mut nested = vec![c0, c1, c1, c0];
        let stats = cancel_identical_pairs(&mut nested);
        assert!(nested.is_empty());
        assert_eq!(stats.ccx_cond_pairs, 2);

        let mut write = Op::empty();
        write.kind = K::BitInvert;
        write.c_target = BitId(0);
        let inner = gate(K::CX, 0, 4, 5);
        let mut write_blocked = vec![c0, inner, inner, write, c0];
        let stats = cancel_identical_pairs(&mut write_blocked);
        assert_eq!(stats.removed_ops, 2);
        assert_eq!(write_blocked, [c0, write, c0]);
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

    fn reference_fixpoint(ops: &mut Vec<Op>) -> PeepholeStats {
        let mut stats = PeepholeStats::default();
        loop {
            let mut alive = vec![true; ops.len()];
            let mut last_touch = HashMap::<u64, usize>::new();
            let mut last_bit_write = HashMap::<u64, usize>::new();
            let mut last_pushpop = None::<usize>;
            let mut last_op = HashMap::<(u8, u64, u64, u64, u64), usize>::new();
            let mut depth = 0usize;
            let mut removed = 0u64;
            for i in 0..ops.len() {
                let op = ops[i];
                match op.kind {
                    K::PushCondition => {
                        last_pushpop = Some(i);
                        depth += 1;
                    }
                    K::PopCondition => {
                        last_pushpop = Some(i);
                        depth -= 1;
                    }
                    K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                        last_bit_write.insert(op.c_target.0, i);
                    }
                    _ => {}
                }
                let touches_outer = wires(&op).any(|q| q == 0);
                if self_inverse_quantum(op.kind) && !touches_outer {
                    let gate_key = key(&op);
                    let previous = last_op.get(&gate_key).copied();
                    let cancel = previous.is_some_and(|p| {
                        last_pushpop.is_none_or(|barrier| barrier < p)
                            && (op.c_condition == NO_BIT
                                || last_bit_write
                                    .get(&op.c_condition.0)
                                    .is_none_or(|&write| write < p))
                            && wires(&op)
                                .all(|wire| last_touch.get(&wire).copied() == Some(p))
                    });
                    if cancel {
                        let previous = previous.expect("checked reference candidate");
                        alive[previous] = false;
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
                        last_op.remove(&gate_key);
                        continue;
                    }
                    last_op.insert(gate_key, i);
                }
                for wire in wires(&op) {
                    last_touch.insert(wire, i);
                }
            }
            if removed == 0 {
                break;
            }
            stats.passes += 1;
            stats.removed_ops += removed;
            let mut read = 0usize;
            ops.retain(|_| {
                let keep = alive[read];
                read += 1;
                keep
            });
        }
        stats
    }

    #[test]
    fn eager_survivor_choice_can_drift_only_across_commuting_ops() {
        let x1 = gate(K::X, 0, 0, 1);
        let cx12 = gate(K::CX, 0, 1, 2);
        let cx23 = gate(K::CX, 0, 2, 3);
        let before = vec![x1, cx12, cx12, x1, cx23, x1];

        let mut reference = before.clone();
        let reference_stats = reference_fixpoint(&mut reference);
        let mut eager = before;
        let eager_stats = cancel_identical_pairs(&mut eager);

        assert_eq!(reference, [x1, cx23]);
        assert_eq!(eager, [cx23, x1]);
        assert_eq!(eager_stats.removed_ops, reference_stats.removed_ops);
        assert_eq!(eager_stats.other_pairs, reference_stats.other_pairs);

        let mut ra = Xor(0x41c6_4e6d_5a82_f317);
        let mut rb = Xor(0x41c6_4e6d_5a82_f317);
        let mut a = Simulator::new(4, 0, &mut ra);
        let mut b = Simulator::new(4, 0, &mut rb);
        for q in 0..4 {
            let all_basis = (0..16).fold(0u64, |mask, lane| {
                mask | ((((lane >> q) & 1) as u64) << lane)
            });
            a.qubits[q] = all_basis;
        }
        b.qubits = a.qubits.clone();
        a.apply_iter(reference.iter());
        b.apply_iter(eager.iter());
        assert_eq!(a.qubits, b.qubits);
        assert_eq!(a.phase, b.phase);
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
            let mut expected = ops.clone();
            let expected_stats = reference_fixpoint(&mut expected);
            let mut filtered = ops.clone();
            let stats = cancel_identical_pairs(&mut filtered);
            let mut expected_keys: Vec<_> = expected
                .iter()
                .filter(|op| self_inverse_quantum(op.kind))
                .map(key)
                .collect();
            let mut filtered_keys: Vec<_> = filtered
                .iter()
                .filter(|op| self_inverse_quantum(op.kind))
                .map(key)
                .collect();
            expected_keys.sort_unstable();
            filtered_keys.sort_unstable();
            assert_eq!(
                filtered_keys, expected_keys,
                "fixed-point survivor multiset mismatch in round {round}"
            );
            assert_eq!(stats.removed_ops, expected_stats.removed_ops);
            assert_eq!(stats.ccx_uncond_pairs, expected_stats.ccx_uncond_pairs);
            assert_eq!(stats.ccx_cond_pairs, expected_stats.ccx_cond_pairs);
            assert_eq!(stats.other_pairs, expected_stats.other_pairs);
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
