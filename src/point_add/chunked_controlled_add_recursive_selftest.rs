//! Remote-only component checks, reached through the existing controlled-add
//! selftest entry point. No trusted harness or evaluator changes are needed.
use super::*;
use crate::circuit::{analyze_ops, BitId, OperationType as K, QubitId, NO_BIT};
use crate::point_add::B;
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

fn rng(label: &[u8]) -> sha3::Shake256Reader {
    let mut seed = Shake256::default();
    seed.update(label);
    seed.finalize_xof()
}

struct Words { values: Vec<u64>, i: usize }
impl XofReader for Words {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.values[self.i].to_le_bytes());
        self.i += 1;
    }
}

struct Env(Vec<(&'static str, Option<std::ffi::OsString>)>);
impl Env {
    fn save() -> Self {
        Self(["MIDQ_CHUNKED_CONTROLLED_ADD", "MIDQ_CONTROLLED_ADD_RECURSIVE",
            "MIDQ_CONTROLLED_ADD_QCAP"].into_iter()
            .map(|key| (key, std::env::var_os(key))).collect())
    }
}
impl Drop for Env {
    fn drop(&mut self) {
        for (key, value) in &self.0 {
            if let Some(value) = value { std::env::set_var(key, value); }
            else { std::env::remove_var(key); }
        }
    }
}

// Audit actual emitted operations, not the plan tree. An internal condition
// must be a fresh HMR outcome measured in this exact enclosing scope. Thus
// every additional condition really contributes an independent factor 1/2.
// External input conditions are fixed enabled for this cost comparison.
fn weighted_t(b: &B, external: &[BitId]) -> f64 {
    let mut measured = std::collections::BTreeMap::new();
    let mut stack = Vec::new();
    let mut weight = 1.0;
    let mut weights = Vec::new();
    let mut total = 0.0;
    for op in &b.ops {
        match op.kind {
            K::Hmr => {
                assert!(measured.insert(op.c_target, stack.clone()).is_none());
            }
            K::PushCondition => {
                weights.push(weight);
                if !external.contains(&op.c_condition) {
                    assert_eq!(measured.get(&op.c_condition), Some(&stack));
                    weight *= 0.5;
                }
                assert!(!stack.contains(&op.c_condition));
                stack.push(op.c_condition);
            }
            K::PopCondition => {
                stack.pop().unwrap();
                weight = weights.pop().unwrap();
            }
            K::CCX | K::CCZ => {
                assert_eq!(op.c_condition, NO_BIT);
                total += weight;
            }
            _ => {}
        }
    }
    assert!(stack.is_empty() && weights.is_empty());
    total
}

#[derive(Clone, Copy)]
enum Route { Recursive, Old, Public }

struct Built {
    b: B,
    ids: Vec<QubitId>,
    external: [BitId; 2],
    nested: bool,
    n: usize,
    accepted: bool,
}

fn build(n: usize, available: usize, budget: usize, nested: bool, route: Route) -> Built {
    let mut c = Circuit::new();
    // Scattered refs: interleaved storage and reversed source ordering.
    let storage = c.alloc_qreg_bits("recursive.test.words", 2 * n);
    let a: Vec<_> = storage.iter().step_by(2).collect();
    let b: Vec<_> = storage.iter().skip(1).step_by(2).rev().collect();
    let g = c.alloc_qreg("recursive.test.control");
    let sign = c.alloc_qreg("recursive.test.sign");
    let live = 1009 - available;
    let spectators = c.alloc_qreg_bits("recursive.test.spectator", live - 2 * n - 2);
    let outer = c.alloc_input_bit();
    let inner = c.alloc_input_bit();
    let ids = a.iter().chain(&b).copied().chain([&g, &sign]).chain(&spectators)
        .map(|q| QubitId(q.id().into())).collect();
    let mut accepted = true;
    let mut emit_body = |c: &mut Circuit| {
        // Quantum sign: ~(~a+b) = a-b modulo 2^n, also when g=0.
        for q in &a { c.cx(&sign, q); }
        match route {
            Route::Recursive => recursive_emit(c, &g, &a, &b, None,
                RecursiveAction::Add(None), available),
            Route::Old => {
                std::env::set_var("MIDQ_CHUNKED_CONTROLLED_ADD", "0");
                crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_hybrid_add_refs(
                    c, &g, &a, &b, budget);
                std::env::set_var("MIDQ_CHUNKED_CONTROLLED_ADD", "1");
            }
            Route::Public => accepted = try_apply(c, &g, &a, &b, budget),
        }
        for q in &a { c.cx(&sign, q); }
    };
    if nested { c.with_conditions(&[outer, inner], &mut emit_body); }
    else { emit_body(&mut c); }
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits as usize, live, "scratch leak");
    assert!(c.b.peak_qubits <= 1009, "cap exceeded n={n} A={available}");
    Built { b: c.into_builder(), ids, external: [BitId(outer.raw().into()), BitId(inner.raw().into())],
        nested, n, accepted }
}

fn input(n: usize, live: usize, first: usize) -> Vec<u64> {
    let mut random = rng(b"recursive-controlled-inputs-v1");
    let mut words = Vec::new();
    for bit in 0..live {
        let mut bytes = [0; 8]; random.read(&mut bytes);
        let mut word = u64::from_le_bytes(bytes).rotate_left((first % 64) as u32);
        if n <= 6 && bit < 2 * n + 2 {
            word = (0..64).fold(0, |v, shot| v | ((((first + shot) >> bit) & 1) as u64) << shot);
        } else if n > 6 && bit < 2 * n + 2 {
            // Explicit 0, all-ones, cross-limb carry/borrow, p and p+1
            // at 256/257 bits. These are raw words, never field-reduced.
            word &= !0xffffffff;
            for shot in 0..32 {
                let pair = shot / 4;
                let value = if bit == 2 * n { shot & 1 != 0 }
                else if bit == 2 * n + 1 { shot & 2 != 0 }
                else if bit >= n {
                    match pair {
                        4 => false,
                        5 => true,
                        6 => (bit - n) % 2 == 0,
                        7 => bit - n == n - 1,
                        _ => bit == n,
                    }
                }
                else {
                    match pair {
                        0 => false,
                        1 => true,
                        2 => bit < [1, 64, 128, 192][first % 4],
                        4 => false,
                        5 => true,
                        6 => bit % 2 != 0,
                        7 => bit == n - 1,
                        _ if n >= 256 => {
                            let low = if first & 1 == 0 { 0xfffffffefffffc2fu64 }
                                else { 0xfffffffefffffc30u64 };
                            if bit < 64 { low >> bit & 1 != 0 } else { bit < 256 }
                        }
                        _ => bit % 2 == 0,
                    }
                };
                word |= u64::from(value) << shot;
            }
        }
        words.push(word);
    }
    words
}

fn expected(built: &Built, input: &[u64]) -> Vec<u64> {
    let n = built.n;
    let mut want = input.to_vec();
    if !built.accepted { return want; }
    let enabled = input[2 * n] & if built.nested { 0x8888888888888888 } else { !0 };
    let sign = input[2 * n + 1];
    let mut carry = 0;
    let mut borrow = 0;
    for i in 0..n {
        let (a, b) = (input[i], input[n + i]);
        want[i] = a ^ (enabled & (b ^ ((carry & !sign) | (borrow & sign))));
        carry = (a & b) | ((a ^ b) & carry);
        borrow = (!a & b) | (!(a ^ b) & borrow);
    }
    want
}

fn check(built: &Built, input: &[u64], mode: usize, transcript: Option<usize>) -> u64 {
    let mut random = rng(b"recursive-controlled-measurements-v1");
    let mut h = 0;
    let values: Vec<_> = built.b.ops.iter().filter_map(|op| {
        if !matches!(op.kind, K::Hmr | K::R) { return None; }
        let mut bytes = [0; 8]; random.read(&mut bytes);
        let mut value = match mode { 0 => 0, 1 => !0, 2 => 0x5555555555555555,
            3 => if h % 2 == 0 { !0 } else { 0 }, _ => u64::from_le_bytes(bytes) };
        if op.kind == K::Hmr {
            if let Some(t) = transcript { value = if t >> h & 1 == 0 { 0 } else { !0 }; }
            h += 1;
        }
        Some(value)
    }).collect();
    let (nq, nb, _, _) = analyze_ops(built.b.ops.iter());
    let nq = nq.max(u64::from(built.b.next_qubit)) as usize;
    let nb = nb.max(built.external[1].0 + 1) as usize;
    let mut r1 = Words { values: values.clone(), i: 0 };
    let mut r2 = Words { values, i: 0 };
    let mut native = Simulator::new(nq, nb, &mut r1);
    let mut audit = Simulator::new(nq, nb + 1, &mut r2);
    for sim in [&mut native, &mut audit] {
        sim.bits.fill(!0); // Stale measurement bits on inactive branches.
        *sim.bit_mut(built.external[0]) = 0xaaaaaaaaaaaaaaaa;
        *sim.bit_mut(built.external[1]) = 0xcccccccccccccccc;
        for (&id, &value) in built.ids.iter().zip(input) { *sim.qubit_mut(id) = value; }
    }
    native.apply_iter(built.b.ops.iter());
    let mut active = !0;
    let mut stack = Vec::new();
    for (i, op) in built.b.ops.iter().enumerate() {
        op.validate();
        match op.kind {
            K::PushCondition => { stack.push(active); active &= audit.bit(op.c_condition); }
            K::PopCondition => active = stack.pop().unwrap(),
            _ => {
                // Check ALL lanes, before reset can conceal a dirty ancilla.
                if op.kind == K::R { assert_eq!(audit.qubit(op.q_target), 0, "dirty pre-reset {i}"); }
                audit.bits[nb] = active & if op.c_condition == NO_BIT { !0 } else { audit.bit(op.c_condition) };
                let mut flat = *op;
                flat.c_condition = BitId(nb as u64);
                audit.apply_iter(std::iter::once(&flat));
            }
        }
    }
    assert!(stack.is_empty());
    assert_eq!(native.qubits, audit.qubits);
    assert_eq!(native.phase, audit.phase);
    assert_eq!(native.stats, audit.stats);
    assert_eq!(native.phase, 0, "n={} mode={mode} transcript={transcript:?}", built.n);
    for (&id, value) in built.ids.iter().zip(expected(built, input)) {
        assert_eq!(native.qubit(id), value, "n={} id={id:?} mode={mode}", built.n);
        *native.qubit_mut(id) = 0;
    }
    assert!(native.qubits.iter().all(|&q| q == 0));
    native.stats.toffoli_gates
}

fn plan_audit() {
    let table = recursive_plans();
    for available in 0..RECURSIVE_MAX_WIDTH {
        for n in 1..=RECURSIVE_MAX_WIDTH {
            let p = table[available][n];
            if available > 0 { assert!(p.phase_cost <= table[available - 1][n].phase_cost); }
            if !p.phase_cost.is_finite() { continue; }
            if p.split == 0 {
                assert!(n - 1 <= available);
                assert_eq!(p.phase_cost, (n - 1) as f64);
            } else {
                let k = p.split;
                assert!(available > 0 && k > 0 && k < n);
                assert_eq!(p.phase_cost, table[available - 1][k].phase_cost + 1.0
                    + table[available - 1][n - k].phase_cost + 0.5 * table[available][k].phase_cost);
            }
        }
    }
    assert!(!prefer_recursive(0, 0, 0));
    assert!(!prefer_recursive(258, 22, 22));
    assert!(!prefer_recursive(256, 0, 0));
    // Proven eight-block construction from the inversion scheduler: adding
    // 256 controlled sum CCX still beats the 14-vent fallback of 752.
    assert!(recursive_cost(256, 14) <= 743.0);
    assert!(prefer_recursive(256, 14, 14));
    assert!(!prefer_recursive(256, 14, 255));
}

fn admission_audit() {
    std::env::remove_var("MIDQ_CONTROLLED_ADD_RECURSIVE");
    let off = build(256, 14, 14, false, Route::Public);
    assert!(!off.accepted);
    assert_eq!(weighted_t(&off.b, &off.external), 0.0);
    let two_level_off = build(256, 32, 32, false, Route::Public);
    std::env::set_var("MIDQ_CONTROLLED_ADD_RECURSIVE", "1");
    let two_level_on = build(256, 32, 32, false, Route::Public);
    assert!(two_level_off.accepted && two_level_on.accepted);
    assert_eq!(two_level_off.b.ops, two_level_on.b.ops, "two-level route changed");
    for n in [0, 1] {
        let tiny = build(n, 0, 0, false, Route::Public);
        assert!(!tiny.accepted);
        assert_eq!(weighted_t(&tiny.b, &tiny.external), 0.0);
    }
    for (n, available, budget) in [(256, 14, 14), (256, 14, 255), (256, 0, 0),
        (256, 14, 0), (256, 32, 32), (16, 15, 15), (258, 14, 14)] {
        let candidate = build(n, available, budget, false, Route::Public);
        let room = available.min(budget);
        let chunks = crate::point_add::clean_chunk_plan::plan(n - 1, room);
        let accepted = room < n - 1 && (chunks.is_some() || prefer_recursive(n, room, budget));
        assert_eq!(candidate.accepted, accepted);
        let cost = if !accepted { 0.0 } else if let Some(chunks) = chunks {
            let replay: usize = chunks.iter().take(chunks.len() - 1).map(|k| k - 1).sum();
            (2 * n - 1) as f64 + 0.5 * replay as f64
        } else { recursive_cost(n, room) };
        assert_eq!(weighted_t(&candidate.b, &candidate.external), cost);
        for mode in 0..5 { check(&candidate, &input(n, candidate.ids.len(), 0), mode, None); }
    }
    // No arithmetic emitted on an alias, including the control itself.
    let mut c = Circuit::new();
    let storage = c.alloc_qreg_bits("alias", 33);
    let a: Vec<_> = storage[..16].iter().collect();
    let mut b: Vec<_> = storage[16..32].iter().collect();
    let before = c.b.ops.len();
    b[0] = a[0];
    assert!(!try_apply(&mut c, &storage[32], &a, &b, 2));
    b[0] = &storage[32];
    assert!(!try_apply(&mut c, &storage[32], &a, &b, 2));
    assert_eq!(c.b.ops.len(), before);
}

pub(super) fn run() {
    let _restore = Env::save();
    std::env::set_var("MIDQ_CHUNKED_CONTROLLED_ADD", "1");
    std::env::set_var("MIDQ_CONTROLLED_ADD_QCAP", "1009");
    plan_audit();
    admission_audit();
    let mut checked = 0;
    for n in 2..=6 {
        for available in 0..n {
            if !recursive_cost(n, available).is_finite() { continue; }
            for nested in [false, true] {
                let built = build(n, available, available, nested, Route::Recursive);
                assert_eq!(weighted_t(&built.b, &built.external), recursive_cost(n, available));
                let hmr = built.b.ops.iter().filter(|op| op.kind == K::Hmr).count();
                for first in (0..1usize << (2 * n + 2)).step_by(64) {
                    let words = input(n, built.ids.len(), first);
                    for mode in 0..5 { check(&built, &words, mode, None); checked += 64; }
                    if n <= 4 {
                        assert!(hmr < 12);
                        let mut total_t = 0u64;
                        for transcript in 0..1usize << hmr {
                            total_t += check(&built, &words, 0, Some(transcript)); checked += 64;
                        }
                        assert_eq!(total_t as f64 / (1usize << hmr) as f64,
                            recursive_cost(n, available) * if nested { 16.0 } else { 64.0 });
                    }
                }
            }
        }
    }
    for n in [16, 73, 85, 128, 255, 256, 257] {
        for available in [4, 8, 10, 14, 18, 22] {
            if !prefer_recursive(n, available, available)
                || crate::point_add::clean_chunk_plan::plan(n - 1, available).is_some() { continue; }
            for nested in [false, true] {
                let new = build(n, available, available, nested, Route::Public);
                let old = build(n, available, available, nested, Route::Old);
                assert!(new.accepted);
                let cost = weighted_t(&new.b, &new.external);
                assert_eq!(cost, recursive_cost(n, available));
                assert_eq!(weighted_t(&old.b, &old.external), fallback_cost(n, available));
                assert!(cost < fallback_cost(n, available));
                for first in 0..4 {
                    let words = input(n, new.ids.len(), first);
                    for mode in 0..5 {
                        check(&new, &words, mode, None);
                        let old_t = check(&old, &words, mode, None);
                        assert_eq!(old_t as f64, fallback_cost(n, available)
                            * if nested { 16.0 } else { 64.0 });
                        checked += 128;
                    }
                }
                eprintln!("CONTROLLED_RECURSIVE_COST n={n} A={available} nested={nested} oldQ={} newQ={} oldT={} weightedT={cost} saving={} emitted={}",
                    old.b.peak_qubits, new.b.peak_qubits, fallback_cost(n, available),
                    fallback_cost(n, available) - cost,
                    new.b.ops.iter().filter(|op| matches!(op.kind, K::CCX | K::CCZ)).count());
            }
        }
    }
    eprintln!("CONTROLLED_RECURSIVE PASS: {checked} cases; exhaustive small words/sign/control and measurement transcripts, forced streams, nested conditions, noncanonical words, source/spectators, phase, dirty pre-reset, Q<=1009 and exact weighted cost");
}
