//! Embedded component checks using the real simulator, not the port's stubs.

use super::*;
use alloy_primitives::U256;
use crate::circuit::{analyze_ops, BitId, Op, OperationType, NO_BIT};
use crate::point_add::B;
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

fn random_word(rng: &mut impl XofReader) -> U256 {
    let mut bytes = [0; 32];
    rng.read(&mut bytes);
    U256::from_le_bytes(bytes)
}

struct Measurements<R> {
    mode: u8,
    rng: R,
}

impl<R: XofReader> XofReader for Measurements<R> {
    fn read(&mut self, bytes: &mut [u8]) {
        match self.mode {
            0 => bytes.fill(0),
            1 => bytes.fill(255),
            _ => self.rng.read(bytes),
        }
    }
}

fn evaluate(b: &B, inputs: &[u64], active: u64, mode: u8) -> (Vec<u64>, u64) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"outer-exact-measurements-v1");
    let mut rng = Measurements { mode, rng: seed.finalize_xof() };
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    sim.qubits[..inputs.len()].copy_from_slice(inputs);
    let scratch = BitId(nb);
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = scratch;
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    let mut stack = Vec::new();
    let mut mask = u64::MAX;
    for (index, op) in b.ops.iter().enumerate() {
        if op.kind == OperationType::PushCondition {
            stack.push(mask); mask &= sim.bit(op.c_condition); continue;
        }
        if op.kind == OperationType::PopCondition {
            mask = stack.pop().expect("balanced condition"); continue;
        }
        if op.kind == OperationType::R {
            let cond = mask & if op.c_condition == NO_BIT { active }
                else { active & sim.bit(op.c_condition) };
            assert_eq!(sim.qubit(op.q_target) & cond, 0,
                "nonzero reset at op {index}, q={:?}", op.q_target);
        }
        *sim.bit_mut(scratch) = mask;
        sim.apply_iter([&push, op, &pop].into_iter());
    }
    assert!(stack.is_empty());
    assert!(sim.qubits[inputs.len()..].iter().all(|v| v & active == 0), "live scratch");
    (sim.qubits[..inputs.len()].to_vec(), sim.phase & active)
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

fn exhaustive_constants() -> usize {
    use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_add_const_gidney;
    let mut checked = 0;
    for n in 2..=6 {
        let mask = (1usize << n) - 1;
        for constant in 0..=mask {
            for subtract in [false, true] {
                let mut c = Circuit::new();
                let a = c.alloc_qreg_bits("test.a", n);
                let donor = c.alloc_qreg_bits("test.donor", n - 1);
                let ctrl = c.alloc_qreg("test.ctrl");
                if subtract { for q in &a { c.x(q); } }
                controlled_add_const_gidney(&mut c, &ctrl, &a, &[constant as u8], &donor);
                if subtract { for q in &a { c.x(q); } }
                let b = c.into_builder();
                for first in (0..1usize << (2 * n)).step_by(64) {
                    let valid = 64.min((1usize << (2 * n)) - first);
                    let active = u64::MAX >> (64 - valid);
                    let mut input = vec![0u64; 2 * n];
                    let mut expected = input.clone();
                    for shot in 0..valid {
                        let bits = first + shot;
                        let old = bits & mask;
                        let enabled = bits >> (2 * n - 1) != 0;
                        let new = if !enabled { old } else if subtract {
                            old.wrapping_sub(constant) & mask
                        } else { (old + constant) & mask };
                        let out = (bits & !mask) | new;
                        for j in 0..input.len() {
                            input[j] |= (((bits >> j) & 1) as u64) << shot;
                            expected[j] |= (((out >> j) & 1) as u64) << shot;
                        }
                    }
                    let (out, phase) = evaluate(&b, &input, active, 2);
                    assert_eq!(out, expected, "constant n={n} c={constant} sub={subtract}");
                    assert_eq!(phase, 0, "constant phase");
                    checked += valid;
                }
            }
        }
    }
    checked
}

#[derive(Clone, Copy, Debug)]
enum Kind { Fold(bool), Double, Halve, Add(bool) }

fn compile(kind: Kind, optimized: bool, nb: usize, alias: Option<usize>) -> B {
    std::env::set_var("MIDQ_OUTER_DIRTY_CONST", if optimized { "1" } else { "0" });
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", 257);
    let b = c.alloc_qreg_bits("test.b", nb);
    let ctrl = c.alloc_qreg("test.ctrl");
    match kind {
        Kind::Fold(sub) => {
            if sub { for q in &a[..RFOLD_WINDOW] { c.x(q); } }
            controlled_rfold_window(&mut c, &a[256], &a, &r_bytes());
            if sub { for q in &a[..RFOLD_WINDOW] { c.x(q); } }
        }
        Kind::Double => mod_double_rfold_mbu(&mut c, &a),
        Kind::Halve => mod_halve_rfold_mbu(&mut c, &a),
        Kind::Add(sub) => {
            let control = alias.map_or(&ctrl, |j| &b[j]);
            if sub { controlled_mod_sub_rfold_mbu(&mut c, control, &a, &b); }
            else { controlled_mod_add_rfold_mbu(&mut c, control, &a, &b); }
        }
    }
    c.into_builder()
}

fn fold(a: U256, enabled: bool, sub: bool) -> U256 {
    if !enabled { return a; }
    let mask = (U256::from(1) << RFOLD_WINDOW) - U256::from(1);
    let r = U256::from_le_bytes(r_bytes());
    let low = if sub { a.wrapping_sub(r) } else { a.wrapping_add(r) } & mask;
    (a & !mask) | low
}

fn reference(kind: Kind, a: U256, b: U256, enabled: bool) -> (U256, bool) {
    match kind {
        Kind::Fold(sub) => (fold(a, enabled, sub), false),
        Kind::Double => (fold(a << 1, a.bit(255), false), false),
        Kind::Halve => {
            let mut out: U256 = fold(a, a.bit(0), true) >> 1;
            out.set_bit(255, a.bit(0));
            (out, false)
        }
        Kind::Add(sub) => {
            let a = if sub { !a } else { a };
            let (sum, overflow) = if enabled { a.overflowing_add(b) } else { (a, false) };
            let out = fold(sum, overflow, false);
            // Preserve the inherited truncated-comparator phase syndrome,
            // including inputs outside its approximation support.
            let syndrome = overflow ^ (enabled && (out >> 192) < (b >> 192));
            (if sub { !out } else { out }, syndrome)
        }
    }
}

fn production_components(vent_cap: Option<usize>, phase_change: bool) -> usize {
    let mut seed = Shake256::default();
    seed.update(b"outer-exact-inputs-v1");
    let mut rng = seed.finalize_xof();
    let r = U256::from_le_bytes(r_bytes());
    let p = U256::ZERO.wrapping_sub(r);
    let mut values = vec![U256::ZERO, U256::from(1), U256::MAX, r, r - U256::from(1),
        r + U256::from(1), p, p - U256::from(1), p + U256::from(1)];
    for i in 1..=255 {
        let boundary: U256 = U256::from(1) << i;
        values.extend([boundary - U256::from(1), boundary, boundary + U256::from(1),
            boundary.wrapping_sub(r), boundary.wrapping_sub(r).wrapping_add(U256::from(1))]);
    }
    for _ in 0..2048 { values.push(random_word(&mut rng)); }
    let mut cases = Vec::new();
    for a in values {
        // Both controls; matching high words; zero, maximal, and random sources.
        for (b, enabled) in [(U256::ZERO, false), (U256::MAX, true),
            (a, false), (a, true), (random_word(&mut rng), false), (random_word(&mut rng), true)] {
            cases.push((a, b, enabled));
        }
    }
    let mut variants = vec![(Kind::Fold(false), 257, None), (Kind::Fold(true), 257, None),
        (Kind::Double, 257, None), (Kind::Halve, 257, None)];
    for nb in [256, 257] {
        for alias in [None, Some(0), Some(96), Some(255)] {
            for sub in [false, true] { variants.push((Kind::Add(sub), nb, alias)); }
        }
    }
    let mut checked = 0;
    for (kind, nb, alias) in variants {
        if phase_change && !matches!(kind, Kind::Add(_)) { continue; }
        if phase_change { std::env::set_var("MIDQ_MEASURED_OUTER_PHASE", "0"); }
        std::env::remove_var("MIDQ_OUTER_VENT_QCAP");
        let old = compile(kind, phase_change || vent_cap.is_some(), nb, alias);
        if let Some(cap) = vent_cap {
            std::env::set_var("MIDQ_OUTER_VENT_QCAP", cap.to_string());
        }
        if phase_change { std::env::set_var("MIDQ_MEASURED_OUTER_PHASE", "1"); }
        let new = compile(kind, true, nb, alias);
        if phase_change {
            assert!(toffoli(&new.ops) <= toffoli(&old.ops));
            assert!(new.peak_qubits <= old.peak_qubits);
        } else if let Some(cap) = vent_cap {
            assert!(new.peak_qubits as usize <= cap.max(old.peak_qubits as usize));
            if matches!(kind, Kind::Add(_)) && nb == 257 {
                assert!(toffoli(&new.ops) < toffoli(&old.ops));
            } else {
                assert_eq!(new.ops, old.ops, "unmodified primitive changed");
            }
        } else {
            assert!(toffoli(&new.ops) < toffoli(&old.ops));
            assert!(new.peak_qubits <= old.peak_qubits);
        }
        eprintln!("OUTER_COMPONENT {kind:?} nb={nb} alias={alias:?}: T {} -> {}, Q {} -> {}",
            toffoli(&old.ops), toffoli(&new.ops), old.peak_qubits, new.peak_qubits);
        for batch in cases.chunks(64) {
            let active = u64::MAX >> (64 - batch.len());
            let mut input = vec![0u64; 257 + nb + 1];
            let mut expected = input.clone();
            let mut syndrome_mask = 0;
            for (shot, &(a, b, control)) in batch.iter().enumerate() {
                let enabled = match kind {
                    Kind::Add(_) => alias.map_or(control, |j| b.bit(j)),
                    _ => control,
                };
                let (out, syndrome) = reference(kind, a, b, enabled);
                syndrome_mask |= u64::from(syndrome) << shot;
                for j in 0..256 {
                    input[j] |= u64::from(a.bit(j)) << shot;
                    expected[j] |= u64::from(out.bit(j)) << shot;
                    let bv = u64::from(b.bit(j)) << shot;
                    input[257 + j] |= bv;
                    expected[257 + j] |= bv;
                }
                if matches!(kind, Kind::Fold(_)) {
                    input[256] |= u64::from(control) << shot;
                    expected[256] |= u64::from(control) << shot;
                }
                input[257 + nb] |= u64::from(control) << shot;
                expected[257 + nb] |= u64::from(control) << shot;
            }
            for mode in 0..=2 {
                for builder in [&old, &new] {
                    let (out, phase) = evaluate(builder, &input, active, mode);
                    assert_eq!(out, expected, "{kind:?} nb={nb} alias={alias:?}");
                    if mode < 2 { assert_eq!(phase, if mode == 1 { syndrome_mask } else { 0 }); }
                    else { assert_eq!(phase & !syndrome_mask, 0, "unexpected phase {kind:?}"); }
                }
            }
            checked += batch.len();
        }
    }
    checked
}

pub(crate) fn run() {
    assert_ne!(std::env::var("POINT_ADD_COUNT_ONLY").ok().as_deref(), Some("1"));
    super::super::configure_sub1000_trailmix_route();
    let saved = std::env::var_os("MIDQ_OUTER_DIRTY_CONST");
    let saved_vents = std::env::var_os("MIDQ_OUTER_VENT_QCAP");
    std::env::remove_var("MIDQ_OUTER_VENT_QCAP");
    let small = exhaustive_constants();
    eprintln!("OUTER_EXHAUSTIVE PASS: {small} basis inputs, all constants/directions/dirty donors");
    let full = production_components(None, false);
    match saved {
        Some(value) => std::env::set_var("MIDQ_OUTER_DIRTY_CONST", value),
        None => std::env::remove_var("MIDQ_OUTER_DIRTY_CONST"),
    }
    match saved_vents {
        Some(value) => std::env::set_var("MIDQ_OUTER_VENT_QCAP", value),
        None => std::env::remove_var("MIDQ_OUTER_VENT_QCAP"),
    }
    eprintln!("MIDQ_OUTER_EXACT_SELFTEST PASS: {small} exhaustive + {full} production-width cases; value, phase support, donors, scratch, pre-reset zero, resources; 3 measurement modes for each production backend");
}

fn compile_integer(n: usize, alias: Option<usize>, sub: bool, padding: usize, cap: usize) -> B {
    std::env::set_var("MIDQ_OUTER_VENT_QCAP", cap.to_string());
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let b = c.alloc_qreg_bits("test.b", n);
    let ctrl = c.alloc_qreg("test.ctrl");
    let _spectators = c.alloc_qreg_bits("test.spectators", padding);
    if sub { for q in &a { c.x(q); } }
    // Exercise draining of pending frees before the compile-time budget read.
    if padding != 0 { drop(c.alloc_qreg_bits("test.pending", 3)); }
    controlled_outer_int_add(&mut c, alias.map_or(&ctrl, |j| &b[j]), &a, &b);
    if sub { for q in &a { c.x(q); } }
    let builder = c.into_builder();
    for op in &builder.ops { op.validate(); }
    builder
}

fn dynamic_vent_budgets() -> usize {
    let mut checked = 0;
    for n in 2..=6 {
        let mask = (1usize << n) - 1;
        for alias in std::iter::once(None).chain((0..n).map(Some)) {
            for padding in [0, 3] {
                let live = 2 * n + 1 + padding;
                let reserve = usize::from(alias.is_some());
                let mut caps = vec![0, live - 1, live, live + 1, live + reserve + 1,
                    live + reserve + n / 2, live + reserve + n + 1];
                caps.sort_unstable();
                caps.dedup();
                for sub in [false, true] {
                    let old = compile_integer(n, alias, sub, padding, 0);
                    for &cap in &caps {
                        let new = compile_integer(n, alias, sub, padding, cap);
                        let vents = cap.saturating_sub(live + reserve).min(n - 1);
                        if vents == 0 {
                            assert_eq!(new.ops, old.ops, "fallback must be byte-identical");
                        } else {
                            assert_eq!(toffoli(&new.ops), 3 * n - 2 - vents);
                        }
                        assert!(new.peak_qubits as usize <= cap.max(old.peak_qubits as usize));
                        for first in (0..1usize << (2 * n + 1)).step_by(64) {
                            let valid = 64.min((1usize << (2 * n + 1)) - first);
                            let active = u64::MAX >> (64 - valid);
                            let mut input = vec![0u64; live];
                            for (j, value) in input.iter_mut().enumerate().skip(2 * n + 1) {
                                *value = 0x5a5a_3c3c_0f0f_a5a5u64.rotate_left(j as u32) & active;
                            }
                            let mut expected = input.clone();
                            for shot in 0..valid {
                                let bits = first + shot;
                                let a = bits & mask;
                                let b = (bits >> n) & mask;
                                let enabled = alias.map_or(bits >> (2 * n) != 0,
                                    |j| (b >> j) & 1 != 0);
                                let out = if !enabled { a } else if sub {
                                    a.wrapping_sub(b) & mask
                                } else { (a + b) & mask };
                                let result = (bits & !mask) | out;
                                for j in 0..2 * n + 1 {
                                    input[j] |= (((bits >> j) & 1) as u64) << shot;
                                    expected[j] |= (((result >> j) & 1) as u64) << shot;
                                }
                            }
                            let (out, phase) = evaluate(&new, &input, active, 2);
                            assert_eq!(out, expected, "n={n} alias={alias:?} cap={cap} sub={sub}");
                            assert_eq!(phase, 0, "vent-adder phase");
                            checked += valid;
                        }
                    }
                }
            }
        }
    }
    // Production-width accounting at, below, and above the requested cap.
    for live in [771usize, 772, 1022, 1023, 1024, 1040] {
        for alias in [None, Some(96)] {
            let reserve = usize::from(alias.is_some());
            let vents = 1024usize.saturating_sub(live + reserve).min(256);
            let old = compile_integer(257, alias, false, live - 515, 0);
            let new = compile_integer(257, alias, false, live - 515, 1024);
            if vents == 0 { assert_eq!(new.ops, old.ops); }
            else { assert_eq!(toffoli(&new.ops), 769 - vents); }
            assert!(new.peak_qubits <= old.peak_qubits.max(1024));
            eprintln!("OUTER_VENT_BUDGET live={live} alias={alias:?} vents={vents} T={}->{} Q={}->{}",
                toffoli(&old.ops), toffoli(&new.ops), old.peak_qubits, new.peak_qubits);
        }
    }
    checked
}

pub(crate) fn run_vents() {
    assert_ne!(std::env::var("POINT_ADD_COUNT_ONLY").ok().as_deref(), Some("1"));
    super::super::configure_sub1000_trailmix_route();
    let saved = ["MIDQ_OUTER_DIRTY_CONST", "MIDQ_OUTER_VENT_QCAP"]
        .map(|name| (name, std::env::var_os(name)));
    let dynamic = dynamic_vent_budgets();
    eprintln!("OUTER_VENT_DYNAMIC PASS: {dynamic} exhaustive basis/budget/direction/alias cases");
    let full = production_components(Some(1024), false);
    for (name, value) in saved {
        match value {
            Some(value) => std::env::set_var(name, value),
            None => std::env::remove_var(name),
        }
    }
    eprintln!("MIDQ_OUTER_VENT_SELFTEST PASS: {dynamic} dynamic exhaustive + {full} production-width cases; values, phase support, preserved controls/sources/spectators, pre-reset zero, capped resources, byte-identical fallback");
}

pub(crate) fn run_phase() {
    super::super::configure_sub1000_trailmix_route();
    let count = production_components(None, true);
    eprintln!("MIDQ_OUTER_PHASE_SELFTEST PASS: {count} production-width value and inherited-phase-syndrome cases across aliases and three measurement modes, pre-reset checked");
}
