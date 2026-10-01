//! Real-Simulator checks, including dirty-reset auditing and coupled error phases.
use super::*;
use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, NO_BIT};
use crate::point_add::B;
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

fn rng(label: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default(); h.update(label); h.finalize_xof()
}

struct Words { values: Vec<u64>, i: usize }
impl XofReader for Words {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.values[self.i].to_le_bytes()); self.i += 1;
    }
}

pub(super) fn run_ops(b: &B, inputs: &[u64], mode: u8, transcript: Option<usize>,
    coupled: Option<(usize, u64)>) -> (Vec<u64>, u64, u64) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let nq = (nq as usize).max(inputs.len()).max(b.next_qubit as usize);
    let nb = nb as usize;
    let mut random = rng(b"cell-folds-measurements-v1");
    let mut h = 0;
    let values: Vec<u64> = b.ops.iter().filter_map(|op| {
        if !matches!(op.kind, K::R | K::Hmr) { return None; }
        let mut bytes = [0; 8]; random.read(&mut bytes);
        let mut value = match mode { 0 => 0, 1 => !0, _ => u64::from_le_bytes(bytes) };
        if op.kind == K::Hmr {
            if let Some(t) = transcript { value = if t >> h & 1 != 0 { !0 } else { 0 }; }
            h += 1;
            if let Some((id, word)) = coupled { if op.q_target.0 as usize == id { value = word; } }
        }
        Some(value)
    }).collect();
    let mut r1 = Words { values: values.clone(), i: 0 };
    let mut r2 = Words { values, i: 0 };
    let mut native = Simulator::new(nq, nb, &mut r1);
    let mut audit = Simulator::new(nq, nb + 1, &mut r2);
    for s in [&mut native, &mut audit] {
        s.qubits[..inputs.len()].copy_from_slice(inputs);
        s.bits.fill(!0);
    }
    native.apply_iter(b.ops.iter());
    let mut active = !0;
    let mut stack = Vec::new();
    for (i, op) in b.ops.iter().enumerate() {
        op.validate();
        match op.kind {
            K::PushCondition => { stack.push(active); active &= audit.bit(op.c_condition); }
            K::PopCondition => { active = stack.pop().unwrap(); }
            _ => {
                if op.kind == K::R { assert_eq!(audit.qubit(op.q_target), 0, "dirty reset {i}: {op:?}"); }
                let mut flat: Op = *op;
                audit.bits[nb] = active & if op.c_condition == NO_BIT { !0 } else { audit.bit(op.c_condition) };
                flat.c_condition = BitId(nb as u64);
                audit.apply_iter(std::iter::once(&flat));
            }
        }
    }
    assert!(stack.is_empty());
    assert_eq!(native.qubits, audit.qubits);
    assert_eq!(native.phase, audit.phase);
    assert_eq!(native.stats, audit.stats);
    assert!(native.qubits[inputs.len()..].iter().all(|&q| q == 0), "scratch");
    (native.qubits[..inputs.len()].to_vec(), native.phase, native.stats.toffoli_gates)
}

fn build_const(n: usize, k: usize, value: &[u8], subtract: bool, old: bool, pad: usize) -> B {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let ctrl = c.alloc_qreg("test.ctrl");
    let dirty = c.alloc_qreg_bits("test.dirty", n.saturating_sub(1));
    let _pad = c.alloc_qreg_bits("test.pad", pad);
    if subtract { for q in &a { c.x(q); } }
    if old {
        crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_add_const_gidney(&mut c, &ctrl, &a, value, &dirty);
    } else { add(&mut c, &a, &ctrl, value, k); }
    if subtract { for q in &a { c.x(q); } }
    c.flush_pending_frees(); c.into_builder()
}

fn exhaustive() -> usize {
    let mut checked = 0;
    for n in 1usize..=7 {
        let mask = (1usize << n) - 1;
        for k in 1..=n {
            for constant in 0..=mask {
                for subtract in [false, true] {
                    let b = build_const(n, k, &[constant as u8], subtract, false, 0);
                    assert_eq!(b.peak_qubits as usize, 2*n + scratch(n, k));
                    for first in (0..1usize << (n+1)).step_by(64) {
                        let input: Vec<u64> = (0..2*n).map(|i| (0..64).fold(0, |word, s|
                            word | ((((first+s).rotate_left(3) ^ (first+s)) >> (i % (n+1)) & 1) as u64) << s)).collect();
                        // Enumerate target/control exactly; dirty donors vary independently.
                        let mut input = input;
                        for i in 0..=n { input[i] = (0..64).fold(0, |word, s| word | ((((first+s) >> i)&1) as u64) << s); }
                        let mut want = input.clone();
                        for i in 0..n { want[i] = 0; }
                        for shot in 0..64 {
                            let old = (first+shot) & mask;
                            let delta = if (first+shot) >> n & 1 != 0 { constant } else { 0 };
                            let value = if subtract { old.wrapping_sub(delta) & mask } else { (old+delta)&mask };
                            for i in 0..n { want[i] |= (((value>>i)&1) as u64) << shot; }
                        }
                        for mode in 0..3 {
                            let (actual, phase, _) = run_ops(&b, &input, mode, None, None);
                            assert_eq!((actual, phase), (want.clone(), 0), "n={n} k={k} const={constant} sub={subtract} mode={mode}");
                            checked += 64;
                        }
                        if n <= 3 {
                            let hmr = b.ops.iter().filter(|op| op.kind == K::Hmr).count();
                            for t in 0..1usize << hmr {
                                let (actual, phase, _) = run_ops(&b, &input, 0, Some(t), None);
                                assert_eq!((actual, phase), (want.clone(), 0)); checked += 64;
                            }
                        }
                    }
                }
            }
        }
    }
    checked
}

fn build_cell(old: bool, inverse: bool, pad: usize) -> B {
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("test.target", 257);
    let source = c.alloc_qreg_bits("test.source", 257);
    let sign = c.alloc_qreg("test.sign");
    let _pad = c.alloc_qreg_bits("test.pad", pad);
    if old {
        std::env::set_var("MIDQ_CELL_FOLDS", "0");
        super::super::midq_mod_signed_add_halve(&mut c, &target, &source, &sign, inverse);
    } else { apply(&mut c, &target, &source, &sign, inverse); }
    c.flush_pending_frees(); c.into_builder()
}

fn exhaustive_sum() -> usize {
    let mut checked = 0;
    for n in 1usize..=7 {
        let mask = (1usize << n) - 1;
        for k in 1..=n {
            let mut c = Circuit::new();
            let a = c.alloc_qreg_bits("test.a", n);
            let b = c.alloc_qreg_bits("test.b", n);
            let out = c.alloc_qreg("test.overflow");
            emit(&mut c, &a, Addend::Word(&b), Some(&out), k);
            c.flush_pending_frees();
            let built = c.into_builder();
            assert_eq!(built.peak_qubits as usize, 2*n+1+scratch(n+1, k));
            for first in (0..1usize << (2*n+1)).step_by(64) {
                let input: Vec<u64> = (0..2*n+1).map(|i| (0..64).fold(0, |v, s| v | ((((first+s)>>i)&1) as u64)<<s)).collect();
                let mut want = input.clone();
                want[..n].fill(0); want[2*n] = 0;
                for shot in 0..64 {
                    let x = first+shot;
                    let sum = (x & mask) + ((x >> n)&mask);
                    for i in 0..n { want[i] |= (((sum>>i)&1) as u64)<<shot; }
                    want[2*n] |= ((((sum>>n)^(x>>(2*n)))&1) as u64)<<shot;
                }
                for mode in 0..3 {
                    let (actual, phase, _) = run_ops(&built, &input, mode, None, None);
                    assert_eq!((actual, phase), (want.clone(), 0), "sum n={n} k={k}");
                    checked += 64;
                }
                if n <= 3 {
                    let hmr = built.ops.iter().filter(|op| op.kind == K::Hmr).count();
                    for t in 0..1usize << hmr {
                        let (actual, phase, _) = run_ops(&built, &input, 0, Some(t), None);
                        assert_eq!((actual, phase), (want.clone(), 0)); checked += 64;
                    }
                }
            }
        }
    }
    checked
}

fn full_width() -> usize {
    use alloy_primitives::U256;
    let mut checked = 0;
    let mut random = rng(b"cell-folds-inputs-v1");
    for pad in [0, 445, 465, 470, 485] {
        for inverse in [false, true] {
            let old = build_cell(true, inverse, pad);
            let new = build_cell(false, inverse, pad);
            assert!(new.peak_qubits <= 1009.max(old.peak_qubits));
            let emitted = |b: &B| b.ops.iter().filter(|op| matches!(op.kind, K::CCX | K::CCZ)).count();
            let mut totals = [0, 0];
            for batch in 0..32 {
                let mut input = vec![0; 515+pad];
                for word in &mut input {
                    let mut bytes = [0; 8]; random.read(&mut bytes); *word = u64::from_le_bytes(bytes);
                }
                // Include 0, all ones, powers of two, and long carries in both
                // registers. The overflow wires are deliberately unrestricted.
                for i in 0..256 {
                    input[i] = (input[i] & !15) | 2 | (if i == batch*8 { 4 } else { 0 });
                    input[257+i] = (input[257+i] & !15) | 8 | (if i < batch*8 { 4 } else { 0 });
                }
                if batch >= 16 {
                    let f = U256::from((1u64 << 32) + 977);
                    let p = U256::MAX - f + U256::from(1);
                    let edge = [U256::ZERO, U256::from(1), f-U256::from(1), f, f+U256::from(1), p-U256::from(1), p, U256::MAX];
                    for i in 0..256 {
                        input[i] = (0..64).fold(0, |v,s| v | (u64::from(edge[s%8].bit(i))<<s));
                        input[257+i] = (0..64).fold(0, |v,s| v | (u64::from(edge[s/8].bit(i))<<s));
                    }
                    input[514] = if batch % 2 == 0 { 0 } else { !0 };
                }
                for mode in 0..3 {
                    let coupled = Some((256, if mode == 0 { 0 } else if mode == 1 { !0 } else { 0xa5a5a5a5a5a5a5a5 }));
                    let (v0, p0, t0) = run_ops(&old, &input, mode, None, coupled);
                    let (v1, p1, t1) = run_ops(&new, &input, mode, None, coupled);
                    assert_eq!((v0,p0), (v1,p1), "full-width cell inverse={inverse} pad={pad} batch={batch} mode={mode}");
                    if mode == 2 { totals[0] += t0; totals[1] += t1; }
                    checked += 64;
                }
            }
            eprintln!("CELL_FOLDS_RESOURCE inverse={inverse} pad={pad} oldQ={} newQ={} old_emitted={} new_emitted={} old_avgT={:.3} new_avgT={:.3}", old.peak_qubits, new.peak_qubits, emitted(&old), emitted(&new), totals[0] as f64 / 2048.0, totals[1] as f64 / 2048.0);
        }
    }
    checked
}

fn recursive_weighted_t(b: &B) -> f64 {
    let mut depth = 0;
    let mut total = 0.0;
    for op in &b.ops {
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => { assert!(depth > 0); depth -= 1; }
            K::CCX | K::CCZ => total += 2.0f64.powi(-depth),
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    total
}

fn recursive_small() -> usize {
    let mut checked = 0;
    for n in 1usize..=7 {
        let mask = (1usize << n) - 1;
        for available in 0..n {
            if !recursive::cost(n, available, false).is_finite() { continue; }
            // Every constant, both arithmetic directions, arbitrary control
            // and spectators. The budget sweep includes multi-level trees.
            for constant in 0..=mask {
                for subtract in [false, true] {
                    let mut c = Circuit::new();
                    let a = c.alloc_qreg_bits("test.a", n);
                    let ctrl = c.alloc_qreg("test.ctrl");
                    let _spectator = c.alloc_qreg("test.spectator");
                    if subtract { for q in &a { c.x(q); } }
                    recursive::add(&mut c, &a, Addend::Constant(&ctrl, &[constant as u8]), None, available);
                    if subtract { for q in &a { c.x(q); } }
                    c.flush_pending_frees();
                    let b = c.into_builder();
                    assert!(b.peak_qubits as usize <= n + 2 + available);
                    assert_eq!(recursive_weighted_t(&b), recursive::exact_cost(n, available, false, constant & 1 != 0));
                    for first in (0..1usize << (n + 2)).step_by(64) {
                        let input: Vec<u64> = (0..n+2).map(|i| (0..64).fold(0, |v,s|
                            v | ((((first+s)>>i)&1) as u64)<<s)).collect();
                        let mut want = input.clone();
                        want[..n].fill(0);
                        for shot in 0..64 {
                            let x = first + shot;
                            let delta = if x >> n & 1 == 0 { 0 } else { constant };
                            let y = if subtract { x.wrapping_sub(delta) } else { x+delta } & mask;
                            for i in 0..n { want[i] |= (((y>>i)&1) as u64)<<shot; }
                        }
                        checked += recursive_check(&b, &input, &want, n <= 4);
                    }
                }
            }
            // XOR, rather than overwrite, the carry into an arbitrary output.
            for with_overflow in [false, true] {
                let mut c = Circuit::new();
                let a = c.alloc_qreg_bits("test.a", n);
                let source = c.alloc_qreg_bits("test.b", n);
                let out = c.alloc_qreg("test.out");
                recursive::add(&mut c, &a, Addend::Word(&source), with_overflow.then_some(&out), available);
                c.flush_pending_frees();
                let b = c.into_builder();
                assert!(b.peak_qubits as usize <= 2*n+1+available);
                assert_eq!(recursive_weighted_t(&b), recursive::cost(n, available, with_overflow));
                for first in (0..1usize << (2*n+1)).step_by(64) {
                    let input: Vec<u64> = (0..2*n+1).map(|i| (0..64).fold(0, |v,s|
                        v | ((((first+s)>>i)&1) as u64)<<s)).collect();
                    let mut want = input.clone();
                    want[..n].fill(0);
                    for shot in 0..64 {
                        let x = first + shot;
                        let y = (x & mask) + ((x >> n) & mask);
                        for i in 0..n { want[i] |= (((y>>i)&1) as u64)<<shot; }
                        if with_overflow { want[2*n] ^= (((y>>n)&1) as u64)<<shot; }
                    }
                    checked += recursive_check(&b, &input, &want, n <= 4);
                }
            }
        }
    }
    checked
}

fn recursive_check(b: &B, input: &[u64], want: &[u64], transcripts: bool) -> usize {
    let mut checked = 0;
    for mode in 0..3 {
        let (actual, phase, _) = run_ops(b, input, mode, None, None);
        assert_eq!((actual.as_slice(), phase), (want, 0));
        checked += 64;
    }
    if transcripts {
        let hmr = b.ops.iter().filter(|op| op.kind == K::Hmr).count();
        assert!(hmr < usize::BITS as usize);
        for transcript in 0..1usize << hmr {
            let (actual, phase, _) = run_ops(b, input, 0, Some(transcript), None);
            assert_eq!((actual.as_slice(), phase), (want, 0));
            checked += 64;
        }
    }
    checked
}

fn recursive_wide() -> usize {
    let mut checked = 0;
    let mut random = rng(b"cell-recursive-inputs-v1");
    let mut p = vec![255u8; 33];
    p[..5].copy_from_slice(&[0x2f, 0xfc, 0xff, 0xff, 0xfe]);
    p[32] = 0;
    let mut p1 = p.clone(); p1[0] += 1;
    let constants = [vec![0xd1, 3, 0, 0, 1], vec![0xe8, 1, 0, 0x80], p, p1,
        vec![0xa5; 33], vec![0; 33]];
    for n in [73, 255, 256, 257] {
        for available in [8, 10, 14, 18, 22] {
            if !recursive::cost(n, available, false).is_finite() { continue; }
            for constant in &constants {
                for subtract in [false, true] {
                    let live = 1009 - available;
                    let mut c = Circuit::new();
                    let a = c.alloc_qreg_bits("test.a", n);
                    let ctrl = c.alloc_qreg("test.ctrl");
                    let _spectators = c.alloc_qreg_bits("test.spectator", live - n - 1);
                    if subtract { for q in &a { c.x(q); } }
                    recursive::add(&mut c, &a, Addend::Constant(&ctrl, constant), None, available);
                    if subtract { for q in &a { c.x(q); } }
                    c.flush_pending_frees();
                    let b = c.into_builder();
                    assert!(b.peak_qubits <= 1009);
                    assert_eq!(recursive_weighted_t(&b), recursive::exact_cost(n, available, false, cbit(constant, 0)));
                    for batch in 0..4 {
                        let mut input = vec![0; live];
                        for word in &mut input {
                            let mut bytes = [0; 8]; random.read(&mut bytes);
                            *word = u64::from_le_bytes(bytes);
                        }
                        // Include all-zero/all-one targets for each control,
                        // plus carries across each of the four 64-bit limbs.
                        for i in 0..n {
                            input[i] = (input[i] & !63) | 10
                                | if i < 64*batch { 48 } else { 0 };
                        }
                        input[n] = (input[n] & !63) | 44;
                        let mut want = input.clone();
                        let mut carry = 0u64;
                        for i in 0..n {
                            let x = if subtract { !input[i] } else { input[i] };
                            let y = if cbit(constant, i) { input[n] } else { 0 };
                            let sum = x ^ y ^ carry;
                            carry = (x & y) | (x & carry) | (y & carry);
                            want[i] = if subtract { !sum } else { sum };
                        }
                        checked += recursive_check(&b, &input, &want, false);
                    }
                }
            }
            eprintln!("CELL_RECURSIVE_PREDICT n={n} available={available} Q<=1009 sum_bound={:.6} const_bound={:.6}",
                recursive::cost(n, available, true), recursive::cost(n, available, false));
        }
    }
    checked
}

fn recursive_dispatch() {
    // Failure/disabled paths must leave arithmetic untouched, including X
    // brackets. Flush before taking the snapshot so allocator housekeeping
    // is not confused with emitted arithmetic.
    for (enabled, live) in [(false, 995), (true, 1009), (true, 995)] {
        std::env::set_var("MIDQ_CELL_RECURSIVE_CARRY", if enabled { "1" } else { "0" });
        let mut c = Circuit::new();
        let a = c.alloc_qreg_bits("test.a", 256);
        let ctrl = c.alloc_qreg("test.ctrl");
        let _pad = c.alloc_qreg_bits("test.pad", live-257);
        c.flush_pending_frees();
        let before = c.b.ops.clone();
        let used = try_constant_update(&mut c, &ctrl, &a, &[0xd1, 3, 0, 0, 1], true);
        assert_eq!(used, enabled && live == 995);
        if !used { assert_eq!(format!("{:?}", c.b.ops), format!("{before:?}")); }
        assert!(c.b.peak_qubits <= 1009);
    }
}

fn recursive_cells(cost_select: bool) -> usize {
    let mut checked = 0;
    let mut random = rng(b"cell-recursive-cells-v1");
    for rotated in [false, true] {
        std::env::set_var("MIDQ_ROTATED_HALVES", if rotated { "1" } else { "0" });
        for inverse in [false, true] {
            for pad in [470, 480, 485] {
                std::env::set_var("MIDQ_CELL_RECURSIVE_CARRY", if cost_select { "1" } else { "0" });
                std::env::set_var("MIDQ_CELL_COST_SELECT", "0");
                let old = build_cell(false, inverse, pad);
                std::env::set_var("MIDQ_CELL_RECURSIVE_CARRY", "1");
                std::env::set_var("MIDQ_CELL_COST_SELECT", if cost_select { "1" } else { "0" });
                let new = build_cell(false, inverse, pad);
                assert!(new.peak_qubits <= old.peak_qubits.max(1009));
                let mut totals = [0u64; 2];
                for batch in 0..8 {
                    let mut input = vec![0; 515+pad];
                    for word in &mut input {
                        let mut bytes = [0; 8]; random.read(&mut bytes);
                        *word = u64::from_le_bytes(bytes);
                    }
                    // Noncanonical all-ones words and all overflow/sign states.
                    for i in 0..256 {
                        input[i] = (input[i] & !255) | 0xaa;
                        input[257+i] = (input[257+i] & !255) | 0xcc;
                    }
                    input[514] = (input[514] & !255) | 0xf0;
                    input[256] = if batch % 2 == 0 { 0 } else { !0 };
                    for mode in 0..3 {
                        let coupled = Some((256, match mode { 0 => 0, 1 => !0, _ => 0xa5a5a5a5a5a5a5a5 }));
                        let (v0, p0, t0) = run_ops(&old, &input, mode, None, coupled);
                        let (v1, p1, t1) = run_ops(&new, &input, mode, None, coupled);
                        assert_eq!((v0, p0), (v1, p1), "recursive cell rotated={rotated} inverse={inverse} pad={pad} batch={batch} mode={mode}");
                        if mode == 2 { totals[0] += t0; totals[1] += t1; }
                        checked += 64;
                    }
                }
                eprintln!("CELL_RECURSIVE_RESOURCE cost_select={cost_select} rotated={rotated} inverse={inverse} live={} oldQ={} newQ={} old_avgT={:.6} new_avgT={:.6}",
                    515+pad, old.peak_qubits, new.peak_qubits, totals[0] as f64/512.0, totals[1] as f64/512.0);
            }
        }
    }
    checked
}

fn recursive_run() {
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "1");
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    std::env::set_var("MIDQ_CHUNK_COMPARE", "1");
    std::env::set_var("MIDQ_VARIABLE_CHUNKS", "1");
    std::env::set_var("MIDQ_CHUNK_COMPARE_QCAP", "1009");
    std::env::set_var("MIDQ_CELL_QCAP", "1009");
    std::env::set_var("MIDQ_CELL_SUM", "1");
    recursive::selftest_plan();
    recursive_dispatch();
    let small = recursive_small();
    eprintln!("CELL_RECURSIVE_SMALL PASS {small} cases, every small measurement transcript");
    let wide = recursive_wide();
    let cells = recursive_cells(false);
    eprintln!("MIDQ_CELL_RECURSIVE_SELFTEST PASS: {} cases, values/phases/pre-reset ancilla audit; resource figures above are component-only", small + wide + cells);
}

// Modes: the validated dispatcher, new cost selector, or a directly emitted
// dirty suffix. The latter independently checks the conservative 3m-4 price.
fn build_cost_selected(n: usize, available: usize, constant: &[u8], subtract: bool, mode: u8) -> (B, bool) {
    std::env::set_var("MIDQ_CELL_COST_SELECT", if mode == 1 { "1" } else { "0" });
    std::env::set_var("MIDQ_CELL_QCAP", (2*n+available).to_string());
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", n);
    let ctrl = c.alloc_qreg("test.ctrl");
    let dirty = c.alloc_qreg_bits("test.dirty", n-1);
    let used = mode != 2 && try_constant_update(&mut c, &ctrl, &a, constant, subtract);
    if !used {
        let skip = if mode == 2 { recursive::trailing_zeros(n, constant) } else { 0 };
        let shifted = recursive::shifted_constant(n, constant, skip);
        let suffix = &a[skip..];
        if subtract { for q in suffix { c.x(q); } }
        crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_add_const_gidney(
            &mut c, &ctrl, suffix, &shifted, &dirty);
        if subtract { for q in suffix { c.x(q); } }
    }
    c.flush_pending_frees();
    (c.into_builder(), used)
}

fn cost_selected_case(n: usize, available: usize, constant: &[u8], subtract: bool, small: bool) -> usize {
    let (old, _) = build_cost_selected(n, available, constant, subtract, 0);
    let (new, used) = build_cost_selected(n, available, constant, subtract, 1);
    let (trimmed, _) = build_cost_selected(n, available, constant, subtract, 2);
    let m = n - recursive::trailing_zeros(n, constant);
    assert_eq!(recursive_weighted_t(&trimmed), recursive::dirty_cost(m));
    assert!(recursive_weighted_t(&new) <= recursive_weighted_t(&old),
        "selector regressed n={n} available={available} c={constant:?}");
    if used { assert!(new.peak_qubits as usize <= (2*n+available).min(1019)); }
    else { assert_eq!(old.ops, new.ops, "declined route must stay byte-identical"); }
    if small && n > 1 {
        if let Some(chunks) = clean_chunk_plan::plan(n-1, available) {
            assert_eq!(recursive_weighted_t(&old), recursive::chunk_cost(&chunks, cbit(constant, 0)));
        }
    }
    let mut random = rng(b"cell-cost-selection-inputs-v1");
    let batches = if small { (1usize << (n+1)).div_ceil(64) } else { 4 };
    let mut checked = 0;
    for batch in 0..batches {
        let mut input = vec![0; 2*n];
        for word in &mut input {
            let mut bytes = [0; 8]; random.read(&mut bytes); *word = u64::from_le_bytes(bytes);
        }
        if small {
            for i in 0..=n {
                input[i] = (0..64).fold(0, |v,s| v | ((((batch*64+s)>>i)&1) as u64)<<s);
            }
        } else {
            for i in 0..n {
                input[i] = (input[i] & !63) | 10 | if i < batch*64 { 48 } else { 0 };
            }
            input[n] = (input[n] & !63) | 44;
        }
        let mut want = input.clone();
        let mut carry = 0;
        for i in 0..n {
            let a = input[i] ^ if subtract { !0 } else { 0 };
            let b = if cbit(constant, i) { input[n] } else { 0 };
            want[i] = a ^ b ^ carry ^ if subtract { !0 } else { 0 };
            carry = (a & b) | (a & carry) | (b & carry);
        }
        checked += recursive_check(&new, &input, &want, small && n <= 4);
        checked += recursive_check(&old, &input, &want, false);
        checked += recursive_check(&trimmed, &input, &want, false);
    }
    if !small && !subtract {
        eprintln!("CELL_COST_SELECT_RESOURCE n={n} available={available} suffix={m} used={used} oldQ={} newQ={} old_expectedT={:.6} new_expectedT={:.6} trimmed_dirtyT={:.6} c={constant:02x?}",
            old.peak_qubits, new.peak_qubits, recursive_weighted_t(&old), recursive_weighted_t(&new), recursive_weighted_t(&trimmed));
    }
    checked
}

fn cost_selection_dispatch() {
    std::env::set_var("MIDQ_CELL_QCAP", "1009");
    std::env::set_var("MIDQ_CELL_COST_SELECT", "1");
    let mut admitted = 0;
    // Scan a bounded set of budgets for cases newly admitted over 7a1784b.
    for available in 1..23 {
        if recursive::cost(256, available, false) < 510.0 { continue; }
        let (old, old_used) = build_cost_selected(256, available, &[0xd1, 3, 0, 0, 1], false, 0);
        let (new, used) = build_cost_selected(256, available, &[0xd1, 3, 0, 0, 1], false, 1);
        assert!(!old_used);
        if used {
            admitted += 1;
            assert!(recursive_weighted_t(&new) < 764.0);
            assert!(recursive_weighted_t(&new) < recursive_weighted_t(&old));
            // If either caller's fallback is unknown, this wider admission
            // must be declined without emitting even subtraction X brackets.
            for flag in ["MIDQ_DIRTY_CONST", "MIDQ_OUTER_DIRTY_CONST"] {
                std::env::set_var(flag, "0");
                let (declined, was_used) = build_cost_selected(256, available, &[0xd1, 3, 0, 0, 1], false, 1);
                assert!(!was_used);
                assert_eq!(declined.ops, old.ops);
                std::env::set_var(flag, "1");
            }
        }
    }
    assert!(admitted > 0, "expanded constant gate must admit a new workspace budget");
    // A full two-level sum plan fits at A=23; the recursive endpoint does
    // not allocate a separate outgoing carry, permitting a cheaper plan.
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.a", 256);
    let b = c.alloc_qreg_bits("test.b", 256);
    let out = c.alloc_qreg("test.out");
    std::env::set_var("MIDQ_CELL_QCAP", "536");
    let chunks = choose(&mut c, 257).unwrap();
    assert!(recursive::try_prefer(&mut c, &a, Addend::Word(&b), Some(&out), false, Some(&chunks)));
    c.flush_pending_frees();
    let built = c.into_builder();
    assert!(built.peak_qubits <= 536);
    assert!(recursive_weighted_t(&built) < recursive::chunk_cost(&chunks, true));
    eprintln!("CELL_COST_SELECT_DISPATCH PASS newly_admitted_budgets={admitted}");
}

fn cost_selection_run() {
    for flag in ["MIDQ_CELL_RECURSIVE_CARRY", "MIDQ_DIRTY_CONST", "MIDQ_OUTER_DIRTY_CONST",
        "MIDQ_COMPACT_CONST_CARRY", "MIDQ_MEASURE_COMPARE", "MIDQ_CHUNK_COMPARE", "MIDQ_VARIABLE_CHUNKS", "MIDQ_CELL_SUM"] {
        std::env::set_var(flag, "1");
    }
    recursive::selftest_plan();
    cost_selection_dispatch();
    // Re-audit the exact first-column discount against emitted recursive
    // networks, including all small measurement transcripts.
    let mut checked = recursive_small();
    for n in 1usize..=7 {
        for available in 0..=n {
            for constant in 0..1usize << n {
                for subtract in [false, true] {
                    checked += cost_selected_case(n, available, &[constant as u8], subtract, true);
                }
            }
        }
    }
    // Widths include the inherited outer window and both coefficient layouts.
    for n in [73usize, 255, 256, 257] {
        let mut top = vec![0; n.div_ceil(8)]; top[(n-1)/8] = 1 << ((n-1)%8);
        let mut outside = vec![0; (n+1).div_ceil(8)]; outside[n/8] = 1 << (n%8);
        let mut p1 = vec![255; 33]; p1[..5].copy_from_slice(&[0x30, 0xfc, 0xff, 0xff, 0xfe]); p1[32] = 0;
        for constant in [vec![0xd1, 3, 0, 0, 1], vec![0xe8, 1, 0, 0x80], p1, vec![0, 0, 0x81], top, outside, vec![]] {
            for available in [7, 8, 9, 10, 14, 22, 23, 32] {
                for subtract in [false, true] {
                    checked += cost_selected_case(n, available, &constant, subtract, false);
                }
            }
        }
    }
    std::env::set_var("MIDQ_CELL_QCAP", "1009");
    std::env::set_var("MIDQ_CHUNK_COMPARE_QCAP", "1009");
    checked += recursive_cells(true);
    eprintln!("MIDQ_CELL_COST_SELECT_SELFTEST PASS: {checked} cases; exact suffix/fallback costs, non-increasing weighted Toffoli, value/phase/ancilla and cap checks");
}

pub(crate) fn run() {
    if std::env::var_os("MIDQ_TAIL_INVERSE_TOP_COMPARE_SELFTEST").is_some() {
        super::inverse_top_checks::run();
        return;
    }
    if std::env::var_os("MIDQ_TAIL_TOP_COMPARE_SELFTEST").is_some() {
        super::fused_rotation::top_compare_selftest();
        return;
    }
    if std::env::var_os("MIDQ_FUSED_ROTATION_CELL_SELFTEST").is_some() {
        super::fused_rotation::selftest();
        return;
    }
    if std::env::var_os("MIDQ_CELL_COST_SELECT_SELFTEST").is_some() {
        cost_selection_run();
        return;
    }
    if std::env::var_os("MIDQ_CELL_RECURSIVE_SELFTEST").is_some() {
        recursive_run();
        return;
    }
    clean_chunk_plan::selftest();
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "1");
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_MEASURE_COMPARE", "1");
    std::env::set_var("MIDQ_CHUNK_COMPARE", "1");
    std::env::set_var("MIDQ_CELL_QCAP", "1009");
    let small = exhaustive();
    eprintln!("CELL_FOLDS_EXHAUSTIVE PASS {small} cases, all small measurement transcripts");
    let sum = exhaustive_sum();
    eprintln!("CELL_FOLDS_SUM PASS {sum} cases, arbitrary overflow bit, all small measurement transcripts");
    let full = full_width();
    eprintln!("MIDQ_CELL_FOLDS_SELFTEST PASS: {} cases, exact finite-width values, coupled noncanonical error phases, donor restoration and pre-reset audit", small + sum + full);
}
