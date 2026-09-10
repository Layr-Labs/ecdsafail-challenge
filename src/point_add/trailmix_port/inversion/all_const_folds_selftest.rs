//! Full-word oracle and actual caller checks for the optional broad dispatch.
use super::*;
use crate::circuit::OperationType as K;
use crate::point_add::B;
use alloy_primitives::U256;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

struct Case { name: &'static str, width: usize, constant: Vec<u8>, outer: bool }

fn build(case: &Case, live: usize, subtract: bool, optimized: bool) -> B {
    std::env::set_var("MIDQ_ALL_CONST_FOLDS", if optimized { "1" } else { "0" });
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("test.target", if case.outer { 257 } else { case.width });
    let control = c.alloc_qreg("test.control");
    let dirty = c.alloc_qreg_bits("test.dirty", if case.outer { 0 } else { case.width - 1 });
    let base = target.len() + 1 + dirty.len();
    let _pad = c.alloc_qreg_bits("test.pad", live - base);
    if case.outer {
        if subtract { for q in &target[..73] { c.x(q); } }
        crate::point_add::trailmix_port::rfold_mbu::controlled_rfold_window(
            &mut c, &control, &target, &case.constant,
        );
        if subtract { for q in &target[..73] { c.x(q); } }
    } else {
        super::super::midq_constant_update(&mut c, &control, &target, &case.constant, &dirty, subtract);
    }
    c.flush_pending_frees(); c.into_builder()
}

fn expected(input: &[u64], case: &Case, subtract: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    let ctrl = input[if case.outer { 257 } else { case.width }];
    let mut carry = 0;
    for i in 0..case.width {
        let a = input[i] ^ if subtract { !0 } else { 0 };
        let b = if cbit(&case.constant, i) { ctrl } else { 0 };
        out[i] = a ^ b ^ carry ^ if subtract { !0 } else { 0 };
        carry = (a & b) | (a & carry) | (b & carry);
    }
    out
}

pub(crate) fn run() {
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_COMPACT_CONST_CARRY", "1");
    std::env::set_var("MIDQ_OUTER_DIRTY_CONST", "1");
    std::env::set_var("MIDQ_CELL_QCAP", "1009");
    let f = U256::from((1u64 << 32) + 977);
    let p = U256::MAX - f + U256::from(1);
    let mut full257 = vec![0xa5; 33]; full257[32] = 1;
    let cases = [
        Case { name: "normalize_p", width: 257, constant: p.to_le_bytes::<32>().to_vec(), outer: false },
        Case { name: "field_neg_p1", width: 257, constant: (p+U256::from(1)).to_le_bytes::<32>().to_vec(), outer: false },
        Case { name: "F256", width: 256, constant: f.to_le_bytes::<32>().to_vec(), outer: false },
        Case { name: "outer_F73", width: 73, constant: f.to_le_bytes::<32>().to_vec(), outer: true },
        Case { name: "arbitrary257", width: 257, constant: full257, outer: false },
    ];
    let mut hash = Shake256::default(); hash.update(b"all-constant-word-oracle-v1");
    let mut random = hash.finalize_xof();
    let mut checked = 0;
    for case in &cases {
        for live in [560, 900, 960, 975, 980, 985, 986, 987, 995, 1005] {
            for subtract in [false, true] {
                let old = build(case, live, subtract, false);
                let new = build(case, live, subtract, true);
                assert!(new.peak_qubits <= 1009.max(old.peak_qubits));
                let fits = clean_chunk_plan::plan(case.width - 1, 1009 - live).is_some();
                if !fits { assert_eq!(old.ops, new.ops, "fallback changed {}", case.name); }
                let mut total = [0u64; 2];
                for batch in 0..16 {
                    let mut input = vec![0u64; live];
                    for word in &mut input {
                        let mut bytes = [0; 8]; random.read(&mut bytes); *word = u64::from_le_bytes(bytes);
                    }
                    // Unrestricted words, plus zero/ones and carry boundaries.
                    // In particular bit 256 is not assumed zero.
                    for i in 0..case.width {
                        input[i] = (input[i] & !15) | 2 |
                            (if i < batch * case.width / 16 { 4 } else { 8 });
                    }
                    let ctrl = if case.outer { 257 } else { case.width };
                    input[ctrl] = (input[ctrl] & !15) | 15;
                    let want = expected(&input, case, subtract);
                    for mode in 0..3 {
                        let (a0, p0, t0) = selftest::run_ops(&old, &input, mode, None, None);
                        let (a1, p1, t1) = selftest::run_ops(&new, &input, mode, None, None);
                        assert_eq!((a0, p0), (want.clone(), 0), "old {} live={live} sub={subtract}", case.name);
                        assert_eq!((a1, p1), (want.clone(), 0), "new {} live={live} sub={subtract}", case.name);
                        if mode == 2 { total[0] += t0; total[1] += t1; }
                        checked += 64;
                    }
                }
                if !subtract {
                    let count = |b: &B| b.ops.iter().filter(|op| matches!(op.kind, K::CCX | K::CCZ)).count();
                    eprintln!("ALL_CONST_RESOURCE name={} live={live} fits={fits} oldQ={} newQ={} old_emitted={} new_emitted={} old_avgT={:.3} new_avgT={:.3}",
                        case.name, old.peak_qubits, new.peak_qubits, count(&old), count(&new), total[0] as f64 / 1024.0, total[1] as f64 / 1024.0);
                }
            }
        }
    }
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("test.alias", 8);
    let before = c.b.ops.len();
    assert!(!try_constant_update(&mut c, &a[0], &a, &[1], false));
    assert_eq!(c.b.ops.len(), before);
    assert!(try_constant_update(&mut c, &a[0], &[], &[255], true));
    assert_eq!(c.b.ops.len(), before);
    std::env::remove_var("MIDQ_ALL_CONST_FOLDS");
    eprintln!("MIDQ_ALL_CONST_FOLDS_SELFTEST PASS: {checked} full-width cases, independent bit-plane oracle, add/sub, real callers, arbitrary bit256, preserved donors, phase/reset audit, exact fallback and cap");
}
