//! Native-Simulator tests, with the existing pre-reset garbage auditor.
use super::*;
use crate::circuit::{BitId, Op, OperationType as OpKind};
use crate::point_add::B;
use alloy_primitives::U256;

#[path="hybrid_margin_near_selftest.rs"]
mod near_checks;

struct Guard(Vec<(&'static str, Option<String>)>);
impl Guard {
    fn new() -> Self {
        Self(
            [
                "MIDQ_FUSED_ROTATION_CELL",
                "MIDQ_TAIL_TOP_COMPARE",
                "MIDQ_PZ_PINGPONG_TAIL",
                "TRAILMIX_SROT_W",
                "MIDQ_CELL_SUM",
                "MIDQ_CELL_RECURSIVE_CARRY",
                "MIDQ_CELL_COST_SELECT",
                "MIDQ_ALL_CONST_FOLDS",
                "MIDQ_DIRTY_CONST",
                "MIDQ_OUTER_DIRTY_CONST",
                "MIDQ_COMPACT_CONST_CARRY",
                "MIDQ_VARIABLE_CHUNKS",
                "MIDQ_MEASURE_COMPARE",
                "MIDQ_CHUNK_COMPARE",
                "MIDQ_ROTATED_HALVES",
                "MIDQ_CELL_QCAP",
                "MIDQ_CHUNK_COMPARE_QCAP",
                "MIDQ_CELL_FOLDS",
            ]
            .into_iter()
            .map(|name| (name, std::env::var(name).ok()))
            .collect(),
        )
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        for (name, old) in &self.0 {
            if let Some(old) = old {
                std::env::set_var(name, old);
            } else {
                std::env::remove_var(name);
            }
        }
    }
}

pub(super) fn run_parametric_margin() {
    let _guard=Guard::new();
    let inverse_old=std::env::var("MIDQ_TAIL_INVERSE_TOP_COMPARE").ok();
    let support_old=std::env::var("HYBRID_MARGIN_SUPPORT").ok();
    assert!(super::super::super::hybrid_margin::named_support_enabled());
    let expected=super::super::super::hybrid_margin::admitted_bounds().expect("admitted source support");
    assert!(expected.full_fused);
    near_checks::run_oracles();
    let mut cases=fixtures();cases.extend(near_checks::selected_cells());
    let cap=super::super::super::hybrid_profile::hard_ceiling().min(1080);
    let mut checked=0;
    for width in [256usize,257] {
        for roundtrip in [false,true] {
            std::env::set_var("MIDQ_TAIL_TOP_COMPARE","0");
            std::env::set_var("MIDQ_TAIL_INVERSE_TOP_COMPARE","0");
            let original=build_cell(width,cap,24,false,roundtrip,None);
            let full=build_cell(width,cap,24,true,roundtrip,None);
            std::env::set_var("MIDQ_TAIL_TOP_COMPARE","1");
            std::env::set_var("MIDQ_TAIL_INVERSE_TOP_COMPARE","1");
            let narrow=build_cell(width,cap,24,true,roundtrip,None);
            if super::super::super::hybrid_profile::legacy_margin_allowed() {
                assert_eq!(top_compare_low_bits(),136);assert_eq!(super::super::inverse_compare_low_bits(),136);
            }else {
                assert_eq!(top_compare_low_bits(),expected.forward_drop.unwrap_or(0));
                assert_eq!(super::super::inverse_compare_low_bits(),expected.inverse_drop.unwrap_or(0));
            }
            for batch in cases.chunks(64) {
                let mut input=vec![0;original.live];let mut wanted=input.clone();
                for (lane,&(a,b,sign,y)) in batch.iter().enumerate() {
                    for bit in 0..256 {
                        input[bit]|=u64::from(a.bit(bit))<<lane;
                        input[width+bit]|=u64::from(b.bit(bit))<<lane;
                        wanted[bit]|=u64::from((if roundtrip {a}else{y}).bit(bit))<<lane;
                        wanted[width+bit]|=u64::from(b.bit(bit))<<lane;
                    }
                    input[2*width]|=u64::from(sign)<<lane;wanted[2*width]|=u64::from(sign)<<lane;
                }
                for mode in 0..3 {
                    for cell in [&original,&full,&narrow] {
                        let(v,p,_)=super::super::selftest::run_ops(&cell.built,&input,mode,None,None);
                        assert_eq!((v,p),(wanted.clone(),0));checked+=batch.len();
                    }
                }
            }
        }
    }
    // Inverse narrowing does not depend on forward fusion being enabled.
    std::env::set_var("MIDQ_FUSED_ROTATION_CELL","0");
    assert!(super::super::inverse_compare_low_bits()>0);
    // For new profiles, absent/incorrect support declarations emit no fused
    // replacement and preserve the full-comparator oracle byte-for-byte.
    if !super::super::super::hybrid_profile::legacy_margin_allowed() {
        for declaration in [None,Some("sampled-positive-l31"),Some("exact-positive-l63")] {
            if let Some(s)=declaration {std::env::set_var("HYBRID_MARGIN_SUPPORT",s);}else{std::env::remove_var("HYBRID_MARGIN_SUPPORT");}
            assert!(!super::super::super::hybrid_margin::full_fused_allowed());
            assert_eq!(super::super::inverse_compare_low_bits(),0);
            std::env::set_var("MIDQ_FUSED_ROTATION_CELL","1");
            let full=build_top_oracle(false);let attempted=build_top_oracle(true);
            assert_eq!(full.ops,attempted.ops);
            failed_admission();
        }
    }
    if let Some(s)=support_old {std::env::set_var("HYBRID_MARGIN_SUPPORT",s);}else{std::env::remove_var("HYBRID_MARGIN_SUPPORT");}
    if let Some(s)=inverse_old {std::env::set_var("MIDQ_TAIL_INVERSE_TOP_COMPARE",s);}else{std::env::remove_var("MIDQ_TAIL_INVERSE_TOP_COMPARE");}
    eprintln!("HYBRID_MARGIN_NATIVE_CELLS PASS cases={checked} profile={} value_bits={} forward_drop={:?} inverse_drop={:?} full_fused=true;original_full/fused_full/fused_narrow value_phase_every_reset_inverse;missing_support_fallback_exact=true",super::super::super::hybrid_profile::SELECTED.id,super::super::super::MIDQ_TAIL_VALUE_WIDTH[0],expected.forward_drop,expected.inverse_drop);
}

fn condition(c: &mut Circuit, enabled: Option<bool>, body: impl FnOnce(&mut Circuit)) {
    if let Some(enabled) = enabled {
        let outer = c.alloc_bit();
        let inner = c.alloc_bit();
        for (bit, value) in [(outer, enabled), (inner, true)] {
            let mut op = Op::empty();
            op.kind = if value {
                OpKind::BitStore1
            } else {
                OpKind::BitStore0
            };
            op.c_target = BitId(bit.raw() as u64);
            c.b.push_op(op);
        }
        c.with_conditions(&[outer, inner], body);
    } else {
        body(c);
    }
}

fn weighted_t(ops: &[Op]) -> f64 {
    let mut depth = 0;
    let mut total = 0.0;
    for op in ops {
        match op.kind {
            OpKind::PushCondition => depth += 1,
            OpKind::PopCondition => depth -= 1,
            OpKind::CCX | OpKind::CCZ => total += 2.0f64.powi(-depth),
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    total
}

fn primitive_tests() -> usize {
    let mut checked = 0;
    for n in 1usize..=8 {
        let mask = (1usize << n) - 1;
        for available in 0..n {
            if !recursive::cost(n, available, false).is_finite() {
                continue;
            }
            for gap in [1i64, 3, 5, 9, 0x1000003d1] {
                for enabled in [None, Some(false), Some(true)] {
                    let mut c = Circuit::new();
                    let target = c.alloc_qreg_bits("test.offset.target", n);
                    let parity = c.alloc_qreg("test.offset.parity");
                    let overflow = c.alloc_qreg("test.offset.overflow");
                    let sign = c.alloc_qreg("test.offset.sign");
                    let _spectator = c.alloc_qreg("test.offset.spectator");
                    condition(&mut c, enabled, |c| {
                        add_selected(c, &target, &parity, &overflow, &sign, gap, available)
                    });
                    c.flush_pending_frees();
                    let built = c.into_builder();
                    assert!(built.peak_qubits as usize <= n + 7 + available);
                    if enabled.is_none() {
                        assert_eq!(
                            weighted_t(&built.ops),
                            2.0 + recursive::cost(n, available, false)
                        );
                    }
                    for first in (0..1usize << (n + 4)).step_by(64) {
                        let input: Vec<u64> = (0..n + 4)
                            .map(|i| {
                                (0..64).fold(0, |v, shot| {
                                    v | ((((first + shot) >> i) & 1) as u64) << shot
                                })
                            })
                            .collect();
                        let mut expected = input.clone();
                        expected[..n].fill(0);
                        for shot in 0..64 {
                            let v = first + shot;
                            let a = v & mask;
                            let p = v >> n & 1;
                            let h = v >> (n + 1) & 1;
                            let s = v >> (n + 2) & 1;
                            let delta = -((p ^ s) as i64) * ((gap - 1) / 2)
                                + (1 - 2 * s as i64) * (h & p) as i64 * gap;
                            let answer = if enabled == Some(false) {
                                a
                            } else {
                                (a as i64 + delta).rem_euclid(1i64 << n) as usize
                            };
                            for i in 0..n {
                                expected[i] |= (((answer >> i) & 1) as u64) << shot;
                            }
                        }
                        for mode in 0..3 {
                            let (value, phase, _) =
                                super::super::selftest::run_ops(&built, &input, mode, None, None);
                            assert_eq!(
                                (value, phase),
                                (expected.clone(), 0),
                                "offset n={n} A={available} gap={gap} enabled={enabled:?}"
                            );
                            checked += 64;
                        }
                        if n <= 3 {
                            let measurements =
                                built.ops.iter().filter(|op| op.kind == OpKind::Hmr).count();
                            for transcript in 0..1usize << measurements {
                                let (value, phase, _) = super::super::selftest::run_ops(
                                    &built,
                                    &input,
                                    0,
                                    Some(transcript),
                                    None,
                                );
                                assert_eq!((value, phase), (expected.clone(), 0));
                                checked += 64;
                            }
                        }
                    }
                }
            }
        }
    }
    checked
}

struct Cell {
    built: B,
    live: usize,
}

fn build_cell(
    width: usize,
    cap: usize,
    headroom: usize,
    fused: bool,
    roundtrip: bool,
    enabled: Option<bool>,
) -> Cell {
    std::env::set_var("MIDQ_CELL_QCAP", cap.to_string());
    std::env::set_var("MIDQ_CHUNK_COMPARE_QCAP", cap.to_string());
    std::env::set_var("MIDQ_FUSED_ROTATION_CELL", if fused { "1" } else { "0" });
    let live = cap - headroom;
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("test.cell.target", width);
    let source = c.alloc_qreg_bits("test.cell.source", width);
    let sign = c.alloc_qreg("test.cell.sign");
    let _spectators = c.alloc_qreg_bits("test.cell.spectator", live - 2 * width - 1);
    condition(&mut c, enabled, |c| {
        if fused {
            assert!(try_apply(c, &target, &source, &sign));
        } else {
            super::super::apply(c, &target, &source, &sign, false);
        }
        if roundtrip {
            super::super::apply(c, &target, &source, &sign, true);
        }
    });
    c.flush_pending_frees();
    let built = c.into_builder();
    assert!(
        built.peak_qubits as usize <= cap,
        "cell cap width={width} cap={cap} headroom={headroom} fused={fused}"
    );
    Cell { built, live }
}

fn fixtures() -> Vec<(U256, U256, bool, U256)> {
    include_str!("fused_rotation_cases.txt")
        .lines()
        .map(|line| {
            let fields: Vec<_> = line.split_whitespace().collect();
            assert_eq!(fields.len(), 4);
            (
                U256::from_str_radix(fields[0], 16).unwrap(),
                U256::from_str_radix(fields[1], 16).unwrap(),
                fields[2] == "1",
                U256::from_str_radix(fields[3], 16).unwrap(),
            )
        })
        .collect()
}

fn certified_cells() -> usize {
    let cases = fixtures();
    assert_eq!(cases.len(), 512);
    let mut checked = 0;
    for width in [256usize, 257] {
        for cap in [1000usize, 1011] {
            for headroom in [12usize, 16, 24, 40] {
                for roundtrip in [false, true] {
                    let old = build_cell(width, cap, headroom, false, roundtrip, None);
                    let new = build_cell(width, cap, headroom, true, roundtrip, None);
                    let mut executed = [0u64; 2];
                    for batch in cases.chunks(64) {
                        let mut input: Vec<_> = (0..old.live)
                            .map(|i| {
                                (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ 0xa55a_c33c_9669_5aa5
                            })
                            .collect();
                        input[..2 * width + 1].fill(0);
                        let mut expected = input.clone();
                        for (shot, &(a, b, sign, result)) in batch.iter().enumerate() {
                            let expected_value = if roundtrip { a } else { result };
                            for i in 0..256 {
                                input[i] |= u64::from(a.bit(i)) << shot;
                                input[width + i] |= u64::from(b.bit(i)) << shot;
                                expected[i] |= u64::from(expected_value.bit(i)) << shot;
                                expected[width + i] |= u64::from(b.bit(i)) << shot;
                            }
                            input[2 * width] |= u64::from(sign) << shot;
                            expected[2 * width] |= u64::from(sign) << shot;
                        }
                        for mode in 0..3 {
                            let r0 = super::super::selftest::run_ops(
                                &old.built, &input, mode, None, None,
                            );
                            let r1 = super::super::selftest::run_ops(
                                &new.built, &input, mode, None, None,
                            );
                            assert_eq!((&r0.0, r0.1), (&expected, 0), "old certificate mismatch");
                            assert_eq!((&r1.0, r1.1), (&expected, 0), "fused width={width} cap={cap} room={headroom} roundtrip={roundtrip}");
                            if mode == 2 {
                                executed[0] += r0.2;
                                executed[1] += r1.2;
                            }
                            checked += batch.len();
                        }
                    }
                    eprintln!("FUSED_ROTATION_CELL_RESOURCE width={width} cap={cap} headroom={headroom} roundtrip={roundtrip} oldQ={} newQ={} old_avgT={} new_avgT={} old_weightedT={} new_weightedT={}",
                        old.built.peak_qubits, new.built.peak_qubits,
                        executed[0] as f64 / cases.len() as f64, executed[1] as f64 / cases.len() as f64,
                        weighted_t(&old.built.ops), weighted_t(&new.built.ops));
                }
            }
        }
    }
    // Complete fused cell under active and inactive nested classical scopes.
    for enabled in [false, true] {
        let cell = build_cell(256, 1000, 16, true, false, Some(enabled));
        for batch in cases[..64].chunks(64) {
            let mut input = vec![0; cell.live];
            let mut expected = input.clone();
            for (shot, &(a, b, sign, result)) in batch.iter().enumerate() {
                let expected_value = if enabled { result } else { a };
                for i in 0..256 {
                    input[i] |= u64::from(a.bit(i)) << shot;
                    input[256 + i] |= u64::from(b.bit(i)) << shot;
                    expected[i] |= u64::from(expected_value.bit(i)) << shot;
                    expected[256 + i] |= u64::from(b.bit(i)) << shot;
                }
                input[512] |= u64::from(sign) << shot;
                expected[512] |= u64::from(sign) << shot;
            }
            for mode in 0..3 {
                let (value, phase, _) =
                    super::super::selftest::run_ops(&cell.built, &input, mode, None, None);
                assert_eq!((value, phase), (expected.clone(), 0));
                checked += batch.len();
            }
        }
    }
    checked
}

fn failed_admission() {
    std::env::set_var("MIDQ_FUSED_ROTATION_CELL", "1");
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("test.fallback.target", 256);
    let source = c.alloc_qreg_bits("test.fallback.source", 256);
    let sign = c.alloc_qreg("test.fallback.sign");
    c.flush_pending_frees();
    std::env::set_var("MIDQ_CELL_QCAP", c.b.active_qubits.to_string());
    let before = c.b.ops.clone();
    assert!(!try_apply(&mut c, &target, &source, &sign));
    assert_eq!(before, c.b.ops);
}

fn outside_support_channel() -> usize {
    let f = U256::from(0x1000003d1u64);
    let k = U256::from(0x800001e8u64);
    let p = U256::MAX - f + U256::from(1);
    let low_mask = (U256::from(1) << 255) - U256::from(1);
    let edges = [
        U256::ZERO,
        U256::from(1),
        f - U256::from(1),
        f,
        f + U256::from(1),
        p - U256::from(1),
        p,
        U256::MAX,
    ];
    let mut cases = Vec::new();
    for a in edges {
        for b in edges {
            for sign in [false, true] {
                for overflow in [false, true] {
                    for source_high in [false, true] {
                        cases.push((a, b, sign, overflow, source_high));
                    }
                }
            }
        }
    }
    let old = build_cell(257, 1000, 16, false, false, None);
    let new = build_cell(257, 1000, 16, true, false, None);
    let mut changed = 0;
    let mut checked = 0;
    for batch in cases.chunks(64) {
        let mut input = vec![0; old.live];
        let mut expected = input.clone();
        let mut old_defect = 0u64;
        let mut new_defect = 0u64;
        for (shot, &(a, b, sign, overflow, source_high)) in batch.iter().enumerate() {
            let framed = if sign { !a } else { a };
            let (sum, carry) = framed.overflowing_add(b);
            let h = carry ^ overflow;
            let folded = sum.wrapping_add(if h { f } else { U256::ZERO });
            let value = if sign { !folded } else { folded };
            let odd = value.bit(0);
            let result: U256 = ((value >> 1usize).wrapping_sub(if odd { k } else { U256::ZERO })
                & low_mask)
                | if odd {
                    U256::from(1) << 255
                } else {
                    U256::ZERO
                };
            let rotation: U256 = (result << 1usize) | (result >> 255usize);
            let rotated_frame = if sign { !rotation } else { rotation };
            let e_old = h ^ (folded < b);
            let e_new = h ^ (rotated_frame < b);
            old_defect |= u64::from(e_old) << shot;
            new_defect |= u64::from(e_new) << shot;
            changed += usize::from(e_old != e_new);
            for i in 0..256 {
                input[i] |= u64::from(a.bit(i)) << shot;
                input[257 + i] |= u64::from(b.bit(i)) << shot;
                expected[i] |= u64::from(result.bit(i)) << shot;
                expected[257 + i] |= u64::from(b.bit(i)) << shot;
            }
            input[256] |= u64::from(overflow) << shot;
            input[513] |= u64::from(source_high) << shot;
            expected[513] |= u64::from(source_high) << shot;
            input[514] |= u64::from(sign) << shot;
            expected[514] |= u64::from(sign) << shot;
        }
        for mode in 0..3 {
            let measurement = [0, u64::MAX, 0xa55a_c33c_9669_5aa5][mode as usize];
            let coupled = Some((256, measurement));
            let a = super::super::selftest::run_ops(&old.built, &input, mode, None, coupled);
            let b = super::super::selftest::run_ops(&new.built, &input, mode, None, coupled);
            assert_eq!((a.0, a.1), (expected.clone(), old_defect & measurement));
            assert_eq!((b.0, b.1), (expected.clone(), new_defect & measurement));
            checked += batch.len();
        }
    }
    assert!(
        changed > 0,
        "fixture must expose qualified rather than all-input phase equivalence"
    );
    eprintln!("FUSED_ROTATION_OUTSIDE_SUPPORT PASS: {checked} coupled measurement cases, exact finite-word values and each implementation's OWN phase map; {changed} input cases intentionally have different phase coefficients");
    checked
}

pub(super) fn run() {
    let _guard = Guard::new();
    // Preserve the original rotation-only selftest's outside-support oracle.
    // The independently selected top-comparison suite qualifies its own change.
    std::env::set_var("MIDQ_TAIL_TOP_COMPARE", "0");
    for flag in [
        "MIDQ_CELL_SUM",
        "MIDQ_CELL_RECURSIVE_CARRY",
        "MIDQ_CELL_COST_SELECT",
        "MIDQ_ALL_CONST_FOLDS",
        "MIDQ_DIRTY_CONST",
        "MIDQ_OUTER_DIRTY_CONST",
        "MIDQ_COMPACT_CONST_CARRY",
        "MIDQ_VARIABLE_CHUNKS",
        "MIDQ_MEASURE_COMPARE",
        "MIDQ_CHUNK_COMPARE",
        "MIDQ_ROTATED_HALVES",
        "MIDQ_CELL_FOLDS",
    ] {
        std::env::set_var(flag, "1");
    }
    let small = primitive_tests();
    let wide = certified_cells();
    let outside = outside_support_channel();
    failed_admission();
    eprintln!("FUSED_ROTATION_CELL_SELFTEST PASS: {small} selected-addend basis/measurement cases, {wide} certified native full-cell cases, {outside} explicit outside-support channel cases; exact value/phase, pre-reset scratch, unchanged source/controls/spectators, nested conditions, caps and old inverse; off-support phase equivalence NOT claimed");
}

fn top_compare_certified_cells() -> usize {
    let cases = fixtures();
    assert_eq!(cases.len(), 512);
    let p = U256::MAX - U256::from(0x1000003d1u64) + U256::from(1);
    for &(a, b, sign, y) in &cases {
        assert!(a < p && b < p && y < p);
        assert!(a.min(p - a) > (U256::from(1) << 137));
        let framed = if sign { !a } else { a };
        let (_, carry) = framed.overflowing_add(b);
        let rotation: U256 = (y << 1usize) | (y >> 255usize);
        let lhs = if sign { !rotation } else { rotation };
        let gap = if lhs >= b { lhs - b } else { b - lhs };
        assert!(gap > (U256::from(1) << 136));
        assert_eq!(lhs < b, carry);
        assert_eq!((lhs >> 136usize) < (b >> 136usize), carry);
    }
    let mut checked = 0;
    for width in [256usize, 257] {
        for headroom in [12usize, 24] {
            for roundtrip in [false, true] {
                std::env::set_var("MIDQ_TAIL_TOP_COMPARE", "0");
                let full = build_cell(width, 1011, headroom, true, roundtrip, None);
                std::env::set_var("MIDQ_TAIL_TOP_COMPARE", "1");
                assert!(top_compare_eligible());
                let top = build_cell(width, 1011, headroom, true, roundtrip, None);
                let mut executed = [0u64; 2];
                for batch in cases.chunks(64) {
                    let mut input: Vec<_> = (0..full.live)
                        .map(|i| {
                            (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ 0xa55a_c33c_9669_5aa5
                        })
                        .collect();
                    input[..2 * width + 1].fill(0);
                    let mut expected = input.clone();
                    for (shot, &(a, b, sign, y)) in batch.iter().enumerate() {
                        for i in 0..256 {
                            input[i] |= u64::from(a.bit(i)) << shot;
                            input[width + i] |= u64::from(b.bit(i)) << shot;
                            expected[i] |=
                                u64::from((if roundtrip { a } else { y }).bit(i)) << shot;
                            expected[width + i] |= u64::from(b.bit(i)) << shot;
                        }
                        input[2 * width] |= u64::from(sign) << shot;
                        expected[2 * width] |= u64::from(sign) << shot;
                    }
                    for mode in 0..3 {
                        let a =
                            super::super::selftest::run_ops(&full.built, &input, mode, None, None);
                        let b =
                            super::super::selftest::run_ops(&top.built, &input, mode, None, None);
                        assert_eq!((&a.0, a.1), (&expected, 0), "full oracle certified cell");
                        assert_eq!((&b.0, b.1), (&expected, 0), "top oracle certified cell");
                        if mode == 2 {
                            executed[0] += a.2;
                            executed[1] += b.2;
                        }
                        checked += batch.len();
                    }
                }
                eprintln!("TAIL_TOP_COMPARE_RESOURCE width={width} room={headroom} roundtrip={roundtrip} fullQ={} topQ={} full_avgT={} top_avgT={}; forward predicate only, inverse unchanged",
                    full.built.peak_qubits,top.built.peak_qubits,
                    executed[0] as f64/cases.len() as f64,executed[1] as f64/cases.len() as f64);
            }
        }
    }
    // Active and inactive nested classical scopes preserve the same guard.
    for enabled in [false, true] {
        std::env::set_var("MIDQ_TAIL_TOP_COMPARE", "1");
        let cell = build_cell(256, 1000, 16, true, false, Some(enabled));
        let batch = &cases[..64];
        let mut input = vec![0; cell.live];
        let mut expected = input.clone();
        for (shot, &(a, b, sign, y)) in batch.iter().enumerate() {
            for i in 0..256 {
                input[i] |= u64::from(a.bit(i)) << shot;
                input[256 + i] |= u64::from(b.bit(i)) << shot;
                expected[i] |= u64::from((if enabled { y } else { a }).bit(i)) << shot;
                expected[256 + i] |= u64::from(b.bit(i)) << shot;
            }
            input[512] |= u64::from(sign) << shot;
            expected[512] |= u64::from(sign) << shot;
        }
        for mode in 0..3 {
            let (out, phase, _) =
                super::super::selftest::run_ops(&cell.built, &input, mode, None, None);
            assert_eq!((out, phase), (expected.clone(), 0));
            checked += 64;
        }
    }
    checked
}

fn build_top_oracle(top: bool) -> B {
    std::env::set_var("MIDQ_TAIL_TOP_COMPARE", if top { "1" } else { "0" });
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("oracle.target", 256);
    let source = c.alloc_qreg_bits("oracle.source", 256);
    let sign = c.alloc_qreg("oracle.sign");
    let overflow = c.alloc_qreg("oracle.overflow");
    for q in &target {
        c.cx(&sign, q)
    }
    clear_rotated_overflow(&mut c, &target, &source, &overflow);
    for q in &target {
        c.cx(&sign, q)
    }
    c.flush_pending_frees();
    c.into_builder()
}

fn top_compare_outside_and_fallback() -> usize {
    let full = build_top_oracle(false);
    let top = build_top_oracle(true);
    let rhs = (U256::from(1) << 200usize) + U256::from(7);
    let mut input = vec![0u64; 514];
    let mut expected = input.clone();
    let mut defect = 0;
    for lane in 0..64 {
        let sign = lane & 1 != 0;
        let lhs = match lane % 3 {
            0 => rhs - U256::from(1),
            1 => rhs,
            _ => rhs + U256::from(1),
        };
        let rotation = if sign { !lhs } else { lhs };
        let y: U256 = (rotation >> 1usize) | (rotation << 255usize);
        let original = lhs < rhs;
        let narrowed = (lhs >> 136usize) < (rhs >> 136usize);
        assert!(
            !narrowed,
            "witness low differences must share the same high word"
        );
        defect |= u64::from(original ^ narrowed) << lane;
        for i in 0..256 {
            input[i] |= u64::from(y.bit(i)) << lane;
            expected[i] |= u64::from(y.bit(i)) << lane;
            input[256 + i] |= u64::from(rhs.bit(i)) << lane;
            expected[256 + i] |= u64::from(rhs.bit(i)) << lane;
        }
        input[512] |= u64::from(sign) << lane;
        expected[512] |= u64::from(sign) << lane;
        input[513] |= u64::from(original) << lane;
    }
    assert_ne!(
        defect, 0,
        "outside-support phase difference must be exercised"
    );
    for mode in 0..3 {
        let measurement = [0, u64::MAX, 0xa55a_c33c_9669_5aa5][mode as usize];
        let coupled = Some((513, measurement));
        let a = super::super::selftest::run_ops(&full, &input, mode, None, coupled);
        let b = super::super::selftest::run_ops(&top, &input, mode, None, coupled);
        assert_eq!((a.0, a.1), (expected.clone(), 0));
        assert_eq!((b.0, b.1), (expected.clone(), defect & measurement));
    }
    // A failed construction guard emits exactly the ordinary full comparator.
    for (name, bad, good) in [
        ("MIDQ_PZ_PINGPONG_TAIL", "0", "1"),
        ("TRAILMIX_SROT_W", "6", "5"),
        ("MIDQ_ROTATED_HALVES", "0", "1"),
        ("MIDQ_MEASURE_COMPARE", "0", "1"),
        ("MIDQ_FUSED_ROTATION_CELL", "0", "1"),
    ] {
        std::env::set_var(name, bad);
        let old = build_top_oracle(false);
        let guarded = build_top_oracle(true);
        assert!(!top_compare_eligible());
        assert_eq!(old.ops, guarded.ops, "fallback {name}");
        std::env::set_var(name, good);
    }
    eprintln!("TAIL_TOP_COMPARE_OUTSIDE_SUPPORT PASS:192 native coupled outcome cases; intentional low136-bit tie phase defect, no all-input equivalence claim; exact full-comparator fallback under every mutable guard");
    192
}

pub(super) fn run_top_compare() {
    let _guard = Guard::new();
    for flag in [
        "MIDQ_CELL_SUM",
        "MIDQ_CELL_RECURSIVE_CARRY",
        "MIDQ_CELL_COST_SELECT",
        "MIDQ_ALL_CONST_FOLDS",
        "MIDQ_DIRTY_CONST",
        "MIDQ_OUTER_DIRTY_CONST",
        "MIDQ_COMPACT_CONST_CARRY",
        "MIDQ_VARIABLE_CHUNKS",
        "MIDQ_MEASURE_COMPARE",
        "MIDQ_CHUNK_COMPARE",
        "MIDQ_ROTATED_HALVES",
        "MIDQ_CELL_FOLDS",
        "MIDQ_FUSED_ROTATION_CELL",
        "MIDQ_PZ_PINGPONG_TAIL",
    ] {
        std::env::set_var(flag, "1")
    }
    std::env::set_var("TRAILMIX_SROT_W", "5");
    let certified = top_compare_certified_cells();
    let outside = top_compare_outside_and_fallback();
    eprintln!("TAIL_TOP_COMPARE_SELFTEST PASS: certified_native_cases={certified} outside_cases={outside}; full256 versus top120 forward fused phase oracle, canonical fixtures, old inverse roundtrips, nested conditions, source/sign/spectator preservation and every-reset scratch audit; input support membership remains a separate obligation");
}
