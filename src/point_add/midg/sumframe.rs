//! Source integration primitive for the post-stage-2 size-sum frame.
//!
//! Called only by the guarded C666_POOL5 layout. The source identity alone
//! does not establish a measured physical saving or circuit qualification.
//!
//! With paid Cross QB30, every nonfinal model-clean paired state has
//! 226 <= bl(r_j)+bl(t_j) <= 257. Indeed p < (q_j+2)*r_j*t_j
//! and q_j<2^30 exclude a sum <=225. Fixed paths retain QB23 and
//! therefore satisfy the stronger lower bound233. This statement starts
//! after DQ/first-HT SY refill. Idle A0 retains the final KD26 bound231;
//! idle B0 is the preceding capped pair and has sum>=226. Thus every
//! supported completed boundary fits the entire bias226 five-bit domain.
//!
//! Encode/decode is a full reversible modulo-256 permutation. The three
//! high SZ owners may be borrowed only inside that frame and must all be
//! returned before decoding. Affine queries below do not read those owners.
//! The raw-SZ readers use SY's low seven bits with zero denoting 128, so
//! they also work while the existing SY-high normalization is held. They
//! must not run while SY's low seven bits hold a different arithmetic view.

use super::super::builder::{B, G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;

pub(super) const BIAS: usize = 226;
pub(super) const CODE_BITS: usize = 5;

/// Record SZ <- SZ + SY - BIAS (mod 256), with no clean helper.
/// For the column-0 raw view the caller must first undo the existing -217
/// offset. This routine's raw input is SZ mod 256, including SZ=256.
pub(super) fn record(b: &mut B, sz: &[QubitId], sy: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(sz.len(), 8);
    assert_eq!(sy.len(), 8);
    assert!(!sz.iter().any(|q| sy.contains(q)));
    let bank: Vec<_> = dirty.iter().copied()
        .filter(|q| !sz.contains(q) && !sy.contains(q)).collect();
    super::super::frogdrop_col::rec(b, |b| {
        super::super::arith::ttk_add(b, sy, sz, None, None);
        let bias = super::super::frogdrop_col::rec(b, |b| {
            super::super::frogdrop::add_const_dirty_exact(b, sz, BIAS, &bank);
        });
        b.play(&bias, true);
    })
}

/// Apply a cyclic up-rotation controlled by a conjunction, using no clean
/// helper. Other cycle cells may be borrowed inside an individual swap:
/// mc_swap returns them before the next cell swap changes the permutation.
fn rotate_controls(b: &mut B, cycle: &[QubitId], amount: usize,
                   controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    let n = cycle.len();
    assert!(n > 0);
    let amount = amount % n;
    if amount == 0 { return; }
    let mut a = n;
    let mut d = amount;
    while d != 0 { let rem = a % d; a = d; d = rem; }
    for start in 0..a {
        let orbit: Vec<_> = (0..n / a).map(|i| cycle[(start + i * amount) % n]).collect();
        for i in (1..orbit.len()).rev() {
            let (x, y) = (orbit[i], orbit[i - 1]);
            if controls.is_empty() { b.swap(x, y); continue; }
            let mut bank = Vec::new();
            for &q in dirty.iter().chain(cycle) {
                if q != x && q != y && !controls.iter().any(|&(c, _)| c == q) && !bank.contains(&q) {
                    bank.push(q);
                }
            }
            super::super::mid2::mc_swap(b, controls, x, y, &[], &bank);
        }
    }
}

/// Full cyclic up-rotation under a conjunction, without a clean flag.
pub(super) fn rot_up_const_controlled(b: &mut B, cycle: &[QubitId], amount: usize,
                                    controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    assert_eq!(cycle.iter().collect::<std::collections::BTreeSet<_>>().len(), cycle.len());
    assert!(!controls.iter().any(|&(q, _)| cycle.contains(&q)));
    rotate_controls(b, cycle, amount, controls, dirty);
}

/// target += zero_extend(code), modulo the target width. Pad the source
/// with arbitrary restored donors D, then cancel their contribution on
/// the high target. For code5, this costs18 CCX on target8 and14 on target7.
pub(super) fn add_zero_extended(
    b: &mut B, code: &[QubitId], target: &[QubitId], dirty: &[QubitId],
) {
    assert_eq!(code.len(), CODE_BITS);
    assert!(target.len() >= code.len());
    let ports: Vec<_> = code.iter().chain(target).copied().collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    let npad = target.len() - code.len();
    let mut pad = Vec::new();
    if npad > 0 {
        for &q in dirty {
            if !ports.contains(&q) && !pad.contains(&q) { pad.push(q); }
            if pad.len() == npad { break; }
        }
    }
    assert_eq!(pad.len(), npad, "not enough distinct returned dirty padding");
    let padded: Vec<_> = code.iter().chain(&pad).copied().collect();
    // +code + 2^CODE_BITS * D. TTK restores every source bit, including D.
    super::super::arith::ttk_add(b, &padded, target, None, None);
    // -2^CODE_BITS * D. The high-target subtraction is exactly the same
    // full-word subtraction because its low CODE_BITS bits are zero.
    match pad.len() {
        0 => {},
        1 => b.cx(pad[0], target[CODE_BITS]),
        _ => {
            let undo_padding = super::super::frogdrop_col::rec(b, |b| {
                super::super::arith::ttk_add(b, &pad, &target[CODE_BITS..], None, None);
            });
            b.play(&undo_padding, true);
        }
    }
}

/// Rotate by raw Z = BIAS + code - SY without reconstructing SZ's three
/// high owners. Like frogdrop::rot_by, inverse=true moves content down.
/// This preserves the entire cycle. SY is in 1..=128; low7 zero means128.
/// Its high owner is never read and can be a parked payload bit.
pub(super) fn rot_raw(b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
                     inverse: bool, dirty: &[QubitId]) {
    rot_raw_impl(b, cycle, code, sy, inverse, dirty, None);
}

/// Same exact permutation, with a separately returned clean flag. The caller
/// must prove the flag is zero at both entry and exit, including inverse plays.
/// Temporarily expose rawSZ-1 in SYlow7 plus flag, rotate by1 plus that view,
/// then restore every address bit. This also covers rawSZ256 on N257/NP259.
/// Physical SY7 is not an address bit; it may be ordinary cycle data.
pub(super) fn rot_raw_clean(
    b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
    inverse: bool, dirty: &[QubitId], flag: QubitId,
) {
    rot_raw_clean_impl(b, cycle, code, sy, inverse, dirty, flag, None);
}

/// The same returned-address transform for an existing support-only frame.
/// `dest` is exactly the caller's inherited DOWN destination support; the
/// intervening body must touch only that support (apart from returned dirt).
/// Keep the unchanged full permutation for callers without this contract.
pub(super) fn rot_raw_clean_care(
    b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
    inverse: bool, dirty: &[QubitId], flag: QubitId, lo: usize, hi: usize,
    dest: &std::collections::BTreeSet<usize>,
) {
    assert!(1 <= lo && lo <= hi && hi <= 256 && hi <= cycle.len());
    assert!(dest.iter().all(|&i| i < cycle.len()));
    rot_raw_clean_impl(b, cycle, code, sy, inverse, dirty, flag, Some((lo, hi, dest)));
}

/// Conjugate a singleton query by the raw-Z address using one returned
/// address epoch. `destination` is the old DOWN-frame lane. The raw lane
/// is (destination+Z)%N. With query=None toggle that lane; with (c,t),
/// toggle t by c & !lane. All other arbitrary cycle passengers return.
/// The inherited whole-column size domain must be contained in lo..=hi.
#[allow(clippy::too_many_arguments)]
pub(super) fn raw_lane_query(
    b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
    flag: QubitId, lo: usize, hi: usize, destination: usize,
    query: Option<(QubitId, QubitId)>, dirty: &[QubitId],
) {
    assert_eq!(code.len(), CODE_BITS);
    assert_eq!(sy.len(), 8);
    assert!(1 <= lo && lo <= hi && hi <= 256 && hi <= cycle.len());
    assert!(destination < cycle.len());
    let ports: Vec<_> = cycle.iter().chain(code).chain(&sy[..7])
        .copied().chain([flag]).collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    assert!(!sy.contains(&flag));
    let protected = match query {
        Some((c, t)) => {
            assert!(c != t && !ports.contains(&c) && !ports.contains(&t));
            assert!(!sy.contains(&c) && !sy.contains(&t));
            vec![c, t]
        }
        None => vec![],
    };
    let mut bank = Vec::new();
    for &q in dirty {
        if q != flag && !code.contains(&q) && !sy.contains(&q)
            && !protected.contains(&q) && !bank.contains(&q) { bank.push(q); }
    }
    assert!(bank.len() >= 8);
    let view: Vec<_> = sy[..7].iter().copied().chain([flag]).collect();
    let zero: Vec<_> = sy[..7].iter().map(|&q| (q, true)).collect();
    let address = super::super::frogdrop_col::rec(b, |b| {
        mc_xor(b, &zero, flag, &[], &bank);
        for &q in &view { b.x(q); }
        add_zero_extended(b, code, &view, &bank);
        super::super::frogdrop::add_const_dirty_exact(b, &view, BIAS, &bank);
    });
    // Postorder binary selection: unary nodes just forward their occupied
    // child. For every valid address the chosen leaf reaches the root.
    fn collect(view: &[QubitId], leaves: &[(usize, QubitId)], level: usize,
               swaps: &mut Vec<(QubitId, QubitId, QubitId)>) -> QubitId {
        assert!(!leaves.is_empty());
        if level == 0 { assert_eq!(leaves.len(), 1); return leaves[0].1; }
        let bit = level - 1;
        let split = leaves.partition_point(|&(v, _)| (v >> bit) & 1 == 0);
        if split == 0 { return collect(view, leaves, bit, swaps); }
        if split == leaves.len() { return collect(view, leaves, bit, swaps); }
        let left = collect(view, &leaves[..split], bit, swaps);
        let right = collect(view, &leaves[split..], bit, swaps);
        swaps.push((view[bit], left, right));
        left
    }
    let leaves: Vec<_> = (lo..=hi).map(|z|
        (z - 1, cycle[(destination + z) % cycle.len()])).collect();
    let mut swaps = Vec::new();
    let root = collect(&view, &leaves, view.len(), &mut swaps);
    assert_eq!(swaps.len(), hi - lo);
    b.play(&address, false);
    for &(c, a, d) in &swaps { b.cswap(c, a, d); }
    match query {
        None => b.x(root),
        Some((c, t)) => { b.x(root); b.ccx(c, root, t); b.x(root); }
    }
    for &(c, a, d) in swaps.iter().rev() { b.cswap(c, a, d); }
    b.play(&address, true);
}

fn rot_raw_clean_impl(
    b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
    inverse: bool, dirty: &[QubitId], flag: QubitId,
    care: Option<(usize, usize, &std::collections::BTreeSet<usize>)>,
) {
    assert_eq!(BIAS, 226);
    assert_eq!(CODE_BITS, 5);
    assert_eq!(code.len(), CODE_BITS);
    assert_eq!(sy.len(), 8);
    assert!(!cycle.is_empty());
    let ports: Vec<_> = cycle.iter().chain(code).chain(&sy[..7]).copied().chain([flag]).collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    assert!(!sy.contains(&flag));
    // Cycle data can be arbitrary restored donors: both complete arithmetic
    // transforms are independent of the donor values at their own entry.
    let mut bank = Vec::new();
    for &q in dirty {
        if q != flag && !code.contains(&q) && !sy.contains(&q) && !bank.contains(&q) {
            bank.push(q);
        }
    }
    assert!(bank.len() >= 8, "eight distinct dirty donors for the constant adder");
    let view: Vec<_> = sy[..7].iter().copied().chain([flag]).collect();
    let zero: Vec<_> = sy[..7].iter().map(|&q| (q, true)).collect();
    let shift = super::super::frogdrop_col::rec(b, |b| {
        // Here view is the logical integer SY in1..128, even if sy[7] is parked.
        for &q in &view { b.x(q); }
        add_zero_extended(b, code, &view, &bank);
        super::super::frogdrop::add_const_dirty_exact(b, &view, 226, &bank);
        // view = ~SY + code +226 = (226+code-SY)-1 = rawSZ-1.
    });
    let rotation = super::super::frogdrop_col::rec(b, |b| {
        mc_xor(b, &zero, flag, &[], &bank);
        b.play(&shift, false);
        // 0<=view<=255; in fact97<=view<=255 for every five-bit code.
        // Sum of these literal rotations is rawSZ modulo cycle.len().
        rotate_controls(b, cycle, 1, &[], &bank);
        if let Some((lo, hi, dest)) = care {
            // UP first moves every original destination d to d+1. The
            // following partial UP must therefore preserve those sources:
            // d+1 -> d+1+(Z-1)=d+Z. The same record inverted restores all
            // other cycle cells after the supported body has returned.
            let support: std::collections::BTreeSet<_> =
                dest.iter().map(|&i| (i + 1) % cycle.len()).collect();
            super::super::frogdrop::rot_by_range_care(b, cycle, &view,
                lo - 1, hi - 1, false, &bank, &support);
        } else { super::super::frogdrop::rot_by(b, cycle, &view, false); }
        b.play(&shift, true);
        mc_xor(b, &zero, flag, &[], &bank);
    });
    b.play(&rotation, inverse);
}

fn rot_raw_impl(b: &mut B, cycle: &[QubitId], code: &[QubitId], sy: &[QubitId],
                inverse: bool, dirty: &[QubitId], flag: Option<QubitId>) {
    assert_eq!(code.len(), CODE_BITS);
    assert_eq!(sy.len(), 8);
    assert!(!cycle.is_empty());
    assert_eq!(cycle.iter().collect::<std::collections::BTreeSet<_>>().len(), cycle.len());
    assert!(!cycle.iter().any(|q| code.contains(q) || sy[..7].contains(q)));
    assert!(!code.iter().any(|q| sy[..7].contains(q)));
    let n = cycle.len();
    let rotation = super::super::frogdrop_col::rec(b, |b| {
        rotate_controls(b, cycle, BIAS, &[], dirty);
        super::super::frogdrop::rot_by(b, cycle, code, false);
        super::super::frogdrop::rot_by(b, cycle, &sy[..7], true);
        let zero: Vec<_> = sy[..7].iter().map(|&q| (q, true)).collect();
        if let Some(flag) = flag {
            let bank: Vec<_> = dirty.iter().copied()
                .filter(|q| *q != flag && !sy[..7].contains(q)).collect();
            mc_xor(b, &zero, flag, &[], &bank);
            rotate_controls(b, cycle, (n - 128 % n) % n, &[(flag, false)], &bank);
            mc_xor(b, &zero, flag, &[], &bank);
        } else {
            rotate_controls(b, cycle, (n - 128 % n) % n, &zero, dirty);
        }
    });
    b.play(&rotation, inverse);
}

fn code_controls(code: &[QubitId], value: usize) -> Vec<(QubitId, bool)> {
    assert_eq!(code.len(), CODE_BITS);
    code.iter().enumerate().map(|(i, &q)| (q, (value >> i) & 1 == 0)).collect()
}

fn returned_bank(code: &[QubitId], sy: &[QubitId], out: QubitId,
                 controls: &[(QubitId, bool)], dirty: &[QubitId]) -> Vec<QubitId> {
    assert_eq!(sy.len(), 8);
    assert!(!code.contains(&out) && !sy.contains(&out));
    assert!(!controls.iter().any(|&(q, _)| q == out));
    dirty.iter().copied().filter(|q| !code.contains(q) && !sy.contains(q) && *q != out
        && !controls.iter().any(|&(c, _)| c == *q)).collect()
}

/// out ^= controls & [raw SZ == value], without decoding the size frame.
/// The physical high SZ lanes are intentionally absent from every argument.
/// All 32 five-bit codes have the affine interpretation BIAS+code-SY.
pub(super) fn xor_raw_eq(b: &mut B, code: &[QubitId], sy: &[QubitId], value: usize,
                        out: QubitId, controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    let bank = returned_bank(code, sy, out, controls, dirty);
    for v in 0..1usize << CODE_BITS {
        let Some(y) = (BIAS + v).checked_sub(value) else { continue; };
        if !(1..=128).contains(&y) { continue; }
        let mut ctl = controls.to_vec();
        ctl.extend(code_controls(code, v));
        ctl.extend(sy[..7].iter().enumerate().map(|(i, &q)| (q, (y >> i) & 1 == 0)));
        mc_xor(b, &ctl, out, &[], &bank);
    }
}

/// out ^= controls & [raw SZ >= value]. For a fixed sum-code this is
/// SY <= BIAS+code-value. The disjoint binary prefix cover uses no flag,
/// prefix ancilla, measurement or borrowed high SZ owner.
pub(super) fn xor_raw_ge(b: &mut B, code: &[QubitId], sy: &[QubitId], value: usize,
                        out: QubitId, controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    let bank = returned_bank(code, sy, out, controls, dirty);
    for v in 0..1usize << CODE_BITS {
        let Some(bound) = (BIAS + v).checked_sub(value) else { continue; };
        let mut common = controls.to_vec();
        common.extend(code_controls(code, v));
        if bound >= 128 {
            mc_xor(b, &common, out, &[], &bank);
            continue;
        }
        if bound == 0 { continue; }
        xor_bits_lt(b, &sy[..7], bound + 1, out, &common, &bank);
        // Low-seven zero denotes 128, outside this nonempty interval.
        let mut zero = common;
        zero.extend(sy[..7].iter().map(|&q| (q, true)));
        mc_xor(b, &zero, out, &[], &bank);
    }
}

fn xor_bits_lt(b: &mut B, bits: &[QubitId], bound: usize, out: QubitId,
               controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    xor_bits_lt_clean(b, bits, bound, out, controls, &[], dirty);
}

fn xor_bits_lt_clean(b: &mut B, bits: &[QubitId], bound: usize, out: QubitId,
                     controls: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
    if bound == 0 { return; }
    if bound >= 1usize << bits.len() { mc_xor(b, controls, out, clean, dirty); return; }
    // Disjoint prefixes of [word < bound]. A supplied globally clean bank
    // is returned by the existing measured-AND ABI after every exact term.
    for bit in (0..bits.len()).rev() {
        if (bound >> bit) & 1 == 0 { continue; }
        let mut ctl = controls.to_vec();
        for i in bit + 1..bits.len() { ctl.push((bits[i], (bound >> i) & 1 == 0)); }
        ctl.push((bits[bit], true));
        mc_xor(b, &ctl, out, clean, dirty);
    }
}

/// out ^= controls & [code < bound], with no reads of the high SZ owners.
pub(super) fn xor_code_lt(b: &mut B, code: &[QubitId], bound: usize, out: QubitId,
                         controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    assert_eq!(code.len(), CODE_BITS);
    assert!(!code.contains(&out) && !controls.iter().any(|&(q, _)| q == out));
    let bank: Vec<_> = dirty.iter().copied().filter(|q| *q != out && !code.contains(q)
        && !controls.iter().any(|&(c, _)| c == *q)).collect();
    xor_bits_lt(b, code, bound, out, controls, &bank);
}

/// Exact five-bit query with globally clean, disjoint returned prefixes.
/// The caller must supply the same clean entry contract on inverse replay.
pub(super) fn xor_code_lt_clean(b: &mut B, code: &[QubitId], bound: usize, out: QubitId,
                               controls: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(code.len(), CODE_BITS);
    assert!(!code.contains(&out) && !controls.iter().any(|&(q, _)| q == out));
    assert_eq!(clean.iter().collect::<std::collections::BTreeSet<_>>().len(), clean.len());
    assert!(clean.iter().all(|q| *q != out && !code.contains(q)
        && !controls.iter().any(|&(c, _)| c == *q)));
    let bank: Vec<_> = dirty.iter().copied().filter(|q| *q != out && !code.contains(q)
        && !clean.contains(q) && !controls.iter().any(|&(c, _)| c == *q)).collect();
    xor_bits_lt_clean(b, code, bound, out, controls, clean, &bank);
}

/// out ^= controls & [raw SZ <= SY]. For a fixed code this is the exact
/// affine inequality SY >= ceil((BIAS+code)/2), without restoring raw SZ.
pub(super) fn xor_raw_le_sy(b: &mut B, code: &[QubitId], sy: &[QubitId], out: QubitId,
                           controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    xor_raw_cmp_sy(b, code, sy, out, controls, dirty, false);
}

/// The same query outside every n7/U frame, with raw SY in 1..=128.
/// `flag` and `one` are globally clean on entry and returned on exit.
/// This uses the original Cross::toggle_ht_w comparator owners, not a
/// conditional size prefix. The output may hold either value on entry.
pub(super) fn xor_raw_le_sy_clean(b: &mut B, code: &[QubitId], sy: &[QubitId],
    out: QubitId, controls: &[(QubitId, bool)], flag: QubitId, one: QubitId,
    dirty: &[QubitId]) {
    assert_eq!(BIAS, 226);
    assert_eq!(code.len(), CODE_BITS);
    assert_eq!(sy.len(), 8);
    let ports: Vec<_> = code.iter().chain(sy).copied().chain([out, flag, one]).collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    assert!(!controls.iter().any(|&(q, _)| ports.contains(&q)));
    let bank: Vec<_> = dirty.iter().copied().filter(|q| !ports.contains(q)
        && !controls.iter().any(|&(c, _)| c == *q)).collect();
    assert!(bank.len() >= 6, "affine size query requires returned dirty donors");
    // On 1..=128, Y>=113 is the disjoint union of Y=128 and
    // Y[6:4]=111 with Y[3:0]!=0. Return the held predicate after Y restores.
    let eligible = super::super::frogdrop_col::rec(b, |b| {
        let mut c = controls.to_vec();
        c.push((sy[7], false));
        mc_xor(b, &c, flag, &[], &bank);
        c = controls.to_vec();
        c.extend(sy[4..7].iter().map(|&q| (q, false)));
        mc_xor(b, &c, flag, &[], &bank);
        c.extend(sy[..4].iter().map(|&q| (q, true)));
        mc_xor(b, &c, flag, &[], &bank);
    });
    let shift = super::super::frogdrop_col::rec(b, |b|
        super::super::frogdrop::add_const_dirty_exact(b, &sy[..5], 15, &bank));
    b.play(&eligible, false);
    b.play(&shift, false);
    // With flag set, V=(Ylow+15) mod32=Y-113 lies in 0..15.
    // Z<=Y iff A=S-226 <= 2V. The carry of ~A+(2V+1) is that predicate.
    for &q in code { b.x(q); }
    b.x(one);
    let twice_plus_one: Vec<_> = std::iter::once(one).chain(sy[..4].iter().copied()).collect();
    super::super::arith::ttk_carry(b, code, &twice_plus_one, flag, out, bank[0]);
    b.x(one);
    for &q in code { b.x(q); }
    b.play(&shift, true);
    b.play(&eligible, true);
}

/// Strict raw Z<SY query outside every n7/U frame, with raw SY in 1..=128.
/// `flag` and `zero` are globally clean on entry and returned on exit.
/// The caller proves its two clean owners at a complete V boundary,
/// before/after all n7 and U records. The output may hold either value on entry.
pub(super) fn xor_raw_lt_sy_clean(b: &mut B, code: &[QubitId], sy: &[QubitId],
    out: QubitId, controls: &[(QubitId, bool)], flag: QubitId, zero: QubitId,
    dirty: &[QubitId]) {
    assert_eq!(BIAS, 226);
    assert_eq!(code.len(), CODE_BITS);
    assert_eq!(sy.len(), 8);
    let ports: Vec<_> = code.iter().chain(sy).copied().chain([out, flag, zero]).collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    assert!(!controls.iter().any(|&(q, _)| ports.contains(&q)));
    let bank: Vec<_> = dirty.iter().copied().filter(|q| !ports.contains(q)
        && !controls.iter().any(|&(c, _)| c == *q)).collect();
    assert!(bank.len() >= 6, "affine size query requires returned dirty donors");
    // On 1..=128, Y>=113 is the disjoint union of Y=128 and
    // Y[6:4]=111 with Y[3:0]!=0. Return the held predicate after Y restores.
    let eligible = super::super::frogdrop_col::rec(b, |b| {
        let mut c = controls.to_vec();
        c.push((sy[7], false));
        mc_xor(b, &c, flag, &[], &bank);
        c = controls.to_vec();
        c.extend(sy[4..7].iter().map(|&q| (q, false)));
        mc_xor(b, &c, flag, &[], &bank);
        c.extend(sy[..4].iter().map(|&q| (q, true)));
        mc_xor(b, &c, flag, &[], &bank);
    });
    let shift = super::super::frogdrop_col::rec(b, |b|
        super::super::frogdrop::add_const_dirty_exact(b, &sy[..5], 15, &bank));
    b.play(&eligible, false);
    b.play(&shift, false);
    // With flag set, V=(Ylow+15) mod32=Y-113 lies in 0..15.
    // Z<Y iff A=S-226 < 2V. The carry of ~A+2V is that predicate.
    for &q in code { b.x(q); }
    let twice: Vec<_> = std::iter::once(zero).chain(sy[..4].iter().copied()).collect();
    super::super::arith::ttk_carry(b, code, &twice, flag, out, bank[0]);
    for &q in code { b.x(q); }
    b.play(&shift, true);
    b.play(&eligible, true);
}

/// Strict version: Z<SY iff SY>=floor((BIAS+code)/2)+1.
pub(super) fn xor_raw_lt_sy(b: &mut B, code: &[QubitId], sy: &[QubitId], out: QubitId,
                           controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    xor_raw_cmp_sy(b, code, sy, out, controls, dirty, true);
}

fn xor_raw_cmp_sy(b: &mut B, code: &[QubitId], sy: &[QubitId], out: QubitId,
                  controls: &[(QubitId, bool)], dirty: &[QubitId], strict: bool) {
    let bank = returned_bank(code, sy, out, controls, dirty);
    for v in 0..1usize << CODE_BITS {
        let bound = if strict { (BIAS + v) / 2 + 1 } else { (BIAS + v + 1) / 2 };
        if bound > 128 { continue; }
        let mut common = controls.to_vec();
        common.extend(code_controls(code, v));
        if bound < 128 {
            mc_xor(b, &common, out, &[], &bank);
            xor_bits_lt(b, &sy[..7], bound, out, &common, &bank);
        }
        // The low-seven zero code is the separately included SY=128.
        common.extend(sy[..7].iter().map(|&q| (q, true)));
        mc_xor(b, &common, out, &[], &bank);
    }
}

/// out ^= controls & [raw SZ + SY == value]. Used by the N257 stage-5
/// leading-bit handoff while the flight lane is a borrowed high SZ owner.
pub(super) fn xor_sum_eq(b: &mut B, code: &[QubitId], value: usize,
                        out: QubitId, controls: &[(QubitId, bool)], dirty: &[QubitId]) {
    assert!(!code.contains(&out) && !controls.iter().any(|&(q, _)| q == out));
    let Some(v) = value.checked_sub(BIAS) else { return; };
    if v >= 1 << CODE_BITS { return; }
    let mut ctl = controls.to_vec();
    ctl.extend(code_controls(code, v));
    let bank: Vec<_> = dirty.iter().copied()
        .filter(|q| *q != out && !ctl.iter().any(|&(c, _)| c == *q)).collect();
    mc_xor(b, &ctl, out, &[], &bank);
}
