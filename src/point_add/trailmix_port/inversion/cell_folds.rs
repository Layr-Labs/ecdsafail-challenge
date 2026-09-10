//! Exact bounded carry cleanup inside the signed-add-and-halve cell.
use super::{env_usize, Circuit, QReg, QubitId};

#[path = "cell_folds_selftest.rs"]
pub(crate) mod selftest;

#[path = "all_const_folds_selftest.rs"]
pub(crate) mod all_const_selftest;

#[path = "../../clean_chunk_plan.rs"]
mod clean_chunk_plan;

#[path = "cell_recursive_carries.rs"]
mod recursive;

#[path = "fused_rotation_cell.rs"]
mod fused_rotation;

struct Boundary { wire: QReg, start: usize, end: usize }

enum Addend<'a> { Constant(&'a QReg, &'a [u8]), Word(&'a [QReg]) }
impl<'a> Addend<'a> {
    fn bit(&self, i: usize) -> (&QReg, bool) {
        match self {
            Self::Constant(ctrl, bytes) => (ctrl, cbit(bytes, i)),
            Self::Word(source) => (&source[i], true),
        }
    }
}

fn cbit(value: &[u8], i: usize) -> bool {
    value.get(i / 8).map_or(false, |v| (v >> (i % 8)) & 1 != 0)
}

fn scratch(n: usize, k: usize) -> usize {
    if n <= 1 { return 0; }
    let count = n - 1;
    let boundaries = count.div_ceil(k) - 1;
    if boundaries == 0 { count }
    else { (k + boundaries - 1).max(count - k * boundaries + boundaries) }
}

fn choose(c: &mut Circuit, n: usize) -> Option<Vec<usize>> {
    c.flush_pending_frees();
    let cap = env_usize("MIDQ_CELL_QCAP", 1009).min(1019);
    let available = cap.saturating_sub(c.b.active_qubits as usize);
    clean_chunk_plan::plan(n - 1, available)
}

// MAJ(a, control*constant, carry) into clean out. Inputs are restored.
fn majority(c: &mut Circuit, a: &QReg, ctrl: &QReg, bit: bool,
    carry: Option<&QReg>, out: &QReg, complement: bool) {
    if complement { c.x(a); }
    if let Some(carry) = carry {
        if bit {
            c.cx(carry, a);
            c.cx(ctrl, carry);
            c.ccx(a, carry, out);
            c.cx(ctrl, carry);
            c.cx(carry, a);
            c.cx(carry, out);
        } else { c.ccx(a, carry, out); }
    } else if bit { c.ccx(a, ctrl, out); }
    if complement { c.x(a); }
}

fn phase_majority(c: &mut Circuit, a: &QReg, ctrl: &QReg, bit: bool,
    carry: Option<&QReg>) {
    c.x(a);
    if bit { c.cz(a, ctrl); }
    if let Some(carry) = carry {
        c.cz(a, carry);
        if bit { c.cz(ctrl, carry); }
    }
    c.x(a);
}

fn clear(c: &mut Circuit, out: &QReg, a: &QReg, ctrl: &QReg, bit: bool,
    carry: Option<&QReg>) {
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.with_condition(m, |c| phase_majority(c, a, ctrl, bit, carry));
    c.free_bit(m);
}

// On all n-bit words, a <- a + ctrl*constant modulo 2^n. No range promise.
fn add(c: &mut Circuit, a: &[QReg], ctrl: &QReg, constant: &[u8], k: usize) {
    emit(c, a, Addend::Constant(ctrl, constant), None, k);
}

fn emit(c: &mut Circuit, a: &[QReg], addend: Addend<'_>, overflow: Option<&QReg>, k: usize) {
    assert!(k > 0);
    let count = a.len().saturating_sub(usize::from(overflow.is_none()));
    let chunks: Vec<_> = (0..count).step_by(k).map(|i| k.min(count - i)).collect();
    emit_plan(c, a, addend, overflow, &chunks);
}

fn emit_plan(c: &mut Circuit, a: &[QReg], addend: Addend<'_>, overflow: Option<&QReg>, chunks: &[usize]) {
    let n = a.len();
    if n == 0 { return; }
    let count = n - usize::from(overflow.is_none());
    assert_eq!(chunks.iter().sum::<usize>(), count);
    let section = c.push_section("midq.cell.const");
    let mut boundaries: Vec<Boundary> = Vec::new();
    let mut start = 0;
    for &k in chunks {
        assert!(k > 0);
        let end = start + k;
        let initial = boundaries.last().map(|b| &b.wire);
        let mut chain: Vec<QReg> = Vec::new();
        for i in start..end {
            let (ctrl, bit) = addend.bit(i);
            let next = c.alloc_qreg("cell.carry");
            let previous = chain.last().or(initial);
            majority(c, &a[i], ctrl, bit, previous, &next, false);
            if let Some(previous) = previous { c.cx(previous, &a[i]); }
            if bit { c.cx(ctrl, &a[i]); }
            chain.push(next);
        }
        let keep = end < count;
        if !keep {
            if let Some(out) = overflow { c.cx(chain.last().unwrap(), out); }
            else {
                c.cx(chain.last().unwrap(), &a[n - 1]);
                let (ctrl, bit) = addend.bit(n - 1);
                if bit { c.cx(ctrl, &a[n - 1]); }
            }
        }
        for j in (0..chain.len() - usize::from(keep)).rev() {
            let (ctrl, bit) = addend.bit(start + j);
            let previous = if j == 0 { initial } else { Some(&chain[j - 1]) };
            clear(c, &chain[j], &a[start + j], ctrl, bit, previous);
        }
        let kept = keep.then(|| chain.pop().unwrap());
        for q in chain { c.zero_and_free(q); }
        if let Some(wire) = kept { boundaries.push(Boundary { wire, start, end }); }
        start = end;
    }
    if count == 0 {
        let (ctrl, bit) = addend.bit(0);
        if bit { c.cx(ctrl, &a[0]); }
    }
    // Updated sum bits determine the same carries through MAJ(~sum,k,carry).
    while let Some(boundary) = boundaries.pop() {
        let initial = boundaries.last().map(|b| &b.wire);
        let m = c.alloc_bit();
        c.hmr(&boundary.wire, m);
        c.with_condition(m, |c| {
            let mut chain: Vec<QReg> = Vec::new();
            for i in boundary.start..boundary.end - 1 {
                let (ctrl, bit) = addend.bit(i);
                let next = c.alloc_qreg("cell.phase.carry");
                majority(c, &a[i], ctrl, bit, chain.last().or(initial), &next, true);
                chain.push(next);
            }
            let (ctrl, bit) = addend.bit(boundary.end - 1);
            phase_majority(c, &a[boundary.end - 1], ctrl, bit, chain.last().or(initial));
            for j in (0..chain.len()).rev() {
                let (ctrl, bit) = addend.bit(boundary.start + j);
                let previous = if j == 0 { initial } else { Some(&chain[j - 1]) };
                clear(c, &chain[j], &a[boundary.start + j], ctrl, bit, previous);
            }
            for q in chain { c.zero_and_free(q); }
        });
        c.free_bit(m);
        c.zero_and_free(boundary.wire);
    }
    c.pop_section(&section);
}

/// Exact target +=/-= ctrl*constant modulo its existing word size. No donor
/// is touched. Return false before emitting arithmetic if the cap cannot fit.
pub(crate) fn try_constant_update(c: &mut Circuit, ctrl: &QReg, target: &[QReg],
    constant: &[u8], subtract: bool) -> bool {
    if target.is_empty() { return true; }
    if target.iter().any(|q| q.id() == ctrl.id()) { return false; }
    let chunks = choose(c, target.len());
    if recursive::try_prefer(c, target, Addend::Constant(ctrl, constant), None, subtract, chunks.as_deref()) {
        return true;
    }
    let Some(chunks) = chunks else {
        return recursive::try_add(c, target, Addend::Constant(ctrl, constant), None, subtract);
    };
    if subtract { for q in target { c.x(q); } }
    emit_plan(c, target, Addend::Constant(ctrl, constant), None, &chunks);
    if subtract { for q in target { c.x(q); } }
    true
}

fn fold(c: &mut Circuit, target: &[QReg], source: &[QReg], ctrl: &QReg, subtract: bool) {
    if !try_constant_update(c, ctrl, &target[..256], &[0xd1, 3, 0, 0, 1], subtract) {
        super::midq_const_fold(c, target, source, ctrl, subtract);
    }
}

fn add_raw_with_overflow(c: &mut Circuit, target: &[QReg], source: &[QReg], overflow: &QReg) {
    use crate::point_add::trailmix_port::arith::cuccaro::add_cuccaro_with_separate_overflow;
    let sum_enabled = std::env::var("MIDQ_CELL_SUM").ok().as_deref() != Some("0");
    let chunks = choose(c, 257).filter(|_| sum_enabled);
    let preferred = sum_enabled && recursive::try_prefer(c, &target[..256],
        Addend::Word(&source[..256]), Some(overflow), false, chunks.as_deref());
    if !preferred {
        if let Some(chunks) = chunks {
            emit_plan(c, &target[..256], Addend::Word(&source[..256]), Some(overflow), &chunks);
        } else if !sum_enabled
            || !recursive::try_add(c, &target[..256], Addend::Word(&source[..256]), Some(overflow), false)
        { add_cuccaro_with_separate_overflow(c, &target[..256], &source[..256], overflow); }
    }
}

// Configuration eligibility only; exact input membership in the coefficient-
// margin support remains required. No forward-fused flag is needed for the
// inverse doubled-coefficient theorem.
fn inverse_top_compare_eligible() -> bool {
    std::env::var("MIDQ_TAIL_INVERSE_TOP_COMPARE").ok().as_deref() == Some("1")
        && std::env::var("MIDQ_MEASURE_COMPARE").ok().as_deref() == Some("1")
        && super::midq_rotated_halves()
        && super::midq_tail_enabled()
        && super::MIDQ_PZ_CUT == 360
        && super::MIDQ_TAIL_ROUNDS == 224
        && super::MIDQ_TAIL_VALUE_WIDTH.iter().all(|&w| w <= 85)
        && super::trailmix_srot_width() <= 5
}

fn clear_signed_add_overflow(c: &mut Circuit, target: &[QReg], source: &[QReg],
    overflow: &QReg, inverse_context: bool) {
    let low = if inverse_context && inverse_top_compare_eligible() { 136 } else { 0 };
    let section = (low != 0).then(|| c.push_section("midq.cell.inverse.top120_compare"));
    // This frame is UNROTATED: target[136..256], not the forward fused
    // oracle's physical target[135..255] slice.
    super::clear_borrow_compare_refs(c, &target[low..256].iter().collect::<Vec<_>>(),
        &source[low..256].iter().collect::<Vec<_>>(), overflow);
    if let Some(section) = section { c.pop_section(&section); }
}

fn signed_add(c: &mut Circuit, target: &[QReg], source: &[QReg], sign: &QReg) {
    signed_add_context(c, target, source, sign, false);
}

fn signed_add_context(c: &mut Circuit, target: &[QReg], source: &[QReg], sign: &QReg,
    inverse_context: bool) {
    assert!(matches!(target.len(), 256 | 257));
    let temporary = (target.len() == 256).then(|| c.alloc_qreg("midq.cell.overflow"));
    let overflow = temporary.as_ref().unwrap_or_else(|| &target[256]);
    for q in &target[..256] { c.cx(sign, q); }
    add_raw_with_overflow(c, target, source, overflow);
    fold(c, target, source, overflow, false);
    clear_signed_add_overflow(c, target, source, overflow, inverse_context);
    for q in &target[..256] { c.cx(sign, q); }
    if let Some(overflow) = temporary { c.zero_and_free(overflow); }
}

pub(super) fn apply(c: &mut Circuit, target: &[QReg], source: &[QReg], sign: &QReg, inverse: bool) {
    if !inverse && fused_rotation::try_apply(c, target, source, sign) { return; }
    if inverse {
        if super::midq_rotated_halves() {
            super::midq_rotated_double(c, target, source);
            c.x(sign);
            signed_add_context(c, target, source, sign, true);
            c.x(sign);
            return;
        }
        let overflow = c.alloc_qreg("midq.fast_double.overflow");
        c.b.swap(QubitId(target[255].id().into()), QubitId(overflow.id().into()));
        for i in (0..255).rev() {
            c.b.swap(QubitId(target[i].id().into()), QubitId(target[i + 1].id().into()));
        }
        fold(c, target, source, &overflow, false);
        c.cx(&target[0], &overflow);
        c.zero_and_free(overflow);
        c.x(sign);
        signed_add_context(c, target, source, sign, true);
        c.x(sign);
    } else {
        signed_add(c, target, source, sign);
        if super::midq_rotated_halves() { return super::midq_rotated_halve(c, target, source); }
        let parity = c.alloc_qreg("midq.fast_halve.parity");
        c.cx(&target[0], &parity);
        fold(c, target, source, &parity, true);
        for i in 0..255 {
            c.b.swap(QubitId(target[i].id().into()), QubitId(target[i + 1].id().into()));
        }
        c.cx(&parity, &target[255]);
        c.cx(&target[255], &parity);
        c.zero_and_free(parity);
    }
}

#[path = "inverse_top_compare_selftest.rs"]
mod inverse_top_checks;
