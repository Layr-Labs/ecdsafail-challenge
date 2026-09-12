//! Exact four-offset numerical map with a support-qualified rotation phase oracle.
//!
//! The number map matches the old finite-word forward cell. Replacing its old
//! overflow phase predicate by the rotation comparison is proved only on the
//! exact-transition coefficient-margin support documented in memory. This is
//! not an all-bit-pattern phase-channel equivalence claim.
use super::*;

struct Selected<'a> {
    controls: [&'a QReg; 3], // negative selector, product selector, their AND
    constants: [i64; 3],
}

impl Selected<'_> {
    fn with_bit(
        &self,
        c: &mut Circuit,
        index: usize,
        body: impl FnOnce(&mut Circuit, &QReg, bool),
    ) {
        let mask: Vec<_> = self
            .constants
            .iter()
            .enumerate()
            .filter_map(|(i, &value)| {
                let bit = if index < 64 {
                    (value as u64 >> index) & 1 != 0
                } else {
                    value < 0
                };
                bit.then_some(i)
            })
            .collect();
        let Some((&pivot, rest)) = mask.split_first() else {
            return body(c, self.controls[0], false);
        };
        for &other in rest {
            c.cx(self.controls[other], self.controls[pivot]);
        }
        body(c, self.controls[pivot], true);
        for &other in rest.iter().rev() {
            c.cx(self.controls[other], self.controls[pivot]);
        }
    }
}

#[derive(Clone, Copy)]
enum Action<'a> {
    Add(Option<&'a QReg>),
    Carry(&'a QReg),
    Phase,
}

fn split(n: usize, available: usize) -> Option<usize> {
    if n - 1 <= available {
        return None;
    }
    assert!(available > 0 && recursive::cost(n, available, false).is_finite());
    (1..n).min_by(|&a, &b| {
        let price = |k| {
            recursive::cost(k, available - 1, false)
                + 1.0
                + recursive::cost(n - k, available - 1, false)
                + 0.5 * recursive::cost(k, available, false)
        };
        price(a)
            .partial_cmp(&price(b))
            .expect("finite or infinite carry price")
    })
}

fn emit(
    c: &mut Circuit,
    target: &[QReg],
    selected: &Selected<'_>,
    start: usize,
    incoming: Option<&QReg>,
    action: Action<'_>,
    available: usize,
) {
    let n = target.len();
    assert!(n > 0);
    if let Some(k) = split(n, available) {
        let boundary = c.alloc_qreg("fused.offset.boundary");
        let low = match action {
            Action::Add(_) => Action::Add(Some(&boundary)),
            _ => Action::Carry(&boundary),
        };
        emit(
            c,
            &target[..k],
            selected,
            start,
            incoming,
            low,
            available - 1,
        );
        emit(
            c,
            &target[k..],
            selected,
            start + k,
            Some(&boundary),
            action,
            available - 1,
        );
        let phase = c.alloc_bit();
        c.hmr(&boundary, phase);
        c.zero_and_free(boundary);
        c.with_condition(phase, |c| {
            emit(
                c,
                &target[..k],
                selected,
                start,
                incoming,
                Action::Phase,
                available,
            );
        });
        c.free_bit(phase);
        return;
    }
    let adding = matches!(action, Action::Add(_));
    let mut chain: Vec<QReg> = Vec::new();
    for i in 0..n - 1 {
        let previous = chain.last().or(incoming);
        let next = c.alloc_qreg("fused.offset.carry");
        selected.with_bit(c, start + i, |c, control, bit| {
            majority(c, &target[i], control, bit, previous, &next, !adding);
            if adding {
                if let Some(previous) = previous {
                    c.cx(previous, &target[i]);
                }
                if bit {
                    c.cx(control, &target[i]);
                }
            }
        });
        chain.push(next);
    }
    let previous = chain.last().or(incoming);
    selected.with_bit(c, start + n - 1, |c, control, bit| match action {
        Action::Add(out) => {
            if let Some(out) = out {
                majority(c, &target[n - 1], control, bit, previous, out, false);
            }
            if let Some(previous) = previous {
                c.cx(previous, &target[n - 1]);
            }
            if bit {
                c.cx(control, &target[n - 1]);
            }
        }
        Action::Carry(out) => majority(c, &target[n - 1], control, bit, previous, out, true),
        Action::Phase => phase_majority(c, &target[n - 1], control, bit, previous),
    });
    while let Some(q) = chain.pop() {
        let i = chain.len();
        selected.with_bit(c, start + i, |c, control, bit| {
            clear(c, &q, &target[i], control, bit, chain.last().or(incoming));
        });
        c.zero_and_free(q);
    }
}

fn add_selected(
    c: &mut Circuit,
    target: &[QReg],
    raw_parity: &QReg,
    overflow: &QReg,
    sign: &QReg,
    gap: i64,
    available: usize,
) {
    assert!(gap > 0 && gap & 1 == 1);
    let k = (gap - 1) / 2;
    let product = c.alloc_qreg("fused.offset.product");
    let negative = c.alloc_qreg("fused.offset.negative");
    let joint = c.alloc_qreg("fused.offset.joint");
    c.ccx(overflow, raw_parity, &product);
    c.cx(raw_parity, &negative);
    c.cx(sign, &negative);
    c.cx(&product, &negative);
    c.ccx(&negative, &product, &joint);
    let selected = Selected {
        controls: [&negative, &product, &joint],
        constants: [-k, k + 1, (-k) ^ (k + 1) ^ (-gap)],
    };
    emit(c, target, &selected, 0, None, Action::Add(None), available);
    // All affine basis changes of the selectors have been restored. The
    // original product inputs are still unchanged at both measured erasures.
    c.clear_and(&joint, &negative, &product);
    c.zero_and_free(joint);
    c.cx(&product, &negative);
    c.cx(sign, &negative);
    c.cx(raw_parity, &negative);
    c.zero_and_free(negative);
    c.clear_and(&product, overflow, raw_parity);
    c.zero_and_free(product);
}

// This is a construction-time configuration guard, not a numeric membership
// test. Positivity, canonical state, exact width/metadata transitions and the
// >2^137 coefficient margin remain the explicitly certified input support.
fn top_compare_eligible() -> bool {
    super::super::hybrid_profile::legacy_margin_allowed()
        && std::env::var("MIDQ_TAIL_TOP_COMPARE").ok().as_deref() == Some("1")
        && std::env::var("MIDQ_FUSED_ROTATION_CELL").ok().as_deref() == Some("1")
        && std::env::var("MIDQ_MEASURE_COMPARE").ok().as_deref() == Some("1")
        && super::super::midq_rotated_halves()
        && super::super::midq_tail_enabled()
        && super::super::MIDQ_PZ_CUT == 360
        && super::super::MIDQ_TAIL_ROUNDS == 224
        && super::super::MIDQ_TAIL_VALUE_WIDTH.iter().all(|&w| w <= 85)
        && super::super::trailmix_srot_width() <= 5
}

fn top_compare_low_bits() -> usize {
    if top_compare_eligible() { return 136; }
    if super::super::hybrid_profile::legacy_margin_allowed()
        || std::env::var("MIDQ_TAIL_TOP_COMPARE").ok().as_deref() != Some("1")
        || std::env::var("MIDQ_FUSED_ROTATION_CELL").ok().as_deref() != Some("1")
        || std::env::var("MIDQ_MEASURE_COMPARE").ok().as_deref() != Some("1")
        || !super::super::midq_rotated_halves() || !super::super::midq_tail_enabled()
    { return 0; }
    super::super::hybrid_margin::forward_drop()
}

fn clear_rotated_overflow(c: &mut Circuit, target: &[QReg], source: &[QReg], overflow: &QReg) {
    let rotated: Vec<_> = std::iter::once(&target[255])
        .chain(&target[..255])
        .collect();
    let rhs: Vec<_> = source[..256].iter().collect();
    // The logical comparator positions are rotated. Dropping its low136 bits
    // leaves physical target[135..255] against source[136..256]. Do NOT slice
    // the unrotated target at136, and do not apply this to inverse signed_add.
    let low = top_compare_low_bits();
    let section = (low != 0).then(|| c.push_section(if super::super::hybrid_profile::legacy_margin_allowed() {"midq.cell.fused_rotation.top120_compare"} else {"midq.cell.fused_rotation.parametric_compare"}));
    super::super::clear_borrow_compare_refs(c, &rotated[low..], &rhs[low..], overflow);
    if let Some(section) = section {
        c.pop_section(&section);
    }
}

pub(super) fn try_apply(c: &mut Circuit, target: &[QReg], source: &[QReg], sign: &QReg) -> bool {
    if (!super::super::hybrid_profile::legacy_margin_allowed()
        && !super::super::hybrid_margin::full_fused_allowed())
        || std::env::var("MIDQ_FUSED_ROTATION_CELL").ok().as_deref() != Some("1")
        || std::env::var("MIDQ_MEASURE_COMPARE").ok().as_deref() != Some("1")
        || !super::super::midq_rotated_halves()
    {
        return false;
    }
    if !matches!(target.len(), 256 | 257) || source.len() < 256 {
        return false;
    }
    let mut ids = std::collections::HashSet::new();
    if target
        .iter()
        .chain(&source[..256])
        .chain([sign])
        .any(|q| !ids.insert(q.id()))
    {
        return false;
    }
    c.flush_pending_frees();
    let cap = env_usize("MIDQ_CELL_QCAP", 1009).min(super::super::hybrid_profile::hard_ceiling());
    let reserve = 3 + usize::from(target.len() == 256);
    let available = cap.saturating_sub(c.b.active_qubits as usize + reserve);
    if !recursive::cost(255, available, false).is_finite() {
        return false;
    }
    let section = c.push_section("midq.cell.fused_rotation");
    let temporary = (target.len() == 256).then(|| c.alloc_qreg("midq.cell.overflow"));
    let overflow = temporary.as_ref().unwrap_or_else(|| &target[256]);
    for q in &target[..256] {
        c.cx(sign, q);
    }
    add_raw_with_overflow(c, target, source, overflow);
    for i in 0..255 {
        c.b.swap(
            QubitId(target[i].id().into()),
            QubitId(target[i + 1].id().into()),
        );
    }
    for q in &target[..255] {
        c.cx(sign, q);
    }
    add_selected(
        c,
        &target[..255],
        &target[255],
        overflow,
        sign,
        0x1000003d1,
        available,
    );
    c.cx(overflow, &target[255]);
    c.cx(sign, &target[255]);

    // rotl1(output), with the old complemented subtraction frame. On the
    // certified margin support, deleting D's <=F-1 correction cannot change
    // this comparison. Numerical outputs are exact even outside that support;
    // the overflow phase channel is intentionally only support-qualified.
    for q in &target[..256] {
        c.cx(sign, q);
    }
    clear_rotated_overflow(c, target, source, overflow);
    for q in &target[..256] {
        c.cx(sign, q);
    }
    if let Some(overflow) = temporary {
        c.zero_and_free(overflow);
    }
    c.pop_section(&section);
    true
}

#[path = "fused_rotation_cell_selftest.rs"]
mod checks;
pub(super) fn selftest() {
    checks::run();
}

pub(super) fn top_compare_selftest() {
    checks::run_top_compare();
}

pub(super) fn parametric_margin_selftest() { checks::run_parametric_margin(); }
