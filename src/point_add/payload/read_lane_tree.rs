//! Pruned reversible read tree. This module allocates no quantum wire and
//! makes no decision from a quantum value: only the public wire map is read.

use super::{B, Mask, QubitId};
use crate::point_add::builder::G;
use std::collections::BTreeSet;

// All used clean prefix cells already belong to Dec's original zero ABI.
// Unused pre cells are not silently reclassified as fresh.
fn geometry(reg: &[QubitId], leaves: &[(usize, QubitId)], extra: &[(QubitId, bool)],
            target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> bool {
    if reg.is_empty() || reg.len() >= usize::BITS as usize || leaves.is_empty() { return false; }
    let h = pre.len().min(reg.len() - 1);
    let old_literals = reg.len() - h + 1 + extra.len();
    let used_temps = temps.len().min(old_literals.saturating_sub(2));
    let mut occupied = BTreeSet::new();
    for q in reg.iter().chain(leaves.iter().map(|(_, q)| q))
        .chain(extra.iter().map(|(q, _)| q)).chain(std::iter::once(&target))
        .chain(pre[..h].iter()).chain(temps[..used_temps].iter()) {
        if !occupied.insert(q.0) { return false; }
    }
    let protected: BTreeSet<_> = reg.iter().chain(extra.iter().map(|(q, _)| q))
        .chain(std::iter::once(&target)).chain(pre[..h].iter()).chain(temps[..used_temps].iter()).map(|q| q.0).collect();
    let source: BTreeSet<_> = leaves.iter().map(|(_, q)| q.0).collect();
    let mut donors = BTreeSet::new();
    for q in dirty {
        if protected.contains(&q.0) || !donors.insert(q.0) { return false; }
    }
    // Old mc_xor filters its donor bank only in the known-prefix path.
    // With >=3 literals and no clean temp it calls mcx_dirty directly. Do
    // not change that unfiltered legacy alias/error behavior here.
    if old_literals > 2 && used_temps == 0 && donors.iter().any(|q| source.contains(q)) { return false; }
    // Enough even if the final prefix predicate uses no clean AND cells.
    // This upper bound also covers the existing known-prefix implementation.
    let available = dirty.iter().filter(|q| **q != leaves[0].1).count();
    if available < reg.len() + extra.len() { return false; }
    leaves.windows(2).all(|w| w[0].0 < w[1].0) && leaves.last().unwrap().0 < (1usize << reg.len())
}

// Postorder: complete both lower-bit subtrees before their parent swap. A
// unary node performs no gate; it forwards the nonempty child's representative.
fn collect_tree(reg: &[QubitId], leaves: &[(usize, QubitId)], level: usize,
                swaps: &mut Vec<(QubitId, QubitId, QubitId)>) -> QubitId {
    assert!(!leaves.is_empty());
    if level == 0 { assert_eq!(leaves.len(), 1); return leaves[0].1; }
    let bit = level - 1;
    let split = leaves.partition_point(|&(v, _)| (v >> bit) & 1 == 0);
    if split == 0 { return collect_tree(reg, leaves, bit, swaps); }
    if split == leaves.len() { return collect_tree(reg, leaves, bit, swaps); }
    let left = collect_tree(reg, &leaves[..split], bit, swaps);
    let right = collect_tree(reg, &leaves[split..], bit, swaps);
    swaps.push((reg[bit], left, right));
    left
}

pub(super) fn tree_record(b: &mut B, reg: &[QubitId], leaves: &[(usize, QubitId)], neg: bool,
                         extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId],
                         temps: &[QubitId], dirty: &[QubitId]) -> Option<Vec<G>> {
    if !geometry(reg, leaves, extra, target, pre, temps, dirty) { return None; }
    let mut swaps = Vec::with_capacity(leaves.len() - 1);
    let root = collect_tree(reg, leaves, reg.len(), &mut swaps);
    assert_eq!(swaps.len(), leaves.len() - 1);
    assert_eq!(root, leaves[0].1);
    // Other permuted source cells may be arbitrary-state dirty donors. They
    // are restored at the tree epoch before its literal inverse. The fixed
    // root is a query control, so explicitly exclude it even with zero temps.
    let donors: Vec<_> = dirty.iter().copied().filter(|q| *q != root).collect();
    let h = pre.len().min(reg.len() - 1);
    let old_literals = reg.len() - h + 1 + extra.len();
    let used_temps = temps.len().min(old_literals.saturating_sub(2));
    let mut clean = pre[..h].to_vec();
    clean.extend_from_slice(&temps[..used_temps]);
    let mut base = extra.to_vec();
    base.push((root, neg));
    let mask = Mask::new(reg, (1usize << reg.len()) - 1, true, base, target, &clean, &donors);
    b.begin();
    for &(control, left, right) in &swaps { b.cswap(control, left, right); }
    // Cover precisely the defined codes. Holes and out-of-range codes are
    // excluded even though an invalid address can select an arbitrary root.
    let mut first = 0;
    while first < leaves.len() {
        let mut last = first;
        while last + 1 < leaves.len() && leaves[last + 1].0 == leaves[last].0 + 1 { last += 1; }
        mask.toggle_range(b, leaves[first].0, leaves[last].0);
        first = last + 1;
    }
    // Literal reverse order, with the same original register controls.
    for &(control, left, right) in swaps.iter().rev() { b.cswap(control, left, right); }
    Some(b.end())
}

/// Exact Toffoli prices of this local IR in both directions. Existing emit()
/// charges Ccx and AndC, and literal inversion exchanges AndC with AndU.
/// No RowAdd, deferred box, classical decision or allocation is admissible here.
pub(super) fn prices(record: &[G]) -> Option<(u64, u64)> {
    let mut forward = 0;
    let mut inverse = 0;
    for gate in record {
        match gate {
            G::Ccx(..) => { forward += 1; inverse += 1; }
            G::AndC(..) => forward += 1,
            G::AndU(..) => inverse += 1,
            G::X(..) | G::Cx(..) => (),
            _ => return None,
        }
    }
    Some((forward, inverse))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn choose_record(b: &mut B, reg: &[QubitId], leaves: &[(usize, QubitId)], neg: bool,
                           extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId],
                           temps: &[QubitId], dirty: &[QubitId], reference: Vec<G>) -> Vec<G> {
    if let Some(tree) = tree_record(b, reg, leaves, neg, extra, target, pre, temps, dirty) {
        if let (Some((old_f, old_i)), Some((new_f, new_i))) = (prices(&reference), prices(&tree)) {
            if new_f <= old_f && new_i <= old_i && (new_f < old_f || new_i < old_i) { return tree; }
        }
    }
    reference
}
