//! Payload ripples with a logical, queried source boundary.
//!
//! The encoded size is not read during the MAJ pass. A query is made only
//! after the current cell has been restored. The caller's size reader must
//! then see its original metadata. In particular, a Q source may contain
//! the five encoded low-size lanes at physical source indices 123..127:
//! high-size queries use the disjoint high tag, while low/medium queries
//! occur after all five of those source cells have been restored.
//!
//! On enabled shots, `size` is in `lo..=hi`, the logical source ends just
//! below `size`, and its boundary bit is zero. The *physical* source cell
//! at and above that boundary may contain arbitrary parked data. Division
//! requires d < 2^(k+1) r at the current restoring-division step. Addition
//! is used only by the digit inverse: negative W gives d<r and e=0; for
//! positive W the accumulated lower digits give W < 2^(size+k+1). These
//! caller bounds make every omitted higher write an identity and preserve
//! the parked quotient. This is not a general truncated-add interface.
//!
//! `mask` enters and leaves zero. Division also requires zero `tmp`; the
//! inverse add/compare never change tmp themselves, so their reader may
//! instead retain its class predicate there for the complete kernel. Such
//! a callback must not treat the held value as a globally-clean prefix.
//! For division e enters zero; for
//! addition e is held. In either writing kernel e=1 implies the size range.
//! `carry` need not be globally clean: the caller supplies its arithmetic
//! value on enabled shots, and the disabled action restores arbitrary
//! carry/source/target data. Capturing and reversing the complete record
//! supplies the inverse contract; it does not require e=0 at inverse entry.

use super::{B, QubitId, mc_xor};
use std::collections::BTreeSet;

/// XOR `[size == value] & extra` into target, restoring all other ports.
/// A true polarity bit in `extra` denotes a negative control, as in mc_xor.
/// The reader must also exclude its metadata from the supplied donor bank.
/// Equalities for distinct values must be disjoint on its complete encoded
/// domain, including padding holes. Production Sizes::{Y,Z} satisfy this:
/// their numeric equality intervals and modulo32 residue classes do not
/// overlap. Metadata read by a returned query may not be changed by the
/// local target writes below; the normalized reader excludes P258/H5.
pub(super) type SizeQuery<'a> = dyn FnMut(
    &mut B, usize, QubitId, &[(QubitId, bool)], &[QubitId], &[QubitId],
) + 'a;

fn donors(t: &[QubitId], s: &[QubitId], roles: &[QubitId], lo: usize, hi: usize,
          dirty: &[QubitId]) -> Vec<QubitId> {
    assert!(!t.is_empty() && !s.is_empty());
    assert!(s.len() == t.len() || s.len() + 1 == t.len(),
        "only the final source lane may be an absent virtual zero");
    assert!(1 <= lo && lo <= hi && hi < t.len());
    let mut used = BTreeSet::new();
    assert!(t.iter().chain(s).chain(roles).all(|q| used.insert(q.0)),
        "joint payload operands and roles must be pairwise disjoint");
    let mut seen = BTreeSet::new();
    dirty.iter().copied()
        .filter(|q| !used.contains(&q.0) && seen.insert(q.0)).collect()
}

fn up(b: &mut B, t: &[QubitId], s: &[QubitId], carry: QubitId) {
    for i in 0..s.len() {
        let x = if i == 0 { carry } else { s[i-1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
}

/// Restore this physical cell before consulting the encoded size. The
/// returned x holds the carry *into* cell i, including an absent last cell.
fn undo_cell(b: &mut B, t: &[QubitId], s: &[QubitId], carry: QubitId,
             i: usize) -> QubitId {
    let x = if i == 0 { carry } else { s[i-1] };
    if i < s.len() {
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
    }
    x
}

fn lower_write(b: &mut B, t: &[QubitId], s: &[QubitId], x: QubitId,
               mask: QubitId, i: usize, hi: usize) {
    // Above the public maximum boundary the strict mask is identically
    // zero. An absent final source cell is never below a valid boundary.
    if i < hi {
        assert!(i < s.len());
        b.cx(s[i], x);
        b.ccx(mask, x, t[i]);
        b.cx(s[i], x);
    }
}

/// Decide one restoring quotient bit and subtract the logical source.
/// At boundary i, virtual s[i]=0 gives carry_(i+1)=t[i]&carry_i for the
/// complemented target. Hence the two e toggles select `enable & !carry`.
/// Keep the complete equality on tmp through the local boundary writes.
/// After lower_write, its mask toggle prepares the next lower cell. This
/// moves the old i+1 query across only undo_cell (which ignores mask) and
/// the next boundary writes (whose distinct equality is disjoint).
/// The same global zero tmp is returned within every iteration. There is
/// no old/new tape capture or extra owner; current5..15-control metadata
/// cubes make this lowering strictly cheaper in both literal directions.
#[allow(clippy::too_many_arguments)]
pub(super) fn virtual_divide(b: &mut B, t: &[QubitId], s: &[QubitId],
    carry: QubitId, enable: QubitId, e: QubitId, mask: QubitId,
    tmp: QubitId, lo: usize, hi: usize, dirty: &[QubitId],
    xor_eq: &mut SizeQuery<'_>) {
    let dirty = donors(t, s, &[carry,enable,e,mask,tmp], lo, hi, dirty);
    for &q in t { b.x(q); }
    up(b, t, s, carry);
    for i in (0..t.len()).rev() {
        let x = undo_cell(b, t, s, carry, i);
        if (lo..=hi).contains(&i) {
            xor_eq(b, i, tmp, &[], &[], &dirty);
            b.ccx(tmp,enable,e);
            mc_xor(b,&[(tmp,false),(enable,false),(t[i],false),(x,false)],
                e,&[],&dirty);
            mc_xor(b,&[(tmp,false),(e,false),(x,false)],t[i],&[],&dirty);
        }
        // The mask is e & [size >= i+1]. When e is decided at i=size,
        // both its previous and current strict predicates are false.
        lower_write(b, t, s, x, mask, i, hi);
        if (lo..=hi).contains(&i) {
            b.ccx(e,tmp,mask);
            xor_eq(b, i, tmp, &[], &[], &dirty);
        }
    }
    b.cx(e, mask); // size>=1 on every e=1 shot
    for &q in t { b.x(q); }
}

/// Add the source under e, with virtual-zero boundary and no writes above
/// it. The caller's digit-inverse bounds in the module contract are needed.
/// tmp is callback-owned query workspace, restored by every query. It may
/// hold an immutable class predicate if that callback explicitly supports
/// it; the arithmetic never reads or writes tmp.
#[allow(clippy::too_many_arguments)]
pub(super) fn virtual_add(b: &mut B, t: &[QubitId], s: &[QubitId],
    carry: QubitId, e: QubitId, mask: QubitId, tmp: QubitId,
    lo: usize, hi: usize, dirty: &[QubitId], xor_eq: &mut SizeQuery<'_>) {
    let dirty = donors(t, s, &[carry,e,mask,tmp], lo, hi, dirty);
    let clean = [tmp];
    up(b, t, s, carry);
    for i in (0..t.len()).rev() {
        let x = undo_cell(b, t, s, carry, i);
        if (lo..=hi).contains(&i) {
            xor_eq(b, i, t[i], &[(e,false),(x,false)], &clean, &dirty);
        }
        if (lo..=hi).contains(&(i+1)) {
            xor_eq(b, i+1, mask, &[(e,false)], &clean, &dirty);
        }
        lower_write(b, t, s, x, mask, i, hi);
    }
    b.cx(e, mask);
}

/// XOR the unsigned virtual-boundary comparison into e under enable & !sv.
/// There are no UMA writes, and sv/enable/source/target/carry are restored.
/// As in virtual_add, tmp belongs solely to the query callback and may
/// retain a class predicate over this complete immutable-metadata epoch.
#[allow(clippy::too_many_arguments)]
pub(super) fn virtual_compare(b: &mut B, t: &[QubitId], s: &[QubitId],
    carry: QubitId, enable: QubitId, e: QubitId, sv: QubitId,
    tmp: QubitId, lo: usize, hi: usize, dirty: &[QubitId],
    xor_eq: &mut SizeQuery<'_>) {
    let dirty = donors(t, s, &[carry,enable,e,sv,tmp], lo, hi, dirty);
    let clean = [tmp];
    for &q in t { b.x(q); }
    up(b, t, s, carry);
    for i in (0..t.len()).rev() {
        let x = undo_cell(b, t, s, carry, i);
        if (lo..=hi).contains(&i) {
            xor_eq(b, i, e, &[(enable,false),(sv,true)], &clean, &dirty);
            xor_eq(b, i, e, &[(enable,false),(sv,true),(t[i],false),(x,false)], &clean, &dirty);
        }
    }
    for &q in t { b.x(q); }
}
