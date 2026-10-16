//! Exact controlled ADD followed by a carry query, as inverse restoring division.
//! No deferred flags, allocation, precision selection, or input-dependent choice.
use crate::point_add::builder::{B, G};
use crate::circuit::QubitId;

/// First cell of a Cuccaro ladder when its carry-in is clean. The first
/// carry stays in c0 instead of s[0], while s[0] and t[0] stay original.
/// Higher cells have the same carry states as the ordinary ladder after
/// substituting c0 for its old first carry owner s[0].
fn clean_up(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId) -> Vec<G> {
    assert!(!t.is_empty() && t.len() == s.len());
    b.begin();
    b.and_c(t[0], s[0], c0);
    for i in 1..t.len() {
        let x = if i == 1 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    b.end()
}

/// Return the direct clean first carry before writing bit zero. At that
/// instant t[0] and s[0] are the unchanged operands that computed c0, so the
/// measured AND erasure is exact in either direction and has no deferred flag.
fn clean_down(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId,
              control: Option<QubitId>) -> Vec<G> {
    assert!(!t.is_empty() && t.len() == s.len());
    b.begin();
    for i in (1..t.len()).rev() {
        let x = if i == 1 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        if let Some(g) = control {
            b.cx(s[i], x);
            b.ccx(g, x, t[i]);
            b.cx(s[i], x);
        }
    }
    b.and_u(t[0], s[0], c0);
    if let Some(g) = control { b.ccx(g, s[0], t[0]); }
    b.end()
}

/// Exact middle comparator with the same callback ordering as payload::ripple.
/// c0 is clean. The callback's carry lane zero is c0; lanes i >= 1 remain s[i].
/// The callback returns all operands before the down pass. Its controls may
/// depend on those carries but must not write t or s.
pub(super) fn clean_ripple(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId,
    complement: bool, mid: &mut dyn FnMut(&mut B),
    gate: &mut dyn FnMut(&mut B, Option<usize>) -> Option<QubitId>) {
    assert!(!t.is_empty() && t.len() == s.len());
    if complement { for &q in t { b.x(q); } }
    let up = clean_up(b, t, s, c0);
    b.play(&up, false);
    mid(b);
    for i in (1..t.len()).rev() {
        let x = if i == 1 { c0 } else { s[i - 1] };
        let g = gate(b, Some(i));
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        if let Some(g) = g {
            b.cx(s[i], x);
            b.ccx(g, x, t[i]);
            b.cx(s[i], x);
        }
    }
    let g = gate(b, Some(0));
    b.and_u(t[0], s[0], c0);
    if let Some(g) = g { b.ccx(g, s[0], t[0]); }
    gate(b, None);
    if complement { for &q in t { b.x(q); } }
}

/// ADD changes only t[..write], and then tail (the latter has zero source).
/// The carry query may extend above that write prefix. It toggles e by
/// accept & !source_mid[reg], for range.0 <= reg <= range.1. Every source, size,
/// scratch and arbitrary dirty passenger is returned. e may be arbitrary,
/// independently of accept; callers need no active-domain restriction here.
///
/// Preconditions: c0, h and pre are clean. h can occur in pre: the query
/// returns that entire bank before h is used by the tail increment. All
/// other ports are pairwise disjoint; dirty is disjoint from these ports.
#[allow(clippy::too_many_arguments)]
pub(super) fn add_compare(b: &mut B, t: &[QubitId], s: &[QubitId], tail: &[QubitId], write: usize,
    query_len: usize, reg: &[QubitId], range: (usize, usize), accept: QubitId, e: QubitId,
    c0: QubitId, h: QubitId, pre: &[QubitId], dirty: &[QubitId]) {
    assert!(!t.is_empty() && t.len() == s.len() && write <= t.len());
    assert!(write > 0 && query_len > 0 && query_len <= t.len());
    assert!(tail.is_empty() || write == t.len());
    let mut seen = std::collections::BTreeSet::new();
    for q in t.iter().chain(s).chain(tail).chain(reg).chain([&accept, &e, &c0, &h]) {
        assert!(seen.insert(q.0));
    }
    let mut prefix = std::collections::BTreeSet::new();
    for q in pre {
        assert!(prefix.insert(q.0) && (*q == h || seen.insert(q.0)));
    }
    let mut donors = std::collections::BTreeSet::new();
    assert!(dirty.iter().all(|q| !seen.contains(&q.0) && donors.insert(q.0)));
    b.begin();
    for &q in t.iter().chain(tail) { b.x(q); }
    let up_query = clean_up(b, &t[..query_len], &s[..query_len], c0);
    b.play(&up_query, false);
    // Query at the EXACT old comparator boundary. The next MAJ would XOR
    // original s[query_len] into the last queried source/carry owner.
    // Moving this query past that MAJ is wrong for arbitrary source data.
    let lane = |v: usize| if v == 0 { Some(c0) } else { s[..query_len].get(v).copied() };
    crate::point_add::payload::read_lane(b, reg, range.0, range.1, &lane, true,
        &[(accept, false)], e, pre, &[], dirty);
    if query_len < t.len() {
        let up_rest = crate::point_add::arith::up_m(b, &t[query_len..], &s[query_len..], if query_len == 1 { c0 } else { s[query_len-1] }, false);
        b.play(&up_rest, false);
    }
    if !tail.is_empty() {
        let cout = if s.len() == 1 { c0 } else { *s.last().unwrap() };
        b.and_c(e, cout, h);
        crate::point_add::frogdrop::inc_mixed(b, h, tail, &[], dirty);
        b.and_u(e, cout, h);
    }
    if write < t.len() {
        let restore_high = crate::point_add::arith::down_m(b, &t[write..], &s[write..], if write == 1 { c0 } else { s[write-1] },
            crate::point_add::arith::Dm::Restore, false);
        b.play(&restore_high, false);
    }
    let write_low = clean_down(b, &t[..write], &s[..write], c0, Some(e));
    b.play(&write_low, false);
    for &q in t.iter().chain(tail) { b.x(q); }
    let restoring: Vec<G> = b.end();
    b.play(&restoring, true);
}

