//! Default-off checkpoint constant fallback with no new quantum workspace.
//! The observed gidney_cadd peak already uses its minimal two clean carries;
//! it has no configurable vent count to clip.
use super::{env_usize, Circuit, QReg};
use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_hybrid_add_refs;

const SCOPE: &str = "checkpoint.cap_aware";
pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_CHECKPOINT_CAP_AWARE").ok().as_deref() == Some("1")
}
pub(super) fn enter(c: &mut Circuit) -> Option<String> {
    enabled().then(|| c.push_section(SCOPE))
}
pub(super) fn leave(c: &mut Circuit, scope: Option<String>) {
    if let Some(scope) = scope {
        c.pop_section(&scope);
    }
}
fn cap() -> usize {
    env_usize("MIDQ_CHECKPOINT_QCAP", env_usize("MIDQ_CELL_QCAP", 1009))
}

// Signed nonadjacent binary expansion. Terms at or above the target width
// vanish modulo its existing word size; no target high bits are discarded.
fn terms(value: u64, width: usize) -> Vec<(usize, bool)> {
    let mut remaining = value as u128;
    let mut bit = 0;
    let mut result = Vec::new();
    while remaining != 0 {
        if remaining & 1 != 0 {
            let positive = remaining & 3 != 3;
            if bit < width {
                result.push((bit, positive));
            }
            if positive {
                remaining -= 1;
            } else {
                remaining += 1;
            }
        }
        remaining >>= 1;
        bit += 1;
    }
    result
}
fn unit(c: &mut Circuit, g: &QReg, target: &[QReg], donor: &[QReg], increment: bool) {
    if target.is_empty() {
        return;
    }
    if target.len() == 1 {
        c.cx(g, &target[0]);
        return;
    }
    let a: Vec<_> = target.iter().collect();
    let d: Vec<_> = donor[..target.len()].iter().collect();
    if increment {
        for q in target {
            c.x(q);
        }
    }
    // D+NOT(D)=-1 modulo2^n. Both controlled adders restore the arbitrary
    // quantum donor. Zero vent budget prevents allocating a clean carry.
    controlled_hybrid_add_refs(c, g, &a, &d, 0);
    for q in &d {
        c.x(q);
    }
    controlled_hybrid_add_refs(c, g, &a, &d, 0);
    for q in &d {
        c.x(q);
    }
    if increment {
        for q in target {
            c.x(q);
        }
    }
}
pub(super) fn try_update(
    c: &mut Circuit,
    g: &QReg,
    target: &[QReg],
    value: &[u8],
    donor: &[QReg],
    subtract: bool,
) -> bool {
    if !enabled() || !c.current_section.split('/').any(|s| s == SCOPE) || target.len() < 2 {
        return false;
    }
    // The checkpoint fold constants F and (F-1)/2 fit u64. Preserve the old
    // route for unrelated larger constants or unsupported donor shapes.
    if value.iter().skip(8).any(|&v| v != 0) {
        return false;
    }
    let v = value
        .iter()
        .take(8)
        .enumerate()
        .fold(0u64, |v, (i, &b)| v | ((b as u64) << (8 * i)));
    let selected = terms(v, target.len());
    let needed = selected
        .iter()
        .map(|&(i, _)| target.len() - i)
        .max()
        .unwrap_or(0);
    if donor.len() < needed {
        return false;
    }
    let mut ids = std::collections::HashSet::new();
    if target
        .iter()
        .chain(&donor[..needed])
        .chain([g])
        .any(|q| !ids.insert(q.id()))
    {
        return false;
    }
    c.flush_pending_frees();
    let before = c.b.active_qubits as usize;
    let limit = cap();
    let dirty_route = std::env::var("MIDQ_DIRTY_CONST").ok().as_deref() == Some("1");
    let compact = std::env::var("MIDQ_COMPACT_CONST_CARRY").ok().as_deref() == Some("1")
        && !target.iter().chain(donor).any(|q| q.id() == g.id());
    // Three lanes are live in the old un-compacted Gidney kernel. If the
    // generic clean-ancilla constant route was requested, do not invent a
    // finite scratch bound for it: this exact donor fallback remains usable.
    let required = if dirty_route {
        if compact {
            2
        } else {
            3
        }
    } else {
        usize::MAX
    };
    if before.saturating_add(required) <= limit {
        return false;
    }
    let previous = c.push_section("checkpoint.zero_clean_constant");
    let peak = c.b.peak_qubits;
    for &(bit, positive) in &selected {
        unit(c, g, &target[bit..], donor, positive != subtract);
    }
    c.flush_pending_frees();
    assert_eq!(
        c.b.active_qubits as usize, before,
        "checkpoint fallback leaked workspace"
    );
    assert_eq!(
        c.b.peak_qubits, peak,
        "zero-clean fallback allocated fresh workspace"
    );
    if std::env::var("MIDQ_CHECKPOINT_CAP_TRACE").ok().as_deref() == Some("1") {
        eprintln!("CHECKPOINT_CAP_UPDATE width={} value={v} subtract={subtract} live={before} requested_cap={limit} added_clean=0 live_floor_exceeds_cap={} terms={}",target.len(),before>limit,selected.len());
    }
    c.pop_section(&previous);
    true
}

#[path = "checkpoint_cap_aware_selftest.rs"]
mod checks;
pub(crate) use checks::{profile, run as selftest};
