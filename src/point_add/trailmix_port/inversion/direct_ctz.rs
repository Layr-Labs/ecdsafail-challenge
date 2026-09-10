//! Bounded active zero-prefix XOR into an arbitrary shift word.
//!
//! The source CTZ helper gives min(ctz(q), q.len()-1), including its q=0
//! sentinel. Therefore the final physical q bit is intentionally not scanned.
//! Only the retained substep's zero/CTZ shift boundaries justify replacing its
//! arithmetic add/subtract with this XOR kernel.
use super::*;

struct Boundary {
    wire: QReg,
    start: usize,
    end: usize,
}

fn deposit(c: &mut Circuit, prefix: &QReg, shift: &[QReg], index: usize) {
    let gray = index ^ (index + 1);
    for (bit, target) in shift.iter().enumerate() {
        if gray >> bit & 1 != 0 {
            c.cx(prefix, target);
        }
    }
}

fn emit(c: &mut Circuit, q: &[QReg], shift: &[QReg], active: &QReg, chunks: &[usize]) {
    let count = q.len().saturating_sub(1);
    assert_eq!(chunks.iter().sum::<usize>(), count);
    assert!(q
        .iter()
        .all(|a| a.id() != active.id() && shift.iter().all(|b| a.id() != b.id())));
    assert!(shift.iter().all(|a| a.id() != active.id()));
    let section = c.push_section("p.ctz.direct");
    for bit in &q[..count] {
        c.x(bit);
    }
    let mut boundaries: Vec<Boundary> = Vec::new();
    let mut start = 0;
    for &size in chunks {
        assert!(size != 0);
        let end = start + size;
        let initial = boundaries.last().map_or(active, |b| &b.wire);
        let mut chain: Vec<QReg> = Vec::new();
        for i in start..end {
            let next = c.alloc_qreg("ctz.prefix");
            c.ccx(chain.last().unwrap_or(initial), &q[i], &next);
            deposit(c, &next, shift, i);
            chain.push(next);
        }
        let keep = end < count;
        for i in (0..chain.len() - usize::from(keep)).rev() {
            let previous = if i == 0 { initial } else { &chain[i - 1] };
            c.clear_and(&chain[i], previous, &q[start + i]);
        }
        let retained = keep.then(|| chain.pop().unwrap());
        for bit in chain {
            c.zero_and_free(bit);
        }
        if let Some(wire) = retained {
            boundaries.push(Boundary { wire, start, end });
        }
        start = end;
    }
    while let Some(boundary) = boundaries.pop() {
        let initial = boundaries.last().map_or(active, |b| &b.wire);
        let phase = c.alloc_bit();
        c.hmr(&boundary.wire, phase);
        c.zero_and_free(boundary.wire);
        c.with_condition(phase, |c| {
            let mut chain: Vec<QReg> = Vec::new();
            for i in boundary.start..boundary.end - 1 {
                let next = c.alloc_qreg("ctz.phase.prefix");
                c.ccx(chain.last().unwrap_or(initial), &q[i], &next);
                chain.push(next);
            }
            c.cz(chain.last().unwrap_or(initial), &q[boundary.end - 1]);
            for i in (0..chain.len()).rev() {
                let previous = if i == 0 { initial } else { &chain[i - 1] };
                c.clear_and(&chain[i], previous, &q[boundary.start + i]);
            }
            for bit in chain {
                c.zero_and_free(bit);
            }
        });
        c.free_bit(phase);
    }
    for bit in &q[..count] {
        c.x(bit);
    }
    c.pop_section(&section);
}

pub(super) fn try_apply(
    c: &mut Circuit,
    q: &[QReg],
    shift: &[QReg],
    active: GateControl<'_>,
) -> bool {
    if std::env::var("MIDQ_DIRECT_CTZ").ok().as_deref() != Some("1") {
        return false;
    }
    // The pinned path is Hybrid and component tests also use Direct. Preserve
    // the older low-scratch/recomputed-control routes as fallbacks for now.
    if !matches!(active, GateControl::Direct(_) | GateControl::Hybrid(_)) {
        return false;
    }
    if q.len() <= 1 || shift.is_empty() {
        return true;
    }
    c.flush_pending_frees();
    let cap = env_usize("MIDQ_PREFIX_QCAP", 1019);
    let gate_room = match active {
        GateControl::Hybrid(control) => usize::from(control.held.borrow().is_none()),
        _ => 0,
    };
    let available = cap.saturating_sub(c.b.active_qubits as usize + gate_room);
    let Some(chunks) = crate::point_add::clean_chunk_plan::plan(q.len() - 1, available) else {
        // Do not materialize a Hybrid AND before rejecting: that could change
        // the old fallback's first scan peak even if it were immediately freed.
        return false;
    };
    with_ctz_gate_control(c, active, |c, gate| {
        emit(c, q, shift, gate, &chunks);
    });
    true
}

#[path = "direct_ctz_selftest.rs"]
mod checks;
pub(super) fn selftest() {
    checks::run();
}
