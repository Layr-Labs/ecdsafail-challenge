//! Packed-prefix `shift ^= gate * ctz(q)` (design 3.1 D12 / 3.2 M2: "direct
//! ctz", `p.ctz.direct`, ~33 T per call): a local twin of
//! `retained_division::direct_ctz::emit` (private to that module), the bounded
//! active zero-prefix XOR into the shift word.
//!
//! Mechanism: with `q`'s bits X-bracketed, the prefix chain
//! `p_i = gate AND [q[0..=i] == 0]` is built one CCX per level; at level `i`
//! the gray-code delta `i XOR (i + 1)` is CX'd into `shift` under `p_i`, so
//! the levels `0..ctz(q)` telescope to `shift ^= gate * ctz(q)` (capped at
//! `q.len() - 1`: the top physical q bit is not scanned, as in the source -
//! `q = 2^(len-1)` gives the cap, which IS its ctz). The chain is cut into
//! chunks by `clean_chunk_plan::plan(count, room)` so that at most `room`
//! prefix wires are live at once: each chunk's last prefix is RETAINED as the
//! next chunk's root while the rest are uncomputed by `clear_and` (0 T), and
//! the retained boundaries are released afterwards by HMR with the phase
//! fix-up replayed under the measured bit (the source's exact form). Cost
//! `count + replay` CCX with `replay = count - room` (0 when the whole chain
//! fits: 1 T per scanned q bit).
//!
//! Self-inverse (a pure XOR deposit), so the backward driver calls the same
//! function; `q` and `gate` are restored. Preconditions: `q`, `shift`, `gate`
//! pairwise disjoint (asserted), `room >= 2` whenever `count > room`
//! (`plan` returns `None` otherwise: asserted with the numbers).

#![allow(dead_code)]

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

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

/// `shift ^= gate * min(ctz(q), q.len() - 1)` with the prefix chain chunked to
/// at most `room` live prefix wires (module doc). `room` is typically
/// `sched::scratch_room(c)`.
pub(crate) fn ctz_xor(c: &mut Circuit, q: &[QReg], shift: &[QReg], gate: &QReg, room: usize) {
    let count = q.len().saturating_sub(1);
    if count == 0 || shift.is_empty() {
        return;
    }
    assert!(
        q.iter().all(|a| a.id() != gate.id() && shift.iter().all(|b| a.id() != b.id()))
            && shift.iter().all(|a| a.id() != gate.id()),
        "ctz_xor: q, shift and gate must be disjoint"
    );
    let chunks = crate::point_add::clean_chunk_plan::plan(count, room)
        .unwrap_or_else(|| panic!("ctz_xor: no chunk plan for {count} q bits in {room} scratch wires"));
    emit(c, q, shift, gate, &chunks);
}

fn emit(c: &mut Circuit, q: &[QReg], shift: &[QReg], active: &QReg, chunks: &[usize]) {
    let count = q.len().saturating_sub(1);
    assert_eq!(chunks.iter().sum::<usize>(), count);
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
            let next = c.alloc_qreg("pctz.prefix");
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
                let next = c.alloc_qreg("pctz.phase.prefix");
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
