//! Exact conjugation of the paired map frame, using only the protected
//! builder's existing public recording/replay API. This is a source draft.
//!
//! P; F; M; F^-1; S under c becomes ctrl(P); U; ctrl(M); U^-1;
//! ctrl(S). U is F with every measured AND replaced by literal CCX, including
//! the inherited classic rows. On c=0 the two arbitrary-data permutations
//! cancel; on c=1 U agrees with F on its original clean-ancilla domain.
//! Neither c nor the clean replay helper occurs anywhere in either frame.

use super::super::builder::{B, G};
use super::super::row_add::{self, Row};
use crate::circuit::QubitId;
use std::collections::BTreeMap;

struct Capture {
    outside: [QubitId; 2],
    frames: Vec<(Vec<G>, bool)>,
    rows: BTreeMap<u32, Row>,
    finished: bool,
}

thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Capture>> = const {
        std::cell::RefCell::new(None)
    };
}

pub(crate) fn begin(outside: [QubitId; 2]) {
    assert_ne!(outside[0], outside[1]);
    CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        assert!(capture.is_none(), "unconsumed pair-control map capture");
        *capture = Some(Capture {
            outside, frames: Vec::new(), rows: BTreeMap::new(), finished: false,
        });
    });
}

// Called at the original frame recording boundary, before ordinary replay.
// Outside the selected clean-control maps it has no effect.
pub(crate) fn capture_frame(frame: &[G], inverse: bool) {
    CAPTURE.with(|capture| {
        if let Some(capture) = capture.borrow_mut().as_mut() {
            assert!(!capture.finished);
            capture.frames.push((frame.to_vec(), inverse));
        }
    });
}

pub(crate) fn finish(rows: BTreeMap<u32, Row>) {
    CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        let capture = capture.as_mut().expect("missing pair-control capture");
        assert!(!capture.finished);
        capture.rows = rows;
        capture.finished = true;
    });
}

fn inverse(gate: G) -> Option<G> {
    Some(match gate {
        G::AndC(a, b, t) => G::AndU(a, b, t),
        G::AndU(a, b, t) => G::AndC(a, b, t),
        G::RowAdd(id, inv) => G::RowAdd(id, !inv),
        G::X(_) | G::Cx(_, _) | G::Ccx(_, _, _) | G::Swap(_, _) => gate,
        _ => return None,
    })
}

fn row_allowed(row: &Row, outside: &[QubitId; 2]) -> bool {
    let classic = 1usize << (usize::BITS - 1);
    !row.signed_binary && row.mux.is_none() && row.chunk & classic != 0
        && [row.g, row.c0, row.h].iter()
            .chain(&row.t).chain(&row.s).chain(&row.tail)
            .chain(&row.bank).chain(&row.dirty)
            .all(|q| !outside.contains(q))
}

fn allowed(gate: G, capture: &Capture) -> bool {
    let outside = &capture.outside;
    match gate {
        G::X(a) => !outside.contains(&a),
        G::Cx(a, b) | G::Swap(a, b) => !outside.contains(&a) && !outside.contains(&b),
        G::Ccx(a, b, t) | G::AndC(a, b, t) | G::AndU(a, b, t) =>
            ![a, b, t].iter().any(|q| outside.contains(q)),
        G::RowAdd(id, _) => capture.rows.get(&id)
            .is_some_and(|row| row_allowed(row, outside)),
        _ => false,
    }
}

// Fresh row IDs are expected when frame_mul records the same frame again.
// Compare the complete public recipe, not IDs, widths, costs or a hash alone.
fn same_recipe(a: G, b: G, capture: &Capture) -> bool {
    match (a, b) {
        (G::RowAdd(ai, av), G::RowAdd(bi, bv)) => av == bv
            && capture.rows.get(&ai).zip(capture.rows.get(&bi))
                .is_some_and(|(a, b)| a == b),
        _ => a == b,
    }
}

fn find_exact(record: &[G], frame: &[G], start: usize) -> Option<usize> {
    if frame.is_empty() || start > record.len() || frame.len() > record.len() - start {
        return None;
    }
    // A short central anchor only accelerates lookup. Admission still
    // compares the complete frame byte-for-byte, including original row IDs.
    let width = frame.len().min(16);
    let offset = (frame.len() - width) / 2;
    let anchor = &frame[offset..offset + width];
    record[start..].windows(width).enumerate().find_map(|(i, window)| {
        if window != anchor { return None; }
        let hit = start + i;
        let first = hit.checked_sub(offset)?;
        let last = first.checked_add(frame.len())?;
        (first >= start && last <= record.len() && record[first..last] == *frame)
            .then_some(first)
    })
}

fn unitary(gate: G) -> Option<G> {
    Some(match gate {
        G::AndC(a, b, t) | G::AndU(a, b, t) => G::Ccx(a, b, t),
        G::X(_) | G::Cx(_, _) | G::Ccx(_, _, _) | G::Swap(_, _) => gate,
        _ => return None,
    })
}

struct Plan {
    a: usize, b: usize, x: usize, y: usize,
    unitary: Vec<G>,
    old_pair_t: u64,
    new_pair_t: u64,
    row_pairs: usize,
}

fn plan(b: &mut B, record: &[G], capture: &Capture) -> Option<Plan> {
    if !capture.finished || capture.frames.len() != 2 || b.force_unitary_and {
        return None;
    }
    let (forward, forward_inv) = &capture.frames[0];
    let (backward, backward_inv) = &capture.frames[1];
    if *forward_inv || !*backward_inv || forward.len() != backward.len()
        || !forward.iter().zip(backward).all(|(&a, &b)|
            allowed(a, capture) && allowed(b, capture) && same_recipe(a, b, capture)) {
        return None;
    }
    let back: Vec<G> = backward.iter().rev().map(|&g| inverse(g))
        .collect::<Option<Vec<_>>>()?;
    let a = find_exact(record, forward, 0)?;
    let end = a + forward.len();
    let x = find_exact(record, &back, end)?;
    let y = x + back.len();
    // U may leave arbitrary dirty banks on skipped shots. The intervening
    // segment must therefore use literal full control: every one of these
    // primitives is identity at c=0 for all data with the helper restored.
    // A factored measured-carry RowAdd would need a separate all-data proof.
    if !record[end..x].iter().all(|gate| matches!(gate,
        G::X(_) | G::Cx(_, _) | G::Ccx(_, _, _) | G::Swap(_, _)
        | G::AndC(_, _, _) | G::AndU(_, _, _))) {
        return None;
    }

    let mut plain = Vec::new();
    let mut old_pair_t = 0u64;
    let mut row_pairs = 0usize;
    for &gate in forward {
        if let G::RowAdd(id, inv) = gate {
            let row = capture.rows.get(&id)?;
            // This branch is the inherited CLASSIC_ROW literal expansion.
            // It has no deferred flags, erasure boxes, allocations or HMR
            // side effects while recorded; B.rows stays private and intact.
            b.begin();
            row_add::emit(b, row, inv);
            let literal = b.end();
            let mut ccx = 0u64;
            let mut ands = 0u64;
            for gate in literal {
                if !allowed(gate, capture) { return None; }
                match gate {
                    G::Ccx(_, _, _) => ccx += 1,
                    G::AndC(_, _, _) | G::AndU(_, _, _) => ands += 1,
                    _ => (),
                }
                plain.push(unitary(gate)?);
            }
            // Existing outer control factors once per complete row. Its
            // pair costs 2*CCX + AndC+AndU + 2 outer AND computations.
            // Every literal is counted; RowAdd itself is never priced 1T.
            old_pair_t += 2 * ccx + ands + 2;
            row_pairs += 1;
        } else {
            old_pair_t += match gate {
                G::Ccx(_, _, _) | G::AndC(_, _, _) | G::AndU(_, _, _) => 4,
                G::Cx(_, _) | G::Swap(_, _) => 2,
                G::X(_) => 0,
                _ => return None,
            };
            plain.push(unitary(gate)?);
        }
    }
    let new_pair_t = 2 * plain.iter().filter(|g| matches!(g, G::Ccx(_, _, _))).count() as u64;
    // A non-improving source price retains the qualified original lowering.
    // Cross-boundary peephole cancellation is measured only by the eventual
    // single whole stream; this pre-peephole price is not a measured result.
    if new_pair_t >= old_pair_t { return None; }
    Some(Plan { a, b: end, x, y, unitary: plain, old_pair_t, new_pair_t, row_pairs })
}

pub(crate) fn play_ctrl_full(b: &mut B, record: &[G], c: QubitId, helper: QubitId) {
    let capture = CAPTURE.with(|capture| capture.borrow_mut().take());
    let Some(capture) = capture else {
        b.play_ctrl_full(record, c, helper);
        return;
    };
    assert_eq!(capture.outside, [c, helper]);
    if let Some(plan) = plan(b, record, &capture) {
        b.play_ctrl_full(&record[..plan.a], c, helper);
        b.play(&plan.unitary, false);
        b.play_ctrl_full(&record[plan.b..plan.x], c, helper);
        b.play(&plan.unitary, true);
        b.play_ctrl_full(&record[plan.y..], c, helper);
        eprintln!("PAIR_CTRL_SOURCE_PRICE old_pair_t={} new_pair_t={} saving={} row_pairs={}",
            plan.old_pair_t, plan.new_pair_t, plan.old_pair_t - plan.new_pair_t, plan.row_pairs);
    } else {
        b.play_ctrl_full(record, c, helper);
    }
}
