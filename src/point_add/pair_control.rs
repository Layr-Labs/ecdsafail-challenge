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

fn row_allowed(row: &Row, outside: &[QubitId]) -> bool {
    let classic = 1usize << (usize::BITS - 1);
    !row.signed_binary && row.mux.is_none() && row.chunk & classic != 0
        && [row.g, row.c0, row.h].iter()
            .chain(&row.t).chain(&row.s).chain(&row.tail)
            .chain(&row.bank).chain(&row.dirty)
            .all(|q| !outside.contains(q))
}

fn allowed(gate: G, capture: &Capture) -> bool {
    allowed_outside(gate, capture, &capture.outside)
}

fn allowed_outside(gate: G, capture: &Capture, outside: &[QubitId]) -> bool {
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

fn plan(b: &mut B, record: &[G], capture: &Capture,
        require_clean_saving: bool) -> Option<Plan> {
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
    // This price is specifically the inherited CLEAN outer control.
    // NAND fallback instead literalizes every row and pays 9T for each
    // CCX/AND, 4T for CX/Swap and 1T for X. Its paired unitary frame is
    // therefore never dearer: each CCX pair costs 2T instead of 18T.
    // Do not reject that exact conjugation using the unrelated clean price.
    if require_clean_saving && new_pair_t >= old_pair_t { return None; }
    Some(Plan { a, b: end, x, y, unitary: plain, old_pair_t, new_pair_t, row_pairs })
}

pub(crate) fn play_ctrl_full(b: &mut B, record: &[G], c: QubitId, helper: QubitId) {
    let capture = CAPTURE.with(|capture| capture.borrow_mut().take());
    let Some(capture) = capture else {
        b.play_ctrl_full(record, c, helper);
        return;
    };
    assert_eq!(capture.outside, [c, helper]);
    if let Some(plan) = plan(b, record, &capture, true) {
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

/// Same paired-frame conjugation with an arbitrary, restored outside
/// helper. The control and helper remain excluded from every record port.
/// Only P/M/S use dirty control; U and U^-1 are unchanged and cancel on
/// control-zero shots even when their temporary banks contain arbitrary data.
pub(crate) fn play_ctrl_full_dirty(b: &mut B, record: &[G], c: QubitId, helper: QubitId) {
    let capture = CAPTURE.with(|capture| capture.borrow_mut().take())
        .expect("dirty paired replay requires the complete classic-map capture");
    assert_eq!(capture.outside, [c, helper]);
    assert!(capture.finished && record.iter().all(|&g| allowed(g, &capture)),
        "dirty helper must be outside every map port, including row donors");
    let selected = plan(b, record, &capture, true);
    let dirty_play = |b: &mut B, segment: &[G]| {
        // The ordinary outer P/M/S segments are literal. A fallback may
        // contain classic rows: expand their exact source recipe and turn
        // measured ANDs into the same unitary extension used for U.
        let mut literal = Vec::new();
        for &gate in segment {
            if let G::RowAdd(id, inv) = gate {
                let row = capture.rows.get(&id).expect("missing classic row");
                assert!(row_allowed(row, &capture.outside));
                b.begin(); row_add::emit(b, row, inv); let row_record = b.end();
                for g in row_record {
                    assert!(allowed(g, &capture));
                    literal.push(unitary(g).expect("classic row must be literal"));
                }
            } else { literal.push(gate); }
        }
        b.play_ctrl_full_dirty(&literal, c, helper);
    };
    if let Some(plan) = selected {
        dirty_play(b, &record[..plan.a]);
        b.play(&plan.unitary, false);
        dirty_play(b, &record[plan.b..plan.x]);
        b.play(&plan.unitary, true);
        dirty_play(b, &record[plan.y..]);
    } else { dirty_play(b, record); }
}

/// Exact SWPH map replay without a held done owner. The two controls and
/// arbitrary dirty helpers are outside every map/row port. Only P/M/S gain
/// NAND control: the same literal U/U^-1 pair still occurs exactly once.
/// On PH&SW=1 all outside segments are identity and the pair cancels for
/// arbitrary skipped data. On its complement the original map is applied.
pub(crate) fn play_ctrl_nand2(b: &mut B, record: &[G], ph: QubitId, sw: QubitId,
                            w1: QubitId, w2: QubitId) {
    let capture = CAPTURE.with(|capture| capture.borrow_mut().take())
        .expect("SWPH paired replay requires the complete classic-map capture");
    assert_eq!(capture.outside, [sw, ph]);
    let outside = [ph,sw,w1,w2];
    assert_eq!(outside.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), 4);
    assert!(capture.finished && record.iter().all(|&g| allowed_outside(g,&capture,&outside)),
        "SWPH controls/helpers must be outside all map and row ports");
    let selected = plan(b, record, &capture, false);
    // The map packet encoder and TZ probe form an exact outer E;F;E^-1.
    // E is literal unitary and avoids PH/SW and both restored dirty
    // helpers, as checked above. Thus ctrl(F) may be conjugated by E on
    // every shot: off-control it is identity on arbitrary E output.
    // Stop before the selected frame pair, preserving its full recipe.
    let limit = selected.as_ref()
        .map(|p| p.a.min(record.len()-p.y))
        .unwrap_or(record.len()/2);
    let shell = unitary_shell_len(record, limit);
    let nand_play = |b: &mut B, segment: &[G]| {
        let mut literal = Vec::new();
        for &gate in segment {
            if let G::RowAdd(id, inv) = gate {
                let row = capture.rows.get(&id).expect("missing classic row");
                assert!(row_allowed(row, &outside));
                b.begin(); row_add::emit(b,row,inv); let row_record=b.end();
                for g in row_record {
                    assert!(allowed_outside(g,&capture,&outside));
                    literal.push(unitary(g).expect("classic row must be literal"));
                }
            } else { literal.push(gate); }
        }
        b.play_ctrl_nand2(&literal,ph,sw,w1,w2);
    };
    b.play(&record[..shell],false);
    if let Some(plan) = selected {
        nand_play(b,&record[shell..plan.a]);
        b.play(&plan.unitary,false);
        nand_play(b,&record[plan.b..plan.x]);
        b.play(&plan.unitary,true);
        nand_play(b,&record[plan.y..record.len()-shell]);
    } else { nand_play(b,&record[shell..record.len()-shell]); }
    b.play(&record[..shell],true);
}

/// Only self-inverse, literal unitary gates may enter this shell. In
/// particular measured ANDs, opaque rows, and merely equal-cost recipes
/// are not a substitute for the exact reverse suffix.
fn unitary_shell_len(record: &[G], limit: usize) -> usize {
    let mut n=0;
    while n<limit.min(record.len()/2) {
        let g=record[n];
        if !matches!(g,G::X(_)|G::Cx(_,_)|G::Ccx(_,_,_)|G::Swap(_,_))
            || record[record.len()-1-n]!=g {break;}
        n+=1;
    }
    n
}

// SOURCE-ONLY extension to append INSIDE the existing pair_control module.
// Uses its private capture/plan/unitary helpers; changes no protected builder.
// Same exact per-primitive price as fixed external donors: X1, CX/Swap4,
// CCX9. Sixteen map owners need no additional globally idle replay helper.
pub(crate) fn play_ctrl_nand2_local(b: &mut B, record: &[G], ph: QubitId, sw: QubitId,
                                  universe: &[QubitId]) {
    let capture = CAPTURE.with(|capture| capture.borrow_mut().take())
        .expect("SWPH paired replay requires the complete classic-map capture");
    assert_eq!(capture.outside, [sw, ph]);
    let outside = [ph,sw];
    assert_ne!(ph,sw);
    assert!(capture.finished && record.iter().all(|&g| allowed_outside(g,&capture,&outside)),
        "SWPH controls must be outside all map and row ports");
    let selected = plan(b, record, &capture, false);
    // The map packet encoder and TZ probe form an exact outer E;F;E^-1.
    // E is literal unitary and avoids PH/SW. Each replay donor is returned
    // inside one primitive before any subsequent original gate reads it. Thus ctrl(F) may be conjugated by E on
    // every shot: off-control it is identity on arbitrary E output.
    // Stop before the selected frame pair, preserving its full recipe.
    let limit = selected.as_ref()
        .map(|p| p.a.min(record.len()-p.y))
        .unwrap_or(record.len()/2);
    let shell = unitary_shell_len(record, limit);
    let nand_play = |b: &mut B, segment: &[G]| {
        let mut literal = Vec::new();
        for &gate in segment {
            if let G::RowAdd(id, inv) = gate {
                let row = capture.rows.get(&id).expect("missing classic row");
                assert!(row_allowed(row, &outside));
                b.begin(); row_add::emit(b,row,inv); let row_record=b.end();
                for g in row_record {
                    assert!(allowed_outside(g,&capture,&outside));
                    literal.push(unitary(g).expect("classic row must be literal"));
                }
            } else { literal.push(gate); }
        }
        for gate in literal {
            let gate=unitary(gate).expect("local NAND requires a literal primitive");
            let mut held=vec![ph,sw];
            match gate {
                G::X(t)=>held.push(t),
                G::Cx(a,t)|G::Swap(a,t)=>held.extend([a,t]),
                G::Ccx(a,c,t)=>held.extend([a,c,t]),
                _=>unreachable!(),
            }
            let mut work=Vec::new();
            for &q in universe {
                if !held.contains(&q)&&!work.contains(&q){work.push(q);if work.len()==2{break;}}
            }
            assert_eq!(work.len(),2,"local NAND needs two restored, nonoperand donors");
            // The protected API's outside-record condition is satisfied for
            // this ONE-gate record. Its returned helpers may be operands of
            // later original gates; no state is retained across this call.
            b.play_ctrl_nand2(&[gate],ph,sw,work[0],work[1]);
        }
    };
    b.play(&record[..shell],false);
    if let Some(plan) = selected {
        nand_play(b,&record[shell..plan.a]);
        b.play(&plan.unitary,false);
        nand_play(b,&record[plan.b..plan.x]);
        b.play(&plan.unitary,true);
        nand_play(b,&record[plan.y..record.len()-shell]);
    } else { nand_play(b,&record[shell..record.len()-shell]); }
    b.play(&record[..shell],true);
}

