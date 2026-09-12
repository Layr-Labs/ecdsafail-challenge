//! Source-context specialization of stable truth-minus-one length predicates.
//! See analyses/nonterminal-prefix.md. This does not apply to arbitrary 9-bit
//! words, shift/epoch counters, address-transformed lengths, or standalone steps.
use super::{Graph, OperationType as K, PendingHmr, Reader, State};
use crate::circuit::QubitId;
use sha3::{Digest, Sha3_256};

const FORWARD: &[u8] = include_bytes!("stable_length_phase_forward_578.hir");
const INVERSE: &[u8] = include_bytes!("stable_length_phase_inverse_578.hir");
const ARCHIVE_SHA3: [u8; 32] = [
    222, 57, 97, 75, 106, 46, 200, 89, 138, 252, 37, 91, 146, 225, 13, 147, 62, 8, 231, 154, 11,
    126, 198, 31, 145, 78, 62, 133, 98, 253, 121, 75,
];
const FRAME: [usize; 44] = [
    0, 1, 3, 531, 532, 533, 534, 535, 536, 537, 538, 539, 549, 550, 551, 552, 553, 554, 555, 556,
    557, 540, 541, 542, 543, 544, 545, 546, 547, 548, 559, 560, 561, 562, 563, 564, 565, 566, 567,
    568, 569, 570, 571, 572,
];
// Original record start, original byte start/end, stable high bit, XOR target.
const SPANS: [(usize, usize, usize, usize, usize); 4] = [
    (0, 0, 326, 539, 560),
    (36, 326, 652, 557, 561),
    (172, 1539, 1865, 557, 561),
    (208, 1865, 2191, 539, 560),
];

#[derive(Default)]
pub(super) struct Tracker {
    pub enabled: bool,
    pub direction: Option<bool>, // false forward, true inverse; direct sweep child only
    pub windows: [usize; 2],
    pub rewrites: usize,
    pub unknown_scratch: usize,
    pub capture_blocked: usize,
    pub boundary_blocked: usize,
    pub alias_blocked: usize,
}

pub(super) fn configure(state: &mut State, graph: &Graph<'_>, archive: &[u8]) {
    if std::env::var("Q834_STABLE_LENGTH_ZERO").ok().as_deref() == Some("0") {
        return;
    }
    let shape = (
        graph.root,
        graph.nodes.len(),
        graph.root_qubits,
        graph.root_bits,
    );
    assert!(matches!(shape, (2269, 2270, 835, 1280) | (2274, 2275, 835, 1280)),
        "stable-length source graph changed: {shape:?}");
    let digest: [u8; 32] = Sha3_256::digest(archive).into();
    assert_eq!(digest, ARCHIVE_SHA3, "stable-length source archive changed");
    state.lengths.enabled = true;
}

/// Bind the semantic promise to the pinned EEA sweep's immediate step calls.
/// Descendants (including the private CZ child) never inherit this admission.
pub(super) fn child_direction(
    state: &State,
    parent: usize,
    ordinal: usize,
    qs: usize,
    qlen: usize,
    cs: usize,
    clen: usize,
    child: usize,
    child_qs: usize,
    child_qlen: usize,
    child_cs: usize,
    child_clen: usize,
    condition_width: usize,
) -> Option<bool> {
    if !state.lengths.enabled
        || (qlen, clen, child_qlen, child_clen, condition_width) != (578, 256, 578, 1, 0)
    {
        return None;
    }
    let inverse = match parent {
        2261 if (146050..147670).contains(&ordinal) && (6..1130).contains(&child) => false,
        2263 if (18429..20049).contains(&ordinal) && (1132..2256).contains(&child) => true,
        _ => return None,
    };
    if state.cmap[child_cs] != state.cmap[cs] {
        return None;
    }
    for &local in &FRAME {
        let parent_local = match local {
            0 => 518,
            1 => 519,
            3 => 521,
            _ => local,
        };
        if state.qmap[child_qs + local] != state.qmap[qs + parent_local] {
            return None;
        }
    }
    Some(inverse)
}

pub(super) struct Window {
    op: usize,
    byte: usize,
}

pub(super) fn try_apply(
    state: &mut State,
    reader: &mut Reader<'_>,
    node: usize,
    op_index: usize,
    op_count: usize,
    qs: usize,
    qlen: usize,
    cs: usize,
    clen: usize,
    window: &mut Option<Window>,
) -> bool {
    if !state.lengths.enabled || (qlen, clen) != (578, 1) {
        return false;
    }
    let Some(inverse) = state.lengths.direction else {
        return false;
    };
    if window.as_ref().is_some_and(|w| op_index >= w.op + 244) {
        *window = None;
    }
    if window.is_none() {
        let pattern = if inverse { INVERSE } else { FORWARD };
        if op_count - op_index < 244
            || reader.data.get(reader.at..reader.at + pattern.len()) != Some(pattern)
        {
            return false;
        }
        // Scratch, metadata and phase flags must be distinct physical wires.
        let wires = FRAME.map(|q| state.qmap[qs + q]);
        if wires.contains(&QubitId(0)) || (0..44).any(|i| wires[i + 1..].contains(&wires[i])) {
            state.lengths.alias_blocked += 1;
            return false;
        }
        state.lengths.windows[inverse as usize] += 1;
        *window = Some(Window {
            op: op_index,
            byte: reader.at,
        });
    }
    let w = window.as_ref().unwrap();
    let Some(&(_, start, end, high, target)) = SPANS.iter().find(|s| w.op + s.0 == op_index) else {
        return false;
    };
    assert_eq!(
        reader.at,
        w.byte + start,
        "stable-length source boundary skipped"
    );
    if state.capture.is_some() || state.comparator_capture.is_some() {
        state.lengths.capture_blocked += 1;
        return false;
    }
    if state.retention.enabled
        && state.retention.locations[node].iter().any(|l| {
            [l.h, l.h + 4, l.re, l.re + 1, l.end]
                .into_iter()
                .any(|i| op_index < i && i < op_index + 36)
        })
    {
        state.lengths.boundary_blocked += 1;
        return false;
    }
    state.flush_raw();
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    if !(565..572).all(|q| state.proof.qubit_is_zero(state.qmap[qs + q].0 as usize)) {
        state.lengths.unknown_scratch += 1;
        return false;
    }
    let high = state.qmap[qs + high];
    let target = state.qmap[qs + target];
    let scratch = state.qmap[qs + 565];
    let classical = state.cmap[cs];
    let op = state.raw(K::CX);
    op.q_control1 = high;
    op.q_target = target;
    // The complete old v-chain corrects every HMR phase, hence its last outcome
    // is fresh and independent. Keep that observable classical write even when
    // the following caller reads it rather than overwriting it.
    let op = state.raw(K::Hmr);
    op.q_target = scratch;
    op.c_target = classical;
    reader.at = w.byte + end;
    state.lengths.rewrites += 1;
    true
}

#[cfg(test)]
#[path = "stable_lengths_tests.rs"]
mod tests;
