//! Source-selected diagnostic for one complete unhosted K1 frame.
//! Qualified PAD_ADD is reused unchanged. No production dispatch calls this module.
use super::builder::{B, G};
use super::k1_pad_add::{self as pad, Enable, Exclusions, Literal};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone)]
pub(crate) struct Layout {
    pub ring: Vec<QubitId>,
    pub q: Vec<QubitId>,
    pub payload: Vec<QubitId>,
    pub y: Vec<QubitId>,
    pub scratch: Vec<QubitId>,
    pub ph: QubitId,
}
impl Layout {
    pub fn allocate(b: &mut B) -> Self {
        assert_eq!(b.width(), 0);
        let ring = b.alloc_n(257);
        let q = b.alloc_n(128);
        let payload = b.alloc_n(258);
        let y = b.alloc_n(7);
        let sum = b.alloc_n(5);
        let tag = b.alloc();
        let cut = b.alloc();
        let toggle = b.alloc();
        let prefix = b.alloc();
        let ph = b.alloc();
        let scratch = [vec![tag], sum, vec![cut, toggle, prefix]].concat();
        assert_eq!((b.width(), prefix.0, ph.0), (660, 658, 659));
        Self {
            ring,
            q,
            payload,
            y,
            scratch,
            ph,
        }
    }
    pub fn m(&self) -> &[QubitId] {
        &self.scratch[1..8]
    }
    pub fn e(&self) -> QubitId {
        self.y[6]
    }
    pub fn g(&self) -> QubitId {
        self.scratch[8]
    }
}
pub(crate) struct Selection {
    pub original: Vec<G>,
    pub rotation: Vec<G>,
    pub llo: usize,
    pub lhi: usize,
    pub source_bound: usize,
    pub target_bound: usize,
    pub tail: usize,
    pub emax: usize,
    pub smax: (usize, usize),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mutation {
    None,
    SameEnable,
    HighSlice,
    Reversal,
    Donor,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FrameError {
    EarlyCancellation,
    Selector,
    Layout,
    Capacity { row: usize },
}
#[derive(Clone, Debug)]
pub(crate) struct Row {
    pub i: usize,
    pub variable: bool,
    pub source: Vec<QubitId>,
    pub target: Vec<QubitId>,
    pub padding: Vec<QubitId>,
    pub donors: Vec<QubitId>,
    pub controls: Vec<QubitId>,
    pub surplus: usize,
    // Half-open literal positions for one complete PAD_ADD, excluding E query.
    pub begin: usize,
    pub end: usize,
}
pub(crate) struct Frame {
    pub tape: Vec<G>,
    pub rows: Vec<Row>,
}
#[derive(Clone, Copy, Default)]
pub(crate) enum Route {
    #[default]
    Original,
    PadAdd,
}
/// Explicit diagnostic selection. The default returns the exact parent tape;
/// production still has no callsite to either diagnostic route.
pub(crate) fn diagnostic(
    b: &mut B,
    l: &Layout,
    s: &Selection,
    route: Route,
) -> Result<Frame, FrameError> {
    match route {
        Route::Original => Ok(Frame {
            tape: s.original.clone(),
            rows: vec![],
        }),
        Route::PadAdd => record(b, l, s, Mutation::None),
    }
}

fn eq(b: &mut B, l: &Layout, value: usize) {
    let controls: Vec<_> = l
        .m()
        .iter()
        .enumerate()
        .map(|(j, &q)| (q, value >> j & 1 == 0))
        .collect();
    // Seven literal controls, zero clean-prefix owners; physical ring order.
    super::mask::mc_xor(b, &controls, l.e(), &[], &l.ring);
}
pub(crate) fn record(
    b: &mut B,
    l: &Layout,
    s: &Selection,
    mutation: Mutation,
) -> Result<Frame, FrameError> {
    // Capture must precede cancellation. Typed fail-closed prerequisite;
    // this is not a claim that legal cancellation changes semantics.
    if b.cancel_simple_pairs || b.cancel_commuting_pairs || b.global_cancel {
        return Err(FrameError::EarlyCancellation);
    }
    if (s.llo, s.lhi, s.source_bound, s.target_bound, s.tail, s.emax) != (1, 122, 122, 128, 40, 31)
        || b.force_unitary_and
        || b.no_rows
    {
        return Err(FrameError::Selector);
    }
    let occupied: Vec<_> = l
        .ring
        .iter()
        .chain(&l.q)
        .chain(&l.payload)
        .chain(&l.y)
        .chain(&l.scratch)
        .copied()
        .chain([l.ph])
        .collect();
    if (
        l.ring.len(),
        l.q.len(),
        l.y.len(),
        l.scratch.len(),
        b.width(),
    ) != (257, 128, 7, 9, 660)
        || occupied.len() != 660
        || occupied.iter().collect::<BTreeSet<_>>().len() != 660
    {
        return Err(FrameError::Layout);
    }
    let v: Vec<_> = (0..257).map(|i| l.ring[(i + 256) % 257]).collect();
    let mut rows = Vec::new();
    // Resolve every live-port exclusion before recording, without selecting
    // input values or changing physical donor order.
    for i in (s.llo..256).rev() {
        let nm = (s.target_bound - 1).min(256 - i);
        let n = nm.min(s.source_bound - 1);
        let h = nm + s.tail.min(256 - i - nm) - n;
        let variable = i < s.lhi;
        let target = v[i + 1..i + 1 + n + h].to_vec();
        let controls = if variable {
            vec![l.e(), v[i]]
        } else {
            vec![v[i]]
        };
        let pool: Vec<_> = l
            .ring
            .iter()
            .copied()
            .filter(|q| !target.contains(q) && !controls.contains(q))
            .collect();
        let needed = usize::from(variable);
        if pool.len() < h + needed + 42 {
            return Err(FrameError::Capacity { row: i });
        }
        rows.push(Row {
            i,
            variable,
            source: l.q[1..1 + n].to_vec(),
            target,
            padding: pool[..h].to_vec(),
            donors: pool[h..h + needed].to_vec(),
            controls,
            surplus: pool.len() - h - needed,
            begin: 0,
            end: 0,
        });
    }
    b.begin();
    b.play(&s.rotation, false);
    let mut begun = false;
    for row in &mut rows {
        if row.variable {
            if !begun {
                b.x(l.e());
                begun = true;
            }
            eq(b, l, row.i);
        }
        let enable = Enable::Literals(
            row.controls
                .iter()
                .map(|&wire| Literal {
                    wire,
                    positive: true,
                })
                .collect(),
        );
        let held: Vec<_> = occupied
            .iter()
            .copied()
            .filter(|q| {
                !row.source.contains(q)
                    && !row.target.contains(q)
                    && !row.padding.contains(q)
                    && !row.donors.contains(q)
                    && !row.controls.contains(q)
            })
            .collect();
        assert!(held.contains(&l.q[0]) && held.contains(&l.ph) && held.contains(&l.g()));
        let exclusions = Exclusions {
            held: &held,
            forbidden: &[],
        };
        let tape = if row.i == 89 && mutation != Mutation::None {
            let which = match mutation {
                Mutation::SameEnable => pad::Mutation::MismatchedEnable,
                Mutation::HighSlice => pad::Mutation::TruncatedTarget,
                Mutation::Reversal => pad::Mutation::ForwardCorrection,
                Mutation::Donor => pad::Mutation::MissingDirtyEcho,
                Mutation::None => unreachable!(),
            };
            pad::mutant_record(
                b,
                &row.source,
                &row.target,
                &row.padding,
                &enable,
                &row.donors,
                exclusions,
                which,
            )
            .expect("qualified primitive contract")
        } else {
            pad::pad_add_f(
                b,
                &row.source,
                &row.target,
                &row.padding,
                &enable,
                &row.donors,
                exclusions,
            )
            .expect("qualified primitive contract")
        };
        row.begin = b.recording_len();
        b.play(&tape, false);
        row.end = b.recording_len();
    }
    if begun {
        eq(b, l, s.llo - 1);
    }
    b.play(&s.rotation, true);
    let tape = b.end();
    assert!(tape
        .iter()
        .all(|g| matches!(g, G::X(..) | G::Cx(..) | G::Ccx(..) | G::Swap(..))));
    assert_eq!(b.width(), 660);
    Ok(Frame { tape, rows })
}
