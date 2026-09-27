//! Allocation-aware replay attribution carried through every simplifier.
use super::*;
use crate::circuit::NO_BIT;

const NONE: u16 = u16::MAX;
const PARTS: usize = 7;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(u8)]
pub(in super::super) enum Part {
    MainAdd,
    Fold,
    FErase,
    BErase,
    PrefixErase,
    Selector,
    #[default]
    Other,
}

#[derive(Clone, Copy, Debug)]
struct Tag {
    round: u16,
    part: Part,
}

impl Default for Tag {
    fn default() -> Self {
        Self {
            round: NONE,
            part: Part::Other,
        }
    }
}

thread_local! {
    static CURRENT: Cell<Tag> = Cell::new(Tag::default());
    static DIRECTION: Cell<&'static str> = const { Cell::new("-") };
}

pub(in super::super) struct Direction(&'static str);
impl Drop for Direction {
    fn drop(&mut self) {
        DIRECTION.set(self.0);
    }
}
pub(in super::super) fn direction(multiply: bool) -> Direction {
    Direction(DIRECTION.replace(if multiply { "mul" } else { "div" }))
}

pub(in super::super) struct Scope(Tag);
impl Drop for Scope {
    fn drop(&mut self) {
        CURRENT.set(self.0);
    }
}
pub(in super::super) fn part(part: Part) -> Scope {
    let old = CURRENT.get();
    CURRENT.set(Tag { part, ..old });
    Scope(old)
}
pub(in super::super) fn default_part(value: Part) -> Scope {
    part(if CURRENT.get().part == Part::Other {
        value
    } else {
        CURRENT.get().part
    })
}

#[derive(Debug)]
struct Row {
    direction: &'static str,
    round: usize,
    path: &'static str,
    entry: u32,
    peak: u32,
    bounds: Vec<(usize, usize)>,
    prefix: usize,
    fold_width: usize,
    saving: Option<f64>,
    candidate_saving: Option<f64>,
    sign: Option<QubitId>,
}

struct Site {
    kind: &'static str,
    direction: &'static str,
    round: Option<usize>,
    width: usize,
    full: usize,
    seeded: bool,
    location: &'static str,
}

#[derive(Default)]
pub(super) struct Trace {
    tags: Vec<Tag>,
    rows: Vec<Row>,
    sites: Vec<Site>,
    pending: Option<(char, usize, usize, usize)>,
    rewrite: Option<(Vec<Tag>, usize)>,
    division_words: Option<(Vec<QubitId>, Vec<QubitId>)>,
}

impl Trace {
    pub(super) fn peak(&mut self, active: u32) {
        let tag = CURRENT.get();
        if tag.round != NONE {
            let row = &mut self.rows[tag.round as usize];
            row.peak = row.peak.max(active);
        }
    }
    pub(super) fn record(&mut self, active: u32, index: usize) {
        assert_eq!(self.tags.len(), index);
        self.tags.push(CURRENT.get());
        self.peak(active);
    }
    pub(super) fn begin_rewrite(&mut self, len: usize) {
        assert_eq!(self.tags.len(), len);
        assert!(self.rewrite.is_none());
        self.rewrite = Some((
            std::mem::replace(&mut self.tags, Vec::with_capacity(len)),
            0,
        ));
    }
    pub(super) fn rewritten_op(&mut self, len: usize) {
        let (input, index) = self.rewrite.as_mut().unwrap();
        let added = len.checked_sub(self.tags.len()).unwrap();
        assert!(added <= 2, "rewrite emitted more than two operations");
        self.tags.extend(std::iter::repeat_n(input[*index], added));
        *index += 1;
    }
    pub(super) fn end_rewrite(&mut self, len: usize) {
        let (input, index) = self.rewrite.take().unwrap();
        assert_eq!(input.len(), index);
        assert_eq!(self.tags.len(), len);
    }
    pub(super) fn append_tail(&mut self, count: usize) {
        self.tags.extend(std::iter::repeat_n(Tag::default(), count));
    }
}

pub(in super::super) fn round(
    round: usize,
    path: &'static str,
    active: u32,
    fold_width: usize,
) -> Scope {
    let old = CURRENT.get();
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            assert_eq!(old.round, NONE, "nested replay round");
            let id = u16::try_from(trace.replay.rows.len()).unwrap();
            assert_ne!(id, NONE);
            trace.replay.rows.push(Row {
                direction: DIRECTION.get(),
                round,
                path,
                entry: active,
                peak: active,
                bounds: Vec::new(),
                prefix: 0,
                fold_width,
                saving: None,
                candidate_saving: None,
                sign: None,
            });
            CURRENT.set(Tag {
                round: id,
                part: Part::Other,
            });
        }
    });
    Scope(old)
}

pub(in super::super) fn division_operands(sign: QubitId, coefficient: &[QubitId], numerator: &[QubitId]) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let tag = CURRENT.get();
            assert_ne!(tag.round, NONE, "division operands outside a replay round");
            trace.replay.rows[tag.round as usize].sign = Some(sign);
            if let Some((known_coefficient, known_numerator)) = &trace.replay.division_words {
                assert_eq!(known_coefficient, coefficient);
                assert_eq!(known_numerator, numerator);
            } else {
                trace.replay.division_words = Some((coefficient.to_vec(), numerator.to_vec()));
            }
        }
    });
}

pub(in super::super) fn plan(
    path: &'static str,
    bounds: &[(usize, usize)],
    prefix: usize,
    saving: Option<f64>,
) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let tag = CURRENT.get();
            if tag.round != NONE {
                let row = &mut trace.replay.rows[tag.round as usize];
                row.path = path;
                row.bounds = bounds.to_vec();
                row.prefix = prefix;
                row.saving = saving;
            }
        }
    });
}

pub(in super::super) fn candidate_saving(saving: f64) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let tag = CURRENT.get();
            if tag.round != NONE {
                trace.replay.rows[tag.round as usize].candidate_saving = Some(saving);
            }
        }
    });
}

pub(in super::super) fn record_replay_site(kind: char, round: usize, pos: usize, width: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            if kind == 'K' {
                trace.replay.sites.push(Site {
                    kind: "K-depth",
                    direction: DIRECTION.get(),
                    round: Some(round),
                    width,
                    full: pos,
                    seeded: false,
                    location: "pingpong::depth",
                });
            } else {
                assert!(trace
                    .replay
                    .pending
                    .replace((kind, round, pos, width))
                    .is_none());
            }
        }
    });
}

pub(in super::super) fn site(
    kind: &'static str,
    width: usize,
    full: usize,
    seeded: bool,
    location: &'static str,
) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let tag = CURRENT.get();
            let round = (tag.round != NONE).then(|| trace.replay.rows[tag.round as usize].round);
            trace.replay.sites.push(Site {
                kind,
                direction: DIRECTION.get(),
                round,
                width,
                full,
                seeded,
                location,
            });
        }
    });
}

pub(in super::super) fn walk_guard(round: usize, width: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            trace.replay.sites.push(Site {
                kind: "walk-width",
                direction: DIRECTION.get(),
                round: Some(round),
                width,
                full: 259,
                seeded: false,
                location: "pingpong::value_width/shrink_to",
            });
        }
    });
}

pub(in super::super) fn compare(width: usize, seeded: bool, location: &'static str) -> Scope {
    let mut kind = Part::PrefixErase;
    let mut label = "exact-local-compare";
    let mut full = width;
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            if let Some((pending, _, pos, recorded_width)) = trace.replay.pending.take() {
                assert_eq!(width, recorded_width);
                kind = if pending == 'B' {
                    Part::BErase
                } else {
                    Part::FErase
                };
                label = if pending == 'B' {
                    "B-compare"
                } else {
                    "F-compare"
                };
                full = pos;
                let tag = CURRENT.get();
                if pending == 'B' && tag.round != NONE {
                    let row = &trace.replay.rows[tag.round as usize];
                    if let Some(&(lo, hi)) = row.bounds.iter().find(|&&(_, hi)| hi == pos) {
                        full = hi - lo;
                    }
                }
            } else if location.ends_with("modular.rs")
                && width == super::super::required_env::<usize>("ERASE_COMPARE")
            {
                label = "shell-square-compare";
                full = 256;
                kind = Part::FErase;
            }
        }
    });
    site(label, width, full, seeded, location);
    part(kind)
}

#[derive(Default)]
pub(super) struct Census {
    trace: Trace,
    counts: Vec<[[u64; 2]; PARTS]>,
    unattributed: u64,
}

pub(super) struct DivisionStep {
    pub(super) round: usize,
    pub(super) path: &'static str,
    pub(super) sign: QubitId,
    pub(super) ops: Range<usize>,
}

impl Census {
    pub(super) fn division_words(&self) -> (&[QubitId], &[QubitId]) {
        let (coefficient, numerator) = self.trace.division_words.as_ref()
            .expect("no division-register metadata");
        (coefficient, numerator)
    }

    pub(super) fn division_steps(&self) -> Vec<DivisionStep> {
        let mut ranges: Vec<Option<Range<usize>>> = vec![None; self.trace.rows.len()];
        for (index, tag) in self.trace.tags.iter().enumerate() {
            if tag.round == NONE || self.trace.rows[tag.round as usize].sign.is_none() {
                continue;
            }
            let range = ranges[tag.round as usize].get_or_insert(index..index);
            assert_eq!(range.end, index, "replay round is not contiguous");
            range.end = index + 1;
        }
        self.trace.rows.iter().zip(ranges).filter_map(|(row, ops)| {
            Some(DivisionStep {
                round: row.round, path: row.path, sign: row.sign?, ops: ops?,
            })
        }).collect()
    }

    pub(super) fn new(ops: &[Op], phases: &[Phase], trace: Trace) -> Self {
        // Hand-built phase-only regression fixtures have no replay metadata.
        if trace.tags.is_empty() {
            return Self::default();
        }
        assert_eq!(trace.tags.len(), ops.len());
        assert!(trace.pending.is_none());
        let mut counts = vec![[[0; 2]; PARTS]; trace.rows.len()];
        let mut depth = 0usize;
        let mut unattributed = 0;
        for ((op, tag), &phase) in ops.iter().zip(&trace.tags).zip(phases) {
            match op.kind {
                OperationType::PushCondition => depth += 1,
                OperationType::PopCondition => depth = depth.checked_sub(1).unwrap(),
                OperationType::CCX | OperationType::CCZ => {
                    if tag.round != NONE {
                        assert_eq!(phase, Phase::Replay);
                        counts[tag.round as usize][tag.part as usize]
                            [usize::from(depth > 0 || op.c_condition != NO_BIT)] += 1;
                    } else if phase == Phase::Replay {
                        unattributed += 1;
                    }
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0);
        Self {
            trace,
            counts,
            unattributed,
        }
    }

    pub(super) fn print(&self, phase_total: u64) {
        let cap = super::super::pingpong::walk_max_qubits() as u32;
        println!("REPLAY_ROUNDS_BEGIN");
        println!("direction\tround\tpath\tlive_entry\tfree_entry\tpeak_live\tfree_at_peak\tfold_width\tbounds\tprefix\tmodel_saving\tretained_candidate_saving\tmain_U\tmain_C\tfold_U\tfold_C\tF_U\tF_C\tB_U\tB_C\tprefix_U\tprefix_C\tselector_U\tselector_C\tother_U\tother_C\temitted\tU_plus_half_C");
        let mut sum = 0;
        for (row, counts) in self.trace.rows.iter().zip(&self.counts) {
            let flat: Vec<_> = counts.iter().flat_map(|p| p.iter()).copied().collect();
            let unconditioned: u64 = counts.iter().map(|p| p[0]).sum();
            let conditioned: u64 = counts.iter().map(|p| p[1]).sum();
            let total = unconditioned + conditioned;
            sum += total;
            println!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.1}",
                row.direction,
                row.round,
                row.path,
                row.entry,
                cap.checked_sub(row.entry).unwrap(),
                row.peak,
                cap.checked_sub(row.peak).unwrap(),
                row.fold_width,
                row.bounds
                    .iter()
                    .map(|(a, b)| format!("{a}:{b}"))
                    .collect::<Vec<_>>()
                    .join(","),
                row.prefix,
                row.saving.map_or("-".into(), |s| format!("{s:.1}")),
                row.candidate_saving
                    .map_or("-".into(), |s| format!("{s:.1}")),
                flat.iter()
                    .map(u64::to_string)
                    .collect::<Vec<_>>()
                    .join("\t"),
                total,
                unconditioned as f64 + conditioned as f64 / 2.0
            );
        }
        println!("REPLAY_ROUNDS_END");
        assert_eq!(sum + self.unattributed, phase_total);
        println!("REPLAY_ROUNDS_TOTAL rows={} attributed={} outside_rounds={} replay_phase={} (U+0.5C is a model, not executed counts)",
            self.trace.rows.len(), sum, self.unattributed, phase_total);
        for direction in ["div", "mul"] {
            let mut rounds: Vec<_> = self
                .trace
                .rows
                .iter()
                .filter(|r| r.direction == direction && r.path != "endpoint")
                .map(|r| r.round)
                .collect();
            rounds.sort_unstable();
            let (widths, mul) = super::super::pingpong::measurement_walk_widths();
            assert_eq!(
                rounds,
                (0..if direction == "div" {
                    widths.len()
                } else {
                    mul
                })
                    .collect::<Vec<_>>()
            );
        }
        println!("APPROXIMATION_SITES_BEGIN");
        println!("kind\tdirection\tround\twidth\tfull_width\tseeded\tlocation");
        for site in &self.trace.sites {
            println!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                site.kind,
                site.direction,
                site.round.map_or("-".into(), |r| r.to_string()),
                site.width,
                site.full,
                site.seeded,
                site.location
            );
        }
        println!("APPROXIMATION_SITES_END");
    }
}

#[test]
fn division_boundaries_follow_deleted_and_expanded_operations() {
    use super::super::affine_simplify::Rewrite;
    let capture = Capture::start();
    let mut op = Op::empty();
    op.kind = OperationType::CCX;
    op.q_control1 = QubitId(0);
    op.q_control2 = QubitId(1);
    op.q_target = QubitId(2);
    {
        let _direction = direction(false);
        let _phase = scope(Phase::Replay);
        let _round = round(2, "fixture", 4, 3);
        division_operands(QubitId(2), &[QubitId(0)], &[QubitId(1)]);
        record_op("pp_div_replay", 4, 0);
        record_op("pp_div_replay", 4, 1);
    }
    begin_rewrite(2);
    let mut output = Vec::new();
    Rewrite::Drop.emit(op, &mut output);
    Rewrite::ComplementedCx(QubitId(3)).emit(op, &mut output);
    end_rewrite(2);
    let trace = capture.finish();
    let census = Census::new(&output, &trace.tags, trace.replay);
    let steps = census.division_steps();
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0].round, 2);
    assert_eq!(steps[0].ops, 0..2);
    assert_eq!(steps[0].sign, QubitId(2));
    assert_eq!(census.division_words(), (&[QubitId(0)][..], &[QubitId(1)][..]));
}

#[test]
fn round_tags_survive_rewrites_and_parts_restore() {
    use super::super::affine_simplify::Rewrite;
    let capture = Capture::start();
    let mut ccx = Op::empty();
    ccx.kind = OperationType::CCX;
    ccx.q_control2 = QubitId(0);
    ccx.q_control1 = QubitId(1);
    ccx.q_target = QubitId(2);
    {
        let _direction = direction(false);
        let _phase = scope(Phase::Replay);
        let _round = round(7, "plain", 1200, 55);
        {
            let _main = default_part(Part::MainAdd);
            record_op("pp_div_replay", 1201, 0);
            {
                let _fold = part(Part::Fold);
                let _nested = default_part(Part::MainAdd);
                record_peak("pp_div_replay", 1251);
                record_op("pp_div_replay", 1240, 1);
            }

            record_op("pp_div_replay", 1201, 2);
        }
        record_replay_site('F', 7, 256, 20);
        {
            let _compare = compare(20, true, "fixture");
            record_op("pp_div_replay", 1220, 3);
        }
    }
    assert_eq!(CURRENT.get().round, NONE);
    begin_rewrite(4);
    let mut ops = Vec::new();
    Rewrite::Drop.emit(ccx, &mut ops);
    Rewrite::Keep.emit(ccx, &mut ops);
    Rewrite::ComplementedCx(QubitId(1)).emit(ccx, &mut ops);
    let mut conditional = ccx;
    conditional.c_condition = crate::circuit::BitId(0);
    Rewrite::Keep.emit(conditional, &mut ops);
    end_rewrite(4);
    let trace = capture.finish();
    let result = Census::new(&ops, &trace.tags, trace.replay);
    assert_eq!(result.counts[0][Part::MainAdd as usize], [0, 0]);
    assert_eq!(result.counts[0][Part::Fold as usize], [1, 0]);
    assert_eq!(result.counts[0][Part::FErase as usize], [0, 1]);
    assert_eq!(result.trace.rows[0].peak, 1251);
    assert!(result.trace.sites[0].seeded);
    assert!(result.trace.pending.is_none());
}
