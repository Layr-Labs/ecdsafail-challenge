//! Apply three reverse-direction NCT folds to fixed source regions, then cancel
//! adjacent identical Toffoli/CCZ pairs. No extra wires or full-size operations
//! vector. The existing forward fold and normal physical execution stay in order.
use super::gate_fold::{lower_configured, Counts};
use crate::circuit::{Op, OperationType as K};
use std::collections::VecDeque;

pub(super) const REGION: usize = 1 << 21;
const BLOCK: usize = 1 << 14;
const LOOKAHEAD: usize = 96;
const ROUNDS: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Mode {
    Wide,
    Moderate,
    NoGrowth,
}

impl Mode {
    fn growth(self, n: usize) -> usize {
        match self {
            Self::Wide => n / 32,
            Self::Moderate => n / 128,
            Self::NoGrowth => 0,
        }
    }
}

pub(super) fn max_growth(n: usize) -> usize {
    let mut m = n;
    for _ in 0..ROUNDS {
        m += Mode::Wide.growth(m);
    }
    m - n
}

struct Stage {
    input: Vec<Op>,
    emitted: Vec<Op>,
    total: usize,
    stats: Counts,
}

impl Stage {
    fn new() -> Self {
        Self {
            input: Vec::with_capacity(BLOCK),
            emitted: Vec::with_capacity(BLOCK + BLOCK / 32),
            total: 0,
            stats: Counts::default(),
        }
    }
}

pub(super) struct Workspace {
    stages: [Stage; ROUNDS],
    burst: Vec<Op>,
    unread: VecDeque<Op>,
}

impl Workspace {
    pub(super) fn new() -> Self {
        Self {
            stages: std::array::from_fn(|_| Stage::new()),
            burst: Vec::new(),
            unread: VecDeque::new(),
        }
    }
}

fn flush(stages: &mut [Stage], mode: Mode, burst: &mut Vec<Op>) {
    let (stage, next) = stages.split_first_mut().unwrap();
    if stage.input.is_empty() {
        return;
    }
    stage.emitted.clear();
    lower_configured(
        &stage.input,
        LOOKAHEAD,
        mode.growth(stage.input.len()),
        |gate| stage.emitted.push(gate),
        &mut stage.stats,
    );
    stage.input.clear();
    stage.total += stage.emitted.len();
    if next.is_empty() {
        burst.extend_from_slice(&stage.emitted);
    } else {
        let mut tail = &stage.emitted[..];
        while !tail.is_empty() {
            let count = tail.len().min(BLOCK - next[0].input.len());
            next[0].input.extend_from_slice(&tail[..count]);
            tail = &tail[count..];
            if next[0].input.len() == BLOCK {
                flush(next, mode, burst);
            }
        }
    }
}

trait ReverseIo {
    fn next(&mut self) -> Op;
    fn write(&mut self, gates: &[Op]);
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Run {
    pub(super) lengths: [usize; ROUNDS],
    pub(super) folds: [Counts; ROUNDS],
    pub(super) output: usize,
    pub(super) peak_lead: usize,
}

fn run<I: ReverseIo>(
    stages: &mut [Stage; ROUNDS],
    burst: &mut Vec<Op>,
    io: &mut I,
    n: usize,
    mode: Mode,
) -> Run {
    for stage in stages.iter_mut() {
        assert!(stage.input.is_empty());
        stage.stats = Counts::default();
        stage.total = 0;
    }
    let mut result = Run::default();
    let mut consumed = 0;
    let mut deliver = |burst: &[Op], consumed: usize, io: &mut I| {
        result.output += burst.len();
        let lead = result.output.min(n).saturating_sub(consumed);
        result.peak_lead = result.peak_lead.max(lead);
        io.write(burst);
    };
    while consumed < n {
        let end = n.min(consumed + BLOCK);
        for _ in consumed..end {
            stages[0].input.push(io.next());
        }
        consumed = end;
        burst.clear();
        flush(stages, mode, burst);
        deliver(burst, consumed, io);
    }
    // Flush the last partial input of each stage after its predecessor has
    // delivered its complete tail. Thus every stage has independent boundaries.
    for i in 1..ROUNDS {
        burst.clear();
        flush(&mut stages[i..], mode, burst);
        deliver(burst, n, io);
    }
    result.lengths = std::array::from_fn(|i| stages[i].total);
    result.folds = std::array::from_fn(|i| stages[i].stats);
    assert_eq!(result.lengths[ROUNDS - 1], result.output);
    result
}

struct Plan<'a> {
    reverse: std::iter::Rev<std::slice::Iter<'a, Op>>,
}
impl ReverseIo for Plan<'_> {
    fn next(&mut self) -> Op {
        *self.reverse.next().unwrap()
    }
    fn write(&mut self, _: &[Op]) {}
}

struct Move<'a> {
    window: &'a mut [Op],
    n: usize,
    loaded: usize,
    written: usize,
    unread: &'a mut VecDeque<Op>,
}

impl ReverseIo for Move<'_> {
    fn next(&mut self) -> Op {
        if let Some(gate) = self.unread.pop_front() {
            return gate;
        }
        self.loaded += 1;
        self.window[self.window.len() - self.loaded]
    }
    fn write(&mut self, gates: &[Op]) {
        let end = self.window.len();
        // Copy each still-unread input threatened by this batch before writing.
        let required = self.n.min(self.written + gates.len());
        while self.loaded < required {
            self.loaded += 1;
            self.unread.push_back(self.window[end - self.loaded]);
        }
        let old = self.written;
        self.written += gates.len();
        let dest = &mut self.window[end - self.written..end - old];
        for (slot, &gate) in dest.iter_mut().rev().zip(gates) {
            *slot = gate;
        }
    }
}

pub(super) struct Region {
    pub(super) mode: Mode,
    pub(super) run: Run,
    pub(super) output: usize,
    pub(super) charged_pair_gates: u64,
}

// Both identical charged gates are self-inverse. Neither writes condition bits
// or changes the captured guard, even when the same explicit condition is set.
// Non-gate records occupy positions on the stack and are always retained.
fn cancel_adjacent(gates: &mut [Op]) -> usize {
    let mut written = 0;
    for i in 0..gates.len() {
        let gate = gates[i];
        if written > 0 && matches!(gate.kind, K::CCX | K::CCZ) && gate == gates[written - 1] {
            written -= 1;
        } else {
            gates[written] = gate;
            written += 1;
        }
    }
    written
}

// The source occupies the RIGHTMOST n slots of window. Use only credit from
// prior completed regions. Callers may omit credit beyond max_growth(n).
pub(super) fn region(space: &mut Workspace, window: &mut [Op], n: usize) -> Region {
    assert!(n <= REGION && n <= window.len());
    let credit = window.len() - n;
    let source = &window[credit..];
    let mut mode = Mode::Wide;
    let mut selected_plan = None;
    let mut reserve = max_growth(n);
    if credit < reserve {
        for candidate in [Mode::Wide, Mode::Moderate, Mode::NoGrowth] {
            let mut plan = Plan {
                reverse: source.iter().rev(),
            };
            let planned = run(&mut space.stages, &mut space.burst, &mut plan, n, candidate);
            if planned.output <= window.len() {
                mode = candidate;
                reserve = planned.peak_lead;
                selected_plan = Some(planned);
                break;
            }
        }
        assert!(selected_plan.is_some());
    }
    // The sum of the per-block expansion bounds cannot exceed the bound
    // obtained by applying the same three growth bounds to any entire prefix.
    assert!(space.unread.is_empty());
    space.unread.reserve_exact(reserve);
    let mut copy = Move {
        window,
        n,
        loaded: 0,
        written: 0,
        unread: &mut space.unread,
    };
    let actual = run(&mut space.stages, &mut space.burst, &mut copy, n, mode);
    assert_eq!(copy.loaded, n);
    assert_eq!(copy.written, actual.output);
    assert!(copy.unread.is_empty() && actual.peak_lead <= reserve);
    if let Some(plan) = selected_plan {
        assert_eq!(actual, plan);
    }
    let start = window.len() - actual.output;
    if start != 0 {
        window.copy_within(start.., 0);
    }
    let output = cancel_adjacent(&mut window[..actual.output]);
    Region {
        mode,
        run: actual,
        output,
        charged_pair_gates: (actual.output - output) as u64,
    }
}

#[derive(Default, Debug)]
pub(super) struct Summary {
    pub(super) input: usize,
    pub(super) output: usize,
    pub(super) regions: [usize; 3],
    pub(super) rounds_saved: [u64; ROUNDS],
    pub(super) adjacent_saved: u64,
    pub(super) peak_lead: usize,
}

pub(super) fn apply_in_place(ops: &mut Vec<Op>) -> Summary {
    let original = ops.len();
    let mut space = Workspace::new();
    let mut result = Summary {
        input: original,
        ..Summary::default()
    };
    let mut start = 0;
    while start < original {
        let end = original.min(start + REGION);
        let change = region(&mut space, &mut ops[result.output..end], end - start);
        result.regions[change.mode as usize] += 1;
        for (acc, step) in result.rounds_saved.iter_mut().zip(&change.run.folds) {
            *acc += step.saved_ccx;
        }
        result.adjacent_saved += change.charged_pair_gates;
        result.peak_lead = result.peak_lead.max(change.run.peak_lead);
        result.output += change.output;
        start = end;
    }
    ops.truncate(result.output);
    result
}
