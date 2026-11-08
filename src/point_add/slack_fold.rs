//! Three local sweeps using a bounded portion of the operation vector's
//! preallocated capacity. Matching identities never need extra circuit wires.
use super::gate_fold::{lower_configured, Counts};
use crate::circuit::{Op, OperationType as K, NO_BIT};
#[path = "commuting_pairs.rs"]
mod commuting_pairs;
use commuting_pairs::Pairs;

const BLOCK: usize = 16_384;
const HORIZON: usize = 256;
const LOCAL_DIVISOR: usize = 32;
const MAX_SLACK: usize = 1 << 22;
const BURST: usize = 1024;

#[derive(Debug, Default)]
pub(super) struct Round {
    pub(super) input: usize,
    pub(super) output: usize,
    pub(super) headroom: usize,
    pub(super) peak_growth: usize,
    pub(super) limited_blocks: usize,
    pub(super) nct_saved: u64,
    pub(super) commuting_records: usize,
    pub(super) commuting_charged: u64,
}

#[derive(Debug, Default)]
pub(super) struct Summary {
    pub(super) input: usize,
    pub(super) output: usize,
    pub(super) headroom: usize,
    pub(super) always_saved: u64,
    pub(super) guarded_raw_saved: u64,
    pub(super) rounds: [Round; 3],
}

fn charge(ops: &[Op]) -> (u64, u64) {
    let (mut fixed, mut guarded, mut depth) = (0, 0, 0usize);
    for op in ops {
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth = depth.checked_sub(1).unwrap(),
            K::CCX | K::CCZ if depth == 0 && op.c_condition == NO_BIT => fixed += 1,
            K::CCX | K::CCZ => guarded += 1,
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    (fixed, guarded)
}

struct Buffers {
    source: Vec<Op>,
    output: Vec<Op>,
    pairs: Pairs,
}

impl Buffers {
    fn new() -> Self {
        Self {
            source: Vec::with_capacity(BLOCK),
            output: Vec::with_capacity(BLOCK + BLOCK / LOCAL_DIVISOR),
            pairs: Pairs::new(),
        }
    }
    fn lower(&mut self, reverse: bool, growth: usize) -> (u64, usize, u64) {
        self.output.clear();
        let mut stats = Counts::default();
        lower_configured(
            &self.source,
            HORIZON,
            growth,
            |g| self.output.push(g),
            &mut stats,
        );
        if reverse {
            self.output.reverse();
        }
        let (records, charged) = self.pairs.reduce(&mut self.output);
        (stats.saved_ccx, records, charged)
    }
}

fn sweep(ops: &mut Vec<Op>, buffers: &mut Buffers, reverse: bool, headroom: usize) -> Round {
    let n = ops.len();
    let storage = n + headroom;
    let mut stat = Round {
        input: n,
        headroom,
        ..Default::default()
    };
    assert!(storage <= ops.capacity() && headroom <= MAX_SLACK);
    ops.resize(storage, Op::empty());
    // For forward reading the unread source must be on the right of the
    // growing output. Reverse reading already starts beside vacant tail slots.
    if !reverse && headroom != 0 {
        ops.copy_within(..n, headroom);
    }
    let mut read = 0;
    let mut written = 0;
    while read < n {
        let count = (n - read).min(BLOCK);
        buffers.source.clear();
        if reverse {
            buffers
                .source
                .extend(ops[n - read - count..n - read].iter().rev());
        } else {
            buffers
                .source
                .extend_from_slice(&ops[headroom + read..headroom + read + count]);
        }
        read += count;
        // Distribute the bounded growth over the full sweep. Previously
        // removed records are immediately usable; BURST allows local spikes.
        let unlocked =
            ((((headroom as u128) * (read as u128) / (n as u128)) as usize) + BURST).min(headroom);
        let available = read + unlocked - written;
        assert!(available >= count);
        let ordinary = count / LOCAL_DIVISOR;
        let mut changes = buffers.lower(reverse, ordinary);
        if buffers.output.len() > available {
            changes = buffers.lower(reverse, ordinary.min(available - count));
            stat.limited_blocks += 1;
        }
        let out = buffers.output.len();
        assert!(out <= available);
        let dest = if reverse {
            storage - written - out
        } else {
            written
        };
        ops[dest..dest + out].copy_from_slice(&buffers.output);
        written += out;
        stat.peak_growth = stat.peak_growth.max(written.saturating_sub(read));
        stat.nct_saved += changes.0;
        stat.commuting_records += changes.1;
        stat.commuting_charged += changes.2;
    }
    if reverse && written != storage {
        ops.copy_within(storage - written..storage, 0);
    }
    ops.truncate(written);
    stat.output = written;
    stat
}

pub(super) fn apply(ops: &mut Vec<Op>) -> Summary {
    let original = ops.len();
    // Both the public builder's large vector and an exactly-sized Vec are
    // supported. The pass never reserves memory on the original Vec.
    let cap = ops.capacity();
    let address = ops.as_ptr();
    let slack = MAX_SLACK.min(original.div_ceil(256)).min(cap - original);
    let before = charge(ops);
    let mut buffers = Buffers::new();
    let mut summary = Summary {
        input: original,
        headroom: slack,
        ..Default::default()
    };
    for (i, reverse) in [false, true, false].into_iter().enumerate() {
        let ceiling = original + slack * (i + 1) / 3;
        let room = (ceiling - ops.len()).min(MAX_SLACK);
        summary.rounds[i] = sweep(ops, &mut buffers, reverse, room);
    }
    let after = charge(ops);
    summary.always_saved = before.0.checked_sub(after.0).unwrap();
    summary.guarded_raw_saved = before.1.checked_sub(after.1).unwrap();
    let counted = summary
        .rounds
        .iter()
        .map(|q| q.nct_saved + q.commuting_charged)
        .sum::<u64>();
    assert_eq!(summary.always_saved + summary.guarded_raw_saved, counted);
    assert_eq!((address, cap), (ops.as_ptr(), ops.capacity()));
    summary.output = ops.len();
    summary
}
