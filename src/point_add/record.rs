//! What the build records about itself.
//!
//! Three recorders in one shape: a struct owned by [`Builder`](super::Builder),
//! `enabled: false` unless its environment flag is set, hooks that return
//! immediately when it is not, and a file or a report written at the end of the
//! build. Two are diagnostics, one per factor of the score; the third is a
//! required input to the GPU screen.
//!
//! **Nothing here can move the op stream.** These only read it, so `ops.bin` is
//! byte-identical with every flag below on or off -- which is what makes them
//! safe to run against a circuit whose tail nonce is already ground.
//!
//! | knob | reports |
//! | --- | --- |
//! | `PEAK_CENSUS_OP_LO` + `PEAK_CENSUS_OP_HI` (both, or off) | who *holds* every live wire at the op that sets the peak |
//! | `PEAK_CENSUS_PHASE` | restrict that search to phases containing this substring |
//! | `TRACE_CCX_SITES=1` | `ccx_sites.tsv`: which construction *emitted* each Toffoli |
//! | `CCX_BACKTRACE=<idx>,...` | a full backtrace at those op indices |
//! | `DUMP_REPLAY_SITES=1` | `replay_sites.tsv`: where the phase-channel repairs are |

use std::collections::HashMap;
use std::fmt::Write;
use std::panic::Location;

use super::{env_flag, optional_env};
use crate::circuit::OperationType;

/// Where the build is at the moment a recorder's hook fires.
///
/// Both censuses key on the op index -- one to window its search, the other to
/// name the gate -- and both report the phase, so this is one argument instead
/// of three repeated across five call sites.
#[derive(Clone, Copy)]
pub struct At {
    pub phase: &'static str,
    /// Index the *next* op will occupy, i.e. `Builder::ops.len()`.
    pub op: usize,
    pub active: u32,
}

/// The site that allocated a wire: the phase it was in, and where in the source.
type Owner = (&'static str, &'static str, u32);

/// Who is holding the wires when the qubit count peaks.
///
/// Half the score is the peak, and lowering it means freeing something that is
/// live at the exact op that sets it -- so the useful question is ownership,
/// not allocation. `TRACE_ALLOC_NEAR_PEAK` used to answer the allocation
/// version and answered it wrongly: it read `Location::caller()` inside
/// `alloc_qubit`, but the closure in `alloc_qubits` is not `#[track_caller]`
/// and breaks the chain, so every batched allocation -- near the peak, all of
/// them -- attributed to that closure. [`PeakCensus::batch`] is the fix.
#[derive(Default)]
pub struct PeakCensus {
    enabled: bool,
    op_lo: usize,
    op_hi: usize,
    phase_filter: Option<String>,

    /// Live wire -> the site that allocated it.
    owner: HashMap<u64, Owner>,
    /// Set while `alloc_qubits` is handing out a batch: its own caller, which
    /// is the construction site the individual `alloc_qubit` calls cannot see.
    batch: Option<(&'static str, u32)>,

    best: Option<Best>,
    printed: bool,
}

/// The highest-water mark seen so far, with the ownership map frozen there.
struct Best {
    active: u32,
    op: usize,
    phase: &'static str,
    owner: HashMap<u64, Owner>,
}

impl PeakCensus {
    pub fn new() -> Self {
        // Both bounds or nothing: half a window is far likelier to be a typo
        // than an intent, and silently censusing the whole build would hide it.
        match (
            optional_env("PEAK_CENSUS_OP_LO"),
            optional_env("PEAK_CENSUS_OP_HI"),
        ) {
            (Some(op_lo), Some(op_hi)) => Self {
                enabled: true,
                op_lo,
                op_hi,
                phase_filter: optional_env::<String>("PEAK_CENSUS_PHASE").filter(|s| !s.is_empty()),
                ..Self::default()
            },
            _ => Self::default(),
        }
    }

    /// Checked at the call site so a disabled build never pays for
    /// `Location::caller()`.
    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// Attribute every wire allocated from now until `batch(None)` to `ctx`,
    /// rather than to the caller `alloc_qubit` sees.
    pub fn batch(&mut self, ctx: Option<(&'static str, u32)>) {
        self.batch = ctx;
    }

    pub fn on_alloc(&mut self, at: At, qid: u64, file: &'static str, line: u32) {
        if !self.enabled {
            return;
        }
        let (file, line) = self.batch.unwrap_or((file, line));
        self.owner.insert(qid, (at.phase, file, line));
        self.sample(at);
    }

    pub fn on_free(&mut self, at: At, qid: u64) {
        if !self.enabled {
            return;
        }
        self.owner.remove(&qid);
        self.sample(at);
    }

    fn sample(&mut self, at: At) {
        if self.printed {
            return;
        }
        // Past the window: report now rather than carrying the map to the end.
        if at.op > self.op_hi {
            self.print();
            return;
        }
        if at.op < self.op_lo || at.active <= self.best.as_ref().map_or(0, |b| b.active) {
            return;
        }
        if let Some(filter) = &self.phase_filter {
            if !at.phase.contains(filter.as_str()) {
                return;
            }
        }
        self.best = Some(Best {
            active: at.active,
            op: at.op,
            phase: at.phase,
            owner: self.owner.clone(),
        });
    }

    /// Report, if the window never closed on its own.
    pub fn finalize(&mut self) {
        if self.enabled && !self.printed {
            self.print();
        }
    }

    fn print(&mut self) {
        self.printed = true;
        let Some(best) = self.best.take() else {
            return;
        };
        let mut hist: HashMap<Owner, u32> = HashMap::new();
        for owner in best.owner.values() {
            *hist.entry(*owner).or_insert(0) += 1;
        }
        let mut rows: Vec<(Owner, u32)> = hist.into_iter().collect();
        rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        eprintln!(
            "PEAK_CENSUS_BEGIN best_active={} best_ops={} best_phase={} n_live={} n_groups={} win=[{},{}]",
            best.active,
            best.op,
            best.phase,
            best.owner.len(),
            rows.len(),
            self.op_lo,
            self.op_hi
        );
        for ((phase, file, line), count) in &rows {
            eprintln!("PEAK_OWN count={count} phase={phase} caller={file}:{line}");
        }
        eprintln!("PEAK_CENSUS_END");
    }
}

/// Which construction emitted each gate the score counts.
///
/// "Scored" is CCX *and* CCZ: `sim.rs` adds both to the same `toffoli_gates`
/// total, so a CCZ costs exactly what a Toffoli costs. This tree emits no CCZ
/// today -- `cz_if` produces `CZ` or `Z`, neither of which is scored, and
/// nothing else names the kind -- but the census is written over
/// [`CcxCensus::scored`] rather than over CCX alone, and `Builder::push_op`
/// carries a tripwire so a future CCZ path cannot go uncounted in silence.
///
/// Tracing at `push_op` would name that function's caller, which is always a
/// gate helper inside `mod.rs` -- useless for attribution. `Builder::ccx` is
/// `#[track_caller]`, so *it* sees the construction that wanted the gate; this
/// records that, keyed by the op index the gate is about to occupy.
#[derive(Default)]
pub struct CcxCensus {
    /// `TRACE_CCX_SITES`. Presence, not value: `TRACE_CCX_SITES=0` enables it,
    /// the same convention as `DUMP_REPLAY_SITES`.
    sites: bool,
    backtrace_at: Vec<usize>,
    rows: Vec<Row>,
    /// Free-form context an emitter attaches to the next Toffoli it emits (see
    /// `pingpong::ccx_note_fold`). Recording it emits no op, so the trace still
    /// cannot perturb the stream.
    note: u64,
}

struct Row {
    op: usize,
    kind: OperationType,
    file: &'static str,
    line: u32,
    phase: &'static str,
    note: u64,
}

impl CcxCensus {
    pub fn new() -> Self {
        Self {
            sites: env_flag("TRACE_CCX_SITES"),
            backtrace_at: optional_env::<String>("CCX_BACKTRACE")
                .unwrap_or_default()
                .split(',')
                .filter_map(|idx| idx.trim().parse().ok())
                .collect(),
            ..Self::default()
        }
    }

    /// Does this gate kind count towards the score? `sim.rs` sums CCX and CCZ
    /// into one `toffoli_gates` total, so both do and nothing else does.
    pub fn scored(kind: OperationType) -> bool {
        matches!(kind, OperationType::CCX | OperationType::CCZ)
    }

    /// True when either knob is on. Checked before `Location::caller()`, which
    /// `Builder::ccx` would otherwise pay for on all ~945,000 gates.
    pub fn watching(&self) -> bool {
        self.sites || !self.backtrace_at.is_empty()
    }

    /// Whether the gate about to occupy `op` was recorded. `Builder::push_op`
    /// asserts this for every scored kind, so adding a CCZ emitter that forgets
    /// to call [`CcxCensus::on_gate`] fails loudly the first time it is traced
    /// instead of quietly leaving gates out of the attribution.
    pub fn covers(&self, op: usize) -> bool {
        !self.sites || matches!(self.rows.last(), Some(row) if row.op == op)
    }

    /// Attach `note` to the next Toffoli emitted.
    pub fn note(&mut self, note: u64) {
        if self.sites {
            self.note = note;
        }
    }

    pub fn on_gate(&mut self, at: At, kind: OperationType, loc: &'static Location<'static>) {
        if self.sites {
            self.rows.push(Row {
                op: at.op,
                kind,
                file: loc.file(),
                line: loc.line(),
                phase: at.phase,
                note: std::mem::take(&mut self.note),
            });
        }
        if self.backtrace_at.contains(&at.op) {
            eprintln!(
                "\n=== {kind:?} op #{} emitted at {}:{} (phase '{}') ===\n{}",
                at.op,
                loc.file(),
                loc.line(),
                at.phase,
                std::backtrace::Backtrace::force_capture()
            );
        }
    }

    /// Write `ccx_sites.tsv`, for joining against the evaluator's
    /// `ccx_candidates.tsv`.
    ///
    /// Called before the tail nonce is appended. That only adds ops to the end,
    /// so every index recorded here still names the same gate afterwards.
    pub fn finalize(&self) {
        if !self.sites {
            return;
        }
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/ccx_sites.tsv");
        let mut body = String::from("op_idx\tkind\tfile\tline\tphase\tnote\n");
        for row in &self.rows {
            writeln!(
                body,
                "{}\t{:?}\t{}\t{}\t{}\t{}",
                row.op, row.kind, row.file, row.line, row.phase, row.note
            )
            .unwrap();
        }
        match std::fs::write(path, body) {
            Ok(()) => println!("  wrote       : {path}"),
            Err(e) => eprintln!("warning: failed to write ccx_sites.tsv: {e}"),
        }
    }
}

/// Where the replay's phase-channel repairs are.
///
/// The chunk-boundary and flag repairs fail through the PHASE channel, so no
/// classical model of the *values* can see them -- but their predicates are
/// entirely classical (`[sum_top < addend_top]` against the true carry). The one
/// thing an outside model cannot reconstruct is WHERE the boundaries are,
/// because `chunk_layout` sizes itself against the live wire count. So the
/// builder writes them out instead of anyone modelling them, and
/// `grind checkpoint` folds `replay_sites.tsv` into the CUDA screen's
/// checkpoint.
///
/// Unlike the two censuses above this one is not a diagnostic: the GPU screen
/// cannot be regenerated without it.
#[derive(Default)]
pub struct ReplaySites {
    enabled: bool,
    rows: Vec<String>,
}

impl ReplaySites {
    pub fn new() -> Self {
        Self {
            enabled: env_flag("DUMP_REPLAY_SITES"),
            ..Self::default()
        }
    }

    /// Record one repair site: `kind` is `B` for a chunk boundary or `F` for the
    /// replay cell's overflow flag, and `pos` the bit above the compared window.
    pub fn record(&mut self, at: At, kind: char, round: usize, pos: usize, width: usize) {
        if !self.enabled {
            return;
        }
        // The two traversals emit the same sites at different rounds, and the
        // phase name is the only thing that distinguishes them here.
        let direction = if at.phase.contains("div") {
            "div"
        } else {
            "mul"
        };
        self.rows
            .push(format!("{kind}\t{direction}\t{round}\t{pos}\t{width}"));
    }

    pub fn finalize(&self) {
        if !self.enabled {
            return;
        }
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/replay_sites.tsv");
        let mut body = String::from("kind\tdir\tround\tpos\twidth\n");
        for row in &self.rows {
            body.push_str(row);
            body.push('\n');
        }
        match std::fs::write(path, body) {
            Ok(()) => println!("  wrote       : {path}"),
            Err(e) => eprintln!("warning: failed to write replay_sites.tsv: {e}"),
        }
    }
}
