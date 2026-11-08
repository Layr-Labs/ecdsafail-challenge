//! Classical-only profiler for the point-add builder.
//!
//! Records, per named scope, how many CCX gates were emitted and how many
//! qubits were live at entry, at exit, and at the scope's local peak. It only
//! observes counters that `B` already maintains (plus a CCX tally bumped in
//! `B::ccx`) and never emits, removes, or reorders ops, so the op stream is
//! byte-identical with or without it.
//!
//! Scopes nest: a scope is keyed by (parent scope, name), so the same
//! subroutine called from pair1 and from pair2 is reported separately.
//! Within a scope, CCX are further split by the builder's existing
//! `set_phase` labels (e.g. the Kaliski step names), giving a leaf breakdown
//! without having to wrap every step.
//!
//! CCX inside an `emit_inverse` closure are tallied once, when the forward
//! block is first emitted; the reversed copy is pushed straight onto `ops`
//! and has the same CCX count, so attribution stays exact. The final report
//! cross-checks the tally against the CCX actually present in the op stream.

use std::collections::HashMap;

struct Scope {
    name: &'static str,
    parent: Option<usize>,
    calls: u64,
    // Inclusive of child scopes.
    ccx: u64,
    // Expected executed Toffolis (CCX/CCZ weighted by ½ per enclosing
    // classical-condition block, since those conditions are uniform X-measurement outcomes).
    exec: f64,
    entry_min: u32,
    entry_max: u32,
    exit_min: u32,
    exit_max: u32,
    local_peak: u32,
}

struct Frame {
    scope: usize,
    ccx_at_entry: u64,
    exec_at_entry: f64,
    local_peak: u32,
}

type LeafKey = (Option<usize>, &'static str);

#[derive(Default)]
pub struct Profiler {
    pub ccx: u64,
    pub exec: f64,
    pub cond_depth: u32,
    scopes: Vec<Scope>,
    index: HashMap<(Option<usize>, &'static str), usize>,
    stack: Vec<Frame>,
    // (scope, phase) -> CCX emitted directly in that scope under that phase.
    leaf: HashMap<LeafKey, u64>,
    leaf_exec: HashMap<LeafKey, f64>,
    leaf_order: Vec<LeafKey>,
    // (scope, phase) -> highest live-qubit count seen while that leaf was active.
    leaf_peak: HashMap<LeafKey, u32>,
    mark: u64,
    mark_exec: f64,
    peak: u32,
    peak_at: Option<LeafKey>,
}

impl Profiler {
    /// One Toffoli-class gate (CCX or CCZ) was emitted.
    pub fn tally(&mut self) {
        self.ccx += 1;
        self.exec += 0.5f64.powi(self.cond_depth as i32);
    }

    fn current(&self) -> Option<usize> {
        self.stack.last().map(|f| f.scope)
    }

    /// Attribute CCX emitted since the last checkpoint to (current scope, phase).
    fn flush(&mut self, phase: &'static str) {
        let d = self.ccx - self.mark;
        if d > 0 {
            let key = (self.current(), phase);
            if !self.leaf.contains_key(&key) {
                self.leaf_order.push(key);
            }
            *self.leaf.entry(key).or_insert(0) += d;
            *self.leaf_exec.entry(key).or_insert(0.0) += self.exec - self.mark_exec;
        }
        self.mark = self.ccx;
        self.mark_exec = self.exec;
    }

    pub fn on_phase_change(&mut self, old_phase: &'static str) {
        self.flush(old_phase);
    }

    pub fn on_alloc(&mut self, active: u32, phase: &'static str) {
        if let Some(f) = self.stack.last_mut() {
            f.local_peak = f.local_peak.max(active);
        }
        let key = (self.current(), phase);
        let e = self.leaf_peak.entry(key).or_insert(0);
        *e = (*e).max(active);
        if active > self.peak {
            self.peak = active;
            self.peak_at = Some((self.current(), phase));
        }
    }

    pub fn begin(&mut self, name: &'static str, active: u32, phase: &'static str) {
        self.flush(phase);
        let parent = self.current();
        let idx = match self.index.get(&(parent, name)) {
            Some(&i) => i,
            None => {
                self.scopes.push(Scope {
                    name,
                    parent,
                    calls: 0,
                    ccx: 0,
                    exec: 0.0,
                    entry_min: u32::MAX,
                    entry_max: 0,
                    exit_min: u32::MAX,
                    exit_max: 0,
                    local_peak: 0,
                });
                self.index.insert((parent, name), self.scopes.len() - 1);
                self.scopes.len() - 1
            }
        };
        let s = &mut self.scopes[idx];
        s.calls += 1;
        s.entry_min = s.entry_min.min(active);
        s.entry_max = s.entry_max.max(active);
        self.stack.push(Frame {
            scope: idx,
            ccx_at_entry: self.ccx,
            exec_at_entry: self.exec,
            local_peak: active,
        });
    }

    pub fn end(&mut self, name: &'static str, active: u32, phase: &'static str) {
        self.flush(phase);
        let f = self.stack.pop().expect("profiler: end without begin");
        let s = &mut self.scopes[f.scope];
        assert_eq!(s.name, name, "profiler: mismatched scope end");
        s.ccx += self.ccx - f.ccx_at_entry;
        s.exec += self.exec - f.exec_at_entry;
        s.exit_min = s.exit_min.min(active);
        s.exit_max = s.exit_max.max(active);
        s.local_peak = s.local_peak.max(f.local_peak);
        if let Some(p) = self.stack.last_mut() {
            p.local_peak = p.local_peak.max(f.local_peak);
        }
    }

    fn path(&self, scope: Option<usize>) -> String {
        let mut parts = Vec::new();
        let mut cur = scope;
        while let Some(i) = cur {
            parts.push(self.scopes[i].name);
            cur = self.scopes[i].parent;
        }
        if parts.is_empty() {
            return "(top level)".to_string();
        }
        parts.reverse();
        parts.join("/")
    }

    fn range(lo: u32, hi: u32) -> String {
        if lo == hi {
            format!("{}", lo)
        } else {
            format!("{}-{}", lo, hi)
        }
    }

    pub fn report(&mut self, final_phase: &'static str, ccx_in_ops: u64, peak_qubits: u32) {
        self.flush(final_phase);
        assert!(self.stack.is_empty(), "profiler: unclosed scope at report");
        let total = self.ccx.max(1) as f64;

        eprintln!("=== PROF: scopes (CCX inclusive of children; qubits = live count) ===");
        eprintln!(
            "PROF\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            "scope", "calls", "ccx", "%tof", "entry_q", "exit_q", "local_peak", "at_peak", "exec_tof"
        );
        let mut children: Vec<Vec<usize>> = vec![Vec::new(); self.scopes.len()];
        let mut roots = Vec::new();
        for (i, s) in self.scopes.iter().enumerate() {
            match s.parent {
                Some(p) => children[p].push(i),
                None => roots.push(i),
            }
        }
        let mut todo: Vec<(usize, usize)> = roots.iter().rev().map(|&r| (r, 0)).collect();
        while let Some((i, depth)) = todo.pop() {
            let s = &self.scopes[i];
            eprintln!(
                "PROF\t{}{}\t{}\t{}\t{:.2}\t{}\t{}\t{}\t{}\t{:.1}",
                "  ".repeat(depth),
                s.name,
                s.calls,
                s.ccx,
                s.ccx as f64 * 100.0 / total,
                Self::range(s.entry_min, s.entry_max),
                Self::range(s.exit_min, s.exit_max),
                s.local_peak,
                if s.local_peak == peak_qubits { "PEAK" } else { "" },
                s.exec
            );
            for &c in children[i].iter().rev() {
                todo.push((c, depth + 1));
            }
        }

        eprintln!("=== PROF: leaves (CCX exclusive, split by set_phase label), largest first ===");
        let mut leaves: Vec<(LeafKey, u64)> =
            self.leaf_order.iter().map(|k| (*k, self.leaf[k])).collect();
        leaves.sort_by(|a, b| b.1.cmp(&a.1));
        for ((scope, phase), n) in leaves {
            eprintln!(
                "PROFLEAF\t{}\t[{}]\t{}\t{:.2}\t{:.1}",
                self.path(scope),
                phase,
                n,
                n as f64 * 100.0 / total,
                self.leaf_exec.get(&(scope, phase)).copied().unwrap_or(0.0)
            );
        }

        eprintln!("=== PROF: leaf peaks (live qubits, per scope × set_phase label), highest first ===");
        let mut peaks: Vec<(LeafKey, u32)> = self.leaf_peak.iter().map(|(k, v)| (*k, *v)).collect();
        peaks.sort_by(|a, b| b.1.cmp(&a.1).then(a.0 .1.cmp(b.0 .1)));
        for ((scope, phase), q) in peaks {
            eprintln!("PROFPEAK\t{}\t[{}]\t{}", self.path(scope), phase, q);
        }

        if let Some((scope, phase)) = self.peak_at {
            eprintln!(
                "PROF peak {} first reached in {} [{}]",
                self.peak,
                self.path(scope),
                phase
            );
        }
        eprintln!(
            "PROF check: toffoli-class (CCX+CCZ) tally={} in op stream={} {}; expected executed per shot = {:.1}",
            self.ccx,
            ccx_in_ops,
            if self.ccx == ccx_in_ops { "MATCH" } else { "MISMATCH" },
            self.exec
        );
    }
}
