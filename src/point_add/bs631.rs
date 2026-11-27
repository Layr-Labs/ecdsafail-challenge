//! q631 / bs (agent bs1, 2026-11-19; LOCAL RESEARCH, never part of a package): the big scans D (index 1), F (2) and F' (6)
//! with a SECOND FREE LANE through their sweeps (report: ~/Projects/ecdsafail/q631/bs/summary.py).
//!   Transform L1s (~/Projects/ecdsafail/q631/bs/xladder.py <shipped trace> <out> 1 - 1): in every hit test of the sweep
//!   EXCEPT the first, the last step of the AND ladder (t_L ^= t_{L-1} & c_L) is removed, its two controls go into the hit-test
//!   MCX instead of t_L (one control more: Khattar-Gidney, +2 Toffoli), and the measurement uncompute of t_L (HMR + CZ) is
//!   removed; later measurement indices are renumbered.  t_L = id 232 in D, id 248 in F and F' (logical 232 / 250 / 248).
//!   Reason the lane is free: the HMR of the FIRST hit test's uncompute resets t_L to |0> on every shot (a measurement
//!   reset), and no later record of the sweep names it.  The MCX computes the same AND (t_L held exactly t_{L-1} & c_L in the
//!   shipped scan, being 0 at every later ladder start), so the scan acts as the shipped one on every input state.
//!   Cost per rewritten hit test: +1 Toffoli (-1 ladder CCX, +2 in the MCX), +1 record (-1 CCX, -1 HMR, -1 CZ, +4 MCX).
//!   data/bs631_d.trc, bs631_f.trc, bs631_fp.trc = the transformed traces (lzma, .lzma container, 16 MiB dictionary).
//!   Switches BS_SCAN_D / BS_SCAN_F / BS_SCAN_FP (all false): when true, `trace_for` (hooked in mod.rs scan_rows after the
//!   si631 hook) returns the transformed trace of that scan.  All false: the build is the tree's, byte for byte.
//!   NOTE: with a switch on, the relabelling tables (i1's relabel.lzma, rp1's table) are bound to the list's positions and
//!   hash and must be re-planned before a full build; the scans are tested by scan-level replay (src/bin/bsrun.rs).
use super::*;
/// scan D (index 1) with the L1s trace in the tree's build: OFF
pub const BS_SCAN_D: bool = false;
/// scan F (index 2) with the L1s trace in the tree's build: OFF
pub const BS_SCAN_F: bool = false;
/// scan F' (index 6) with the L1s trace in the tree's build: OFF
pub const BS_SCAN_FP: bool = false;
/// the L1s trace of scan i (1 = D, 2 = F, 6 = F'), decoded
pub fn bs_trace(i: usize) -> Vec<u8> {
    let d: &[u8] = match i { 1 => include_bytes!("data/bs631_d.trc"), 2 => include_bytes!("data/bs631_f.trc"), 6 => include_bytes!("data/bs631_fp.trc"), _ => panic!("bs631 trace: scan {}", i) };
    lzma::decode(d).expect("bs631 trace")
}
/// scan_rows hook: the trace that scan i expands (the L1s trace when its switch is on, else the given one, unchanged)
pub fn trace_for(i: usize, given: Vec<u8>) -> Vec<u8> {
    if (i == 1 && BS_SCAN_D) || (i == 2 && BS_SCAN_F) || (i == 6 && BS_SCAN_FP) { bs_trace(i) } else { given }
}
