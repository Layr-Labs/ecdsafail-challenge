//! y33 "clears": Toffoli that only clear a wire before its reset, measured away instead.
//!
//! One sweep over the finished op stream, called once from `build_point_add` (through `Builder::y33_clears`) just
//! before the totals are printed. For every wire a RUN starts at an unconditional CCX into it and collects the
//! unconditional gates that only WRITE it (CCX into it, CX into it, X on it). A gate that reads the wire (a control
//! of a CX or CCX; any CZ, CCZ, Z, SWAP; a register line), a write under a condition, or an HMR ends the run with
//! nothing done. An unconditional R on the wire ends it with a SITE: every Toffoli of the run only prepared the wire
//! for that reset. In this tree the sites are a rail's top wire: an add writes the top sum bit (one Toffoli for the
//! carry into the top position), nothing reads it, and the rail then gives the wire up as a sign copy.
//!
//! At a site the wire q is measured in the X basis (HMR into a bit m of its own) where the run's first CCX stood,
//! and every gate of the run becomes its phase twin under m, in place: CCX(a, b, q) -> CZ(a, b); CX(s, q) -> Z(s);
//! X(q) -> NEG. The reset R(q) goes: q is clean from the measurement on.
//!
//! Why this is the same circuit on EVERY shot, not only where the released wire comes out clean: R is an X-basis
//! measurement whose outcome is thrown away. With q0 the wire before the run and f the XOR of all the run writes,
//! the old form resets q and flips the phase by r AND (q0 ^ f), r being the reset's own random outcome. The new form
//! flips it by m AND q0 at the measurement and by m AND f through the twins: m AND (q0 ^ f). Nothing reads q in
//! between, so every other wire is the same in both forms. Where q0 ^ f = 0 (the rail fits, the wire is clean)
//! neither form adds a phase; where it is 1 both add one fair coin, the old form's from the reset's random word, the
//! new form's from the measurement's.

use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

/// The switch. false: the base's gate list byte for byte.
pub(super) const Y33_CLEARS: bool = true;
/// Research knob (false in every build that is kept): each site's reset R(q) stays (it finds a clean wire), so the
/// list draws as many random words, in the same places, as a base with one idle measurement before each site.
pub(super) const Y33_KEEP_R: bool = false;
/// Fault control of the paired tests (None in every build that is kept): Some((site, gate)) leaves out the phase
/// twin of gate number `gate` of the run of site number `site` (gate 0 is the first CCX: its CZ).
pub(super) const Y33_FAULT: Option<(usize, usize)> = None;

struct Site {
    q: u64,
    run: Vec<usize>,
    release: usize,
}

fn find(ops: &[Op]) -> Vec<Site> {
    let mut run: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut depth = 0usize;
    let mut sites = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        let plain = depth == 0 && op.c_condition == NO_BIT;
        let t = op.q_target.0;
        match op.kind {
            OperationType::CX | OperationType::X | OperationType::CCX => {
                if op.kind != OperationType::X {
                    run.remove(&op.q_control1.0);
                }
                if op.kind == OperationType::CCX {
                    run.remove(&op.q_control2.0);
                }
                if !plain {
                    run.remove(&t);
                } else if let Some(r) = run.get_mut(&t) {
                    r.push(i);
                } else if op.kind == OperationType::CCX {
                    run.insert(t, vec![i]);
                }
            }
            OperationType::R => {
                if let Some(r) = run.remove(&t) {
                    if plain {
                        sites.push(Site { q: t, run: r, release: i });
                    }
                }
            }
            OperationType::PushCondition => depth += 1,
            OperationType::PopCondition => depth -= 1,
            OperationType::Neg | OperationType::BitInvert | OperationType::BitStore0 | OperationType::BitStore1 => {}
            _ => {
                // HMR, Z, CZ, CCZ, SWAP, register lines, debug prints: the wire is read or measured
                for q in [op.q_control2, op.q_control1, op.q_target] {
                    if q != NO_QUBIT {
                        run.remove(&q.0);
                    }
                }
            }
        }
    }
    sites
}

/// The phase twin of a run's gate under the bit `m`.
fn twin(op: &Op, m: BitId) -> Op {
    let mut z = Op::empty();
    z.c_condition = m;
    match op.kind {
        OperationType::CCX => {
            z.kind = OperationType::CZ;
            z.q_control1 = op.q_control1;
            z.q_target = op.q_control2;
        }
        OperationType::CX => {
            z.kind = OperationType::Z;
            z.q_target = op.q_control1;
        }
        OperationType::X => z.kind = OperationType::Neg,
        k => panic!("y33: {k:?} in a run"),
    }
    z
}

/// Rewrite every site of `ops` in place. The bits come from `next_bit` on (one a site, never reused: a site's bit
/// lives from its measurement to its last twin, across other measurements). Returns (sites, Toffoli removed).
pub(super) fn sweep(ops: &mut Vec<Op>, next_bit: &mut u32) -> (usize, usize) {
    let sites = find(ops);
    // op index -> (site, Some(gate number in the run) or None for the release)
    let mut act: HashMap<usize, (usize, Option<usize>)> = HashMap::new();
    let mut toffoli = 0;
    for (k, s) in sites.iter().enumerate() {
        let n = s.run.iter().filter(|&&j| ops[j].kind == OperationType::CCX).count();
        toffoli += n;
        eprintln!("Y33_SITE {k} q={} first={} release={} gates={} toffoli={n}", s.q, s.run[0], s.release, s.run.len());
        for (g, &j) in s.run.iter().enumerate() {
            act.insert(j, (k, Some(g)));
        }
        act.insert(s.release, (k, None));
    }
    let old = std::mem::take(ops);
    ops.reserve(old.len() + sites.len());
    for (i, op) in old.into_iter().enumerate() {
        let Some(&(k, g)) = act.get(&i) else {
            ops.push(op);
            continue;
        };
        let m = BitId(u64::from(*next_bit) + k as u64);
        match g {
            None => {
                if Y33_KEEP_R {
                    ops.push(op);
                }
            }
            Some(g) => {
                if g == 0 {
                    let mut h = Op::empty();
                    h.kind = OperationType::Hmr;
                    h.q_target = QubitId(sites[k].q);
                    h.c_target = m;
                    ops.push(h);
                }
                if Y33_FAULT != Some((k, g)) {
                    ops.push(twin(&op, m));
                }
            }
        }
    }
    *next_bit += u32::try_from(sites.len()).expect("site count fits in u32");
    (sites.len(), toffoli)
}
