//! Exhaustive `Simulator` harness for `onehot_stream` (pattern of
//! `retained_division.rs::tests` / `measured_demux::selftest`): every exponent
//! value, both gate values, both directions, measured and coherent clears,
//! nested classical conditions; value, phase and freed-ancilla checks; the
//! forward-then-inverse round trip; T per visited index against
//! `unary_iterate_log_star` on the same task.
//!
//! Adversarial review additions (2026-09-13, `run_adversarial`):
//! * an exact classical T model (`expected_t`: visited internal nodes per
//!   level + the fold's retarget sequence) asserted on EVERY built circuit,
//!   so the count is checked, not only printed;
//! * k = 9 windows on every quadrant / half boundary of the fold ([0,1),
//!   [511,512), [255,257), [256,257), [127,129), [383,385), [128,384), one
//!   quadrant only, [226,257) = the M1 class e_B in [226,256], [1,512),
//!   [0,511), ...), both gate modes, both clear modes, forward, inverse,
//!   forward+inverse, inverse+forward and inverse+inverse round trips;
//! * the design's real engine windows at 9 bits from `tools/packed_prefix_model.py`
//!   states (D4 `(lo_A, W_A]`, D7 zone `[max(lo_A, 257-W_c), W_A)`, M5 zone in
//!   e_cb terms `[257-W_A, W_c+1)`, role compute `[W_c-78, W_c)`) at steps 0,
//!   10, 100, 200, 300, 378 (3000-input and the design's 1M envelopes), 440,
//!   480, 529, and D0's 5-bit `s_rot` window `[0, 29)`; every exponent value is
//!   run through each, so the sampled real states (tight R1 gap 0, e_A = W_A
//!   with off = 0, ca_old = 0 rows, draining rows e_A = 0 / e_ca = 256) are a
//!   subset;
//! * the design's two leaf uses as bodies: the thermometer `f = [i < exp]`
//!   (2.2; toggle before use ascending = MAJ, use then toggle descending = UMA,
//!   the pair restores `f`) and the capture `out ^= g_i AND src[i]` (2.3) with
//!   src all-ones (foreign bits on every neighbour of the fired leaf) and a
//!   value-dependent pattern, with and without body-owned scratch;
//! * empty gated windows and the `hi > 2^k` precondition panic.

use super::onehot_stream_with;
use crate::circuit::{analyze_ops, BitId, Op, OperationType, QubitId};
use crate::point_add::trailmix_port::arith::khattar_gidney::unary_iterate_log_star;
use crate::point_add::trailmix_port::circuit::{Cbit, Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::predicate_clear_selftest::checked_apply;
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

struct Measurements {
    forced: Option<u8>,
    random: sha3::Shake256Reader,
}

impl XofReader for Measurements {
    fn read(&mut self, bytes: &mut [u8]) {
        if let Some(value) = self.forced {
            bytes.fill(value);
        } else {
            self.random.read(bytes);
        }
    }
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

struct Built {
    ops: Vec<Op>,
    /// exp bits, then the gate (if gated), then the window's leaf wires.
    ids: Vec<QubitId>,
    k: usize,
    lo: usize,
    hi: usize,
    gated: bool,
    /// Toffoli of the whole circuit (the body is CX-only, so all of it is the engine's).
    t: usize,
    /// Engine wire peak above the pre-allocated registers.
    engine_wires: u32,
    /// Classical condition bits when built inside `with_conditions`.
    conditions: Option<(Cbit, Cbit)>,
}

/// Gate list with qubit ids renamed by first appearance (resets and register
/// bookkeeping dropped), so two circuits can be compared up to allocation order.
fn canonical(ops: impl Iterator<Item = Op>) -> Vec<(OperationType, [usize; 3])> {
    let mut names: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
    let mut out = Vec::new();
    for op in ops {
        if !matches!(op.kind, OperationType::X | OperationType::CX | OperationType::CCX) {
            continue;
        }
        let mut slots = [usize::MAX; 3];
        for (slot, q) in slots.iter_mut().zip([op.q_control2, op.q_control1, op.q_target]) {
            if q != crate::circuit::NO_QUBIT {
                let next = names.len();
                *slot = *names.entry(q.0).or_insert(next);
            }
        }
        out.push((op.kind, slots));
    }
    out
}

/// Build `passes.len()` consecutive `onehot_stream` calls (each entry = its
/// `inverse` flag) over shared leaf wires `out[i - lo] ^= flag_i`, checking at
/// build time that every call visits exactly the window once, in order.
fn build(k: usize, lo: usize, hi: usize, gated: bool, coherent: bool, passes: &[bool], nested: bool) -> Built {
    let mut c = Circuit::new();
    let exp = c.alloc_qreg_bits("exp", k);
    let gate = if gated { Some(c.alloc_qreg("gate")) } else { None };
    let out = c.alloc_qreg_bits("leaf", hi - lo);
    let base = c.b.peak_qubits;
    let conditions = if nested { Some((c.alloc_input_bit(), c.alloc_input_bit())) } else { None };
    for &inverse in passes {
        let mut visited: Vec<usize> = Vec::new();
        {
            let mut body = |c: &mut Circuit, i: usize, flag: &QReg| {
                visited.push(i);
                c.cx(flag, &out[i - lo]);
            };
            match conditions {
                Some((outer, inner)) => c.with_conditions(&[outer, inner], |c| {
                    onehot_stream_with(c, &exp, lo, hi, gate.as_ref(), inverse, coherent, &mut body)
                }),
                None => onehot_stream_with(&mut c, &exp, lo, hi, gate.as_ref(), inverse, coherent, &mut body),
            }
        }
        let mut want: Vec<usize> = (lo..hi).collect();
        if inverse {
            want.reverse();
        }
        assert_eq!(visited, want, "visit order k={k} [{lo},{hi}) gated={gated} inverse={inverse}");
    }
    c.flush_pending_frees();
    let ids = exp.iter().chain(gate.iter()).chain(&out).map(|q| QubitId(q.id().into())).collect();
    let t = toffoli(&c.b.ops);
    let engine_wires = c.b.peak_qubits - base;
    Built { ops: c.b.ops.clone(), ids, k, lo, hi, gated, t, engine_wires, conditions }
}

/// Run every exponent value (x both gate values) through `b` under four
/// measurement regimes; return the number of shots checked.
fn check(b: &Built, odd_passes: bool) -> usize {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let nq = (nq as usize).max(b.ids.iter().map(|q| q.0 as usize + 1).max().unwrap());
    let nb = (nb as usize).max(b.conditions.map_or(0, |(_, inner)| inner.raw() as usize + 1));
    let width = b.hi - b.lo;
    let mut inputs: Vec<u64> = Vec::new();
    for value in 0u64..1 << b.k {
        for gate_v in if b.gated { 0..=1u64 } else { 1..=1u64 } {
            let mut bits = value;
            if b.gated {
                bits |= gate_v << b.k;
            }
            inputs.push(bits);
        }
    }
    let gate_bit = b.k; // position of the gate in `bits` (unused when ungated)
    let first_leaf = b.k + usize::from(b.gated);
    assert_eq!(b.ids.len(), first_leaf + width);
    let mut checked = 0;
    for forced in [Some(0u8), Some(255), Some(0x55), None] {
        let mut hash = Shake256::default();
        hash.update(b"packed-onehot-stream-v1");
        hash.update(&(b.k as u64).to_le_bytes());
        hash.update(&(b.lo as u64).to_le_bytes());
        let mut rng = Measurements { forced, random: hash.finalize_xof() };
        for batch in inputs.chunks(64) {
            let mask = u64::MAX >> (64 - batch.len());
            let mut sim = Simulator::new(nq, nb + 1, &mut rng);
            let outer_mask = 0xaaaa_aaaa_aaaa_aaaa;
            let inner_mask = 0xcccc_cccc_cccc_cccc;
            if let Some((outer, inner)) = b.conditions {
                *sim.bit_mut(BitId(outer.raw().into())) = outer_mask;
                *sim.bit_mut(BitId(inner.raw().into())) = inner_mask;
            }
            // Load exp and the gate; the leaf wires start at |0>.
            for (bit, &id) in b.ids.iter().enumerate().take(first_leaf) {
                for (shot, &value) in batch.iter().enumerate() {
                    *sim.qubit_mut(id) |= ((value >> bit) & 1) << shot;
                }
            }
            checked_apply(&mut sim, &b.ops, mask);
            assert_eq!(sim.phase & mask, 0, "phase k={} [{},{}) gated={}", b.k, b.lo, b.hi, b.gated);
            for (shot, &value) in batch.iter().enumerate() {
                let exp = (value & ((1 << b.k) - 1)) as usize;
                let enabled = !b.gated || (value >> gate_bit) & 1 != 0;
                let selected = b.conditions.is_none() || (outer_mask & inner_mask) >> shot & 1 != 0;
                let fires = odd_passes && enabled && selected && (b.lo..b.hi).contains(&exp);
                for (bit, &id) in b.ids.iter().enumerate() {
                    // exp and gate unchanged; exactly the leaf `exp - lo` set when it fires.
                    let want = if bit < first_leaf {
                        (value >> bit) & 1
                    } else {
                        u64::from(fires && bit - first_leaf == exp - b.lo)
                    };
                    assert_eq!(
                        (sim.qubit(id) >> shot) & 1,
                        want,
                        "k={} [{},{}) gated={} exp={} enabled={} bit {} of {} (leaf wires from {})",
                        b.k, b.lo, b.hi, b.gated, exp, enabled, bit, b.ids.len(), first_leaf
                    );
                }
            }
            for &id in &b.ids {
                *sim.qubit_mut(id) = 0;
            }
            assert!(sim.qubits.iter().all(|v| v & mask == 0), "dirty scratch k={} [{},{})", b.k, b.lo, b.hi);
            checked += batch.len();
        }
    }
    checked
}

/// The same task on `unary_iterate_log_star`: it walks 0..hi (no window
/// pruning), the body ignores indices below `lo`. Returns its Toffoli count.
fn uls_toffoli(k: usize, lo: usize, hi: usize) -> usize {
    let mut c = Circuit::new();
    let exp = c.alloc_qreg_bits("exp", k);
    let out = c.alloc_qreg_bits("leaf", hi - lo);
    let refs: Vec<&QReg> = exp.iter().collect();
    unary_iterate_log_star(&mut c, &refs, hi, |c, i, flag| {
        if i >= lo {
            c.cx(flag, &out[i - lo]);
        }
    });
    c.flush_pending_frees();
    toffoli(&c.b.ops)
}

/// Number of aligned `size`-blocks inside `[base, base + span)` that meet `[lo, hi)`.
fn blocks(lo: usize, hi: usize, base: usize, span: usize, size: usize) -> usize {
    let a = lo.max(base);
    let b = hi.min(base + span);
    if a >= b {
        0
    } else {
        (b - 1) / size - a / size + 1
    }
}

/// Visited internal nodes of a subtree `[base, base + 2^levels)` with `levels` levels.
fn subtree_nodes(lo: usize, hi: usize, base: usize, levels: usize) -> usize {
    (1..=levels).map(|l| blocks(lo, hi, base, 1 << levels, 1 << l)).sum()
}

/// Exact Toffoli model of the engine (measured clears): one CCX per visited
/// internal node, plus the fold's retarget sequence for a gate with k >= 3
/// (root creation 1, `t` 1 per retarget: first quadrant 2, same-half move 1,
/// cross-half move 2, release 1). Coherent clears double it.
fn expected_t(k: usize, lo: usize, hi: usize, gated: bool, coherent: bool) -> usize {
    if lo < hi && gated && k >= 7 {
        let size = 1usize << (k - 4);
        let groups: Vec<usize> = (0..16).filter(|&i| blocks(lo, hi, i*size, size, size) > 0).collect();
        let nodes: usize = groups.iter().map(|&i| subtree_nodes(lo, hi, i*size, k-4)).sum();
        return if coherent { 2*nodes + 14 + 5*(groups.len()-1) }
               else { nodes + 7 + 3*(groups.len()-1) };
    }
    if lo < hi && gated && k >= 5 {
        let size = 1usize << (k - 3);
        let octants: Vec<usize> = (0..8).filter(|&i| blocks(lo, hi, i * size, size, size) > 0).collect();
        let nodes: usize = octants.iter().map(|&i| subtree_nodes(lo, hi, i * size, k - 3)).sum();
        return if coherent { 2 * nodes + 10 + 3 * (octants.len() - 1) }
               else { nodes + 5 + 2 * (octants.len() - 1) };
    }
    let t = if lo >= hi {
        0
    } else if gated && k >= 3 {
        let quarter = 1usize << (k - 2);
        let qs: Vec<usize> = (0..4).filter(|&q| blocks(lo, hi, q * quarter, quarter, quarter) > 0).collect();
        let nodes: usize = qs.iter().map(|&q| subtree_nodes(lo, hi, q * quarter, k - 2)).sum();
        let mut fold = 2 + 1;
        for w in qs.windows(2) {
            fold += if w[0] >> 1 == w[1] >> 1 { 1 } else { 2 };
        }
        nodes + fold
    } else if gated {
        subtree_nodes(lo, hi, 0, k)
    } else {
        let half = 1usize << (k - 1);
        subtree_nodes(lo, hi, 0, k - 1) + subtree_nodes(lo, hi, half, k - 1)
    };
    if coherent { 2 * t } else { t }
}

/// The design's two leaf uses (2.2 thermometer, 2.3 capture) as engine bodies.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum BodyKind {
    /// `f` starts at |1>; ascending: `f ^= flag` then `therm[i] ^= f`;
    /// descending (the inverse): `therm[i] ^= f` then `f ^= flag`.
    Therm,
    /// `out ^= flag AND src[i]`, optionally through a body-owned scratch wire.
    Capture { scratch: bool, ones: bool },
}

struct BuiltBody {
    ops: Vec<Op>,
    /// exp bits, then the gate (if gated).
    ctrl: Vec<QubitId>,
    /// Therm: `f` then `therm[0..width)`; Capture: `src[0..width)` then `out`.
    data: Vec<QubitId>,
    k: usize,
    lo: usize,
    hi: usize,
    gated: bool,
    kind: BodyKind,
    t: usize,
    engine_wires: u32,
}

fn build_body(k: usize, lo: usize, hi: usize, gated: bool, coherent: bool, kind: BodyKind, passes: &[bool]) -> BuiltBody {
    let mut c = Circuit::new();
    let exp = c.alloc_qreg_bits("exp", k);
    let gate = if gated { Some(c.alloc_qreg("gate")) } else { None };
    let width = hi - lo;
    let (single, many) = match kind {
        BodyKind::Therm => (c.alloc_qreg("therm.f"), c.alloc_qreg_bits("therm", width)),
        BodyKind::Capture { .. } => (c.alloc_qreg("capture.out"), c.alloc_qreg_bits("src", width)),
    };
    let base = c.b.peak_qubits;
    for &inverse in passes {
        let mut visited: Vec<usize> = Vec::new();
        let mut body = |c: &mut Circuit, i: usize, flag: &QReg| {
            visited.push(i);
            match kind {
                BodyKind::Therm if !inverse => {
                    c.cx(flag, &single);
                    c.cx(&single, &many[i - lo]);
                }
                BodyKind::Therm => {
                    c.cx(&single, &many[i - lo]);
                    c.cx(flag, &single);
                }
                BodyKind::Capture { scratch: false, .. } => c.ccx(flag, &many[i - lo], &single),
                BodyKind::Capture { scratch: true, .. } => {
                    let a = c.alloc_qreg("body.t");
                    c.ccx(flag, &many[i - lo], &a);
                    c.cx(&a, &single);
                    if coherent {
                        c.ccx(flag, &many[i - lo], &a);
                    } else {
                        c.clear_and(&a, flag, &many[i - lo]);
                    }
                    c.zero_and_free(a);
                }
            }
        };
        onehot_stream_with(&mut c, &exp, lo, hi, gate.as_ref(), inverse, coherent, &mut body);
        let mut want: Vec<usize> = (lo..hi).collect();
        if inverse {
            want.reverse();
        }
        assert_eq!(visited, want, "visit order k={k} [{lo},{hi}) gated={gated} inverse={inverse} {kind:?}");
    }
    c.flush_pending_frees();
    let ctrl = exp.iter().chain(gate.iter()).map(|q| QubitId(q.id().into())).collect();
    let data = match kind {
        BodyKind::Therm => std::iter::once(&single).chain(&many).map(|q| QubitId(q.id().into())).collect(),
        BodyKind::Capture { .. } => many.iter().chain(std::iter::once(&single)).map(|q| QubitId(q.id().into())).collect(),
    };
    let t = toffoli(&c.b.ops);
    let engine_wires = c.b.peak_qubits - base;
    BuiltBody { ops: c.b.ops.clone(), ctrl, data, k, lo, hi, gated, kind, t, engine_wires }
}

/// Value-dependent src pattern for the capture body (bit `j` for exponent `exp`).
fn src_bit(exp: usize, j: usize) -> u64 {
    let h = (exp as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left((j % 61) as u32) ^ ((exp as u64) >> (j % 9));
    (h >> 17) & 1
}

/// Every exponent value x both gate values under four measurement regimes.
fn check_body(b: &BuiltBody, odd_passes: bool) -> usize {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let nq = (nq as usize).max(b.ctrl.iter().chain(&b.data).map(|q| q.0 as usize + 1).max().unwrap());
    let width = b.hi - b.lo;
    let mut inputs: Vec<u64> = Vec::new();
    for value in 0u64..1 << b.k {
        for gate_v in if b.gated { 0..=1u64 } else { 1..=1u64 } {
            inputs.push(value | if b.gated { gate_v << b.k } else { 0 });
        }
    }
    let mut checked = 0;
    for forced in [Some(0u8), Some(255), Some(0x55), None] {
        let mut hash = Shake256::default();
        hash.update(b"packed-onehot-stream-body-v1");
        hash.update(&(b.k as u64).to_le_bytes());
        hash.update(&(b.lo as u64).to_le_bytes());
        let mut rng = Measurements { forced, random: hash.finalize_xof() };
        for batch in inputs.chunks(64) {
            let mask = u64::MAX >> (64 - batch.len());
            let mut sim = Simulator::new(nq, nb as usize + 1, &mut rng);
            let mut init: Vec<u64> = vec![0; b.data.len()];
            for (shot, &value) in batch.iter().enumerate() {
                for (bit, &id) in b.ctrl.iter().enumerate() {
                    *sim.qubit_mut(id) |= ((value >> bit) & 1) << shot;
                }
                let exp = (value & ((1 << b.k) - 1)) as usize;
                match b.kind {
                    BodyKind::Therm => init[0] |= 1 << shot,
                    BodyKind::Capture { ones, .. } => {
                        for j in 0..width {
                            let v = if ones { 1 } else { src_bit(exp, j) };
                            init[j] |= v << shot;
                        }
                    }
                }
            }
            for (&id, &v) in b.data.iter().zip(&init) {
                *sim.qubit_mut(id) = v;
            }
            checked_apply(&mut sim, &b.ops, mask);
            assert_eq!(sim.phase & mask, 0, "phase k={} [{},{}) gated={} {:?}", b.k, b.lo, b.hi, b.gated, b.kind);
            for (shot, &value) in batch.iter().enumerate() {
                let exp = (value & ((1 << b.k) - 1)) as usize;
                let enabled = !b.gated || (value >> b.k) & 1 != 0;
                let fires = enabled && (b.lo..b.hi).contains(&exp);
                for (bit, &id) in b.ctrl.iter().enumerate() {
                    assert_eq!((sim.qubit(id) >> shot) & 1, (value >> bit) & 1, "control wire {bit} changed, exp={exp}");
                }
                for (j, &id) in b.data.iter().enumerate() {
                    let got = (sim.qubit(id) >> shot) & 1;
                    let want = match (b.kind, odd_passes) {
                        (BodyKind::Therm, true) if j == 0 => u64::from(!fires),
                        (BodyKind::Therm, true) => {
                            // f = [i < exp] on rows with the gate on and exp >= lo;
                            // otherwise f keeps its initial |1> (the callers' precondition).
                            if enabled && exp >= b.lo { u64::from(b.lo + j - 1 < exp) } else { 1 }
                        }
                        (BodyKind::Therm, false) => u64::from(j == 0),
                        (BodyKind::Capture { .. }, _) if j < width => (init[j] >> shot) & 1,
                        (BodyKind::Capture { .. }, true) => {
                            if fires { (init[exp - b.lo] >> shot) & 1 } else { 0 }
                        }
                        (BodyKind::Capture { .. }, false) => 0,
                    };
                    assert_eq!(
                        got, want,
                        "k={} [{},{}) gated={} {:?} exp={} enabled={} data wire {} (odd_passes={})",
                        b.k, b.lo, b.hi, b.gated, b.kind, exp, enabled, j, odd_passes
                    );
                }
            }
            for &id in b.ctrl.iter().chain(&b.data) {
                *sim.qubit_mut(id) = 0;
            }
            assert!(sim.qubits.iter().all(|v| v & mask == 0), "dirty scratch k={} [{},{}) {:?}", b.k, b.lo, b.hi, b.kind);
            checked += batch.len();
        }
    }
    checked
}

/// One window through the leaf body in every mode, direction and round trip,
/// with the T model asserted; returns (shots, circuits, measured gated T).
fn leaf_window(k: usize, lo: usize, hi: usize) -> (usize, usize, usize) {
    let mut checked = 0;
    let mut cases = 0;
    let mut gated_t = 0;
    for gated in [true, false] {
        let expected_wires = (if gated && k >= 7 { k - 3 } else if gated && k >= 5 { k - 2 } else if gated && k <= 2 { k } else { k - 1 }) as u32;
        for coherent in [false, true] {
            let fwd = build(k, lo, hi, gated, coherent, &[false], false);
            let inv = build(k, lo, hi, gated, coherent, &[true], false);
            let want_t = expected_t(k, lo, hi, gated, coherent);
            assert_eq!(fwd.t, want_t, "T model k={k} [{lo},{hi}) gated={gated} coherent={coherent}");
            assert_eq!(inv.t, want_t, "T model (inverse) k={k} [{lo},{hi}) gated={gated} coherent={coherent}");
            assert_eq!(fwd.engine_wires, expected_wires, "k={k} [{lo},{hi}) gated={gated} engine wires");
            assert_eq!(inv.engine_wires, expected_wires);
            if coherent && !(gated && k >= 7) {
                assert_eq!(
                    canonical(fwd.ops.iter().rev().cloned()),
                    canonical(inv.ops.iter().cloned()),
                    "k={k} [{lo},{hi}) gated={gated}: inverse is not the mirror"
                );
            }
            if gated && !coherent {
                gated_t = fwd.t;
            }
            checked += check(&fwd, true) + check(&inv, true);
            for passes in [[false, true], [true, false], [true, true]] {
                let round = build(k, lo, hi, gated, coherent, &passes, false);
                assert_eq!(round.t, 2 * want_t);
                checked += check(&round, false);
            }
            cases += 5;
        }
    }
    (checked, cases, gated_t)
}

/// One window through the thermometer and capture bodies (gated unless
/// `ungated_too`), forward, inverse and the forward+inverse pair.
fn body_window(k: usize, lo: usize, hi: usize, ungated_too: bool) -> (usize, usize) {
    let mut checked = 0;
    let mut cases = 0;
    let width = hi - lo;
    let kinds = [
        BodyKind::Therm,
        BodyKind::Capture { scratch: false, ones: true },
        BodyKind::Capture { scratch: false, ones: false },
        BodyKind::Capture { scratch: true, ones: true },
    ];
    for gated in if ungated_too { vec![true, false] } else { vec![true] } {
        let engine_wires = (if gated && k >= 7 { k - 3 } else if gated && k >= 5 { k - 2 } else if gated && k <= 2 { k } else { k - 1 }) as u32;
        for coherent in [false, true] {
            for kind in kinds {
                let engine_t = expected_t(k, lo, hi, gated, coherent);
                let body_t = match kind {
                    BodyKind::Therm => 0,
                    BodyKind::Capture { scratch: false, .. } => width,
                    BodyKind::Capture { scratch: true, .. } => if coherent { 2 * width } else { width },
                };
                let scratch = matches!(kind, BodyKind::Capture { scratch: true, .. });
                let fwd = build_body(k, lo, hi, gated, coherent, kind, &[false]);
                let inv = build_body(k, lo, hi, gated, coherent, kind, &[true]);
                let round = build_body(k, lo, hi, gated, coherent, kind, &[false, true]);
                assert_eq!(fwd.t, engine_t + body_t, "T k={k} [{lo},{hi}) gated={gated} coherent={coherent} {kind:?}");
                assert_eq!(inv.t, engine_t + body_t);
                assert_eq!(round.t, 2 * (engine_t + body_t));
                assert_eq!(fwd.engine_wires, engine_wires + u32::from(scratch), "wires k={k} [{lo},{hi}) {kind:?}");
                assert_eq!(inv.engine_wires, engine_wires + u32::from(scratch));
                if coherent && !(gated && k >= 7) {
                    assert_eq!(
                        canonical(fwd.ops.iter().rev().cloned()),
                        canonical(inv.ops.iter().cloned()),
                        "k={k} [{lo},{hi}) gated={gated} {kind:?}: inverse is not the mirror"
                    );
                }
                if kind != BodyKind::Therm {
                    // The capture body is self-inverse: a descending pass alone
                    // must give the same capture as the ascending one.
                    checked += check_body(&inv, true);
                    cases += 1;
                }
                checked += check_body(&fwd, true) + check_body(&round, false);
                cases += 2;
            }
        }
    }
    (checked, cases)
}

/// Adversarial review cases (module doc); returns (shots, circuits).
fn run_adversarial() -> (usize, usize) {
    let mut checked = 0usize;
    let mut cases = 0usize;
    // (a) k = 9: every quadrant / half boundary of the fold, the register
    // ends, single leaves, the M1 class [226, 257), the D11 class e_A = W_A
    // (leaf at the window top, one past it, one below it).
    let boundary: [(usize, usize); 20] = [
        (0, 1), (511, 512), (255, 257), (256, 257), (127, 129), (383, 385), (128, 384), (130, 200), (300, 350),
        (400, 500), (226, 257), (1, 512), (0, 511), (256, 512), (0, 256), (255, 512), (128, 129), (384, 385),
        (129, 257), (257, 384),
    ];
    let mut line = String::from("PACKED_ONEHOT_STREAM adversarial k=9 boundary windows (gated measured T):");
    for &(lo, hi) in &boundary {
        let (s, c, t) = leaf_window(9, lo, hi);
        checked += s;
        cases += c;
        line.push_str(&format!(" [{lo},{hi})={t}"));
    }
    eprintln!("{line}");
    // (b) the design's engine windows on real packed_prefix_model states at
    // 9 bits: (step, W_A, W_c) from the exact pz_prefix recurrence over 3000
    // inputs (tools/packed_prefix_model.py semantics; scratch script
    // real_states.py) plus the design's own 1M-envelope step 378 (76, 256).
    // Sampled real states inside them (all values are run anyway): step 0
    // e_A=256 e_B=252 e_cb=1 (tight gap 0, e_A = W_A, off = 0, d = 2);
    // step 10 e_A=250 e_B=250 e_ca=5 e_cb=7 (gap 0, s = 0); step 378 e_B=48
    // e_cb=206 off=1; step 480+ draining e_A=0 e_B=1 e_ca=256 e_cb=254..255.
    let env: [(usize, usize, usize); 10] = [
        (0, 256, 1), (10, 253, 13), (100, 211, 77), (200, 159, 137), (300, 108, 207), (378, 68, 251), (378, 76, 256),
        (440, 33, 256), (480, 15, 256), (529, 1, 256),
    ];
    let mut real: Vec<(String, usize, usize)> = Vec::new();
    for &(step, wa, wc) in &env {
        let lo_a = wa.saturating_sub(78);
        real.push((format!("s{step}.D4"), lo_a + 1, wa + 1));
        real.push((format!("s{step}.D7z"), lo_a.max(257 - wc), wa));
        real.push((format!("s{step}.M5z"), 257 - wa, wc + 1));
        real.push((format!("s{step}.role"), wc.saturating_sub(78), wc));
    }
    let mut line = String::from("PACKED_ONEHOT_STREAM adversarial real windows k=9 (name=[lo,hi):T gated measured,+over width):");
    let mut over_sum = 0usize;
    let mut over_n = 0usize;
    for (name, lo, hi) in &real {
        if lo >= hi {
            let mut c = Circuit::new();
            let exp = c.alloc_qreg_bits("exp", 9);
            let gate = c.alloc_qreg("gate");
            onehot_stream_with(&mut c, &exp, *lo, *hi, Some(&gate), false, false, &mut |_, _, _| panic!("empty window visited"));
            assert!(c.b.ops.is_empty(), "{name}: empty gated window emits ops");
            line.push_str(&format!(" {name}=[{lo},{hi}):empty"));
            continue;
        }
        let (s, c, t) = leaf_window(9, *lo, *hi);
        checked += s;
        cases += c;
        let (s, c) = body_window(9, *lo, *hi, false);
        checked += s;
        cases += c;
        over_sum += t - (hi - lo);
        over_n += 1;
        line.push_str(&format!(" {name}=[{lo},{hi}):{t},+{}", t - (hi - lo)));
    }
    line.push_str(&format!(" | mean overhead over 1 T/leaf: {:.1} T per call", over_sum as f64 / over_n as f64));
    eprintln!("{line}");
    // D0: the 5-bit s_rot engine over [0, 29) (s <= 28), rooted at a gate.
    let (s, c, t) = leaf_window(5, 0, 29);
    checked += s;
    cases += c;
    let (s2, c2) = body_window(5, 0, 29, true);
    checked += s2;
    cases += c2;
    eprintln!("PACKED_ONEHOT_STREAM adversarial D0 k=5 [0,29): gated measured T={t} (model {})", expected_t(5, 0, 29, true, false));
    // (c) the thermometer and capture bodies on the author's windows too,
    // gated and ungated, and on the boundary windows that touch the fold.
    for &(k, lo, hi) in &[(9usize, 0usize, 512usize), (9, 5, 20), (9, 100, 130), (9, 226, 257), (9, 255, 257), (9, 511, 512), (9, 0, 1), (4, 0, 16), (3, 5, 8), (2, 0, 4), (1, 0, 2)] {
        let (s, c) = body_window(k, lo, hi, true);
        checked += s;
        cases += c;
    }
    // (d) the T model on the author's windows for every k (gated/ungated, both
    // clear modes) - checked again here so a change to the engine that keeps
    // the values right but changes the count is caught.
    for k in 1usize..=9 {
        let span = 1usize << k;
        for (lo, hi) in [(0usize, span), (5usize, 20usize.min(span)), (100usize, 130usize.min(span)), (span - 1, span)] {
            if lo >= hi {
                continue;
            }
            for gated in [true, false] {
                for coherent in [false, true] {
                    let b = build(k, lo, hi, gated, coherent, &[false], false);
                    assert_eq!(b.t, expected_t(k, lo, hi, gated, coherent), "T model k={k} [{lo},{hi}) gated={gated} coherent={coherent}");
                }
            }
        }
    }
    // (e) preconditions: hi > 2^k must panic (the design only supplies hi <= 2^k).
    {
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut c = Circuit::new();
            let exp = c.alloc_qreg_bits("exp", 5);
            onehot_stream_with(&mut c, &exp, 0, 33, None, false, false, &mut |_, _, _| {});
        }));
        std::panic::set_hook(hook);
        assert!(r.is_err(), "hi > 2^k did not panic");
    }
    (checked, cases)
}

pub(crate) fn run() {
    let mut checked = 0usize;
    let mut cases = 0usize;
    for k in 3usize..=9 {
        let span = 1usize << k;
        for (lo, hi) in [(0usize, span), (5usize, 20usize.min(span)), (100usize, 130usize.min(span))] {
            if lo >= hi {
                continue;
            }
            let width = hi - lo;
            let mut line = format!("PACKED_ONEHOT_STREAM k={k} window=[{lo},{hi}) ({width} idx):");
            for gated in [true, false] {
                let expected_wires = (if gated && k >= 7 { k - 3 } else if gated && k >= 5 { k - 2 } else if gated && k <= 2 { k } else { k - 1 }) as u32;
                let mut reported = false;
                for coherent in [false, true] {
                    for nested in [false, true] {
                        if nested && (k != 4 || lo != 5) {
                            continue;
                        }
                        let fwd = build(k, lo, hi, gated, coherent, &[false], nested);
                        let inv = build(k, lo, hi, gated, coherent, &[true], nested);
                        let round = build(k, lo, hi, gated, coherent, &[false, true], nested);
                        let twice = build(k, lo, hi, gated, coherent, &[false, false], nested);
                        assert_eq!(fwd.t, inv.t, "direction changes T");
                        assert_eq!(fwd.t, expected_t(k, lo, hi, gated, coherent), "T model k={k} [{lo},{hi}) gated={gated} coherent={coherent}");
                        if coherent && !(gated && k >= 7) {
                            // Descending = the exact gate-for-gate mirror of ascending.
                            assert_eq!(
                                canonical(fwd.ops.iter().rev().cloned()),
                                canonical(inv.ops.iter().cloned()),
                                "k={k} [{lo},{hi}) gated={gated}: inverse is not the mirror"
                            );
                        }
                        assert_eq!(fwd.engine_wires, expected_wires, "k={k} gated={gated} engine wires");
                        assert_eq!(inv.engine_wires, expected_wires);
                        for b in [&fwd, &inv] {
                            checked += check(b, true);
                        }
                        if coherent && gated && k >= 7 {
                            // The four-bit fold reuses clean endpoint wires in
                            // a different order. A global wire renaming is not
                            // a lifetime-aware comparison. Test the literal
                            // coherent inverse as well as both emitted orders.
                            let mut literal = build(k, lo, hi, gated, coherent, &[false], nested);
                            literal.ops = fwd.ops.iter().rev().filter(|op|
                                matches!(op.kind, OperationType::X | OperationType::CX | OperationType::CCX)
                            ).cloned().collect();
                            checked += check(&literal, true);
                        }
                        for b in [&round, &twice] {
                            checked += check(b, false);
                        }
                        cases += 4;
                        if !coherent && !nested && !reported {
                            reported = true;
                            line.push_str(&format!(
                                " {}: T={} ({:.2}/idx, wires {})",
                                if gated { "gated" } else { "ungated" },
                                fwd.t,
                                fwd.t as f64 / width as f64,
                                fwd.engine_wires
                            ));
                        } else if coherent && !nested && gated {
                            line.push_str(&format!(" coherent-gated: T={}", fwd.t));
                        }
                    }
                }
            }
            let uls = uls_toffoli(k, lo, hi);
            line.push_str(&format!(" | unary_iterate_log_star: T={uls} ({:.2}/idx)", uls as f64 / width as f64));
            eprintln!("{line}");
        }
    }
    // Small k (no fold / trivial trees) and empty windows.
    for k in 1usize..=2 {
        for gated in [true, false] {
            for coherent in [false, true] {
                let fwd = build(k, 0, 1 << k, gated, coherent, &[false], false);
                let inv = build(k, 0, 1 << k, gated, coherent, &[true], false);
                let expected_wires = (if gated { k } else { k - 1 }) as u32;
                assert_eq!(fwd.engine_wires, expected_wires, "k={k} gated={gated} engine wires");
                if coherent {
                    assert_eq!(canonical(fwd.ops.iter().rev().cloned()), canonical(inv.ops.iter().cloned()));
                }
                checked += check(&fwd, true) + check(&inv, true);
                let round = build(k, 0, 1 << k, gated, coherent, &[false, true], false);
                checked += check(&round, false);
                cases += 3;
                let single = build(k, 1, 2, gated, coherent, &[false], false);
                checked += check(&single, true);
                cases += 1;
            }
        }
    }
    {
        let mut c = Circuit::new();
        let exp = c.alloc_qreg_bits("exp", 5);
        let mut fired = 0usize;
        onehot_stream_with(&mut c, &exp, 7, 7, None, false, false, &mut |_, _, _| fired += 1);
        assert_eq!(fired, 0);
        assert!(c.b.ops.is_empty(), "empty window emits ops");
    }
    let (adv_checked, adv_cases) = run_adversarial();
    checked += adv_checked;
    cases += adv_cases;
    eprintln!(
        "PACKED_ONEHOT_STREAM PASS: {checked} exponent/gate/measurement shots over {cases} circuits (k=1..9, three windows, both directions, measured+coherent clears, nested conditions, forward+inverse round trips; adversarial: {adv_checked} shots / {adv_cases} circuits on fold-boundary, register-end and real packed_prefix_model windows, thermometer and capture bodies, T model asserted); phase 0, freed ancillae clean"
    );
}
