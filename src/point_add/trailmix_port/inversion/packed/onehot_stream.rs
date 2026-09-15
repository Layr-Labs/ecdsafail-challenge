//! Packed-prefix primitive `onehot_stream` (tools/spike/packed_design.md, section 2.2):
//! the DFS one-hot engine generalised from `inversion/measured_demux.rs::visit`.
//!
//! `onehot_stream(c, exp, lo, hi, gate, inverse, body)` iterates the k-bit
//! little-endian exponent register `exp` (`exp[0]` = LSB, k <= 9 in the design,
//! any k >= 1 accepted) over the index window `[lo, hi)` and calls
//! `body(c, i, flag)` once per index `i` of the window with a `flag` wire that
//! is |1> exactly when `gate AND [exp == i]` (`gate == None`: `[exp == i]`).
//! Indices outside the window are never visited: every subtree of the address
//! tree that is disjoint from `[lo, hi)` is pruned, so the cost is ~1 T per
//! visited index (see below), not per address.
//!
//! Mechanism (the prefix-AND tree of `measured_demux::visit`, leaf callback
//! instead of the XOR target): at a node whose parent flag `p` is |1> iff the
//! address bits above the node match its base, `child = p AND bit` (1 CCX);
//! the in-range half with `bit = 1` is visited under `child`, `cx(p, child)`
//! turns it into `p AND NOT bit` (0 T) for the other half, and `child` is
//! uncomputed with `clear_and` (HMR + `cz_if_bit`, the exact measured
//! AND-uncompute, 0 T). The last level hands each leaf its one-hot wire the
//! same way. Both halves of a node share one CCX, so the engine costs one T per
//! visited internal node = `(hi - lo) + O(k)` T, ~1 T per visited index; with
//! `MIDQ_ONEHOT_COHERENT=1` every clear is a CCX again (2 T per node, no
//! measurement) - the debug switch named in the design.
//!
//! Direction: `inverse = false` visits `lo, lo+1, ..., hi-1` (the `bit = 0`
//! half of every node first); `inverse = true` visits `hi-1, ..., lo` (the
//! child order swapped). In coherent mode the descending call emits, gate for
//! gate, the mirror image of the ascending call, so
//! `onehot_stream(.., inverse = true, body_inverse)` is the exact inverse of
//! `onehot_stream(.., inverse = false, body)`; with measured clears the two
//! differ only in the (exact, 0 T) uncompute of the same flags.
//!
//! Wires: one per tree level. With a gate and k >= 3 the two top address bits
//! are folded into the gate: the root of every visited quadrant subtree is
//! `gate AND [b_{k-1} == h] AND [b_{k-2} == l]` held in ONE wire, so the
//! peak is `k - 1` wires (8 for a 9-bit exponent, 7 with 7-bit rebased
//! exponents, as the design's peak table counts). Design choice (the design
//! says "by one `mcx_clean_k(3)`"): the fold is built from a *transient*
//! level-1 node `t = gate AND b_{k-1}` that is materialised (1 CCX), used to
//! (re)target the root, and cleared (0 T) again before the subtree is entered,
//! so only `root + t` = 2 <= k - 1 wires are live between quadrants. The
//! root moves between adjacent quadrants by a `cx(t, root)` flip and between
//! halves by one clear + one CCX: 3 T for one visited quadrant, 7 T for all
//! four, against 12 T for four `mcx_clean_k(3)` compute/uncompute pairs, with
//! identical wire counts and no X gate on the address. With a gate and
//! k <= 2 the plain tree (k wires) is used - folding cannot save a wire there.
//! Without a gate the top address bit itself is the level-1 flag (X-bracketed
//! while its `bit = 0` half is visited: the only transient change to `exp`),
//! giving `k - 1` wires as well (0 for k = 1, where the flag IS `exp[0]`).
//!
//! Contract for `body`: it may use `flag` as a control and must not write
//! `flag`, `exp` or `gate` (they are the engine's live controls; the derived
//! thermometer `f = [i < exp]` of design 2.2 is the caller's own wire,
//! toggled `f ^= flag` at the leaf). No section is pushed: the engine's T is
//! attributed to the calling primitive's section. Preconditions:
//! `hi <= 2^k`; an empty window (`lo >= hi`) emits nothing.
//!
//! Selftest (`MIDQ_PACKED_SELFTEST=1`, `onehot_stream_selftest.rs`): for
//! k = 3..=9, every exponent value, both gate values, windows `[0, 2^k)`,
//! `[5, 20)`, `[100, 130)` (clipped to `2^k`), both directions, measured and
//! coherent clears, nested classical conditions: exactly one leaf fires and
//! it is the exponent (none when outside the window or gate = 0), phase 0,
//! every freed ancilla clean, forward-then-inverse restores; T per visited
//! index and the engine's wire peak are printed next to
//! `unary_iterate_log_star` on the same task.

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "onehot_stream_selftest.rs"]
mod selftest_impl;

/// DFS one-hot engine over `exp` on the window `[lo, hi)`; see the module doc.
#[allow(dead_code)]
pub(crate) fn onehot_stream(
    c: &mut Circuit,
    exp: &[QReg],
    lo: usize,
    hi: usize,
    gate: Option<&QReg>,
    inverse: bool,
    body: &mut dyn FnMut(&mut Circuit, usize, &QReg),
) {
    let coherent = std::env::var("MIDQ_ONEHOT_COHERENT").ok().as_deref() == Some("1");
    onehot_stream_with(c, exp, lo, hi, gate, inverse, coherent, body);
}

/// `onehot_stream` with the clear mode chosen by the caller (`coherent`: CCX
/// uncomputes instead of `clear_and`).
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn onehot_stream_with(
    c: &mut Circuit,
    exp: &[QReg],
    lo: usize,
    hi: usize,
    gate: Option<&QReg>,
    inverse: bool,
    coherent: bool,
    body: &mut dyn FnMut(&mut Circuit, usize, &QReg),
) {
    let k = exp.len();
    assert!(k >= 1, "onehot_stream: empty exponent register");
    assert!(k < usize::BITS as usize - 1, "onehot_stream: {k}-bit exponent");
    assert!(hi <= 1usize << k, "onehot_stream: hi {hi} exceeds 2^{k}");
    if lo >= hi {
        return;
    }
    let eng = Engine { exp, lo, hi, descending: inverse, coherent };
    match gate {
        Some(g) if k >= 3 => eng.folded_root(c, g, body),
        Some(g) => eng.visit(c, k, 0, g, body),
        None => {
            // The top bit is its own flag: |1> on the upper half, X-bracketed
            // on the lower half. No wire, no T.
            let bit = &exp[k - 1];
            let half = 1usize << (k - 1);
            for lower_half in eng.side_order() {
                if lower_half && eng.in_range(0, half) {
                    c.x(bit);
                    eng.visit(c, k - 1, 0, bit, body);
                    c.x(bit);
                } else if !lower_half && eng.in_range(half, half) {
                    eng.visit(c, k - 1, half, bit, body);
                }
            }
        }
    }
}

struct Engine<'a> {
    exp: &'a [QReg],
    lo: usize,
    hi: usize,
    descending: bool,
    coherent: bool,
}

impl Engine<'_> {
    /// Does the subtree `[base, base + size)` meet the window?
    fn in_range(&self, base: usize, size: usize) -> bool {
        base < self.hi && base + size > self.lo
    }

    /// Visiting order of a node's halves: `true` = the `bit = 0` (lower) half.
    fn side_order(&self) -> [bool; 2] {
        if self.descending { [false, true] } else { [true, false] }
    }

    /// Uncompute `t = a AND b` (t returns to |0>): measured by default, CCX in
    /// coherent mode.
    fn clear(&self, c: &mut Circuit, t: &QReg, a: &QReg, b: &QReg) {
        if self.coherent {
            c.ccx(a, b, t);
        } else {
            c.clear_and(t, a, b);
        }
    }

    /// Visit the subtree with `level` address bits left below `parent`, which
    /// is |1> iff the gate holds and the address bits above `level` spell
    /// `base`. Only called on subtrees that meet the window.
    fn visit(
        &self,
        c: &mut Circuit,
        level: usize,
        base: usize,
        parent: &QReg,
        body: &mut dyn FnMut(&mut Circuit, usize, &QReg),
    ) {
        if level == 0 {
            body(c, base, parent);
            return;
        }
        let bit = &self.exp[level - 1];
        let half = 1usize << (level - 1);
        let lower = self.in_range(base, half);
        let upper = self.in_range(base + half, half);
        debug_assert!(lower || upper, "onehot_stream: visited a pruned subtree");
        let child = c.alloc_qreg("onehot.node");
        c.ccx(parent, bit, &child); // child = parent AND bit
        for lower_half in self.side_order() {
            if lower_half && lower {
                c.cx(parent, &child); // parent AND NOT bit
                self.visit(c, level - 1, base, &child, body);
                c.cx(parent, &child); // back to parent AND bit
            } else if !lower_half && upper {
                self.visit(c, level - 1, base + half, &child, body);
            }
        }
        self.clear(c, &child, parent, bit);
        c.zero_and_free(child);
    }

    /// Gated, k >= 3: the two top address bits are folded with the gate into
    /// one root wire per visited quadrant `q` (`q >> 1` = value of `b_{k-1}`,
    /// `q & 1` = value of `b_{k-2}`); quadrant subtrees have `k - 2` levels.
    fn folded_root(&self, c: &mut Circuit, g: &QReg, body: &mut dyn FnMut(&mut Circuit, usize, &QReg)) {
        let k = self.exp.len();
        let quarter = 1usize << (k - 2);
        let mut quadrants: Vec<usize> = (0..4).filter(|&q| self.in_range(q * quarter, quarter)).collect();
        if self.descending {
            quadrants.reverse();
        }
        let mut root: Option<QReg> = None;
        let mut current: Option<usize> = None;
        for &q in &quadrants {
            self.retarget(c, g, &mut root, current, Some(q));
            current = Some(q);
            let r = root.as_ref().expect("onehot_stream: root materialised");
            self.visit(c, k - 2, q * quarter, r, body);
        }
        self.retarget(c, g, &mut root, current, None);
        debug_assert!(root.is_none());
    }

    /// Move the root flag from quadrant `from` to quadrant `to` (`None` =
    /// no root held) through the transient level-1 node `t = g AND b_{k-1}`.
    /// Emits a palindromic gate sequence, so `retarget(a, b)` is the exact
    /// mirror of `retarget(b, a)` in coherent mode.
    fn retarget(&self, c: &mut Circuit, g: &QReg, root: &mut Option<QReg>, from: Option<usize>, to: Option<usize>) {
        let k = self.exp.len();
        let b1 = &self.exp[k - 1];
        let b0 = &self.exp[k - 2];
        let t = c.alloc_qreg("onehot.t");
        c.ccx(g, b1, &t);
        let mut t_is = 1usize; // t = g AND [b1 == t_is]
        let mut aim_t = |c: &mut Circuit, want: usize| {
            if t_is != want {
                c.cx(g, &t);
                t_is = want;
            }
        };
        match (from, to) {
            (None, None) => {}
            (None, Some(tq)) => {
                aim_t(c, tq >> 1);
                let r = c.alloc_qreg("onehot.root");
                c.ccx(&t, b0, &r);
                if tq & 1 == 0 {
                    c.cx(&t, &r);
                }
                *root = Some(r);
            }
            (Some(fq), Some(tq)) if fq >> 1 == tq >> 1 => {
                // Same half: flip the root's b0 polarity in place (0 T).
                aim_t(c, fq >> 1);
                let r = root.as_ref().expect("onehot_stream: root held");
                if fq & 1 == 0 {
                    c.cx(&t, r); // root = t AND b0
                }
                if tq & 1 == 0 {
                    c.cx(&t, r); // root = t AND NOT b0
                }
            }
            (Some(fq), to) => {
                aim_t(c, fq >> 1);
                let r = root.take().expect("onehot_stream: root held");
                if fq & 1 == 0 {
                    c.cx(&t, &r); // root = t AND b0
                }
                self.clear(c, &r, &t, b0);
                c.zero_and_free(r);
                if let Some(tq) = to {
                    aim_t(c, tq >> 1);
                    let r = c.alloc_qreg("onehot.root");
                    c.ccx(&t, b0, &r);
                    if tq & 1 == 0 {
                        c.cx(&t, &r);
                    }
                    *root = Some(r);
                }
            }
        }
        aim_t(c, 1);
        self.clear(c, &t, g, b1);
        c.zero_and_free(t);
    }
}

/// Selftest entry called by `packed::selftest_all` (MIDQ_PACKED_SELFTEST=1).
#[allow(dead_code)]
pub(crate) fn selftest() {
    selftest_impl::run();
}
