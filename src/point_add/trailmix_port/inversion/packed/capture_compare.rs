//! Packed-prefix primitive: the capture compare (`tools/spike/packed_design.md`
//! 2.3; consumers D4/D9 -> `off`, M10 -> `carry`, role compute/clear -> `role`).
//!
//! `capture_compare(c, root, v, u, addr, window, out)` runs the borrow cascade of
//! `borrow_compare_refs` (`shrunken_pz_primitives.rs:28-63`) UNGATED over the
//! classical window of cascade cells `v[0..n)` vs `u[0..n)` (cell 0 = the field's
//! LSB) and captures the borrow at the QUANTUM field end selected by `addr`:
//!
//! ```text
//!   out ^= root AND [addr in window] AND [ v mod 2^k  <  u mod 2^k ],
//!   k = window.cells(addr)   (the number of cascade cells inside the field)
//! ```
//!
//! `v`, `u`, `addr`, `root` are restored exactly; the primitive is self-inverse
//! (apply it again to clear `out`), so the backward driver runs the identical
//! call. The flag is written directly into its consumer: no `less` temp, no
//! clear pair, no measured phase oracle.
//!
//! # Precondition (exactness of the plain cascade)
//!
//! The captured bit is the compare of the LOW `k` cells. It is the full compare
//! `[v < u]` the callers want iff the operands tie above the field
//! (`v >> k == u >> k`). The design's structural fact - at every step end
//! `max(bl ca, bl cb) <= 257 - max(bl A, bl B)` (0 violations / 8.96M
//! step-states) - makes this hold for the role compare: with the capture at
//! `Q = 257 - max(e_ca, e_cb)` both rings are zero on `[max(e_A, e_B), Q)`, so
//! the plain cascade is exact and no window tie residue exists. D4/D9/M10 capture
//! exactly at the field end `e_B` / `e_cb` where both fields end; the cells
//! below cell 0 (`lo_A`, `lo_c`) are today's `narrow_lt` tie residue of the
//! support model. Bits ABOVE the capture position never influence the captured
//! value (the MAJ carry chain flows upward only, and the reverse cascade restores
//! them) - this is what the 257-wide foreign-bit selftest checks.
//!
//! # Mechanism
//!
//! The design says "between the two cascades the borrow after cell i-1 sits in
//! `b[i-1]`". Literally that is true only for the top cell: a MAJ cell `i` does
//! `cx(b[i], b[i-1])`, which mixes `~v[i]` into `b[i-1]` (the standard Cuccaro
//! carry line). The pure carry `c_{k-1} = [v mod 2^k < u mod 2^k]` therefore sits
//! on `b[k-1]` exactly BETWEEN cell `k-1` and cell `k`, and the capture of leaf
//! `k` is emitted there: the cascade cells are interleaved with the ascending
//! one-hot sweep (cells `0..k_lo` before it, cell `k` inside leaf `k`'s body
//! right after `out ^= g_k AND b[k-1]`, the cells above `k_hi` after it), then
//! the reverse cascade undoes the garbage - the same "capture inside the sweep"
//! pattern as `masked_add`'s carry/absorb leaves. Leaves are visited in
//! ascending `k`: ascending `addr` for `FieldEnd::AddrMinus`, descending `addr`
//! for `FieldEnd::BaseMinusAddr` (the role compare's `k = 257 - m`).
//!
//! The one-hot engine is a LOCAL copy of the design's DFS engine (2.2:
//! `measured_demux::visit` generalised with a leaf body, `[lo, hi]` pruning,
//! direction, gate root and the top-two-address-bit fold through one
//! `mcx_clean_k(3)`-shaped AND) because `packed::onehot_stream` is still a stub
//! in this tree; swap it for `onehot_stream` once that lands - the gate
//! structure is the same (1 CCX per visited tree node, `clear_and` uncomputes).
//! Debug switches: `MIDQ_ONEHOT_COHERENT=1` (CCX uncomputes instead of
//! `clear_and`), `MIDQ_ONEHOT_NOFOLD=1` (no top-two-bit fold; +1 engine wire).
//!
//! # Cost
//!
//! Toffoli `2n` (cascade forward + reverse) `+ ~z` (engine: tree nodes ~= leaves,
//! `+3` per visited top quarter for the fold) `+ z` (one capture per leaf), i.e.
//! `2n + 2z + O(log)`: measured 321 T for n = z = 78 (design: 314). Wires:
//! `bc.c` (1) + the engine's one-per-level (`m - 1` for an `m`-bit address with
//! the fold: 8 for the 9-bit exponents) = the design's "engine 8 + bc.c 1".
//!
//! # Choices where the design is silent
//!
//! * `window` is an INCLUSIVE address range `[lo, hi]` plus the address-to-cell
//!   map; addresses outside it (the width miss) capture nothing and leave `out`
//!   unchanged. Addresses mapping to `k = 0` (empty field: `[0 < 0] = 0`) are
//!   dropped from the sweep, `hi` is clamped to the address space; `k > n` is a
//!   caller error (assert).
//! * An empty effective range emits nothing at all (the cascade would be a
//!   no-op anyway).

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "capture_compare_selftest.rs"]
mod selftest_impl;

/// How the quantum address selects the cascade cell whose borrow is captured
/// (`k` = the number of cascade cells inside the field, capture on `b[k-1]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum FieldEnd {
    /// `k = addr - offset`: D4/D9 (cascade from wire `lo_A`, `addr = e_B`,
    /// `offset = lo_A`), M10 (`addr = e_cb`, `offset = lo_c`).
    AddrMinus(usize),
    /// `k = base - addr`: the role compare (cascade from wire 0, `addr = m =
    /// max(e_ca, e_cb)`, `base = 257`, capture at `Q - 1 = 256 - m`).
    BaseMinusAddr(usize),
}

/// The classical window of the sweep: address values `[lo, hi]` (inclusive)
/// and the address-to-cell map.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) struct CaptureWindow {
    pub lo: usize,
    pub hi: usize,
    pub field: FieldEnd,
}

impl CaptureWindow {
    /// Number of cascade cells inside the field for address value `a`
    /// (`None` when the map underflows, i.e. the address is off the window).
    #[allow(dead_code)]
    pub(crate) fn cells(&self, a: usize) -> Option<usize> {
        match self.field {
            FieldEnd::AddrMinus(offset) => a.checked_sub(offset),
            FieldEnd::BaseMinusAddr(base) => base.checked_sub(a),
        }
    }
}

fn env_flag(name: &str) -> bool {
    std::env::var(name).ok().as_deref() == Some("1")
}

/// Uncompute `t == a AND b`: `clear_and` (HMR + `cz_if_bit`, 0 T) or a CCX.
fn clear(c: &mut Circuit, t: &QReg, a: &QReg, b: &QReg, coherent: bool) {
    if coherent {
        c.ccx(a, b, t);
    } else {
        c.clear_and(t, a, b);
    }
}

/// DFS one-hot sweep below `parent` over the address bits `bits` (LSB first;
/// the top bit is split first), values `[prefix, prefix + 2^bits.len())`,
/// pruned to `[lo, hi]`. At each leaf `body(c, g, value)` with
/// `g = parent AND [bits == value - prefix]`.
fn visit(
    c: &mut Circuit,
    parent: &QReg,
    bits: &[QReg],
    prefix: usize,
    lo: usize,
    hi: usize,
    ascending: bool,
    coherent: bool,
    body: &mut dyn FnMut(&mut Circuit, &QReg, usize),
) {
    let span = 1usize << bits.len();
    if prefix + span <= lo || prefix > hi {
        return;
    }
    let Some((bit, lower)) = bits.split_last() else {
        body(c, parent, prefix);
        return;
    };
    let half = 1usize << lower.len();
    let want0 = prefix <= hi && prefix + half > lo;
    let want1 = prefix + half <= hi && prefix + 2 * half > lo;
    let child = c.alloc_qreg("oh.node");
    match (want0, want1) {
        (true, true) if ascending => {
            c.x(bit);
            c.ccx(parent, bit, &child); // parent AND NOT bit
            c.x(bit);
            visit(c, &child, lower, prefix, lo, hi, ascending, coherent, body);
            c.cx(parent, &child); // parent AND bit
            visit(c, &child, lower, prefix + half, lo, hi, ascending, coherent, body);
            clear(c, &child, parent, bit, coherent);
        }
        (true, true) => {
            c.ccx(parent, bit, &child); // parent AND bit
            visit(c, &child, lower, prefix + half, lo, hi, ascending, coherent, body);
            c.cx(parent, &child); // parent AND NOT bit
            visit(c, &child, lower, prefix, lo, hi, ascending, coherent, body);
            c.x(bit);
            clear(c, &child, parent, bit, coherent);
            c.x(bit);
        }
        (true, false) => {
            c.x(bit);
            c.ccx(parent, bit, &child);
            visit(c, &child, lower, prefix, lo, hi, ascending, coherent, body);
            clear(c, &child, parent, bit, coherent);
            c.x(bit);
        }
        (false, true) => {
            c.ccx(parent, bit, &child);
            visit(c, &child, lower, prefix + half, lo, hi, ascending, coherent, body);
            clear(c, &child, parent, bit, coherent);
        }
        (false, false) => unreachable!("pruned above"),
    }
    c.zero_and_free(child);
}

/// The DFS one-hot engine rooted at `root` over the whole address, with the
/// two top address bits folded into the root by one 3-control AND (design
/// 2.2: one engine wire per level, `m - 1` for `m` bits). Leaves in `[lo, hi]`
/// in ascending or descending value order.
fn onehot_sweep(
    c: &mut Circuit,
    root: &QReg,
    addr: &[QReg],
    lo: usize,
    hi: usize,
    ascending: bool,
    body: &mut dyn FnMut(&mut Circuit, &QReg, usize),
) {
    let m = addr.len();
    assert!(lo <= hi && hi < (1usize << m), "capture window [{lo}, {hi}] outside a {m}-bit address");
    let coherent = env_flag("MIDQ_ONEHOT_COHERENT");
    if m < 3 || env_flag("MIDQ_ONEHOT_NOFOLD") {
        visit(c, root, addr, 0, lo, hi, ascending, coherent, body);
        return;
    }
    let (top1, top0) = (&addr[m - 1], &addr[m - 2]);
    let lower = &addr[..m - 2];
    let quarter = 1usize << (m - 2);
    let mut quarters: Vec<usize> = (0..4)
        .filter(|q| q * quarter <= hi && (q + 1) * quarter > lo)
        .collect();
    if !ascending {
        quarters.reverse();
    }
    for q in quarters {
        let (b1, b0) = (q >> 1 & 1 == 1, q & 1 == 1);
        if !b1 { c.x(top1); }
        if !b0 { c.x(top0); }
        // node = root AND top1' AND top0' (mcx_clean_k(3) shape: 2 CCX + clear_and)
        let t = c.alloc_qreg("oh.fold.t");
        c.ccx(root, top1, &t);
        let node = c.alloc_qreg("oh.fold");
        c.ccx(&t, top0, &node);
        clear(c, &t, root, top1, coherent);
        c.zero_and_free(t);
        visit(c, &node, lower, q * quarter, lo, hi, ascending, coherent, body);
        // uncompute node: recompute t, clear node against (t, top0), clear t.
        let t = c.alloc_qreg("oh.fold.t");
        c.ccx(root, top1, &t);
        clear(c, &node, &t, top0, coherent);
        clear(c, &t, root, top1, coherent);
        c.zero_and_free(t);
        c.zero_and_free(node);
        if !b0 { c.x(top0); }
        if !b1 { c.x(top1); }
    }
}

/// `out ^= root AND [addr in window] AND [v mod 2^k < u mod 2^k]`,
/// `k = window.cells(addr)`; see the module doc. `v[i]`/`u[i]` = cascade cell
/// `i` (cell 0 = the field's LSB; wires are the caller's, contiguous or not).
#[allow(dead_code)]
pub(crate) fn capture_compare(
    c: &mut Circuit,
    root: &QReg,
    v: &[&QReg],
    u: &[&QReg],
    addr: &[QReg],
    window: CaptureWindow,
    out: &QReg,
) {
    let n = v.len();
    assert_eq!(u.len(), n, "capture_compare: operand widths differ");
    assert!(window.lo <= window.hi, "capture_compare: empty window");
    assert!(addr.len() < usize::BITS as usize, "capture_compare: address too wide");
    debug_assert!(
        v.iter().chain(u.iter()).all(|q| q.id() != out.id() && q.id() != root.id())
            && addr.iter().all(|q| q.id() != out.id() && q.id() != root.id())
            && out.id() != root.id(),
        "capture_compare: out/root must be distinct from the operands and the address"
    );
    // Effective address range: the values in [lo, hi] whose field has 1..=n
    // cells (values above the address space cannot occur: clamp).
    let hi_addr = (1usize << addr.len()) - 1;
    let mut eff: Option<(usize, usize)> = None;
    for a in window.lo..=window.hi.min(hi_addr) {
        let Some(k) = window.cells(a) else { continue };
        assert!(k <= n, "capture_compare: address {a} selects {k} cells, cascade has {n}");
        if k == 0 { continue; }
        eff = Some(match eff { None => (a, a), Some((l, h)) => (l.min(a), h.max(a)) });
    }
    let Some((lo, hi)) = eff else { return };
    let ascending = matches!(window.field, FieldEnd::AddrMinus(_));
    let k_lo = window.cells(if ascending { lo } else { hi }).unwrap();
    let k_hi = window.cells(if ascending { hi } else { lo }).unwrap();
    debug_assert!(1 <= k_lo && k_lo <= k_hi && k_hi <= n);

    let section = c.push_section("p.ccmp");
    for q in v {
        c.x(q); // v -> ~v
    }
    let a = u; // accumulator (sum line)
    let b = v; // = ~v (carry line)
    let cc = c.alloc_qreg("bc.c");
    // MAJ cell i (carry-in on b[i-1], or cc for i = 0): leaves c_i on b[i].
    let cell = |c: &mut Circuit, i: usize| {
        if i == 0 {
            c.cx(b[0], a[0]);
            c.cx(b[0], &cc);
            c.ccx(&cc, a[0], b[0]);
        } else {
            c.cx(b[i], a[i]);
            c.cx(b[i], b[i - 1]);
            c.ccx(b[i - 1], a[i], b[i]);
        }
    };
    for i in 0..k_lo {
        cell(c, i);
    }
    let mut next_cell = k_lo;
    {
        let mut body = |c: &mut Circuit, g: &QReg, value: usize| {
            let k = window.cells(value).unwrap();
            assert_eq!(k, next_cell, "capture leaves must arrive in ascending cell order");
            c.ccx(g, b[k - 1], out); // the pure carry c_{k-1} sits on b[k-1] here
            if k < n {
                cell(c, k);
            }
            next_cell = k + 1;
        };
        onehot_sweep(c, root, addr, lo, hi, ascending, &mut body);
    }
    debug_assert_eq!(next_cell, k_hi + 1);
    for i in (k_hi + 1)..n {
        cell(c, i);
    }
    // Reverse cascade: restore ~v, u and cc.
    for i in (1..n).rev() {
        c.ccx(b[i - 1], a[i], b[i]);
        c.cx(b[i], b[i - 1]);
        c.cx(b[i], a[i]);
    }
    c.ccx(&cc, a[0], b[0]);
    c.cx(b[0], &cc);
    c.cx(b[0], a[0]);
    c.zero_and_free(cc);
    for q in v {
        c.x(q);
    }
    c.pop_section(&section);
}

/// Entry called by `packed::selftest_all` (`MIDQ_PACKED_SELFTEST=1`).
#[allow(dead_code)]
pub(crate) fn selftest() {
    selftest_impl::run();
}
