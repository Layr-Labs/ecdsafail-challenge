//! Packed-prefix primitive: the two aligned-window exponent scans of
//! `tools/spike/packed_design.md` 2.4 (with the 2026-09-13 refuter fixes folded
//! in), plus the sub-ring rotation and the narrow controlled adder they need.
//!
//! * [`aligned_scan_top`] = **D11** (design 3.1): the drop scan after a division.
//!   R1 is in the s-frame (`A_new >> s` on `[0, E)`, `E = e_B + off`). Rotate the
//!   sub-ring `[L, W_A)`, `L = max(0, lo_B - 32)`, UP by the 7-bit quantum amount
//!   `t7 = W_A - e_B` so that s-frame wire `e_B - 1` (a field wire for both `off`
//!   values) lands at the ring top `W_A - 1`; the classical 32-window
//!   `[W_A - 32, W_A)` then holds s-frame wires `[e_B - 32, e_B)`: R's MSB at index
//!   `k = 31 + off - d` (`d = e_A_old - bl(A_new) >= 1`, `d <= 31 + off` on the
//!   support; measured max 24) with only R's own zeros above it. The plain KG
//!   ladder `bit_length_lean_middle` (top-down, 3n form) deposits `k` into a
//!   6-bit `pos`; `e_A += gate * (pos - 31)`; the same ladder un-deposits; the
//!   ring is rotated back DOWN by the recomputed `t7`. Net with D7b's `-off`:
//!   `e_A -= d`. When `W_A < 32` the window is `[0, W_A)` (`n_w = W_A`) and the
//!   update is `e_A += gate * (pos - (n_w - 1))`.
//!   - The e_A update is the design's literal form: a 6-bit narrow controlled
//!     add of `pos` (zero-extended into the 9-bit e_A) then a controlled constant
//!     subtract of `n_w - 1`, so the terminal override D11t (`e_A -= pos; e_A -=
//!     shift; e_A += 30`, run by the caller through `hook` while `pos` is
//!     deposited) cancels it exactly whatever garbage / sentinel `pos` holds on
//!     an exact-division row (A_new = 0). With `MIDQ_KG_ZERO_LAYER=1` an all-zero
//!     window deposits the sentinel `pos = 63`. The hook runs after the update in
//!     the forward direction and before its inverse in the inverse direction.
//!   - Inverse = the same rotations and ladders with `e_A -= gate*(pos-(n_w-1))`;
//!     the alignment amount depends on `e_B` only (design 3.4), never on `e_A`.
//! * [`aligned_scan_bottom`] = **M1** (design 3.2): the gap scan before a
//!   multiply. R2 is in the LSB frame (`B` on `[0, e_B)`, `ca_old` MSB-anchored at
//!   wire 256). Rotate the sub-ring `[lo_B, T)`, `T = min(257, W_B + 32)`, DOWN by
//!   `t7 = e_B - lo_B` so that the window `[lo_B, lo_B + 32)` holds original wires
//!   `[e_B, e_B + 32)` (wrapping B's wires from `lo_B` up into positions
//!   `>= T - e_B` when `e_B + 32 > T`): gap zeros then ca's MSB at position
//!   `g = 257 - e_B - e_ca` on `ca_old != 0` rows (gap <= 25 measured; `gap_bound`
//!   miss for gap > 31). The ladder runs in ASCENDING wire order (the window
//!   passed reversed), so it deposits `pos = 31 - g`, or the sentinel 63 on an
//!   all-zero window (`MIDQ_KG_ZERO_LAYER=1` is REQUIRED and asserted). Then:
//!   `pos ^= 31` (free) turns the low 5 bits into `g` and bit 5 into the
//!   sentinel flag; `e_B` is transformed in place into `u = 257 - e_B` (X on bits
//!   0-7, KG increment of bits 1-8); the 9-bit borrow compare of
//!   `v = g + 256 * sentinel` against `u` gives **`nz = [pos != 63] AND [g < 257 -
//!   e_B]`** in one cascade (the sentinel operand 256 never passes `< 257 - e_B`
//!   for `e_B >= 1`, i.e. on every row with `B != 0`); `g' = gate AND nz`;
//!   `e_ca += g' * g; e_ca -= g' * u` (net `e_ca -= 257 - e_B - g`, exactly
//!   `bl(ca_old)`, leaving 0); `g'` released by `clear_and`; the same compare
//!   clears `nz` (the operands `v`, `u` are untouched by the erase); `u` is
//!   transformed back; un-deposit; rotate back UP. `ca_old = 0` rows (the first
//!   multiply of every input) give `nz = 0` whatever the window holds (all-zero
//!   -> sentinel; `e_B > 225` -> B's wrapped bits at `g >= 257 - e_B`), so `e_ca`
//!   stays 0 with no assumption on the window content (refuter 2's fix).
//!   Inverse = the same sequence with `e_ca += g' * u; e_ca -= g' * g` (restores
//!   `bl(ca_old)` from 0, the backward driver's use).
//!
//! Choices where the design leaves room (all documented above): the rotation
//! amounts are formed by one uncontrolled 7-bit Cuccaro add against an X-bracket
//! (`t7 = ~(~W_A + e_B)` / `t7 = ~(lo_B + ~e_B)`, 14 T each way, no add_const);
//! the ascending ladder yields `31 - g` rather than `g` (a free XOR fixes it);
//! `nz`'s two terms are one 9-bit cascade with the sentinel bit as operand bit 8
//! (3 clean zero-extension wires, freed between the compares); the erase is
//! `+g, -u` in that order (no transient wrap); D11's update is the literal
//! form `pos - (n_w - 1)` (6-bit narrow add with the `+1` as its carry-in, then
//! a NAF constant subtract of `n_w`: one 4-bit controlled decrement for the
//! 32-window, 22 + 6 = 28 T measured) rather than the 5-bit complement trick, so D11t can use
//! the full 6-bit `pos` as written.
//!
//! The sub-ring rotation lives here as [`subring_rotate`] (the `ring_rotate`
//! primitive was written concurrently; `ring_rotate::ring_rotate(c, &r[l..t],
//! amount, inverse)` is the drop-in once both are landed): layer i is the
//! cycle decomposition of `w -> (w + 2^i mod S) mod S`, `S - gcd(2^i, S)`
//! Fredkins, no precondition. `exponent_arith::gap_erase/gap_deposit` overlap
//! M1's internal erase; M1 keeps its own because its `pos` convention
//! (`31 - g`, XOR'd to `g`, sentinel in bit 5) and the `nz` gate are one unit.
//!
//! **Environment preconditions** (both scans build `bit_length_lean_middle`,
//! whose ladder is env-selected): `MIDQ_KG_ZERO_LAYER=1` for M1 (required) and
//! for the D11 sentinel claim; `MIDQ_CHUNKED_PREFIX` must NOT be `1` whenever
//! the zero layer is wanted - `chunked_bitlength::xor` (the production route's
//! default, `trailmix_port::configure_sub1000_trailmix_route`) has no k = -1
//! layer, so an all-zero window would deposit 0 and M1's `nz` gate would erase
//! `e_ca` by a garbage amount while the `MIDQ_KG_ZERO_LAYER` assert still
//! passes (found by the 2026-09-13 review; both scans now refuse to build in
//! that case). `MIDQ_CHUNK_COMPARE=1` (+ `MIDQ_VARIABLE_CHUNKS`) swaps the 9-bit
//! `nz` cascade for the chunked measured compare - exact, different T (the
//! selftest runs a pass under the production route with the chunked prefix
//! forced off). `LOWQ_ONE_A_ELIM` / `LOWQ_COMPACT_KGANC` only change the
//! ladder's scratch (10 -> 9 wires for D11).
//!
//! Off the support both circuits are still permutations and `inverse = true`
//! is the exact gate-inverse of `inverse = false` for ANY input (the selftest
//! round-trips random garbage), so a missed row (`drop_bound`, `gap_bound`,
//! width) corrupts only its own exponent and is undone by the backward pass.
//!
//! Selftest: `aligned_scan_selftest.rs` (MIDQ_PACKED_SELFTEST=1).

use crate::point_add::trailmix_port::arith::cuccaro::{
    add_cuccaro_3n_uncontrolled_refs, controlled_add_cuccaro_3n_refs,
};
use crate::point_add::trailmix_port::arith::khattar_gidney::{cinc_khattar_gidney_refs, inc_khattar_gidney_refs};
use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::borrow_compare_refs;

use super::super::{bit_length_lean_middle, bit_length_lean_middle_refs, kg_zero_layer_enabled, xor_const};

#[path = "aligned_scan_selftest.rs"]
mod aligned_scan_selftest;

/// Exponent width (design: 9-bit bit-lengths 0..256).
pub(crate) const EXP_BITS: usize = 9;
/// Alignment-amount width (design: 7-bit sub-ring rotations).
pub(crate) const T7_BITS: usize = 7;
/// Aligned window width.
pub(crate) const WINDOW: usize = 32;
/// `pos` width (holds the initial |n> = 32 and the sentinel 63).
pub(crate) const POS_BITS: usize = 6;

/// Cyclic rotation of the sub-ring `ring` (S wires) by the quantum amount
/// `amount` (LSB first): the value at `ring[w]` moves to `ring[(w + amount) mod S]`
/// when `up`, and the exact gate-inverse (`(w - amount) mod S`) when `!up`.
/// Layer i is the permutation `w -> (w + 2^i mod S) mod S` as a product of
/// cycles, `S - gcd(2^i mod S, S)` Fredkins (`cswap` = CX-CCX-CX, 1 T each)
/// controlled on `amount[i]`; layers with `2^i = 0 (mod S)` are skipped.
/// `!up` emits the layers in descending order with each swap list reversed
/// (a Fredkin is self-inverse). No precondition: a permutation of the ring.
pub(crate) fn subring_rotate(c: &mut Circuit, ring: &[&QReg], amount: &[QReg], up: bool) {
    let s = ring.len();
    if s < 2 || amount.is_empty() {
        return;
    }
    let prev = c.push_section("p.rot");
    let mut layers: Vec<(usize, Vec<(usize, usize)>)> = Vec::new();
    for (i, _) in amount.iter().enumerate() {
        let k = (1usize << i) % s;
        if k == 0 {
            continue;
        }
        let mut visited = vec![false; s];
        let mut swaps = Vec::new();
        for start in 0..s {
            if visited[start] {
                continue;
            }
            visited[start] = true;
            let mut w = (start + k) % s;
            while w != start {
                visited[w] = true;
                swaps.push((start, w));
                w = (w + k) % s;
            }
        }
        layers.push((i, swaps));
    }
    if !up {
        layers.reverse();
        for layer in layers.iter_mut() {
            layer.1.reverse();
        }
    }
    for (i, swaps) in layers {
        for (a, b) in swaps {
            c.cswap(&amount[i], ring[a], ring[b]);
        }
    }
    c.pop_section(&prev);
}

/// Toffoli count of one `subring_rotate` of a ring of `s` wires by a `bits`-bit
/// amount (for reporting).
pub(crate) fn subring_rotate_toffoli(s: usize, bits: usize) -> usize {
    if s < 2 {
        return 0;
    }
    (0..bits)
        .map(|i| {
            let k = (1usize << i) % s;
            if k == 0 { 0 } else { s - gcd(k, s) }
        })
        .sum()
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The alignment amount `t` (T7_BITS wires, |0> on entry) from the exponent `e`
/// and the classical `konst`, mod 2^7:
/// * `negate_e`: `t := konst - e`  (D11: `W_A - e_B`), as `t = ~(~konst + e)`;
/// * else:       `t := e - konst`  (M1: `e_B - lo_B`), as `t = ~(konst + ~e)`.
/// One uncontrolled 7-bit Cuccaro add (2n = 14 T measured) against
/// X-brackets; `e` is restored. `uncompute` returns `t` to
/// |0> by the algebraic inverse (the same adder orientation, so both ways cost
/// the same).
fn exp_offset(c: &mut Circuit, t: &[QReg], e: &[QReg], konst: usize, negate_e: bool, uncompute: bool, clean_carry: Option<&QReg>) {
    let w = t.len();
    let konst = konst % (1 << w);
    let tr: Vec<&QReg> = t.iter().collect();
    let er: Vec<&QReg> = e[..w].iter().collect();
    let add = |c: &mut Circuit| {
        if let Some(carry) = clean_carry {
            assert!(t.iter().chain(e).all(|q| q.id() != carry.id()));
            offset_shift(c, t, &e[..w], carry, false);
        } else {
            add_cuccaro_3n_uncontrolled_refs(c, &tr, &er);
        }
    };
    let x_all = |c: &mut Circuit, regs: &[&QReg]| {
        for q in regs {
            c.x(q);
        }
    };
    if negate_e {
        if !uncompute {
            // t = 0 -> konst -> ~konst -> ~konst + e -> ~(~konst + e) = konst - e.
            xor_const(c, t, konst);
            x_all(c, &tr);
            add(c);
            x_all(c, &tr);
        } else {
            // t = konst - e -> konst -> 0.
            add(c);
            xor_const(c, t, konst);
        }
    } else if !uncompute {
        // t = 0 -> konst -> konst + ~e -> ~(konst + ~e) = e - konst.
        xor_const(c, t, konst);
        x_all(c, &er);
        add(c);
        x_all(c, &er);
        x_all(c, &tr);
    } else {
        // t = e - konst -> (e - konst) + ~e = ~konst -> konst -> 0.
        x_all(c, &er);
        add(c);
        x_all(c, &tr);
        x_all(c, &er);
        xor_const(c, t, konst);
    }
}

/// `a[0..n) += ctrl * (b[0..w) + carry_in)` (`b` zero-extended, `w <= n`): the
/// 3n controlled Cuccaro on the low `w` cells; between its MAJ and UMA passes
/// the ripple wire holds the carry out of cell `w-1`, which drives a KG
/// increment of `a[w..n)` through the AND `ctrl AND carry` (1 CCX, released by
/// `clear_and`). With `carry_in` the ripple wire starts at `ctrl` (2 CX, 0 T):
/// the MAJ/UMA passes are exact inverses for any initial carry, so the sum
/// gains exactly `ctrl` and the wire returns to `ctrl` before it is cleared.
/// Cost `3w + 1 + cinc(n - w)` T; two clean ancillae (ripple + AND).
pub(crate) fn ctrl_add_narrow(c: &mut Circuit, ctrl: &QReg, a: &[&QReg], b: &[&QReg], carry_in: bool) {
    let n = a.len();
    let w = b.len();
    assert!(w <= n, "ctrl_add_narrow: operand wider than target");
    if w == 0 {
        if carry_in {
            cinc_khattar_gidney_refs(c, a, ctrl);
        }
        return;
    }
    let prev = c.push_section("p.add");
    let cy = c.alloc_qreg("pas.cy");
    if carry_in {
        c.cx(ctrl, &cy);
    }
    for i in 0..w {
        c.cx(&cy, b[i]);
        c.cx(&cy, a[i]);
        c.ccx(a[i], b[i], &cy);
    }
    if n == w + 1 {
        c.ccx(ctrl, &cy, a[w]);
    } else if w < n {
        // cy = carry into bit w of a + b (+ carry_in), independent of ctrl.
        let g2 = c.alloc_qreg("pas.g2");
        c.ccx(ctrl, &cy, &g2);
        match n - w {
            // a[w..] += g2 on one or two bits: no KG ancilla (the 7-bit rebased
            // exponents: e_A (7) += pos (6), e_ca (7) += g (5); the generic
            // `cinc` would hold one more wire at the M1 erase moment).
            1 => c.cx(&g2, a[w]),
            2 => {
                c.ccx(&g2, a[w], a[w + 1]);
                c.cx(&g2, a[w]);
            }
            _ => cinc_khattar_gidney_refs(c, &a[w..], &g2),
        }
        c.clear_and(&g2, ctrl, &cy);
        c.zero_and_free(g2);
    }
    for i in (0..w).rev() {
        c.ccx(a[i], b[i], &cy);
        c.cx(&cy, a[i]);
        c.ccx(ctrl, b[i], a[i]);
        c.cx(&cy, b[i]);
    }
    if carry_in {
        c.cx(ctrl, &cy);
    }
    c.zero_and_free(cy);
    c.pop_section(&prev);
}

/// Add a short word with a borrowed zero carry; the two high cells need no
/// extra workspace. X-conjugation of the target gives subtraction.
fn offset_shift(c: &mut Circuit, a: &[QReg], b: &[QReg], carry: &QReg, subtract: bool) {
    assert!(b.len() <= a.len() && a.len() - b.len() <= 2);
    if subtract { for q in a { c.x(q); } }
    for i in 0..b.len() {
        c.cx(carry, &b[i]);
        c.cx(carry, &a[i]);
        c.ccx(&a[i], &b[i], carry);
    }
    let w = b.len();
    if a.len() - w == 2 { c.ccx(carry, &a[w], &a[w + 1]); }
    if w < a.len() { c.cx(carry, &a[w]); }
    for i in (0..w).rev() {
        c.ccx(&a[i], &b[i], carry);
        c.cx(carry, &a[i]);
        c.cx(&b[i], &a[i]);
        c.cx(carry, &b[i]);
    }
    if subtract { for q in a { c.x(q); } }
}

/// `a -= ctrl * (b + carry_in)` (zero-extended `b`): X-bracket of
/// [`ctrl_add_narrow`] (`a - v = ~(~a + v)`).
pub(crate) fn ctrl_sub_narrow(c: &mut Circuit, ctrl: &QReg, a: &[&QReg], b: &[&QReg], carry_in: bool) {
    for q in a {
        c.x(q);
    }
    ctrl_add_narrow(c, ctrl, a, b, carry_in);
    for q in a {
        c.x(q);
    }
}

/// `a += ctrl * val (mod 2^|a|)`: the constant in non-adjacent form, one KG
/// controlled increment (`+2^i`: `cinc(a[i..])`) or decrement (`-2^i`:
/// X-bracketed `cinc(a[i..])`) per signed digit, all controlled on `ctrl`.
/// `-32` costs one X-bracketed `cinc(4)` (the generic KG classical-quantum
/// adder `controlled_classical_quantum_add_refs` measured 150 T for `-31` on
/// 9 bits, so it is not used; the `+1` of `-31` rides as the narrow adder's
/// carry-in instead).
pub(crate) fn ctrl_add_const(c: &mut Circuit, ctrl: &QReg, a: &[&QReg], val: usize) {
    let n = a.len();
    let val = val & ((1usize << n) - 1);
    if val == 0 {
        return;
    }
    // signed value in (-2^(n-1), 2^(n-1)], then its NAF digits (LSB first)
    let mut v: i64 = val as i64;
    if v > (1i64 << (n - 1)) {
        v -= 1i64 << n;
    }
    let mut digits: Vec<(usize, i64)> = Vec::new();
    let mut i = 0usize;
    while v != 0 {
        if v & 1 == 1 {
            let d = 2 - (v & 3); // 1 or -1
            digits.push((i, d));
            v -= d;
        }
        v /= 2;
        i += 1;
    }
    let prev = c.push_section("p.addc");
    for (i, d) in digits {
        if i >= n {
            break;
        }
        if d < 0 {
            for q in &a[i..] {
                c.x(q);
            }
        }
        cinc_khattar_gidney_refs(c, &a[i..], ctrl);
        if d < 0 {
            for q in &a[i..] {
                c.x(q);
            }
        }
    }
    c.pop_section(&prev);
}

/// `a += k (mod 2^|a|)` for a classical `k`: the non-adjacent form of `k` as
/// KG increments / X-bracketed increments of the sub-registers `a[j..]`
/// (the unconditional twin of [`ctrl_add_const`]; `exponent_arith::add_const`
/// is the same construction on owned registers).
fn add_const_refs(c: &mut Circuit, a: &[&QReg], k: i64) {
    let n = a.len();
    if n == 0 {
        return;
    }
    let m = 1i64 << n;
    let mut v = k.rem_euclid(m);
    if v >= m / 2 {
        v -= m;
    }
    let mut digits: Vec<(usize, bool)> = Vec::new();
    let mut j = 0usize;
    while v != 0 {
        if v & 1 == 1 {
            let d = 2 - v.rem_euclid(4); // +1 or -1
            if j < n {
                digits.push((j, d < 0));
            }
            v -= d;
        }
        v /= 2;
        j += 1;
    }
    if digits.is_empty() {
        return;
    }
    let prev = c.push_section("p.addc");
    for (j, neg) in digits {
        if neg {
            for q in &a[j..] {
                c.x(q);
            }
        }
        inc_khattar_gidney_refs(c, &a[j..]);
        if neg {
            for q in &a[j..] {
                c.x(q);
            }
        }
    }
    c.pop_section(&prev);
}

/// `e := (k - e) mod 2^|e|` in place (`X` on every bit gives `2^|e| - 1 - e`,
/// then `+= k + 1`); `undo` is the exact inverse. For the 9-bit `u = 257 - e`
/// of the design this is the X-bracket plus one 8-bit KG increment (+2, the
/// +256 is a single X): 15 T measured (`u=257-e` piece); for the rebased
/// 7-bit registers `k = 257 - base_v - base_c` (mod 128).
fn exp_to_k_minus(c: &mut Circuit, e: &[&QReg], k: i64, undo: bool) {
    if !undo {
        for q in e {
            c.x(q);
        }
        add_const_refs(c, e, k + 1);
    } else {
        add_const_refs(c, e, -(k + 1));
        for q in e {
            c.x(q);
        }
    }
}

/// `bit_length_lean_middle` emits the k = -1 (all-zero) layer only on its KG
/// path; `MIDQ_CHUNKED_PREFIX=1` (a production-route default) routes it through
/// `chunked_bitlength::xor`, which has no such layer. Refuse to build a scan
/// that relies on the sentinel in that configuration instead of silently
/// building the wrong circuit.
fn assert_zero_layer_reachable(who: &str) {
    assert!(
        kg_zero_layer_enabled(),
        "{who} needs MIDQ_KG_ZERO_LAYER=1 (all-zero-window sentinel, design 2.4)"
    );
    assert!(
        std::env::var("MIDQ_CHUNKED_PREFIX").ok().as_deref() != Some("1"),
        "{who}: MIDQ_CHUNKED_PREFIX=1 routes bit_length_lean_middle through chunked_bitlength::xor, \
         which has no k = -1 layer (no all-zero-window sentinel): unset it for the packed scans \
         (configure_sub1000_trailmix_route sets it by default)"
    );
}

/// D11 geometry for a ring top `w_a` and schedule lower bound `lo_b`:
/// `(L, S, n_w)` = ring bottom, ring size, window width.
pub(crate) fn top_geometry(w_a: usize, lo_b: usize) -> (usize, usize, usize) {
    let l = lo_b.saturating_sub(WINDOW).min(w_a);
    let s = w_a - l;
    (l, s, s.min(WINDOW))
}

/// M1 geometry for a value envelope `w_b` and schedule lower bound `lo_b`:
/// `(T, S)` = ring top (exclusive), ring size; the window is `[lo_b, lo_b + 32)`.
pub(crate) fn bottom_geometry(w_b: usize, lo_b: usize) -> (usize, usize) {
    let t = (w_b + WINDOW).min(257);
    (t, t - lo_b)
}

/// **D11**: the drop scan after a division (module doc). `r1` is the 257-wire
/// value ring in the s-frame; `e_b`, `e_a` the exponents (9-bit, or the 7-bit
/// rebased registers holding `e - base`: the alignment amount is then
/// `(w_a - base) - e_B_reg`, everything else is base-free); `gate` the held
/// division gate (`gate_div`); `w_a` the value envelope (ring top, `A` and `B`
/// lie inside `[0, w_a)`); `lo_b` the schedule's lower bound of `e_B`
/// (`e_B in [lo_b, w_a]` on the support; `w_a - lo_b <= 127`). `hook` runs
/// while `pos` is deposited (the terminal override D11t; pass `|_, _| {}` when
/// not needed) - after the e_A update forward, before it on the inverse.
/// Effect on the support: `e_A += gate * (pos - (n_w - 1))` with
/// `pos = n_w - 1 + off - d`, i.e. `e_A += gate * (off - d)`; `r1`, `e_b`
/// restored; every ancilla freed at |0>; no phase.
///
/// Preconditions (the "support"; asserted where marked):
/// * `1 <= w_a <= r1.len()`, `lo_b <= w_a`, `w_a - lo_b <= 127` (asserted);
///   `e_b`, `e_a` 9 bits (asserted); `gate` aliases none of the registers;
/// * on a `gate = 1` row: `r1` holds `A_new >> s` on `[0, E)`, `E = e_B + off`
///   (the s-frame after D7), with only its own zeros between its MSB and wire
///   `E - 1`; wires `[E, w_a)` (gap, cb's in-ring bits, A's wrapped low bits)
///   and `[w_a, 257)` are arbitrary; `1 <= e_B`, `lo_b <= e_B <= w_a`;
///   `e_a = e_A_old - off` (D7b already applied); the drop
///   `d = e_A_old - bl(A_new)` satisfies `1 <= d <= n_w - 1 + off`
///   (`drop_bound`; `n_w = min(32, w_a)`), or A_new = 0 (terminal row: `pos`
///   is garbage / the sentinel, the caller's D11t cancels the update);
/// * `MIDQ_KG_ZERO_LAYER=1` is optional here (all-zero window -> `pos = 63`;
///   without it `pos = 0`), but when it is set `MIDQ_CHUNKED_PREFIX` must not be
///   `1` (asserted; module doc);
/// * `gate = 0` rows and rows off the support: `r1`, `e_b`, `e_a` are still
///   restored by the inverse call (exact gate-inverse for any input); only a
///   `gate = 1` row off the support gets a wrong `e_a`.
/// With `compact_position`, the caller must disable `gate` on terminal rows
/// and ignore their position in the hook: the zero-window sentinel is truncated.
#[allow(clippy::too_many_arguments)]
pub(crate) fn aligned_scan_top(
    c: &mut Circuit,
    r1: &[QReg],
    e_b: &[QReg],
    e_a: &[QReg],
    gate: &QReg,
    w_a: usize,
    lo_b: usize,
    base: usize,
    inverse: bool,
    clean_position_bit: Option<&QReg>,
    fused_return_shift: Option<&[QReg]>,
    compact_position: bool,
    hook: impl FnOnce(&mut Circuit, &[&QReg]),
) {
    assert!(e_b.len() >= T7_BITS && e_b.len() <= EXP_BITS, "aligned_scan_top: e_B width {}", e_b.len());
    assert!(e_a.len() >= POS_BITS && e_a.len() <= EXP_BITS, "aligned_scan_top: e_A width {}", e_a.len());
    assert!(base <= w_a, "aligned_scan_top: exponent base {base} above W_A = {w_a}");
    assert!(w_a >= 1 && w_a <= r1.len(), "aligned_scan_top: W_A = {w_a} outside [1, {}]", r1.len());
    assert!(lo_b <= w_a, "aligned_scan_top: lo_B = {lo_b} > W_A = {w_a}");
    assert!(w_a - lo_b < (1 << T7_BITS), "aligned_scan_top: W_A - lo_B = {} needs > 7 bits", w_a - lo_b);
    if kg_zero_layer_enabled() {
        assert_zero_layer_reachable("aligned_scan_top");
    }
    let (l, _s, n_w) = top_geometry(w_a, lo_b);
    let ring: Vec<&QReg> = r1[l..w_a].iter().collect();
    let win: Vec<&QReg> = r1[w_a - n_w..w_a].iter().collect();
    let prev = c.push_section("p.pscan.top");

    // 1. align: rotate the ring UP by t7 = W_A - e_B = (W_A - base) - e_B_reg
    //    (wire e_B - 1 -> W_A - 1).
    let align = |c: &mut Circuit, up: bool, fused: bool| {
        if ring.len() < 2 {
            return; // a 1-wire ring: every rotation is the identity
        }
        let t7 = c.alloc_qreg_bits("pas.t7", T7_BITS);
        // off is clean before/after the alignment, as well as the position scan.
        exp_offset(c, &t7, e_b, w_a - base, true, false, clean_position_bit);
        if fused {
            assert_eq!(l, 0, "fused D10/D11 requires identical rings");
            offset_shift(c, &t7, fused_return_shift.unwrap(), clean_position_bit.unwrap(), true);
        }
        if super::window_gather::enabled() && fused_return_shift.is_none() {
            let reversed: Vec<&QReg> = ring.iter().rev().copied().collect();
            super::window_gather::gather(c, &reversed, &t7, n_w, !up);
        } else {
            subring_rotate(c, &ring, &t7, up);
        }
        if fused {
            offset_shift(c, &t7, fused_return_shift.unwrap(), clean_position_bit.unwrap(), false);
        }
        exp_offset(c, &t7, e_b, w_a - base, true, true, clean_position_bit);
        for q in t7 {
            c.zero_and_free(q);
        }
    };
    // On support t7-s = W_A-e_A_old+off is nonnegative and below 128.
    // Therefore the modulo-128 subtraction is also the actual ring offset.
    align(c, true, inverse && fused_return_shift.is_some());

    // 2. deposit pos = MSB index of the window (top-down KG ladder, 3n form).
    let pos_bits = POS_BITS - usize::from(compact_position);
    let pos_owned = c.alloc_qreg_bits("pas.pos", pos_bits - usize::from(clean_position_bit.is_some()));
    let mut pos: Vec<&QReg> = pos_owned.iter().collect();
    if let Some(q) = clean_position_bit {
        assert!(r1.iter().chain(e_b).chain(e_a).all(|r| r.id() != q.id()) && gate.id() != q.id());
        pos.push(q);
    }
    for (i, q) in pos.iter().enumerate() { if n_w & (1 << i) != 0 { c.x(q); } }
    bit_length_lean_middle_refs(c, &win, &pos, |_| false);

    // 3. e_A += gate * (pos - (n_w - 1))   [inverse: -=], hook while pos is live.
    //    As gate*(pos + 1) (carry-in) then gate*(-n_w) (NAF cinc/cdec; -32 is one
    //    4-bit controlled decrement): ~29 T for the 32-window.
    let ea: Vec<&QReg> = e_a.iter().collect();
    let pr = &pos;
    if !inverse {
        ctrl_add_narrow(c, gate, &ea, &pr, true);
        ctrl_add_const(c, gate, &ea, (1usize << ea.len()) - n_w);
        hook(c, &pos);
    } else {
        hook(c, &pos);
        ctrl_add_const(c, gate, &ea, n_w);
        ctrl_sub_narrow(c, gate, &ea, &pr, true);
    }

    // 4. un-deposit (the ladder is a self-inverse XOR), free pos.
    bit_length_lean_middle_refs(c, &win, &pos, |_| false);
    for (i, q) in pos.iter().enumerate() { if n_w & (1 << i) != 0 { c.x(q); } }
    for q in pos_owned {
        c.zero_and_free(q);
    }

    // 5. rotate back DOWN by the recomputed t7.
    align(c, false, !inverse && fused_return_shift.is_some());
    c.pop_section(&prev);
}

/// **M1**: the gap scan before a multiply (module doc). `r2` is the 257-wire
/// ring in the LSB frame (`B` on `[0, e_B)`, `ca_old` MSB-anchored at wire 256);
/// `e_b`, `e_ca` the exponents (9-bit with `base_v = base_c = 0`, or the 7-bit
/// rebased registers holding `e_B - base_v` / `e_ca - base_c`); `gate` the
/// held multiply gate; `w_b` the value envelope (`e_B <= w_b`); `lo_b` the
/// schedule's lower bound of `e_B` (`lo_b <= 225` so the 32-window fits below
/// wire 257; `w_b - lo_b <= 127`).
///
/// In the rebased frame: the alignment amount is `e_B - lo_b = e_B_reg -
/// (lo_b - base_v)`; the erase `e_ca -= 257 - e_B - g` becomes `e_ca_reg -=
/// (257 - base_v - base_c) - e_B_reg - g` (mod 2^7, so `e_ca_reg` ends at 0
/// on the support - the value `e_ca = base_c` is the fictitious intermediate
/// M6' overwrites); and the `nz` gate's second term `[g < 257 - e_B]` is
/// identically true whenever every representable `e_B` is `<= 225`
/// (`base_v + 2^7 - 1 <= 225`), so there `nz = [pos != 63] = NOT pos[5]` (the
/// sentinel bit of the deposit) and the cascade is not built; otherwise
/// (`w_a >= 226`, the first ~30 rows, where `base_c = 0`) the compare runs on
/// `[e_B_reg | z]` transformed in place to `257 - base_v - e_B_reg` (8 bits:
/// `<= 158`) against `g + 128 * sentinel` - exact for every representable
/// `e_B >= 129`, and every such row with `e_B < 129` is below the schedule's
/// `lo_b + 1 >= 149` (off the support: M1's own rotation precondition fails
/// there first).
/// Effect on the support (`e_B >= 1`): forward `e_ca -= gate * [ca_old != 0] *
/// (257 - e_B - g)` = `e_ca -= gate * bl(ca_old)` (leaves 0); inverse adds it
/// back. `r2`, `e_b` restored; every ancilla freed at |0>; no phase.
/// Requires `MIDQ_KG_ZERO_LAYER=1` (the all-zero-window sentinel) and
/// `MIDQ_CHUNKED_PREFIX != 1` (both asserted; module doc).
///
/// Preconditions (the "support"; asserted where marked):
/// * `r2.len() >= 257`, `lo_b <= w_b <= 256`, `lo_b + 32 <= 257`,
///   `w_b - lo_b <= 127` (asserted); `e_b`, `e_ca` 9 bits (asserted); `gate`
///   aliases none of the registers;
/// * on a `gate = 1` row: `r2 = [B | zeros | ca_old]` with `bl(B) = e_B`,
///   `bl(ca_old) = e_ca` (forward) and `bl(B) + bl(ca_old) <= 257` (the packing
///   invariant, so the window's leading zeros are gap zeros); `1 <= e_B`
///   (`e_B = 0` would let the sentinel pass the compare: `256 < 257`);
///   `lo_b <= e_B <= w_b`; `gap = 257 - e_B - e_ca <= 31` whenever
///   `ca_old != 0` (`gap_bound`); `ca_old = 0` rows need nothing of the window;
/// * inverse: `e_ca = 0` on entry (it receives `bl(ca_old)` back);
/// * `gate = 0` rows and rows off the support: restored exactly by the inverse
///   call (exact gate-inverse for any input).
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn aligned_scan_bottom(
    c: &mut Circuit,
    r2: &[QReg],
    e_b: &[QReg],
    e_ca: &[QReg],
    gate: &QReg,
    w_b: usize,
    lo_b: usize,
    base_v: usize,
    base_c: usize,
    inverse: bool,
    clean_position_bit: Option<&QReg>,
) {
    let w = e_b.len();
    assert!(w >= T7_BITS && w <= EXP_BITS, "aligned_scan_bottom: e_B width {w}");
    assert_eq!(e_ca.len(), w, "aligned_scan_bottom: e_ca width");
    assert_zero_layer_reachable("aligned_scan_bottom");
    assert!(r2.len() >= 257, "aligned_scan_bottom: R2 must be the 257-wire ring");
    assert!(lo_b <= w_b && w_b <= 256, "aligned_scan_bottom: lo_B = {lo_b}, W_B = {w_b}");
    assert!(lo_b + WINDOW <= 257, "aligned_scan_bottom: lo_B = {lo_b} > 225, window would pass wire 257");
    assert!(w_b - lo_b < (1 << T7_BITS), "aligned_scan_bottom: W_B - lo_B = {} needs > 7 bits", w_b - lo_b);
    let (top, _s) = bottom_geometry(w_b, lo_b);
    let ring: Vec<&QReg> = r2[lo_b..top].iter().collect();
    // ascending wire order: the ladder's "MSB" is the lowest 1 of the window.
    let win_rev: Vec<&QReg> = r2[lo_b..lo_b + WINDOW].iter().rev().collect();
    let prev = c.push_section("p.pscan.bot");

    // 1. align: rotate the ring DOWN by t7 = e_B - lo_B = e_B_reg - (lo_B - base_v)
    //    (wire e_B -> lo_B).
    let k_align = (lo_b as i64 - base_v as i64).rem_euclid(1i64 << T7_BITS) as usize;
    let align = |c: &mut Circuit, up: bool| {
        let t7 = c.alloc_qreg_bits("pas.t7", T7_BITS);
        exp_offset(c, &t7, e_b, k_align, false, false, None);
        if super::window_gather::enabled() {
            super::window_gather::gather(c, &ring, &t7, WINDOW, up);
        } else {
            subring_rotate(c, &ring, &t7, up);
        }
        exp_offset(c, &t7, e_b, k_align, false, true, None);
        for q in t7 {
            c.zero_and_free(q);
        }
    };
    align(c, false);

    // 2. deposit pos = 31 - g (g = lowest 1 of the window), or 63 if all zero.
    let pos_owned = c.alloc_qreg_bits("pas.pos", POS_BITS - usize::from(clean_position_bit.is_some()));
    let mut pos: Vec<&QReg> = pos_owned.iter().collect();
    if let Some(q) = clean_position_bit {
        assert!(r2.iter().chain(e_b).chain(e_ca).all(|r| r.id() != q.id()) && gate.id() != q.id());
        pos.push(q);
    }
    for (i, q) in pos.iter().enumerate() { if WINDOW >> i & 1 != 0 { c.x(q); } }
    bit_length_lean_middle_refs(c, &win_rev, &pos, |_| false);

    // 3. pos ^= 31: low 5 bits = g (0 on the sentinel), bit 5 = sentinel flag.
    for q in &pos[..5] {
        c.x(q);
    }
    let g5: Vec<&QReg> = pos[..5].to_vec();
    let eca: Vec<&QReg> = e_ca.iter().collect();
    // The erase constant: e_ca_reg -= g' * ((257 - base_v - base_c) - e_B_reg - g).
    let k_erase = 257i64 - base_v as i64 - base_c as i64;
    // The second nz term [g < 257 - e_B] with g <= 31 is identically true when
    // every representable e_B is <= 225.
    let cheap_nz = base_v + (1usize << w) - 1 <= 225;
    if cheap_nz {
        // 4. u = (257 - base_v - base_c) - e_B_reg in place (mod 2^w).
        let u: Vec<&QReg> = e_b.iter().collect();
        exp_to_k_minus(c, &u, k_erase, false);
        // 5./6. g' = gate AND [pos != 63] = gate AND NOT pos[5]; e_ca += g'*g; e_ca -= g'*u.
        let gp = c.alloc_qreg("pas.gp");
        c.x(&pos[5]);
        c.ccx(gate, &pos[5], &gp);
        if !inverse {
            ctrl_add_narrow(c, &gp, &eca, &g5, false);
            ctrl_sub_full(c, &gp, &eca, &u);
        } else {
            ctrl_add_full(c, &gp, &eca, &u);
            ctrl_sub_narrow(c, &gp, &eca, &g5, false);
        }
        c.clear_and(&gp, gate, &pos[5]);
        c.x(&pos[5]);
        c.zero_and_free(gp);
        // 8. undo u.
        exp_to_k_minus(c, &u, k_erase, true);
    } else {
        // The rows where a representable e_B can exceed 225 (w_a >= 226, the
        // first ~80 rows; base_c = 0 there since w_c <= 21). With the same
        // in-place transform as the cheap rows, u = (257 - base_v - e_B_reg)
        // mod 2^w = 257 - e_B whenever that lies in [1, 2^w) - for w = 7 every
        // e_B in [130, 256], and every row with e_B < 130 lies below the
        // schedule's lo_B + 1 >= 149 (off the support: M1's rotation
        // precondition already fails there); for the plain 9-bit register
        // every e_B. Then [g < 257 - e_B] = [g < u] = OR(u[5..w)) OR [g < u
        // mod 32] with g < 32: the 5-cell borrow cascade of g against u[0..5)
        // holds [g mod 32 < u mod 32] on its top carry wire between its two
        // passes, and one multi-controlled X with a DIRTY ancilla (a garbage
        // carry wire of the cascade) folds `gate AND NOT [g < u]` into g'
        // directly; the sentinel (`lt = 1` on an all-zero window, g = 0, since
        // u >= 1) is XORed in as `gate AND s`. So g' = gate AND [pos != 63]
        // AND [g < 257 - e_B] with NO nz wire and no zero-extension wires: the
        // M1 moments of these rows equal the cheap rows' (pos + g' + the
        // adder's two wires), one below the masked-adder moment.
        assert_eq!(base_c, 0, "aligned_scan_bottom: the full nz compare needs base_c = 0 (w_a >= 226 rows)");
        assert!(w >= POS_BITS, "aligned_scan_bottom: exponent width {w} below the 6-bit deposit");
        let u: Vec<&QReg> = e_b.iter().collect();
        exp_to_k_minus(c, &u, k_erase, false);
        // g' ^= gate AND ([g < u] XOR s), applied once to set g' and once to release it.
        let toggle_gp = |c: &mut Circuit, gp: &QReg| {
            let prev = c.push_section("p.cmp5");
            let cc = c.alloc_qreg("pas.cc");
            // borrow cascade (v = g X-bracketed on the carry line, a = u[0..5)):
            // after cell i the borrow out of cells [0, i] sits on g[i].
            for i in 0..5 {
                c.x(&pos[i]);
            }
            let cell = |c: &mut Circuit, i: usize| {
                let (a, b) = (&e_b[i], &pos[i]);
                let prev_c: &QReg = if i == 0 { &cc } else { &pos[i - 1] };
                c.cx(b, a);
                c.cx(b, prev_c);
                c.ccx(prev_c, a, b);
            };
            for i in 0..5 {
                cell(c, i);
            }
            // g' ^= gate;  g' ^= gate AND NOT [g < u] = gate AND ~u[5] .. ~u[w-1] AND ~borrow
            c.cx(gate, gp);
            let mut ctrls: Vec<&QReg> = vec![gate];
            ctrls.extend(e_b[5..].iter());
            ctrls.push(&pos[4]);
            for q in &ctrls[1..] {
                c.x(q);
            }
            if ctrls.len() <= 5 {
                crate::point_add::trailmix_port::arith::mcx::mcx_dirty(c, &ctrls, gp, &pos[0]);
            } else {
                mcx_clean_k(c, &ctrls, gp);
            }
            for q in &ctrls[1..] {
                c.x(q);
            }
            for i in (0..5).rev() {
                let (a, b) = (&e_b[i], &pos[i]);
                let prev_c: &QReg = if i == 0 { &cc } else { &pos[i - 1] };
                c.ccx(prev_c, a, b);
                c.cx(b, prev_c);
                c.cx(b, a);
            }
            for i in 0..5 {
                c.x(&pos[i]);
            }
            c.zero_and_free(cc);
            c.ccx(gate, &pos[5], gp); // the sentinel
            c.pop_section(&prev);
        };
        let gp = c.alloc_qreg("pas.gp");
        toggle_gp(c, &gp);
        // 6. e_ca += g'*g; e_ca -= g'*u  (inverse: += u, -= g).
        if !inverse {
            ctrl_add_narrow(c, &gp, &eca, &g5, false);
            ctrl_sub_full(c, &gp, &eca, &u);
        } else {
            ctrl_add_full(c, &gp, &eca, &u);
            ctrl_sub_narrow(c, &gp, &eca, &g5, false);
        }
        toggle_gp(c, &gp);
        c.zero_and_free(gp);
        // 8. undo u.
        exp_to_k_minus(c, &u, k_erase, true);
    }
    // 8b. undo the pos XOR.
    for q in &pos[..5] {
        c.x(q);
    }

    // 9. un-deposit, free pos.
    bit_length_lean_middle_refs(c, &win_rev, &pos, |_| false);
    for (i, q) in pos.iter().enumerate() { if WINDOW >> i & 1 != 0 { c.x(q); } }
    for q in pos_owned {
        c.zero_and_free(q);
    }

    // 10. rotate back UP by the recomputed t7.
    align(c, true);
    c.pop_section(&prev);
}

/// `a += ctrl * b`, equal widths (3n controlled Cuccaro).
fn ctrl_add_full(c: &mut Circuit, ctrl: &QReg, a: &[&QReg], b: &[&QReg]) {
    let prev = c.push_section("p.add");
    controlled_add_cuccaro_3n_refs(c, ctrl, a, b);
    c.pop_section(&prev);
}

/// `a -= ctrl * b`, equal widths (X-bracketed 3n controlled Cuccaro).
fn ctrl_sub_full(c: &mut Circuit, ctrl: &QReg, a: &[&QReg], b: &[&QReg]) {
    let prev = c.push_section("p.sub");
    for q in a {
        c.x(q);
    }
    controlled_add_cuccaro_3n_refs(c, ctrl, a, b);
    for q in a {
        c.x(q);
    }
    c.pop_section(&prev);
}

/// Selftest entry (mod.rs): forward + inverse on real `packed_prefix_model`
/// states incl. the refuters' classes; value, phase, ancillae; prints T.
#[allow(dead_code)]
pub(crate) fn selftest() {
    aligned_scan_selftest::run();
}
