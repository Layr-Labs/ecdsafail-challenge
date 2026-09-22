//! Packed-prefix primitive: exponent arithmetic on the persisted 9-bit
//! bit-length registers `e_A, e_B, e_ca, e_cb` (tools/spike/packed_design.md,
//! sections 3.1-3.4, plan item 6). Every operation here is an in-place update of
//! a small register; nothing is ever erased by a scan (the design's central
//! rule), so each op is either self-inverse or has a gate-for-gate twin below.
//!
//! Register convention: `&[QReg]` slices, LSB first, any width (9 bits for the
//! v1 exponents, 7 bits for the rebased lever, 5 bits for `s_rot`, 6 bits for
//! the scan deposit `pos`). Mixed widths are supported where the design needs
//! them (`e_A += pos`, `e_ca += shift`): the shorter register is zero-extended
//! arithmetically, never with borrowed zero wires (the D11/M1 scan moments are
//! 864-865 wires; three zero-extension wires would own the peak).
//!
//! Operations and where the step uses them (T = Toffoli, measured by the
//! selftest and printed; the numbers in brackets are the 9-bit counts):
//!
//! * [`add_reg`] / [`sub_reg`]: unconditional `a ±= b`, equal width, X-bracketed
//!   uncontrolled Cuccaro (2n T [18]; the state machine's `sub_refs` pays 27 by
//!   gating on a fixed |1>).
//! * [`ctrl_add_reg`] / [`ctrl_sub_reg`]: `a ±= g*b` with `|b| <= |a|`. Equal
//!   width is the plain 3n controlled Cuccaro; the mixed form runs the MAJ
//!   chain over the low `|b|` cells, propagates the carry into the high part by
//!   one `cinc(g AND carry)` and unwinds with the UMA chain (3|b| + 1 + cinc T).
//!   Used by D11 (`e_A += gate*pos`), D11t, M1 (`e_ca += g'*pos`, `e_ca += g'*e_B`),
//!   M6' (`e_ca += gate*shift`).
//! * [`add_const`] / [`ctrl_add_const`]: `a += k` / `a += g*k` mod 2^|a| for a
//!   signed classical `k`. `add_const` is the per-step REBASE of the 7-bit
//!   exponent lever (`e_X -= min_env_X(i+1) - min_env_X(i)`, unconditional, once
//!   per exponent per step; the rebased register must stay in
//!   `[0, 2^w)` on the support = the `exp_range` miss kind). Both split `k`
//!   into its non-adjacent form and add each signed digit `±2^j` as one KG
//!   (controlled) increment of the top sub-register `a[j..]` [9-bit: 15-21 T
//!   unconditional, 21-27 T controlled]; the design-named
//!   `controlled_classical_quantum_add_refs` measures 110-154 T on 9 bits
//!   (Theta(n^1.58) compare-based Vandaele) and is kept only as
//!   [`ctrl_add_const_vandaele`] for the selftest's comparison; the
//!   unconditional Vandaele (`ripple_add::add_const`, 46-68 T) is taken by
//!   `add_const` only when the measured cost model prices it lower (never for
//!   n <= 9). D11 `-31 = +1 - 32`, D11t `+30 = +32 - 2`, M1 `-257 = -1 - 256`.
//! * [`ctrl_inc`] / [`ctrl_dec`]: Khattar-Gidney controlled increment (D6, D6',
//!   M8, the carry deposit of M6').
//! * [`xor_diff_low`]: `shift ^= gate * (e_a - e_b)[0..|shift|]` = D1 (s_raw)
//!   and M12; this is `clz_diff_positions` with `lo = 0` and no constant folds
//!   (`e_a -= e_b`, gated CCX per shift bit, `e_a += e_b`). Self-inverse.
//! * [`deposit_sum`] / [`undeposit_sum`]: M6' `e_ca := e_cb + s2 + carry`
//!   (9 CCX XOR-copy, mixed controlled add of `shift`, `ctrl_inc` on
//!   `gate AND carry`). PRE `e_ca = 0` on active rows.
//! * [`max_into_second`] / [`unmax_into_second`]: the role compare's
//!   max-by-cswap (`flag ^= [e_x < e_y]`, X, 9 cswaps; afterwards `e_y = max`,
//!   `e_x = min`, `flag = [e_x_old >= e_y_old]` live for the undo).
//! * [`offset_apply`] / [`offset_release`] (+ inverses): D6 `shift -= off`,
//!   `e_B += off` (-> E) and D6' `e_B -= off` (before D9 clears `off`).
//! * [`gap_erase`] / [`gap_deposit`]: M1 `e_ca -= g'*(257 - e_B - pos)` as three
//!   controlled 9-bit ops (`+= g'*e_B`, `+= g'*pos`, `-= g'*257`).
//! * [`off_update`] / [`off_update_inverse`]: D7b `e_A -= gate AND off`.
//! * [`drop_update`] / [`drop_update_inverse`]: D11 `e_A += gate*(pos - 31)`
//!   (with D7b the net effect is `e_A -= d`, `d = 31 + off - pos`).
//! * [`terminal_override`] / [`terminal_override_inverse`]: D11t under `term`:
//!   `e_A -= pos; e_A -= shift; e_A += 30` (garbage `pos`, `e_A_old = 1 + s`,
//!   off = 0: `1 + s + pos - 31 - pos - s + 30 = 0`).
//! * [`load_affine`] / [`unload_affine`]: the 7-bit alignment amounts
//!   `t7 := (W_A - e_B) mod 128` (D11, `negate = true`) and
//!   `t7 := (e_B - lo_B) mod 128` (M1, `negate = false`): CX copy of the low
//!   `|t|` bits, optional X-bracket, one `add_const`.
//! * [`xor_eq_const`], [`xor_is_zero`], [`xor_nonzero`]: 9-bit predicates by one
//!   `mcx_clean_k` (2k-3 = 15 T): `eq1 = [e_B == 1]` (the D0 root) and the
//!   terminal-aware swap's `a_nonzero = OR(e_A)` / `[e_A == 0]` (3.3).
//! * [`term_toggle`]: the terminal predicate D0, see below.
//!
//! # The terminal predicate `term` (D0 / D11t / D0-clear) and its ordering contract
//!
//! `term ^= gate_div AND [e_B == 1] AND [A mod 2^shift == 0]` where `A` is read
//! from the LSB-frame window `R1[0..n)` (n = 28 in the design; every division
//! with B = 1 has `shift = e_A - 1 <= 27` on the support) and `shift` is the
//! 5-bit `s_rot`. Structure (refuter fix 3, design 3.1 D0): `eq1 = [e_B == 1]`
//! (mcx_clean_k), `root = gate_div AND eq1` (1 CCX, released by `clear_and`), the
//! Khattar-Gidney prefix-AND ladder ascending over the X-bracketed window
//! (`AND(~A[0..i))` at layer i, 3 compact ancillae), and a DFS one-hot CURSOR on
//! `shift` rooted at `root` that walks the leaves 0, 1, ..., min(n, 31) in
//! lockstep with the ladder layers (one wire per address level, the leaf wire
//! `g_i = root AND [shift == i]`); at layer i the capture is
//! `term ^= g_i AND AND(ctrls_i)` (1-2 CCX, `mcx_clean_k` on <= 3 controls).
//! The cursor is the leaf-by-leaf form of `measured_demux::visit` (gray-code
//! transitions: pop the trailing-ones levels with `clear_and`, one CX flip,
//! re-push): ~1 T per visited leaf, exactly the DFS engine's cost, and it is
//! what lets the one-hot engine be NESTED inside the streaming ladder, whose
//! callback cannot be re-entered. Leaves `i > n` (shift wider than the window)
//! are pruned: they never fire, on the compute and on the clear alike.
//!
//! Ordering contract (the refuter's fix; the design's row order is
//! D1, D0, D3, D4, D5, D6, D7, D7b, D8, D6', D9, D11 (D11t inside), D10, D0-clear, D12):
//!
//! 1. COMPUTE strictly after D1 and before D3: `shift` holds `s_raw = e_A - e_B`
//!    and R1 is in the LSB frame (D3 rotates it). With shift = 0 (before D1)
//!    the predicate degenerates to `gate_div AND [e_B == 1]`, which is the bug
//!    the refuter found (it fired on every B = 1 row).
//! 2. `term` is LIVE across D3..D10 (the peak table's 1 wire); D11t consumes it
//!    while `pos` is deposited.
//! 3. CLEAR strictly after D10 and before D12: R1 is back in the LSB frame and
//!    `shift` still holds `s`. On the rows where `root = 1` (division, B = 1)
//!    `off = 0` (A >> s_raw = 1 >= B), so `s = s_raw`, and the subtract
//!    `A -= 2^s` leaves the bits below `s` untouched, so the predicate has the
//!    same value at the clear and the same circuit clears it. On every other
//!    row (multiply, draining A = 0 / B = 1, frozen) `root = 0` and the
//!    ladder / cursor touch nothing whatever `shift` holds.
//! 4. The same function is its own inverse in the backward driver (compute
//!    between D12^-1 and D10^-1, clear between D3^-1 and D1^-1).
//!
//! Choices where the design is silent, documented here: the window width `n`
//! is a parameter (the caller passes `R1[0..28)`); leaves above the window are
//! pruned rather than captured; the two-control ladder layers use a fresh flag
//! per capture (`mcx_clean_k(3)`), not a persisted one; `MIDQ_ONEHOT_COHERENT=1`
//! makes the cursor's clears coherent CCX (debug switch of design 2.2).
//! Measured (selftest, window 28, 5-bit shift): 173 T per toggle (203 coherent),
//! scratch peak 11 wires = eq1 + root + 5 cursor levels + 3 KG + 1 capture flag,
//! i.e. the design's "D0 compute <= 865" plus the transient flag = 866 on rows
//! >= 378, equal to (not above) the masked-adder moment; the flag could be
//! traded for ~2 T per two-control leaf with `mcx_dirty` on a cursor level if a
//! wire is ever needed there.
//!
//! On the task's wording "term = [e_A == 0]": at D0 time `e_A` is not yet 0
//! (D11t is what zeroes it, under `term`), so `term` cannot be read off `e_A`;
//! the `[e_A == 0]` / `OR(e_A)` predicates are the terminal-aware SWAP's
//! `a_nonzero` (design 3.3) and are provided as [`xor_is_zero`] / [`xor_nonzero`].

#![allow(dead_code)]

use crate::point_add::trailmix_port::arith::cuccaro::{
    add_cuccaro_3n_uncontrolled_refs, controlled_add_cuccaro_3n_refs,
};
use crate::point_add::trailmix_port::arith::khattar_gidney::{
    cinc_khattar_gidney_refs, controlled_classical_quantum_add_refs,
    kg_prefix_compact_ancilla_count, KgPrefixAnd,
};
use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::borrow_compare_refs;

#[path = "exponent_arith_selftest.rs"]
mod selftest_impl;

fn refs(r: &[QReg]) -> Vec<&QReg> {
    r.iter().collect()
}

/// `k mod 2^n` as little-endian bytes for the constant adders.
fn const_bytes(k: i64, n: usize) -> Vec<u8> {
    let val = (i128::from(k)).rem_euclid(1i128 << n) as u128;
    (0..n.div_ceil(8).max(1)).map(|i| (val >> (8 * i)) as u8).collect()
}

// ---------------------------------------------------------------- adders

/// `a += b (mod 2^|a|)`, unconditional, `|b| == |a|`. 2n T.
pub(crate) fn add_reg(c: &mut Circuit, a: &[QReg], b: &[QReg]) {
    assert_eq!(a.len(), b.len(), "add_reg: width mismatch");
    let prev = c.push_section("p.exp.add");
    add_cuccaro_3n_uncontrolled_refs(c, &refs(a), &refs(b));
    c.pop_section(&prev);
}

/// `a -= b (mod 2^|a|)`, unconditional, `|b| == |a|` (X-bracket + add). 2n T.
pub(crate) fn sub_reg(c: &mut Circuit, a: &[QReg], b: &[QReg]) {
    assert_eq!(a.len(), b.len(), "sub_reg: width mismatch");
    let prev = c.push_section("p.exp.sub");
    for q in a {
        c.x(q);
    }
    add_cuccaro_3n_uncontrolled_refs(c, &refs(a), &refs(b));
    for q in a {
        c.x(q);
    }
    c.pop_section(&prev);
}

/// `a += g * b (mod 2^|a|)` with `|b| <= |a|` (`b` zero-extended). Equal width:
/// the 3n controlled Cuccaro. Mixed: MAJ chain over the low `|b|` cells, the
/// carry out of cell `|b|-1` (unconditional in the MAJ form) is folded into the
/// high part as `a[|b|..] += g AND carry` (one CCX, one `cinc`, one `clear_and`),
/// then the UMA chain restores the carry and writes the gated sum bits.
pub(crate) fn ctrl_add_reg(c: &mut Circuit, g: &QReg, a: &[QReg], b: &[QReg]) {
    let n = a.len();
    let m = b.len();
    assert!(m <= n, "ctrl_add_reg: |b| = {m} exceeds |a| = {n}");
    if m == 0 {
        return;
    }
    let prev = c.push_section("p.exp.cadd");
    let ar = refs(a);
    let br = refs(b);
    if m == n {
        controlled_add_cuccaro_3n_refs(c, g, &ar, &br);
        c.pop_section(&prev);
        return;
    }
    if m == 1 {
        // a += g * b[0]: one controlled increment on `a` gated by g AND b0.
        let gb = c.alloc_qreg("exp.gb");
        c.ccx(g, &b[0], &gb);
        cinc_khattar_gidney_refs(c, &ar, &gb);
        c.clear_and(&gb, g, &b[0]);
        c.zero_and_free(gb);
        c.pop_section(&prev);
        return;
    }
    let carry = c.alloc_qreg("exp.cadd.c");
    for i in 0..m {
        c.cx(&carry, br[i]);
        c.cx(&carry, ar[i]);
        c.ccx(ar[i], br[i], &carry);
    }
    // carry = carry out of the low m cells of (a + b), independent of g.
    let gc = c.alloc_qreg("exp.cadd.gc");
    c.ccx(g, &carry, &gc);
    cinc_khattar_gidney_refs(c, &ar[m..], &gc);
    c.clear_and(&gc, g, &carry);
    c.zero_and_free(gc);
    for i in (0..m).rev() {
        c.ccx(ar[i], br[i], &carry);
        c.cx(&carry, ar[i]);
        c.ccx(g, br[i], ar[i]);
        c.cx(&carry, br[i]);
    }
    c.zero_and_free(carry);
    c.pop_section(&prev);
}

/// `a -= g * b (mod 2^|a|)`, `|b| <= |a|` (X-bracket of `a` + [`ctrl_add_reg`]).
pub(crate) fn ctrl_sub_reg(c: &mut Circuit, g: &QReg, a: &[QReg], b: &[QReg]) {
    for q in a {
        c.x(q);
    }
    ctrl_add_reg(c, g, a, b);
    for q in a {
        c.x(q);
    }
}

/// Non-adjacent form of `k mod 2^n` (the symmetric representative in
/// `[-2^(n-1), 2^(n-1))`, so `-1` is one term): signed digits `(position, negative)`
/// with no two adjacent nonzero digits; at most `ceil((n+1)/2)` terms.
fn naf_terms(k: i64, n: usize) -> Vec<(usize, bool)> {
    let m = 1i64 << n;
    let mut v = k.rem_euclid(m);
    if v >= m / 2 {
        v -= m;
    }
    let mut terms = Vec::new();
    let mut j = 0usize;
    while v != 0 {
        if v & 1 == 1 {
            let d = 2 - (v.rem_euclid(4)); // +1 or -1
            if j < n {
                terms.push((j, d < 0));
            }
            v -= d;
        }
        v /= 2;
        j += 1;
    }
    terms
}

/// Toffoli price of the NAF form against the Vandaele CQ adder, from the
/// selftest's measured unit table: KG `inc` on m bits = max(0, 3m - 9), `cinc`
/// = 3m - 6 (m >= 2); unconditional Vandaele ~7.5 T per bit on 7-9 bits, the
/// controlled one 110-154 T on 9 bits (never competitive there).
fn naf_is_cheaper(terms: &[(usize, bool)], n: usize, controlled: bool) -> bool {
    if controlled {
        return true;
    }
    let naf: usize = terms.iter().map(|&(j, _)| (3 * (n - j)).saturating_sub(9)).sum();
    naf <= 15 * n / 2
}

/// `a += k (mod 2^|a|)` for a signed classical `k`: the per-step REBASE of the
/// 7-bit exponent lever (and any unconditional constant fold). The constant is
/// split into its non-adjacent form and each signed digit `±2^j` is one
/// Khattar-Gidney increment / X-bracketed increment of the sub-register
/// `a[j..]` (0 T for the top bit, ~2(n - j) T otherwise); the Vandaele CQ adder
/// (`ripple_add::add_const`) is used only when the model prices it lower.
pub(crate) fn add_const(c: &mut Circuit, a: &[QReg], k: i64) {
    use crate::point_add::trailmix_port::arith::khattar_gidney::inc_khattar_gidney_refs;
    let n = a.len();
    if n == 0 {
        return;
    }
    let terms = naf_terms(k, n);
    if terms.is_empty() {
        return;
    }
    let prev = c.push_section("p.exp.addk");
    if naf_is_cheaper(&terms, n, false) {
        let ar = refs(a);
        for &(j, neg) in &terms {
            if neg {
                for q in &ar[j..] {
                    c.x(q);
                }
            }
            inc_khattar_gidney_refs(c, &ar[j..]);
            if neg {
                for q in &ar[j..] {
                    c.x(q);
                }
            }
        }
    } else {
        crate::point_add::trailmix_port::arith::ripple_add::add_const(c, a, &const_bytes(k, n));
    }
    c.pop_section(&prev);
}

/// `a += g * k (mod 2^|a|)` for a signed classical `k`: the non-adjacent form
/// of `k` as controlled increments / decrements of `a[j..]` (D11 `-31` =
/// `+1 - 32`, D11t `+30` = `+32 - 2`, M1 `-257` = `-1 - 256`). The generic
/// `controlled_classical_quantum_add_refs` (khattar_gidney.rs:2115) is kept as
/// `ctrl_add_const_vandaele` for reference; it measures 110-154 T on 9 bits
/// against 20-30 T here.
pub(crate) fn ctrl_add_const(c: &mut Circuit, g: &QReg, a: &[QReg], k: i64) {
    let n = a.len();
    if n == 0 {
        return;
    }
    let terms = naf_terms(k, n);
    if terms.is_empty() {
        return;
    }
    let prev = c.push_section("p.exp.caddk");
    if naf_is_cheaper(&terms, n, true) {
        let ar = refs(a);
        for &(j, neg) in &terms {
            if neg {
                for q in &ar[j..] {
                    c.x(q);
                }
            }
            cinc_khattar_gidney_refs(c, &ar[j..], g);
            if neg {
                for q in &ar[j..] {
                    c.x(q);
                }
            }
        }
    } else {
        controlled_classical_quantum_add_refs(c, g, &refs(a), &const_bytes(k, n));
    }
    c.pop_section(&prev);
}

/// The design-named generic form (`controlled_classical_quantum_add_refs`),
/// kept for the selftest's cost comparison.
pub(crate) fn ctrl_add_const_vandaele(c: &mut Circuit, g: &QReg, a: &[QReg], k: i64) {
    let n = a.len();
    if n == 0 {
        return;
    }
    let bytes = const_bytes(k, n);
    if bytes.iter().all(|&b| b == 0) {
        return;
    }
    let prev = c.push_section("p.exp.caddk.vandaele");
    controlled_classical_quantum_add_refs(c, g, &refs(a), &bytes);
    c.pop_section(&prev);
}

/// `a += g` (Khattar-Gidney controlled increment).
pub(crate) fn ctrl_inc(c: &mut Circuit, g: &QReg, a: &[QReg]) {
    cinc_khattar_gidney_refs(c, &refs(a), g);
}

/// `a -= g` (X-bracket + controlled increment).
pub(crate) fn ctrl_dec(c: &mut Circuit, g: &QReg, a: &[QReg]) {
    for q in a {
        c.x(q);
    }
    cinc_khattar_gidney_refs(c, &refs(a), g);
    for q in a {
        c.x(q);
    }
}

// ------------------------------------------------------- step arithmetic

/// D1 / M12: `shift ^= gate * (e_a - e_b)[0..|shift|]` — `clz_diff_positions`
/// with `lo = 0` on the persisted exponents: `e_a -= e_b`, one gated CCX per
/// shift bit, `e_a += e_b`. Self-inverse; `e_a`, `e_b` restored.
pub(crate) fn xor_diff_low(c: &mut Circuit, gate: &QReg, e_a: &[QReg], e_b: &[QReg], shift: &[QReg]) {
    assert!(shift.len() <= e_a.len(), "xor_diff_low: shift wider than the exponent");
    let prev = c.push_section("p.exp.diff");
    sub_reg(c, e_a, e_b);
    for (bit, target) in e_a.iter().zip(shift) {
        c.ccx(gate, bit, target);
    }
    add_reg(c, e_a, e_b);
    c.pop_section(&prev);
}

/// M6': `e_ca := e_cb + shift + carry` on active rows (`gate = 1`; PRE
/// `e_ca = 0` there): `e_ca ^= gate*e_cb` (9 CCX), `e_ca += gate*shift`
/// (mixed controlled add), `e_ca += gate AND carry` (`ctrl_inc`).
pub(crate) fn deposit_sum(
    c: &mut Circuit, gate: &QReg, e_ca: &[QReg], e_cb: &[QReg], shift: &[QReg], carry: &QReg,
) {
    assert_eq!(e_ca.len(), e_cb.len());
    let prev = c.push_section("p.exp.deposit");
    for (src, dst) in e_cb.iter().zip(e_ca) {
        c.ccx(gate, src, dst);
    }
    ctrl_add_reg(c, gate, e_ca, shift);
    let gc = c.alloc_qreg("exp.dep.gc");
    c.ccx(gate, carry, &gc);
    ctrl_inc(c, &gc, e_ca);
    c.clear_and(&gc, gate, carry);
    c.zero_and_free(gc);
    c.pop_section(&prev);
}

/// Inverse of [`deposit_sum`] (the backward driver's M6'): `e_ca -= gate AND
/// carry`, `e_ca -= gate*shift`, `e_ca ^= gate*e_cb` -> 0 on active rows.
pub(crate) fn undeposit_sum(
    c: &mut Circuit, gate: &QReg, e_ca: &[QReg], e_cb: &[QReg], shift: &[QReg], carry: &QReg,
) {
    assert_eq!(e_ca.len(), e_cb.len());
    let prev = c.push_section("p.exp.undeposit");
    let gc = c.alloc_qreg("exp.dep.gc");
    c.ccx(gate, carry, &gc);
    ctrl_dec(c, &gc, e_ca);
    c.clear_and(&gc, gate, carry);
    c.zero_and_free(gc);
    ctrl_sub_reg(c, gate, e_ca, shift);
    for (src, dst) in e_cb.iter().zip(e_ca) {
        c.ccx(gate, src, dst);
    }
    c.pop_section(&prev);
}

/// Role compare (3.3): `flag ^= [e_x < e_y]`, `X(flag)`, `cswap(flag, e_x[k],
/// e_y[k])`. After: `e_y = max(e_x, e_y)`, `e_x = min`, `flag = [e_x_old >= e_y_old]`
/// (live; the capture leaf `256 - max` is read off `e_y`). 2n + n T.
pub(crate) fn max_into_second(c: &mut Circuit, e_x: &[QReg], e_y: &[QReg], flag: &QReg) {
    assert_eq!(e_x.len(), e_y.len());
    let prev = c.push_section("p.exp.max");
    borrow_compare_refs(c, &refs(e_x), &refs(e_y), flag);
    c.x(flag);
    for (x, y) in e_x.iter().zip(e_y) {
        c.cswap(flag, x, y);
    }
    c.pop_section(&prev);
}

/// Inverse of [`max_into_second`]: un-swap under `flag`, `X(flag)`, then the
/// same compare on the restored registers clears `flag`.
pub(crate) fn unmax_into_second(c: &mut Circuit, e_x: &[QReg], e_y: &[QReg], flag: &QReg) {
    assert_eq!(e_x.len(), e_y.len());
    let prev = c.push_section("p.exp.unmax");
    for (x, y) in e_x.iter().zip(e_y).rev() {
        c.cswap(flag, x, y);
    }
    c.x(flag);
    borrow_compare_refs(c, &refs(e_x), &refs(e_y), flag);
    c.pop_section(&prev);
}

/// D6: `shift -= off` (s_raw -> s) and `e_b += off` (e_B -> E = the field end
/// D7's mask reads). `off` is the D4 capture (0 on inactive rows).
pub(crate) fn offset_apply(c: &mut Circuit, off: &QReg, shift: &[QReg], e_b: &[QReg]) {
    let prev = c.push_section("p.exp.offset");
    ctrl_dec(c, off, shift);
    ctrl_inc(c, off, e_b);
    c.pop_section(&prev);
}

/// D6': `e_b -= off` (E -> e_B). Must run BEFORE D9 clears `off`; `shift`
/// keeps `s` (D12 clears it from q).
pub(crate) fn offset_release(c: &mut Circuit, off: &QReg, e_b: &[QReg]) {
    let prev = c.push_section("p.exp.offset_release");
    ctrl_dec(c, off, e_b);
    c.pop_section(&prev);
}

/// Inverse of [`offset_apply`] (the backward driver's D6): `e_b -= off`, `shift += off`.
pub(crate) fn offset_apply_inverse(c: &mut Circuit, off: &QReg, shift: &[QReg], e_b: &[QReg]) {
    let prev = c.push_section("p.exp.offset_inv");
    ctrl_dec(c, off, e_b);
    ctrl_inc(c, off, shift);
    c.pop_section(&prev);
}

/// Inverse of [`offset_release`]: `e_b += off`.
pub(crate) fn offset_release_inverse(c: &mut Circuit, off: &QReg, e_b: &[QReg]) {
    let prev = c.push_section("p.exp.offset_release_inv");
    ctrl_inc(c, off, e_b);
    c.pop_section(&prev);
}

/// M1's erase: `e_ca -= g * (257 - e_b - pos)` with `pos = gap` (6-bit deposit),
/// `g = gate AND nz`: `e_ca += g*e_b; e_ca += g*pos; e_ca -= g*257` (three
/// controlled 9-bit ops; on the support `e_ca_old = 257 - e_b - gap`, so
/// `e_ca` ends at 0 on active rows).
pub(crate) fn gap_erase(c: &mut Circuit, g: &QReg, e_ca: &[QReg], e_b: &[QReg], pos: &[QReg]) {
    let prev = c.push_section("p.exp.gap_erase");
    ctrl_add_reg(c, g, e_ca, e_b);
    ctrl_add_reg(c, g, e_ca, pos);
    ctrl_add_const(c, g, e_ca, -257);
    c.pop_section(&prev);
}

/// Inverse of [`gap_erase`]: `e_ca += g * (257 - e_b - pos)` (the backward
/// driver's M1 and the cut-384/480 repack).
pub(crate) fn gap_deposit(c: &mut Circuit, g: &QReg, e_ca: &[QReg], e_b: &[QReg], pos: &[QReg]) {
    let prev = c.push_section("p.exp.gap_deposit");
    ctrl_add_const(c, g, e_ca, 257);
    ctrl_sub_reg(c, g, e_ca, pos);
    ctrl_sub_reg(c, g, e_ca, e_b);
    c.pop_section(&prev);
}

/// D7b: `e_a -= gate AND off` (the `-off` part of the drop while `off` is live).
pub(crate) fn off_update(c: &mut Circuit, gate: &QReg, off: &QReg, e_a: &[QReg]) {
    let prev = c.push_section("p.exp.off");
    let g = c.alloc_qreg("exp.goff");
    c.ccx(gate, off, &g);
    ctrl_dec(c, &g, e_a);
    c.clear_and(&g, gate, off);
    c.zero_and_free(g);
    c.pop_section(&prev);
}

/// Inverse of [`off_update`]: `e_a += gate AND off`.
pub(crate) fn off_update_inverse(c: &mut Circuit, gate: &QReg, off: &QReg, e_a: &[QReg]) {
    let prev = c.push_section("p.exp.off_inv");
    let g = c.alloc_qreg("exp.goff");
    c.ccx(gate, off, &g);
    ctrl_inc(c, &g, e_a);
    c.clear_and(&g, gate, off);
    c.zero_and_free(g);
    c.pop_section(&prev);
}

/// D11: `e_a += gate * (pos - 31)` with `pos` the 6-bit deposit `k = 31 + off - d`
/// (net with D7b: `e_a -= d`).
pub(crate) fn drop_update(c: &mut Circuit, gate: &QReg, e_a: &[QReg], pos: &[QReg]) {
    let prev = c.push_section("p.exp.drop");
    ctrl_add_reg(c, gate, e_a, pos);
    ctrl_add_const(c, gate, e_a, -31);
    c.pop_section(&prev);
}

/// Inverse of [`drop_update`].
pub(crate) fn drop_update_inverse(c: &mut Circuit, gate: &QReg, e_a: &[QReg], pos: &[QReg]) {
    let prev = c.push_section("p.exp.drop_inv");
    ctrl_add_const(c, gate, e_a, 31);
    ctrl_sub_reg(c, gate, e_a, pos);
    c.pop_section(&prev);
}

/// D11t: under `term` (while `pos` is deposited, garbage on the terminal row):
/// `e_a -= pos; e_a -= shift; e_a += 30`. On the terminal row `e_a_old = 1 + s`,
/// off = 0 and D11 added `pos - 31`, so `e_a` ends at exactly 0.
pub(crate) fn terminal_override(
    c: &mut Circuit, term: &QReg, e_a: &[QReg], pos: &[QReg], shift: &[QReg],
) {
    let prev = c.push_section("p.exp.term_override");
    ctrl_sub_reg(c, term, e_a, pos);
    ctrl_sub_reg(c, term, e_a, shift);
    ctrl_add_const(c, term, e_a, 30);
    c.pop_section(&prev);
}

/// Inverse of [`terminal_override`].
pub(crate) fn terminal_override_inverse(
    c: &mut Circuit, term: &QReg, e_a: &[QReg], pos: &[QReg], shift: &[QReg],
) {
    let prev = c.push_section("p.exp.term_override_inv");
    ctrl_add_const(c, term, e_a, -30);
    ctrl_add_reg(c, term, e_a, shift);
    ctrl_add_reg(c, term, e_a, pos);
    c.pop_section(&prev);
}

/// Alignment amount: `t := (k - e) mod 2^|t|` when `negate` (D11: `t7 = W_A - e_B`)
/// or `t := (e + k) mod 2^|t|` otherwise (M1: `t7 = e_B - lo_B`, `k = -lo_B`).
/// PRE `t = 0`; reads the low `|t|` bits of `e` (exact whenever the true amount
/// lies in `[0, 2^|t|)`, i.e. on the support; reversible regardless).
pub(crate) fn load_affine(c: &mut Circuit, e: &[QReg], t: &[QReg], k: i64, negate: bool) {
    assert!(t.len() <= e.len());
    let prev = c.push_section("p.exp.t7");
    for (src, dst) in e.iter().zip(t) {
        c.cx(src, dst);
    }
    if negate {
        // t = e -> ~e = -e - 1 -> k - e
        for q in t {
            c.x(q);
        }
        add_const(c, t, k + 1);
    } else {
        add_const(c, t, k);
    }
    c.pop_section(&prev);
}

/// Inverse of [`load_affine`] (returns `t` to 0).
pub(crate) fn unload_affine(c: &mut Circuit, e: &[QReg], t: &[QReg], k: i64, negate: bool) {
    assert!(t.len() <= e.len());
    let prev = c.push_section("p.exp.t7_inv");
    if negate {
        add_const(c, t, -(k + 1));
        for q in t {
            c.x(q);
        }
    } else {
        add_const(c, t, -k);
    }
    for (src, dst) in e.iter().zip(t) {
        c.cx(src, dst);
    }
    c.pop_section(&prev);
}

// ------------------------------------------------------------ predicates

/// `out ^= [e == k]` (X-bracket of the zero bits of `k`, one `mcx_clean_k`).
pub(crate) fn xor_eq_const(c: &mut Circuit, e: &[QReg], k: usize, out: &QReg) {
    let n = e.len();
    if n == 0 {
        if k == 0 {
            c.x(out);
        }
        return;
    }
    if k >> n != 0 {
        return; // unreachable constant: predicate is identically 0
    }
    let prev = c.push_section("p.exp.eq");
    let zero_bits: Vec<&QReg> = e.iter().enumerate().filter(|(j, _)| (k >> j) & 1 == 0).map(|(_, q)| q).collect();
    for q in &zero_bits {
        c.x(q);
    }
    mcx_clean_k(c, &refs(e), out);
    for q in &zero_bits {
        c.x(q);
    }
    c.pop_section(&prev);
}

/// `out ^= [e == 0]`.
pub(crate) fn xor_is_zero(c: &mut Circuit, e: &[QReg], out: &QReg) {
    xor_eq_const(c, e, 0, out);
}

/// `out ^= [e != 0]` = the terminal-aware swap's `a_nonzero = OR(e_A)`.
pub(crate) fn xor_nonzero(c: &mut Circuit, e: &[QReg], out: &QReg) {
    xor_eq_const(c, e, 0, out);
    c.x(out);
}

// ------------------------------------------------- the terminal predicate

fn onehot_coherent() -> bool {
    std::env::var("MIDQ_ONEHOT_COHERENT").ok().as_deref() == Some("1")
}

/// Leaf-by-leaf DFS one-hot engine on `addr` (design 2.2 in cursor form)
/// rooted at the FOLDED root `root = gate AND eq1 AND [addr[w-1] == h]`
/// (`eq1 = [e_b == 1]`, recomputed transiently whenever the root is (re)made:
/// at the start, when the walk crosses from the lower half `h = 0` to the
/// upper half `h = 1`, and at the end), so neither `eq1` nor a separate
/// unfolded root is held during the ladder: the live wires are the root and
/// one level per remaining address bit (`w - 1`), i.e. one fewer than the
/// unfolded form (the D0 moment must not exceed the masked-adder moment once
/// the 7-bit exponents have moved that moment down). Level `l` (1-based
/// below the root) holds `root AND [addr[w-1-l..w-1) == the corresponding
/// bits of the current leaf]`; the leaf wire is the deepest level (the root
/// itself for `w = 1`). Ascending only: `advance` moves from leaf i to i+1 by
/// clearing the trailing-ones levels, one CX flip and re-pushing them (~1 CCX
/// per visited leaf); the half crossing re-targets the root (two
/// `mcx_clean_k(3)` and two `eq1` computes). Inactive rows (`gate = 0`, or
/// `e_b != 1`) hold every level at 0.
struct OnehotCursor<'a> {
    gate: &'a QReg,
    e_b: &'a [QReg],
    addr: &'a [QReg],
    root: Option<QReg>,
    /// The folded top-bit value of the held root.
    root_h: bool,
    levels: Vec<QReg>,
    cur: Option<usize>,
    coherent: bool,
}

impl<'a> OnehotCursor<'a> {
    fn new(gate: &'a QReg, e_b: &'a [QReg], addr: &'a [QReg]) -> Self {
        assert!(!addr.is_empty(), "onehot cursor: empty address");
        Self { gate, e_b, addr, root: None, root_h: false, levels: Vec::new(), cur: None, coherent: onehot_coherent() }
    }

    fn w(&self) -> usize {
        self.addr.len()
    }

    /// Number of cursor levels below the root (the top address bit is folded).
    fn depth(&self) -> usize {
        self.w() - 1
    }

    /// `root := gate AND eq1 AND [addr[w-1] == h]` (eq1 transient).
    fn set_root(&mut self, c: &mut Circuit, h: bool) {
        debug_assert!(self.root.is_none() && self.levels.is_empty());
        let eq1 = c.alloc_qreg("pk.eq1");
        xor_eq_const(c, self.e_b, 1, &eq1);
        let root = c.alloc_qreg("pk.term_root");
        let top = &self.addr[self.w() - 1];
        if !h {
            c.x(top);
        }
        mcx_clean_k(c, &[self.gate, &eq1, top], &root);
        if !h {
            c.x(top);
        }
        xor_eq_const(c, self.e_b, 1, &eq1);
        c.zero_and_free(eq1);
        self.root = Some(root);
        self.root_h = h;
    }

    /// Release the root (the same 3-control AND, XOR is self-inverse).
    fn clear_root(&mut self, c: &mut Circuit) {
        debug_assert!(self.levels.is_empty());
        let root = self.root.take().expect("onehot cursor: root held");
        let eq1 = c.alloc_qreg("pk.eq1");
        xor_eq_const(c, self.e_b, 1, &eq1);
        let top = &self.addr[self.w() - 1];
        if !self.root_h {
            c.x(top);
        }
        mcx_clean_k(c, &[self.gate, &eq1, top], &root);
        if !self.root_h {
            c.x(top);
        }
        xor_eq_const(c, self.e_b, 1, &eq1);
        c.zero_and_free(eq1);
        c.zero_and_free(root);
    }

    fn parent(&self, depth: usize) -> &QReg {
        if depth == 0 { self.root.as_ref().expect("onehot cursor: root held") } else { &self.levels[depth - 1] }
    }

    /// Address bit of level `depth` (0-based below the root): the bits below
    /// the folded top bit, MSB first.
    fn bit(&self, depth: usize) -> &QReg {
        &self.addr[self.w() - 2 - depth]
    }

    /// Materialise the wire at `depth` (0-based) = parent AND [bit == b].
    fn push(&mut self, c: &mut Circuit, depth: usize, b: bool) {
        debug_assert_eq!(self.levels.len(), depth);
        let child = c.alloc_qreg("pk.onehot");
        {
            let parent = self.parent(depth);
            let bit = self.bit(depth);
            if !b {
                c.x(bit);
            }
            c.ccx(parent, bit, &child);
            if !b {
                c.x(bit);
            }
        }
        self.levels.push(child);
    }

    fn pop(&mut self, c: &mut Circuit, depth: usize, b: bool) {
        debug_assert_eq!(self.levels.len(), depth + 1);
        let child = self.levels.pop().expect("onehot cursor: empty");
        {
            let parent = self.parent(depth);
            let bit = self.bit(depth);
            if !b {
                c.x(bit);
            }
            if self.coherent {
                c.ccx(parent, bit, &child);
            } else {
                c.clear_and(&child, parent, bit);
            }
            if !b {
                c.x(bit);
            }
        }
        c.zero_and_free(child);
    }

    /// parent AND NOT bit  <->  parent AND bit  (0 T).
    fn flip(&mut self, c: &mut Circuit, depth: usize) {
        let parent = self.parent(depth);
        c.cx(parent, &self.levels[depth]);
    }

    fn leaf(&self) -> &QReg {
        if self.depth() == 0 { self.root.as_ref().expect("onehot cursor: root held") } else { &self.levels[self.depth() - 1] }
    }

    /// Move to the next leaf (leaf 0 from the idle state).
    fn advance(&mut self, c: &mut Circuit) {
        let d = self.depth();
        match self.cur {
            None => {
                self.set_root(c, false);
                for depth in 0..d {
                    self.push(c, depth, false);
                }
                self.cur = Some(0);
            }
            Some(i) => {
                assert!(i + 1 < (1usize << self.w()), "onehot cursor: past the last leaf");
                let t = (i.trailing_ones() as usize).min(d);
                for depth in (d - t..d).rev() {
                    self.pop(c, depth, true);
                }
                if t == d {
                    // the low d bits of i are all ones: i + 1 crosses into the upper half
                    debug_assert!(!self.root_h && i + 1 == 1usize << d);
                    self.clear_root(c);
                    self.set_root(c, true);
                } else {
                    self.flip(c, d - 1 - t);
                }
                for depth in d - t..d {
                    self.push(c, depth, false);
                }
                self.cur = Some(i + 1);
            }
        }
    }

    /// Unwind every level and the root (from the current leaf to the idle state).
    fn finish(&mut self, c: &mut Circuit) {
        if let Some(i) = self.cur.take() {
            let d = self.depth();
            for depth in (0..d).rev() {
                let b = (i >> (d - 1 - depth)) & 1 == 1;
                self.pop(c, depth, b);
            }
            self.clear_root(c);
        }
    }
}

/// D0 and D0-clear: `term ^= gate_div AND [e_b == 1] AND [a_win mod 2^shift == 0]`
/// (see the module doc for the structure and the ORDERING CONTRACT: compute
/// after D1 with `shift = s_raw` in the LSB frame, clear between D10 and D12).
/// `a_win` = the LSB-frame value window `R1[0..n)`; leaves `shift > n` are
/// pruned (never fire). Self-inverse; every ancilla (eq1, the folded root,
/// the KG ancillae, the cursor levels, the capture flags) is returned to 0.
/// Wires at the ladder moment: root 1 + cursor levels `w - 1` + KG ancillae +
/// the capture flag + `term` (10 for the 5-bit shift and the 28-window).
pub(crate) fn term_toggle(
    c: &mut Circuit, gate_div: &QReg, e_b: &[QReg], shift: &[QReg], a_win: &[QReg], term: &QReg,
) {
    term_toggle_with_workspace(c, gate_div, e_b, shift, a_win, term, None);
}

pub(crate) fn term_toggle_with_workspace(
    c: &mut Circuit, gate_div: &QReg, e_b: &[QReg], shift: &[QReg], a_win: &[QReg], term: &QReg,
    clean: Option<&QReg>,
) {
    let n = a_win.len();
    let w = shift.len();
    let prev = c.push_section("p.exp.term");
    if n == 0 {
        // A mod 1 == 0 always: term ^= gate_div AND eq1 AND [shift == 0].
        let eq1 = c.alloc_qreg("pk.eq1");
        xor_eq_const(c, e_b, 1, &eq1);
        let zero_bits = refs(shift);
        for q in &zero_bits {
            c.x(q);
        }
        let mut ctrls: Vec<&QReg> = vec![gate_div, &eq1];
        ctrls.extend(zero_bits.iter().copied());
        mcx_clean_k(c, &ctrls, term);
        for q in &zero_bits {
            c.x(q);
        }
        xor_eq_const(c, e_b, 1, &eq1);
        c.zero_and_free(eq1);
    } else {
        let hi = if w >= usize::BITS as usize { n } else { n.min((1usize << w) - 1) };
        for q in a_win {
            c.x(q);
        }
        let count = kg_prefix_compact_ancilla_count(n);
        let borrow = clean.filter(|_| count > 0);
        if let Some(q) = borrow {
            assert!(e_b.iter().chain(shift).chain(a_win).all(|r| r.id() != q.id()));
            assert!(q.id() != term.id() && q.id() != gate_div.id());
        }
        let anc = c.alloc_qreg_bits("pk.term_kg", count - usize::from(borrow.is_some()));
        let mut anc_refs: Vec<&QReg> = anc.iter().collect();
        anc_refs.extend(borrow);
        let mut cursor = OnehotCursor::new(gate_div, e_b, shift);
        {
            let win = refs(a_win);
            let kg = KgPrefixAnd::new_compact_borrowed(&win, &anc_refs);
            let done = kg.forward(c, |c, i, ctrls| {
                if i > hi {
                    return;
                }
                cursor.advance(c);
                let mut all: Vec<&QReg> = vec![cursor.leaf()];
                all.extend(ctrls.iter().copied());
                if all.len() == 3 {
                    // The exponent is read-only during the capture. Borrow one
                    // of its bits and restore it, instead of a fresh clean flag.
                    crate::point_add::trailmix_port::arith::mcx::mcx_dirty(c, &all, term, &e_b[0]);
                } else {
                    mcx_clean_k(c, &all, term);
                }
            });
            cursor.finish(c);
            done.reverse(c, |_, _, _| {});
        }
        for q in anc {
            c.zero_and_free(q);
        }
        for q in a_win {
            c.x(q);
        }
    }
    c.pop_section(&prev);
}

/// Selftest entry (`MIDQ_PACKED_SELFTEST=1`): exhaustive over the 9-bit values of
/// every op, forward + inverse on the same data, phase 0, ancillae clean, T printed.
pub(crate) fn selftest() {
    selftest_impl::run();
}
