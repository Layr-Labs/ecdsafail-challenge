//! PP_J_YFUSE (agent J): exact fusions of the numerator's coordinate
//! subtractions with the replay's round-0 halving / doubling.
//!
//! Divide: the replay's round 0 is `y <- y/2 (mod p)` and is the first thing
//! that touches `y` after `coord_y_sub`. Both are folded into one
//! `y <- (y - oy)/2 (mod p)`: the subtraction's borrow `c` and the halving's
//! parity `par` select ONE correction `k*f`, `k = c + par in {0,1,2}`, in a
//! single per-position ladder one bit wider than `f_slice` (the same shape as
//! `round0_reverse`).  `par` leaves on the top wire exactly as in
//! `finish_halving`; `c` is erased with the unchanged top-bit compare.
//!
//! Multiply: the replay's round 0 is `y <- 2y (mod p)` and is the last thing
//! that touches `y` before `coord_y_sub_final`.  Both become one
//! `y <- 2y - oy (mod p)`: the doubling's overflow `o` and the borrow `c`
//! select one `(c - o)*f` correction (`o` a complement sandwich around one
//! `f_slice` fold).  `o ^ c` is the parity of `r + oy`, so it is erased with
//! CX gates; `c` is `[r + oy >= 2^256]`, the unchanged top-bit compare.
//!
//! Neither fold window nor compare width moves: both new folds are at least
//! `f_slice` wide and there is one truncated fold per site instead of two.

use super::compare::erase_with_compare;
use super::const_arith::cadd_const_per_position_trunc;
use super::modular::{add_f_window, f, f_slice, ripple_add};
use super::{env_flag, Builder, N};
use crate::circuit::QubitId;

pinned_env!(erase_compare, "ERASE_COMPARE");

pub fn j_yfuse() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_YFUSE"))
}

fn trace() -> bool {
    env_flag("PP_J_TRACE")
}

/// `acc <- (acc - value)/2 (mod p)`.
pub fn mod_sub_halve(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    let n = acc.len();
    assert_eq!(n, N);
    assert_eq!(value.len(), n);
    let before = circ.i35_cost();
    circ.x_all(acc);
    let c = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(c));
    // acc = ~D with D = y - oy + c*2^256.
    let a = circ.alloc_qubit();
    circ.cx(acc[0], a);
    circ.x(a); // a = D0 = (k odd)
    let par = circ.alloc_qubit();
    circ.cx(a, par);
    circ.cx(c, par); // par = D0 ^ c: parity of s = D - c*f
    let b2 = circ.alloc_qubit();
    circ.ccx(c, par, b2); // k == 2
    let g = circ.alloc_qubit();
    circ.cx(a, g);
    circ.cx(b2, g); // k != 0
    // Position 0: acc0 = ~a, addend a: sum 1, carry 0.
    circ.cx(a, acc[0]);
    let width = super::modular::go_fs("GO_FG_J") + 1;
    let fc = f();
    let controls: Vec<Option<QubitId>> = (1..width)
        .map(|i| match (fc.bit(i), fc.bit(i - 1)) {
            (false, false) => None,
            (true, false) => Some(a),
            (false, true) => Some(b2),
            (true, true) => Some(g),
        })
        .collect();
    cadd_const_per_position_trunc(circ, &acc[1..width], &controls);
    circ.cx(b2, g);
    circ.cx(a, g);
    circ.free(g);
    let m = circ.alloc_bit();
    circ.hmr(b2, m);
    circ.cz_if(c, par, m);
    circ.free_bit(m);
    circ.free(b2);
    circ.cx(par, a);
    circ.cx(c, a);
    circ.free(a);
    let k = erase_compare();
    erase_with_compare(circ, c, &acc[n - k..], &value[n - k..], None);
    circ.free(c);
    circ.x_all(acc);
    // acc = D - k*f, bit 0 clear: rotate down, parity onto the top wire.
    for i in 0..n - 1 {
        circ.swap(acc[i], acc[i + 1]);
    }
    circ.cx(par, acc[n - 1]);
    circ.cx(acc[n - 1], par);
    circ.free(par);
    if trace() {
        eprintln!("J_SUBHALVE {}", circ.i35_cost() - before);
    }
}

/// `acc <- 2*acc - value (mod p)`.
pub fn mod_double_sub(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) {
    let n = acc.len();
    assert_eq!(n, N);
    assert_eq!(value.len(), n);
    let before = circ.i35_cost();
    let o = circ.alloc_qubit();
    circ.swap(acc[n - 1], o);
    for i in (0..n - 1).rev() {
        circ.swap(acc[i], acc[i + 1]);
    }
    // acc = A = 2y mod 2^256, A0 = 0; o = 2y >> 256.
    circ.x_all(acc);
    let c = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(c));
    // acc = w = ~D, D = A - oy + c*2^256; 2y - oy == D + (o - c)*f (mod p).
    // In the complemented frame that is w += (c - o)*f.
    let width = super::modular::go_fs("GO_FG_J");
    circ.cx(o, c); // c = o ^ c: a correction is due
    for &q in &acc[..width] {
        circ.cx(o, q);
    }
    add_f_window(circ, c, acc, width, false);
    for &q in &acc[..width] {
        circ.cx(o, q);
    }
    // r = ~acc satisfies 2y = r + oy + (o - c)*p, so e = o ^ c = r0 ^ oy0,
    // which is ~acc0 ^ value0.  Wire c holds e; XOR it into o (o becomes the
    // borrow) and clear wire c with the parity itself.
    circ.cx(c, o);
    circ.cx(acc[0], c);
    circ.x(c);
    circ.cx(value[0], c);
    circ.free(c);
    // o = borrow = [r + oy >= 2^256] = [~r < oy] (threshold p when e = 1:
    // the two differ only for r + oy in [p, 2^256)).
    let k = erase_compare();
    erase_with_compare(circ, o, &acc[n - k..], &value[n - k..], None);
    circ.free(o);
    circ.x_all(acc);
    if trace() {
        eprintln!("J_DOUBLESUB {}", circ.i35_cost() - before);
    }
}


// ---- PP_J_XFUSE: coord_x_sub's fold moved into the walk's round-0 lift ----
//
// `coord_x_sub` stops after its ripple: x holds D = x - ox (mod 2^256) and the
// borrow `c` stays live, so the true denominator is a = D - c*f.  The divide's
// round-0 lift already adds one selected sparse constant to floor(a/2); writing
// floor(a/2) = floor(D/2) - c*(h + a0) turns the four lift arms into four arms
// over the same magnitudes {f, h+1, h, 0}, so the coordinate fold disappears.
// `c` is erased afterwards with the same top-bit compare against ox, on D's
// top bits, which neither fold window reaches.

static X_CARRY: std::sync::Mutex<Option<(QubitId, Vec<crate::circuit::BitId>)>> =
    std::sync::Mutex::new(None);

pub fn j_xfuse() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_XFUSE"))
}

pub fn take_x_carry() -> Option<(QubitId, Vec<crate::circuit::BitId>)> {
    X_CARRY.lock().unwrap().take()
}

/// `acc <- acc - value (mod 2^256)`; returns the borrow wire, left live.
pub fn mod_sub_keep_borrow(
    circ: &mut Builder,
    value: &[QubitId],
    acc: &[QubitId],
    coord: &[crate::circuit::BitId],
) {
    circ.x_all(acc);
    let c = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(c));
    circ.x_all(acc);
    let prev = X_CARRY.lock().unwrap().replace((c, coord.to_vec()));
    assert!(prev.is_none());
}

/// Erase the kept borrow: `c = [~D_top < ox_top]`, the same predicate
/// `mod_sub_vented` erases with. `d_top` are D's top `erase_compare()` bits.
pub fn erase_x_carry(circ: &mut Builder, c: QubitId, d_top: &[QubitId], coord: &[crate::circuit::BitId]) {
    let k = d_top.len();
    assert_eq!(k, erase_compare());
    let ox_top = &coord[coord.len() - k..];
    let temp = circ.alloc_qubits(k);
    for (&q, &b) in temp.iter().zip(ox_top) {
        circ.x_if_bit(q, b);
    }
    circ.x_all(d_top);
    if super::modular::r5_ccmp(1) { super::compare::erase_with_compare_v0(circ, c, d_top, &temp, ox_top[0]); } else {
    erase_with_compare(circ, c, d_top, &temp, None);
    }
    circ.x_all(d_top);
    for (&q, &b) in temp.iter().zip(ox_top) {
        circ.x_if_bit(q, b);
    }
    for q in temp {
        circ.free(q);
    }
    circ.free(c);
}

pub fn x_erase_width() -> usize {
    erase_compare()
}


// ---- PP_J_AFUSE / PP_J_RFUSE: round0_reverse's fold moved into the next
// coordinate op (coord_add3x after the divide, coord_rsub_final after the
// multiply).
//
// round0_reverse turns the walk's half-state into a == R + k*f (mod 2^256),
// where R is the shifted state and k = a0 - 2*!a1.  Deferred, x holds R while
// the coordinate ripple runs; the ripple's carry then joins the same selected
// {0, f, 2f} correction, so one truncated ladder replaces two (the coordinate
// op's own f_slice fold disappears).  a0 and !a1 are recovered from the low two
// bits of the result (one majority AND); the carry is erased by the unchanged
// top-bit compare.  Neither fold window nor compare width moves.

static R0_STASH: std::sync::Mutex<Option<(QubitId, QubitId)>> = std::sync::Mutex::new(None);

pub fn j_afuse() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_AFUSE"))
}

pub fn j_rfuse() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_RFUSE"))
}

pub fn defer_r0_reverse(phase: &str) -> bool {
    (phase == "pp_div_walkback" && j_afuse()) || (phase == "pp_mul_walkback" && j_rfuse())
}

pub fn stash_r0(a0: QubitId, n: QubitId) {
    let prev = R0_STASH.lock().unwrap().replace((a0, n));
    assert!(prev.is_none());
}

pub fn take_r0() -> Option<(QubitId, QubitId)> {
    R0_STASH.lock().unwrap().take()
}

/// `acc[..f_slice()+1] -= M` if `neg` else `+= M`, with M = (alpha + gamma)*f,
/// truncated to the window exactly like `round0_reverse`'s ladder.
fn selected_f_or_2f(circ: &mut Builder, acc: &[QubitId], alpha: QubitId, gamma: QubitId, neg: QubitId) {
    let b = circ.alloc_qubit();
    circ.ccx(alpha, gamma, b); // magnitude 2f
    let g = circ.alloc_qubit();
    circ.cx(alpha, g);
    circ.cx(gamma, g); // magnitude f
    let o = circ.alloc_qubit();
    circ.cx(g, o);
    circ.cx(b, o); // nonzero
    let width = super::modular::go_fs("GO_FG_J") + 1;
    let fc = f();
    let controls: Vec<Option<QubitId>> = (0..width)
        .map(|i| match (fc.bit(i), i > 0 && fc.bit(i - 1)) {
            (false, false) => None,
            (true, false) => Some(g),
            (false, true) => Some(b),
            (true, true) => Some(o),
        })
        .collect();
    circ.cx_all(neg, &acc[..width]);
    cadd_const_per_position_trunc(circ, &acc[..width], &controls);
    circ.cx_all(neg, &acc[..width]);
    circ.cx(b, o);
    circ.cx(g, o);
    circ.free(o);
    circ.cx(gamma, g);
    circ.cx(alpha, g);
    circ.free(g);
    let m = circ.alloc_bit();
    circ.hmr(b, m);
    circ.cz_if(alpha, gamma, m);
    circ.free_bit(m);
    circ.free(b);
}

/// `out ^= maj(!x0, q, r)` as `((!x0^r) & (q^r)) ^ r`: one Toffoli, measured
/// back out.
fn xor_low_maj(circ: &mut Builder, out: QubitId, x0: QubitId, q: QubitId, r: QubitId) {
    circ.cx(r, x0);
    circ.x(x0);
    circ.cx(r, q);
    let t = circ.alloc_qubit();
    circ.ccx(x0, q, t);
    circ.cx(t, out);
    circ.cx(r, out);
    let m = circ.alloc_bit();
    circ.hmr(t, m);
    circ.cz_if(x0, q, m);
    circ.free_bit(m);
    circ.free(t);
    circ.cx(r, q);
    circ.x(x0);
    circ.cx(r, x0);
}

/// PP_J_AFUSE: `acc <- a + value (mod p)` where acc holds the deferred R.
pub fn mod_add_r0fused(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], a0: QubitId, n: QubitId) {
    let n_bits = acc.len();
    assert_eq!(n_bits, N);
    assert_eq!(value.len(), N);
    let before = circ.i35_cost();
    let c = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(c));
    // acc = R + K - c*2^256; the result is acc + (k + c)*f: add (a0 + c)*f when
    // a1, subtract (2 - a0 - c)*f when !a1 -- magnitude (a0^n) + (c^n).
    circ.cx(n, a0);
    circ.cx(n, c);
    selected_f_or_2f(circ, acc, a0, c, n);
    circ.cx(n, c);
    circ.cx(n, a0);
    // acc = a + K - c*p and f == 1 (mod 4), so a == x - K - c (mod 4).
    circ.cx(acc[0], a0);
    circ.cx(value[0], a0);
    circ.cx(c, a0);
    circ.free(a0);
    // a1 = x1 ^ K1 ^ maj(!x0, K0, c).
    circ.cx(acc[1], n);
    circ.cx(value[1], n);
    circ.x(n);
    xor_low_maj(circ, n, acc[0], value[0], c);
    circ.free(n);
    let k = erase_compare();
    erase_with_compare(circ, c, &acc[n_bits - k..], &value[n_bits - k..], None);
    circ.free(c);
    if trace() {
        eprintln!("J_ADDFUSED {}", circ.i35_cost() - before);
    }
}

/// PP_J_RFUSE: `acc <- ox - a (mod p)` where acc holds the deferred R and
/// `value` holds t1 = ox + 1.
pub fn mod_rsub_r0fused(circ: &mut Builder, value: &[QubitId], acc: &[QubitId], a0: QubitId, n: QubitId) {
    let n_bits = acc.len();
    assert_eq!(n_bits, N);
    assert_eq!(value.len(), N);
    let before = circ.i35_cost();
    circ.x_all(acc);
    let c = circ.alloc_qubit();
    ripple_add(circ, value, acc, None, Some(c));
    // acc = ox - R + cbar*2^256; the result is acc - (k + cbar)*f: subtract
    // (a0 + cbar)*f when a1, add (2 - a0 - cbar)*f when !a1.
    circ.x(c); // cbar
    circ.cx(n, a0);
    circ.cx(n, c);
    circ.x(n); // subtract when a1
    selected_f_or_2f(circ, acc, a0, c, n);
    circ.x(n);
    circ.cx(n, c);
    circ.cx(n, a0);
    circ.x(c);
    // acc = ox - a + cbar*p, so sigma := a + 1 == t1 + !x + c (mod 4).
    // a0 = !sigma0 = t1_0 ^ x0 ^ c.
    circ.cx(acc[0], a0);
    circ.cx(value[0], a0);
    circ.cx(c, a0);
    circ.free(a0);
    // !a1 = sigma0 ^ sigma1 = t1_0 ^ t1_1 ^ x0 ^ x1 ^ c ^ maj(t1_0, !x0, c).
    circ.cx(value[0], n);
    circ.cx(value[1], n);
    circ.cx(acc[0], n);
    circ.cx(acc[1], n);
    circ.cx(c, n);
    xor_low_maj(circ, n, acc[0], value[0], c);
    circ.free(n);
    let k = erase_compare();
    erase_with_compare(circ, c, &acc[n_bits - k..], &value[n_bits - k..], None);
    circ.free(c);
    if trace() {
        eprintln!("J_RSUBFUSED {}", circ.i35_cost() - before);
    }
}


// ---- PP_J_SFUSE: the square's last subtraction + the multiply's round 0 ----
//
// The square's C branch ends `x -= rot(C)` with a full mod_addsub.  The next op
// on x is the multiply walk's round-0 lift, exactly as coord_x_sub precedes the
// divide's (PP_J_XFUSE): keep the borrow, let the lift arms absorb its -f fold,
// then erase the borrow with the unchanged top-bit compare against rot(C)'s top
// bits, which are still live inside with_square.  The window adds in between
// stop below the compare window, so D's top bits are the same bits.

pub fn j_sfuse() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_SFUSE"))
}

/// PP_J_SFUSE_B: the same fusion on the B branch, run last (see `sub_square`).
pub fn j_sfuse_b() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_SFUSE_B"))
}

/// PP_J_WCIN: in the square's rotated folds the ripple's carry `c` is not
/// folded by its own f_slice ladder.  Its `c*f` terms at 2^4, 2^6, 2^10, 2^32
/// ride as carry-ins on the rotated fold's own NAF window adds (same shifts,
/// same signs, carry-in is free), and only the unit term is added by a
/// `PP_J_WCIN_W`-bit increment.  `c` is then erased by the unchanged top-bit
/// compare, which no window reaches.
pub fn j_wcin() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_WCIN"))
}

/// PP_J_WCIN_B0LAST (with PP_J_SFUSE_B): B's plain shift-0 subtract runs last
/// and is the one fused into round 0, so the 2^32 term gets carry-in windows.
pub fn j_wcin_b0last() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_WCIN_B0LAST"))
}

/// PP_J_BMERGE (needs WCIN_B0LAST): the B square's NAF folds at 2^4, 2^6,
/// 2^10 and 2^32 share ONE set of (f-1) windows.  Their wrapped limbs are
/// nested prefixes of b2's top bits, so the windows carry
/// `R = high32 + high10 - high6 + high4` (0 <= R < 2^33) built in scratch from
/// b2 and unbuilt after.  The 2^32 fold's carry rides those windows (WCIN);
/// the three small folds keep the plain mod_addsub carry fold.
pub fn j_bmerge() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_J_BMERGE"))
}

pub fn wcin_w() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| super::optional_env::<usize>("PP_J_WCIN_W").unwrap_or(super::fold_guard() + 1))
}

/// `acc <- acc - value (mod 2^256)`, the mod_addsub add; returns the live borrow.
pub fn sub_keep_borrow_q(circ: &mut Builder, value: &[QubitId], acc: &[QubitId]) -> QubitId {
    circ.x_all(acc);
    let c = circ.alloc_qubit();
    super::modular::peak_fitted_add(circ, value, acc, c);
    circ.x_all(acc);
    c
}

/// Erase a kept subtract borrow against a quantum subtrahend's top bits:
/// `c = [~D_top < value_top]`, as mod_addsub's negated erase.
pub fn erase_q_carry(circ: &mut Builder, c: QubitId, d_top: &[QubitId], value_top: &[QubitId]) {
    assert_eq!(d_top.len(), erase_compare());
    assert_eq!(value_top.len(), d_top.len());
    circ.x_all(d_top);
    erase_with_compare(circ, c, d_top, value_top, None);
    circ.x_all(d_top);
    circ.free(c);
}
