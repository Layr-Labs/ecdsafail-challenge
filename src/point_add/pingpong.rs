//! H5.A1: ping-pong GCD in-place multiplier and divider, after Long et al.,
//! "Efficient Record-and-Replay Arithmetic for Quantum Elliptic-Curve Point
//! Addition" (arXiv:2609.28882).
//!
//! GCD on signed odd (ρ0, ρ1) = (p, x*), x* = x if x is odd else x − p. Round i
//! has source s = ρ_{i mod 2} and target t = ρ_{1 − i mod 2}; the tape bit
//! e = t[1] ⊕ s[1] (two CNOTs) chooses t ← (t + (−1)^e s)/2, which is odd again.
//! No comparison and no swap: one add-subtract per round on the fitted width.
//! After PP_ROUNDS rounds (ρ0, ρ1) = (±1, ±1) and only the two signs σ are kept.
//! Every register is a fixed multiple of x mod p, so the tape replayed on
//! (z0, z1) mod p gives
//!   divide (rounds in order, z_t ← (z_t ± z_s)/2): (0, y) → (±y/x, ±y/x),
//!   multiply (rounds reversed, z_t ← 2z_t ∓ z_s): (±y, ±y) → (0, x·y).
//! Classical checks: experiments/moonshots/pingpong.py (algebra),
//! ppcell.py (bit-exact cells); round count and widths: pp_widths.rs.

use super::eea::add_c_low;
use super::pp_widths::{PP_ROUNDS, PP_WIDTH};
use super::*;

/// Low bits that receive the κ·c correction (carry loss ≈ 2^-41 per cell; H5.A3: 85 → 80, H5.A5: → 74).
const PP_WINDOW: usize = 74;
/// Top bits compared to clear e2 (miss ≈ 2^-40 per cell; H5.A3: 64 → 48, H5.A5: → 40).
const PP_CMP_BITS: usize = 40;
/// H5.A2: the 258-bit replay add runs as two chunks split at this bit.
const PP_CHUNK: usize = 128;
/// H5.A2: top bits of the low chunk compared to clear its carry-out (miss ≈ 2^-41 per cell; H5.A5: 48 → 40).
const PP_CHUNK_CMP: usize = 40;
/// H5.A2: rounds below this compare the whole low chunk (z0 ≡ 0 at rounds 0–1).
const PP_EXACT_ROUNDS: usize = 4;
/// H5.A2: the κ operand c·o + 2c·g fits in 34 bits.
const PP_KAPPA_BITS: usize = 34;

pub(super) struct PpTape {
    e: Vec<QubitId>,
    sigma: [QubitId; 2],
}

/// Signed register length at the entry of round i (fitted bitlen + sign).
fn sw(i: usize) -> usize {
    PP_WIDTH[i] as usize + 1
}

/// ρ1 keeps x's own qubit ids for its low n bits; those are reserved while
/// free so that only step-local scratch may borrow them.
fn take(b: &mut B, k: usize, j: usize, x: &[QubitId]) -> QubitId {
    if k == 1 && j < x.len() { b.alloc_specific(x[j]) } else { b.alloc_qubit() }
}

fn give(b: &mut B, k: usize, j: usize, x: &[QubitId], q: QubitId) {
    if k == 1 && j < x.len() { b.free_reserved(q) } else { b.free(q) }
}

/// Resize both signed registers to `len`, dropping or adding sign copies.
fn resize(b: &mut B, regs: &mut [Vec<QubitId>; 2], len: usize, x: &[QubitId]) {
    for k in 0..2 {
        while regs[k].len() > len {
            let q = regs[k].pop().expect("nonempty");
            let top = *regs[k].last().expect("nonempty");
            b.cx(top, q);
            give(b, k, regs[k].len(), x, q);
        }
        while regs[k].len() < len {
            let j = regs[k].len();
            let q = take(b, k, j, x);
            b.cx(regs[k][j - 1], q);
            regs[k].push(q);
        }
    }
}

fn roles(i: usize) -> (usize, usize) {
    if i % 2 == 0 { (0, 1) } else { (1, 0) }
}

/// reg ±= ctl·k over reg's full length (k < 2^256), with a zero-padded operand.
fn cadd_const(b: &mut B, reg: &[QubitId], k: U256, ctl: QubitId, add: bool) {
    let op = b.alloc_qubits(reg.len());
    for j in 0..reg.len().min(256) {
        if bit(k, j) {
            b.cx(ctl, op[j]);
        }
    }
    if add { add_nbit_qq_fast(b, &op, reg) } else { sub_nbit_qq_fast(b, &op, reg) }
    for j in 0..reg.len().min(256) {
        if bit(k, j) {
            b.cx(ctl, op[j]);
        }
    }
    b.free_vec(&op);
}

/// One forward round: e ← t[1] ⊕ s[1]; t ← (t + (−1)^e s)/2.
fn round_fwd(b: &mut B, regs: &[Vec<QubitId>; 2], i: usize, e: QubitId) {
    let (si, ti) = roles(i);
    let n = regs[ti].len();
    b.cx(regs[ti][1], e);
    b.cx(regs[si][1], e);
    let te = b.alloc_qubit();
    b.cx(regs[ti][n - 1], te);
    let se = b.alloc_qubit();
    b.cx(regs[si][n - 1], se);
    let mut t = regs[ti].clone();
    t.push(te);
    let mut s = regs[si].clone();
    s.push(se);
    // t − s = ¬(¬t + s): flip the target under e around one adder.
    for &q in &t {
        b.cx(e, q);
    }
    // H5.A5: t, s odd, so bit 0's carry is t[0] (= 1 ⊕ e here) and its sum is t[0] ⊕ 1.
    cuccaro_add_fast(b, &s[1..], &t[1..], t[0]);
    b.x(t[0]);
    for &q in &t {
        b.cx(e, q);
    }
    b.cx(regs[si][n - 1], se);
    b.free(se);
    // t is even: halve by moving the zero bit 0 to the top.
    for j in 0..n {
        b.swap(t[j], t[j + 1]);
    }
    b.free(te);
}

/// Inverse of `round_fwd`; clears e.
fn round_bwd(b: &mut B, regs: &[Vec<QubitId>; 2], i: usize, e: QubitId) {
    let (si, ti) = roles(i);
    let n = regs[ti].len();
    let te = b.alloc_qubit();
    let mut t = regs[ti].clone();
    t.push(te);
    for j in (0..n).rev() {
        b.swap(t[j], t[j + 1]);
    }
    let se = b.alloc_qubit();
    b.cx(regs[si][n - 1], se);
    let mut s = regs[si].clone();
    s.push(se);
    for &q in &t {
        b.cx(e, q);
    }
    b.x(t[0]);
    cuccaro_sub_fast(b, &s[1..], &t[1..], t[0]);
    for &q in &t {
        b.cx(e, q);
    }
    b.cx(regs[si][n - 1], se);
    b.free(se);
    b.cx(regs[ti][n - 1], te);
    b.free(te);
    b.cx(regs[ti][1], e);
    b.cx(regs[si][1], e);
}

/// GCD construction. x (n qubits, value in [1, p)) is consumed: its qubits are
/// |0⟩ and reserved on return; the tape and the terminal signs hold x.
pub(super) fn gcd_forward(b: &mut B, x: &[QubitId], p: U256) -> PpTape {
    let n = x.len();
    let mut r1 = x.to_vec();
    r1.push(b.alloc_qubit());
    let r0 = b.alloc_qubits(n + 1);
    for j in 0..n {
        if bit(p, j) {
            b.x(r0[j]);
        }
    }
    // x* = x − p·[x even]; afterwards the sign bit equals [x even].
    let ctl = b.alloc_qubit();
    b.x(x[0]);
    b.cx(x[0], ctl);
    b.x(x[0]);
    cadd_const(b, &r1, p, ctl, false);
    b.cx(r1[n], ctl);
    b.free(ctl);
    let mut regs = [r0, r1];
    let mut tape = Vec::with_capacity(PP_ROUNDS);
    for i in 0..PP_ROUNDS {
        resize(b, &mut regs, sw(i), x);
        let e = b.alloc_qubit();
        round_fwd(b, &regs, i, e);
        tape.push(e);
    }
    resize(b, &mut regs, sw(PP_ROUNDS), x);
    // (ρ0, ρ1) = (±1, ±1): bit 0 is 1, every higher bit is the sign.
    let mut sigma = [QubitId(0); 2];
    for k in 0..2 {
        let reg = regs[k].clone();
        b.x(reg[0]);
        for j in 2..reg.len() {
            b.cx(reg[1], reg[j]);
        }
        sigma[k] = b.alloc_qubit();
        b.swap(reg[1], sigma[k]);
        for j in (0..reg.len()).rev() {
            give(b, k, j, x, reg[j]);
        }
    }
    PpTape { e: tape, sigma }
}

/// Inverse of `gcd_forward`: rebuilds x on its own qubits, frees the tape and signs.
pub(super) fn gcd_backward(b: &mut B, x: &[QubitId], tape: PpTape, p: U256) {
    let n = x.len();
    let len = sw(PP_ROUNDS);
    let mut regs: [Vec<QubitId>; 2] = [Vec::new(), Vec::new()];
    for k in 0..2 {
        for j in 0..len {
            let q = take(b, k, j, x);
            regs[k].push(q);
        }
        let reg = &regs[k];
        b.swap(reg[1], tape.sigma[k]);
        b.free(tape.sigma[k]);
        for j in 2..reg.len() {
            b.cx(reg[1], reg[j]);
        }
        b.x(reg[0]);
    }
    for i in (0..PP_ROUNDS).rev() {
        resize(b, &mut regs, sw(i), x);
        round_bwd(b, &regs, i, tape.e[i]);
        b.free(tape.e[i]);
    }
    let [r0, r1] = regs;
    let ctl = b.alloc_qubit();
    b.cx(r1[n], ctl);
    cadd_const(b, &r1, p, ctl, true);
    b.x(x[0]);
    b.cx(x[0], ctl);
    b.x(x[0]);
    b.free(ctl);
    b.free(r1[n]);
    for j in 0..n {
        if bit(p, j) {
            b.x(r0[j]);
        }
    }
    b.free_vec(&r0);
}

/// lo (window) ±= κ·c mod 2^|lo|, κ ∈ {−1, 0, 1, 2} encoded mod 4 as (o, e2):
/// the operand is c under o ∧ ¬f, 2c under e2 ∧ ¬f, 2^W − c under f = o ∧ e2.
fn add_kappa_c(b: &mut B, lo: &[QubitId], c: U256, o: QubitId, e2: QubitId, add: bool) {
    // H5.A2: κ = −1 (f = 1) is +c in the f-complemented frame, so the operand is
    // c·o + 2c·(e2 ⊕ f) (the two terms never overlap) on 34 bits only.
    let c2 = c << 1usize;
    let f = b.alloc_qubit();
    b.ccx(o, e2, f);
    let op = b.alloc_qubits(PP_KAPPA_BITS);
    let load = |b: &mut B| {
        for j in 0..PP_KAPPA_BITS {
            if bit(c, j) {
                b.cx(o, op[j]);
            }
            if bit(c2, j) {
                b.cx(e2, op[j]);
                b.cx(f, op[j]);
            }
        }
    };
    // Complement lo under f (and always when subtracting: lo − v = ¬(¬lo + v)).
    let frame = |b: &mut B| {
        for &q in lo {
            b.cx(f, q);
            if !add {
                b.x(q);
            }
        }
    };
    load(b);
    frame(b);
    let c_in = b.alloc_qubit();
    add_short(b, &op, lo, c_in);
    b.free(c_in);
    frame(b);
    load(b);
    b.free_vec(&op);
    let mf = b.alloc_bit();
    b.hmr(f, mf);
    b.cz_if(o, e2, mf);
    b.free(f);
}

/// H5.A2: acc += a + c_in mod 2^n, a (m bits) zero-extended to n = |acc| > m bits. The
/// measured Cuccaro sweep on the low m bits continues as a plain carry chain
/// c_{j+1} = acc_j ∧ c_j above them, so the zero operand bits need no qubits.
/// n − 1 Toffolis and n − 1 carry ancillas; a and c_in are unchanged.
pub(super) fn add_short(b: &mut B, a: &[QubitId], acc: &[QubitId], c_in: QubitId) {
    let (m, n) = (a.len(), acc.len());
    assert!(m >= 1 && n > m);
    let carries = b.alloc_qubits(n - 1);
    // Low sweep (as cuccaro_add_fast_uncapped): afterwards a[i] holds the carry into bit i + 1.
    b.cx(a[0], acc[0]);
    b.cx(a[0], c_in);
    b.ccx(c_in, acc[0], carries[0]);
    b.cx(carries[0], a[0]);
    for i in 1..m {
        b.cx(a[i], acc[i]);
        b.cx(a[i], a[i - 1]);
        b.ccx(a[i - 1], acc[i], carries[i]);
        b.cx(carries[i], a[i]);
    }
    // Carry chain over the zero operand bits; hold(j) is the qubit holding c_j.
    let hold = |j: usize| if j == m { a[m - 1] } else { carries[j - 1] };
    for j in m..n - 1 {
        b.ccx(hold(j), acc[j], carries[j]);
    }
    b.cx(hold(n - 1), acc[n - 1]);
    for j in (m..n - 1).rev() {
        let mb = b.alloc_bit();
        b.hmr(carries[j], mb);
        b.cz_if(hold(j), acc[j], mb);
        b.cx(hold(j), acc[j]);
    }
    for i in (1..m).rev() {
        b.cx(carries[i], a[i]);
        let mb = b.alloc_bit();
        b.hmr(carries[i], mb);
        b.cz_if(a[i - 1], acc[i], mb);
        b.cx(a[i], a[i - 1]);
        b.cx(a[i - 1], acc[i]);
    }
    b.cx(carries[0], a[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, acc[0], m0);
    b.cx(a[0], c_in);
    b.cx(c_in, acc[0]);
    b.free_vec(&carries);
}

/// Runs `body` with lt = [r_hi < Z_hi] on the top PP_CMP_BITS bits, where
/// Z = zs if a else ¬zs, and o temporarily holding o ⊕ a.
fn with_e2_terms<F: FnOnce(&mut B, QubitId)>(b: &mut B, r: &[QubitId], zs: &[QubitId], o: QubitId, a: QubitId, body: F) {
    let n = r.len();
    let hi = n - PP_CMP_BITS;
    b.cx(a, o);
    b.x(a);
    for j in hi..n {
        b.cx(a, zs[j]);
    }
    b.x(a);
    let lt = b.alloc_qubit();
    with_lt(b, &r[hi..], &zs[hi..], lt, |b| body(b, lt));
    b.free(lt);
    b.x(a);
    for j in hi..n {
        b.cx(a, zs[j]);
    }
    b.x(a);
    b.cx(a, o);
}

/// T ← T ± zs on 258 bits (T = zt ‖ o ‖ e2): subtract when a = 0.
/// H5.A2: two chunks split at PP_CHUNK. The low chunk's carry-out cc feeds the high
/// chunk, then is X-measured; its phase fix uses cc = [r_lo < zs_lo] (raw frame, no
/// carry-in), on the top PP_CHUNK_CMP bits unless `exact`.
fn addsub_258(b: &mut B, zt: &[QubitId], zs: &[QubitId], o: QubitId, e2: QubitId, a: QubitId, sub: bool, exact: bool) {
    let mut t = zt.to_vec();
    t.push(o);
    t.push(e2);
    // T − zs under a is T + zs under ¬a in the flipped frame.
    let flip = |b: &mut B| {
        if !sub {
            b.x(a);
        }
        for &q in &t {
            b.cx(a, q);
        }
        if !sub {
            b.x(a);
        }
    };
    let k = PP_CHUNK;
    flip(b);
    let cc = b.alloc_qubit();
    let c0 = b.alloc_qubit();
    let mut lo = t[..k].to_vec();
    lo.push(cc);
    add_short(b, &zs[..k], &lo, c0);
    b.free(c0);
    add_short(b, &zs[k..], &t[k..], cc);
    let mc = b.alloc_bit();
    b.hmr(cc, mc);
    b.free(cc);
    b.push_condition(mc);
    let kk = if exact { k } else { PP_CHUNK_CMP };
    let lt = b.alloc_qubit();
    with_lt(b, &t[k - kk..k], &zs[k - kk..k], lt, |b| b.z_if(lt, mc));
    b.free(lt);
    b.pop_condition();
    flip(b);
}

/// Multiply-direction cell: zt ← 2·zt − (−1)^a·zs mod p.
fn cell_mul(b: &mut B, zt: &[QubitId], zs: &[QubitId], a: QubitId, p: U256, exact: bool) {
    let n = zt.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1u64));
    let o = b.alloc_qubit();
    b.swap(zt[n - 1], o);
    for i in (0..n - 1).rev() {
        b.swap(zt[i], zt[i + 1]);
    }
    let e2 = b.alloc_qubit();
    addsub_258(b, zt, zs, o, e2, a, false, exact);
    add_kappa_c(b, &zt[..PP_WINDOW], c, o, e2, true);
    // e2 = (o ⊕ a) ∧ (lt ⊕ ¬a): X-measure it, fix its phase in half the shots.
    let ce = b.alloc_bit();
    b.hmr(e2, ce);
    b.free(e2);
    b.push_condition(ce);
    with_e2_terms(b, zt, zs, o, a, |b, lt| {
        b.cz(o, lt);
        b.x(a);
        b.cz(o, a);
        b.x(a);
    });
    b.pop_condition();
    // o = r[0] ⊕ zs[0].
    b.cx(zt[0], o);
    b.cx(zs[0], o);
    b.free(o);
}

/// Divide-direction cell, the inverse of `cell_mul`: zt ← (zt + (−1)^a·zs)/2 mod p.
fn cell_div(b: &mut B, zt: &[QubitId], zs: &[QubitId], a: QubitId, p: U256, exact: bool) {
    let n = zt.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1u64));
    let o = b.alloc_qubit();
    b.cx(zt[0], o);
    b.cx(zs[0], o);
    let e2 = b.alloc_qubit();
    with_e2_terms(b, zt, zs, o, a, |b, lt| {
        b.x(a);
        b.cx(a, lt);
        b.ccx(o, lt, e2);
        b.cx(a, lt);
        b.x(a);
    });
    add_kappa_c(b, &zt[..PP_WINDOW], c, o, e2, false);
    addsub_258(b, zt, zs, o, e2, a, true, exact);
    b.free(e2);
    for i in 0..n - 1 {
        b.swap(zt[i], zt[i + 1]);
    }
    b.swap(zt[n - 1], o);
    b.free(o);
}

/// z0 ⊕= p·(a ∨ z1[0]): the round-1 fix (the multiply cell leaves p, not 0,
/// exactly in that case; the divide applies it before its round 1).
fn round1_fix(b: &mut B, z0: &[QubitId], z1: &[QubitId], a: QubitId, p: U256) {
    let fl = b.alloc_qubit();
    b.x(a);
    b.x(z1[0]);
    b.ccx(a, z1[0], fl);
    b.x(fl);
    for j in 0..z0.len() {
        if bit(p, j) {
            b.cx(fl, z0[j]);
        }
    }
    b.x(fl);
    let m = b.alloc_bit();
    b.hmr(fl, m);
    b.cz_if(a, z1[0], m);
    b.x(z1[0]);
    b.x(a);
    b.free(fl);
}

/// v ← p − v if ctl (v in [1, p)): complement under ctl, then −ctl·(c − 1).
fn cneg(b: &mut B, v: &[QubitId], ctl: QubitId, p: U256, dirty: &[QubitId]) {
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1u64));
    for &q in v {
        b.cx(ctl, q);
    }
    add_c_low(b, v, c - U256::from(1u64), ctl, dirty, false);
}

/// (z0, z1) = (s0·v, s1·v) ↔ (0, v) with s_k = (−1)^{σ_k}; `to_signed` picks the direction.
fn sign_spread(b: &mut B, z0: &[QubitId], z1: &[QubitId], sigma: [QubitId; 2], p: U256, dirty: &[QubitId], to_signed: bool) {
    let d = b.alloc_qubit();
    b.cx(sigma[0], d);
    b.cx(sigma[1], d);
    if to_signed {
        cneg(b, z1, sigma[1], p, dirty);
        for j in 0..z0.len() {
            b.cx(z1[j], z0[j]);
        }
        cneg(b, z0, d, p, dirty);
    } else {
        cneg(b, z0, d, p, dirty);
        for j in 0..z0.len() {
            b.cx(z1[j], z0[j]);
        }
        cneg(b, z1, sigma[1], p, dirty);
    }
    b.cx(sigma[0], d);
    b.cx(sigma[1], d);
    b.free(d);
}

/// y ← y·x mod p in place (x unchanged; x in [1, p), y in [1, p)).
pub(super) fn mul_inplace(b: &mut B, x: &[QubitId], y: &[QubitId], p: U256) {
    b.set_phase("pp_gcd_fwd");
    let tape = b.prof("gcd_forward", |b| gcd_forward(b, x, p));
    b.set_phase("pp_replay");
    let z0: Vec<QubitId> = x.iter().map(|&q| b.alloc_specific(q)).collect();
    b.prof("replay_mul", |b| {
        sign_spread(b, &z0, y, tape.sigma, p, &tape.e, true);
        let z = [z0.clone(), y.to_vec()];
        for i in (0..PP_ROUNDS).rev() {
            let (si, ti) = roles(i);
            cell_mul(b, &z[ti], &z[si], tape.e[i], p, i < PP_EXACT_ROUNDS);
            if i == 1 {
                round1_fix(b, &z[0], &z[1], tape.e[1], p);
            }
        }
    });
    for &q in &z0 {
        b.free_reserved(q);
    }
    b.set_phase("pp_gcd_bwd");
    b.prof("gcd_backward", |b| gcd_backward(b, x, tape, p));
}

/// y ← y / x mod p in place (x unchanged; x in [1, p), y in [1, p)).
pub(super) fn div_inplace(b: &mut B, x: &[QubitId], y: &[QubitId], p: U256) {
    b.set_phase("pp_gcd_fwd");
    let tape = b.prof("gcd_forward", |b| gcd_forward(b, x, p));
    b.set_phase("pp_replay");
    let z0: Vec<QubitId> = x.iter().map(|&q| b.alloc_specific(q)).collect();
    b.prof("replay_div", |b| {
        let z = [z0.clone(), y.to_vec()];
        for i in 0..PP_ROUNDS {
            let (si, ti) = roles(i);
            if i == 1 {
                round1_fix(b, &z[0], &z[1], tape.e[1], p);
            }
            cell_div(b, &z[ti], &z[si], tape.e[i], p, i < PP_EXACT_ROUNDS);
        }
        sign_spread(b, &z0, y, tape.sigma, p, &tape.e, false);
    });
    for &q in &z0 {
        b.free_reserved(q);
    }
    b.set_phase("pp_gcd_bwd");
    b.prof("gcd_backward", |b| gcd_backward(b, x, tape, p));
}
