//! Original secp256k1 point-addition circuit (Claude-authored entry).
//!
//! Built from scratch on the neutral `builder` layer. Development is staged
//! and primitive-tested: each reversible field primitive is validated in
//! isolation against the trusted `Simulator` (see `tests/primitives.rs`)
//! before being composed into the full affine point-addition law.
//!
//! Status: foundation + integer arithmetic primitives. `build()` is a stub
//! until the full composition lands.

pub mod builder;

use crate::circuit::{Op, QubitId};
use alloy_primitives::U256;
use builder::B;

/// secp256k1 field prime p = 2^256 - 2^32 - 977.
pub fn secp_p() -> U256 {
    U256::from_str_radix(
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
        16,
    )
    .unwrap()
}

/// Run `f`, then append the exact inverse of everything it emitted.
/// Valid because every gate used here (X/CX/CCX/Swap) is its own inverse, so
/// reversing the emitted gate sequence inverts the circuit. `f` must be clean
/// (balanced alloc/free, no R/Hmr).
pub fn emit_inverse<F: FnOnce(&mut B)>(b: &mut B, f: F) {
    let start = b.ops.len();
    f(b);
    b.ops[start..].reverse();
}

// ---- constant / controlled-constant helpers ------------------------------

/// X the qubits where constant `c` has a 1 bit. Self-inverse (call twice to
/// load then unload a scratch register initialised to |0>).
fn xor_const(b: &mut B, qs: &[QubitId], c: U256) {
    for (i, &q) in qs.iter().enumerate() {
        if c.bit(i) {
            b.x(q);
        }
    }
}

/// `acc = (acc + c) mod 2^len`, constant `c`, via a loaded scratch register.
fn add_const(b: &mut B, acc: &[QubitId], c: U256) {
    let ca = b.alloc_qubits(acc.len());
    xor_const(b, &ca, c);
    let cin = b.alloc_qubit();
    cuccaro_add(b, &ca, acc, cin);
    b.free(cin);
    xor_const(b, &ca, c);
    b.free_all(&ca);
}

/// `acc -= c` (controlled on qubit `ctrl`), constant `c`. Scratch holds
/// `ctrl ? c : 0`, so the subtract is a no-op when ctrl=0.
fn csub_const(b: &mut B, acc: &[QubitId], c: U256, ctrl: QubitId) {
    let ca = b.alloc_qubits(acc.len());
    for (i, &q) in ca.iter().enumerate() {
        if c.bit(i) {
            b.cx(ctrl, q);
        }
    }
    let cin = b.alloc_qubit();
    cuccaro_sub(b, &ca, acc, cin);
    b.free(cin);
    for (i, &q) in ca.iter().enumerate() {
        if c.bit(i) {
            b.cx(ctrl, q);
        }
    }
    b.free_all(&ca);
}

/// `flag ^= (x < y)` as unsigned n-bit integers. `x`, `y` preserved.
/// Borrow chain b_{i+1} = majority(¬x_i, y_i, b_i); borrow-out = (x < y).
pub fn cmp_lt_into(b: &mut B, x: &[QubitId], y: &[QubitId], flag: QubitId) {
    let n = x.len();
    assert_eq!(n, y.len());
    let bor = b.alloc_qubits(n + 1);
    for i in 0..n {
        b.x(x[i]);
        b.ccx(x[i], y[i], bor[i + 1]);
        b.ccx(x[i], bor[i], bor[i + 1]);
        b.ccx(y[i], bor[i], bor[i + 1]);
        b.x(x[i]);
    }
    b.cx(bor[n], flag);
    for i in (0..n).rev() {
        b.x(x[i]);
        b.ccx(y[i], bor[i], bor[i + 1]);
        b.ccx(x[i], bor[i], bor[i + 1]);
        b.ccx(x[i], y[i], bor[i + 1]);
        b.x(x[i]);
    }
    b.free_all(&bor);
}

// ---- modular add / sub mod p ---------------------------------------------

/// `acc = (acc + a) mod p`, in place. Requires `acc, a < p` (n = 256).
/// `a` preserved. Uses the guard-bit + conditional-subtract construction with
/// a comparator-based flag uncompute (general method).
pub fn mod_add_p(b: &mut B, acc: &[QubitId], a: &[QubitId], p: U256) {
    let n = acc.len();
    assert_eq!(n, a.len());
    let c = U256::ZERO.wrapping_sub(p); // 2^256 - p  (small: 2^32 + 977)

    let g_acc = b.alloc_qubit();
    let g_a = b.alloc_qubit();
    let mut acc_ext = acc.to_vec();
    acc_ext.push(g_acc);
    let mut a_ext = a.to_vec();
    a_ext.push(g_a);

    // Step 1: full (n+1)-bit add. acc_ext = acc + a  (< 2p).
    let cin = b.alloc_qubit();
    cuccaro_add(b, &a_ext, &acc_ext, cin);
    b.free(cin);

    // Step 2: add c. Now bit n (g_acc) == (acc + a >= p).
    add_const(b, &acc_ext, c);

    // Step 3: flag := g_acc.
    let flag = b.alloc_qubit();
    b.cx(g_acc, flag);

    // Step 4: if flag==0, undo the +c (restores non-reduced sum).
    b.x(flag);
    csub_const(b, &acc_ext, c, flag);
    b.x(flag);

    // Step 5: if flag==1, drop the 2^n bit (yields acc + a - p).
    b.cx(flag, g_acc);

    // Step 6: uncompute flag == (result < a).
    cmp_lt_into(b, acc, a, flag);
    b.free(flag);

    b.free(g_a);
    b.free(g_acc);
}

/// `acc = (acc - a) mod p`, the inverse of `mod_add_p`.
pub fn mod_sub_p(b: &mut B, acc: &[QubitId], a: &[QubitId], p: U256) {
    let acc_v = acc.to_vec();
    let a_v = a.to_vec();
    emit_inverse(b, move |b| mod_add_p(b, &acc_v, &a_v, p));
}

/// `acc = (2 * acc) mod p`, in place. Requires `acc < p`, p odd (n = 256).
/// Left-shift by 1 (free SWAPs) into a guard bit, then conditionally subtract
/// p. The reduction flag is uncomputed from the result's parity: p is odd, so
/// the result is odd iff a reduction happened.
pub fn mod_double_p(b: &mut B, acc: &[QubitId], p: U256) {
    let n = acc.len();
    let c = U256::ZERO.wrapping_sub(p); // 2^256 - p

    let g = b.alloc_qubit();
    // Shift values up by one position; 0 enters at bit 0, top bit lands in g.
    b.swap(acc[n - 1], g);
    for i in (1..n).rev() {
        b.swap(acc[i], acc[i - 1]);
    }

    let mut ext = acc.to_vec();
    ext.push(g);

    add_const(b, &ext, c); // g := (2*acc >= p)
    let flag = b.alloc_qubit();
    b.cx(g, flag);
    b.x(flag);
    csub_const(b, &ext, c, flag); // if flag==0 undo +c
    b.x(flag);
    b.cx(flag, g); // if flag==1 drop 2^n bit

    // Uncompute flag: reduced <=> result odd (p odd, 2*acc even).
    b.cx(acc[0], flag);
    b.free(flag);
    b.free(g);
}

/// `acc = (acc + x) mod p` controlled on qubit `ctrl`. `x`, `ctrl` preserved.
pub fn cmod_add_p(b: &mut B, acc: &[QubitId], x: &[QubitId], ctrl: QubitId, p: U256) {
    let n = acc.len();
    let sc = b.alloc_qubits(n);
    // sc = ctrl ? x : 0. When x[j] aliases ctrl (e.g. a squaring x==y), the
    // Toffoli would have equal controls (ctrl AND ctrl = ctrl), so emit a CX.
    for j in 0..n {
        if x[j] == ctrl {
            b.cx(ctrl, sc[j]);
        } else {
            b.ccx(ctrl, x[j], sc[j]);
        }
    }
    mod_add_p(b, acc, &sc, p);
    for j in 0..n {
        if x[j] == ctrl {
            b.cx(ctrl, sc[j]);
        } else {
            b.ccx(ctrl, x[j], sc[j]);
        }
    }
    b.free_all(&sc);
}

/// `res = (x * y) mod p`. `res` is a zeroed 256-qubit register; `x`, `y`
/// preserved. Double-and-add from the top bit of `y`.
pub fn modmul_p(b: &mut B, res: &[QubitId], x: &[QubitId], y: &[QubitId], p: U256) {
    let n = res.len();
    for i in (0..n).rev() {
        mod_double_p(b, res, p);
        cmod_add_p(b, res, x, y[i], p);
    }
}

/// Out-of-place ripple-carry adder.
///
/// Computes `s = a + b` where `a`, `b` are `n`-bit little-endian qubit
/// registers (preserved) and `s` is an `n+1`-bit zeroed qubit register that
/// receives the sum (including the final carry in `s[n]`). `carry` is an
/// `n+1`-bit zeroed ancilla register; it is fully uncomputed back to |0> here.
///
/// Toffoli cost: 6n. Used as the verifiable building block for modular
/// arithmetic; a lower-cost in-place adder replaces it in the optimized path.
pub fn add_oop(b: &mut B, a: &[QubitId], binp: &[QubitId], s: &[QubitId], carry: &[QubitId]) {
    let n = a.len();
    assert_eq!(binp.len(), n);
    assert_eq!(s.len(), n + 1);
    assert_eq!(carry.len(), n + 1);

    // Forward: compute carry[i+1] = majority(a[i], b[i], carry[i]) and
    // s[i] = a[i] ^ b[i] ^ carry[i]. carry[0] is a fresh |0>.
    for i in 0..n {
        b.ccx(a[i], binp[i], carry[i + 1]);
        b.ccx(a[i], carry[i], carry[i + 1]);
        b.ccx(binp[i], carry[i], carry[i + 1]);
        b.cx(a[i], s[i]);
        b.cx(binp[i], s[i]);
        b.cx(carry[i], s[i]);
    }
    // Top carry out.
    b.cx(carry[n], s[n]);

    // Uncompute carries (reverse order; a, b, s untouched by this phase).
    for i in (0..n).rev() {
        b.ccx(binp[i], carry[i], carry[i + 1]);
        b.ccx(a[i], carry[i], carry[i + 1]);
        b.ccx(a[i], binp[i], carry[i + 1]);
    }
}

// ---- in-place ripple-carry (Cuccaro MAJ/UMA) -----------------------------
// Standard Cuccaro ripple-carry construction (general method). `acc += a`
// and `acc -= a` modulo 2^n, in place, with a single carry ancilla `c_in`
// that enters and exits at |0>. `a` is preserved. The high carry is
// discarded (pure mod-2^n), which is exactly reversible.

fn maj(b: &mut B, x: QubitId, y: QubitId, w: QubitId) {
    b.cx(w, y);
    b.cx(w, x);
    b.ccx(x, y, w);
}

fn uma(b: &mut B, x: QubitId, y: QubitId, w: QubitId) {
    b.ccx(x, y, w);
    b.cx(w, x);
    b.cx(x, y);
}

fn inv_maj(b: &mut B, x: QubitId, y: QubitId, w: QubitId) {
    b.ccx(x, y, w);
    b.cx(w, x);
    b.cx(w, y);
}

fn inv_uma(b: &mut B, x: QubitId, y: QubitId, w: QubitId) {
    b.cx(x, y);
    b.cx(w, x);
    b.ccx(x, y, w);
}

/// `acc = (acc + a) mod 2^n`, in place. `a` preserved; `c_in` |0>→|0>.
pub fn cuccaro_add(b: &mut B, a: &[QubitId], acc: &[QubitId], c_in: QubitId) {
    let n = a.len();
    assert_eq!(n, acc.len());
    if n == 0 {
        return;
    }
    if n == 1 {
        b.cx(c_in, acc[0]);
        b.cx(a[0], acc[0]);
        return;
    }
    maj(b, c_in, acc[0], a[0]);
    for i in 1..n - 1 {
        maj(b, a[i - 1], acc[i], a[i]);
    }
    b.cx(a[n - 2], acc[n - 1]);
    b.cx(a[n - 1], acc[n - 1]);
    for i in (1..n - 1).rev() {
        uma(b, a[i - 1], acc[i], a[i]);
    }
    uma(b, c_in, acc[0], a[0]);
}

/// `acc = (acc - a) mod 2^n`, the exact inverse gate sequence of `cuccaro_add`.
pub fn cuccaro_sub(b: &mut B, a: &[QubitId], acc: &[QubitId], c_in: QubitId) {
    let n = a.len();
    assert_eq!(n, acc.len());
    if n == 0 {
        return;
    }
    if n == 1 {
        b.cx(a[0], acc[0]);
        b.cx(c_in, acc[0]);
        return;
    }
    inv_uma(b, c_in, acc[0], a[0]);
    for i in 1..n - 1 {
        inv_uma(b, a[i - 1], acc[i], a[i]);
    }
    b.cx(a[n - 1], acc[n - 1]);
    b.cx(a[n - 2], acc[n - 1]);
    for i in (1..n - 1).rev() {
        inv_maj(b, a[i - 1], acc[i], a[i]);
    }
    inv_maj(b, c_in, acc[0], a[0]);
}

// ---- classical modular arithmetic helpers (compile-time) -----------------

/// `base^e mod p` by square-and-multiply.
fn modpow(mut base: U256, mut e: U256, p: U256) -> U256 {
    let mut r = U256::from(1u64);
    base %= p;
    while e > U256::ZERO {
        if e.bit(0) {
            r = r.mul_mod(base, p);
        }
        base = base.mul_mod(base, p);
        e >>= 1;
    }
    r
}

/// Modular inverse of `a` mod prime `p` via Fermat (`a^(p-2)`).
fn modinv(a: U256, p: U256) -> U256 {
    modpow(a, p - U256::from(2u64), p)
}

// ---- modular negate / multiply-accumulate --------------------------------

/// `v = (-v) mod p`, in place. Valid for `v != 0` (generic case): maps
/// `v -> p - v`. Construction: bitwise complement (`v -> 2^n-1-v`) then add
/// `p+1`, whose low-256 result is `p - v` for `v in [1, p)`.
pub fn mod_neg_p(b: &mut B, v: &[QubitId], p: U256) {
    for &q in v {
        b.x(q);
    }
    add_const(b, v, p.wrapping_add(U256::from(1u64)));
}

/// `acc = (acc + x*y) mod p`. `x`, `y` preserved; one scratch product register
/// allocated and uncomputed.
pub fn modmul_acc(b: &mut B, acc: &[QubitId], x: &[QubitId], y: &[QubitId], p: U256) {
    let n = acc.len();
    let tmp = b.alloc_qubits(n);
    modmul_p(b, &tmp, x, y, p);
    mod_add_p(b, acc, &tmp, p);
    let xv = x.to_vec();
    let yv = y.to_vec();
    let tv = tmp.clone();
    emit_inverse(b, move |b| modmul_p(b, &tv, &xv, &yv, p));
    b.free_all(&tmp);
}

/// `acc = (acc - x*y) mod p`. `x`, `y` preserved.
pub fn modmul_sub(b: &mut B, acc: &[QubitId], x: &[QubitId], y: &[QubitId], p: U256) {
    let n = acc.len();
    let tmp = b.alloc_qubits(n);
    modmul_p(b, &tmp, x, y, p);
    mod_sub_p(b, acc, &tmp, p);
    let xv = x.to_vec();
    let yv = y.to_vec();
    let tv = tmp.clone();
    emit_inverse(b, move |b| modmul_p(b, &tv, &xv, &yv, p));
    b.free_all(&tmp);
}

/// `inv = (C * r) mod p`, constant `C`, into a zeroed register `inv`. `r`
/// preserved. Horner double-and-add; the `C` bit tests are classical so no
/// quantum control is spent.
pub fn const_modmul_into(b: &mut B, inv: &[QubitId], r: &[QubitId], c: U256, p: U256) {
    let n = inv.len();
    for i in (0..n).rev() {
        mod_double_p(b, inv, p);
        if c.bit(i) {
            mod_add_p(b, inv, r, p);
        }
    }
}

// ---- Kaliski binary-GCD modular inverse ----------------------------------
// Standard binary almost-inverse (qrisp-style standard form), authored on the
// neutral builder with only self-inverse gates (X/CX/CCX/Swap) so the backward
// (uncompute) pass is the exact gate-reversal of the forward pass.
//
// After `ITERS` iterations on a nonzero input `a`, the coefficient register `r`
// satisfies the loop invariant  r * a ≡ -2^ITERS (mod p), independent of the
// per-input natural iteration count (post-termination steps keep doubling r,
// which is consistent with the invariant). Hence `r = -a^{-1} * 2^ITERS mod p`
// and a single constant multiply by `C = -2^{-ITERS} mod p` recovers `a^{-1}`.

/// Fixed iteration count: for n=256 the binary almost-inverse terminates in
/// k ≤ 2n steps for any nonzero input, so 2n iterations always suffice.
const KAL_ITERS: usize = 512;

/// Net doubling exponent of the r-channel over `KAL_ITERS` iterations:
/// `r * v_in ≡ -2^KAL_SCALE_EXP (mod p)`. With plain (unreduced) `s`
/// accumulation this is exactly `KAL_ITERS` (every iteration doubles r once).
/// The `kaliski_inv_correct_and_clean` test guards this against drift.
const KAL_SCALE_EXP: u64 = KAL_ITERS as u64;

struct KalState {
    u: Vec<QubitId>,
    v: Vec<QubitId>,
    r: Vec<QubitId>,
    s: Vec<QubitId>,
    m: Vec<QubitId>,
    f: QubitId,
}

/// `flag ^= (v == 0)` for the duration of `body`, then uncompute the scratch.
/// Clean OR-reduction chain (self-inverse gates).
fn with_is_zero<F: FnOnce(&mut B)>(b: &mut B, v: &[QubitId], flag: QubitId, body: F) {
    let n = v.len();
    assert!(n >= 2);
    let ch = b.alloc_qubits(n - 1);
    or_into(b, v[0], v[1], ch[0]);
    for i in 1..n - 1 {
        or_into(b, ch[i - 1], v[i + 1], ch[i]);
    }
    // ch[n-2] = (v != 0); flag ^= NOT(ch) = (v == 0)
    b.x(ch[n - 2]);
    b.cx(ch[n - 2], flag);
    b.x(ch[n - 2]);
    body(b);
    // restore flag to its entry value
    b.x(ch[n - 2]);
    b.cx(ch[n - 2], flag);
    b.x(ch[n - 2]);
    for i in (1..n - 1).rev() {
        or_into_inv(b, ch[i - 1], v[i + 1], ch[i]);
    }
    or_into_inv(b, v[0], v[1], ch[0]);
    b.free_all(&ch);
}

/// `out ^= (a OR b)`; assumes `out == 0` so it sets `out = a OR b`.
fn or_into(b: &mut B, a: QubitId, bq: QubitId, out: QubitId) {
    b.x(a);
    b.x(bq);
    b.ccx(a, bq, out); // out ^= (NOT a) AND (NOT b)
    b.x(a);
    b.x(bq);
    b.x(out); // out = NOT((NOT a) AND (NOT b)) = a OR b
}

/// Exact gate-reversal of [`or_into`]; restores `out` to |0>.
fn or_into_inv(b: &mut B, a: QubitId, bq: QubitId, out: QubitId) {
    b.x(out);
    b.x(a);
    b.x(bq);
    b.ccx(a, bq, out);
    b.x(a);
    b.x(bq);
}

/// Controlled swap (Fredkin): swap `x`,`y` iff `ctrl`. 1 Toffoli.
fn cswap(b: &mut B, ctrl: QubitId, x: QubitId, y: QubitId) {
    b.cx(y, x);
    b.ccx(ctrl, x, y);
    b.cx(y, x);
}

/// One Kaliski iteration (standard form). `m_i` is this iteration's history
/// bit (persists until the backward pass); `f` is the running flag. Transforms
/// the persistent (u,v,r,s,m_i,f) state; all iteration-local ancilla return to
/// |0>.
fn kal_iter(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    m_i: QubitId,
    f: QubitId,
    p: U256,
) {
    let n = u.len();
    let a_f = b.alloc_qubit();
    let b_f = b.alloc_qubit();
    let add_f = b.alloc_qubit();

    // STEP 0: m_i ^= f AND (v==0); f ^= m_i.  `add_f` is borrowed as the
    // is-zero flag here and restored to |0> by `with_is_zero` before STEP 4.
    with_is_zero(b, v, add_f, |b| {
        b.ccx(f, add_f, m_i);
    });
    b.cx(m_i, f);

    // STEP 1:
    //   a_f ^= f AND NOT u[0]
    //   m_i ^= f AND u[0] AND NOT v[0]
    //   b_f  = a_f XOR m_i
    b.x(u[0]);
    b.ccx(f, u[0], a_f); // a_f = f AND NOT u0
    b.x(u[0]);
    b.x(v[0]);
    // m_i ^= f AND u0 AND NOT v0, via a fresh ancilla z = f AND u0
    {
        let z = b.alloc_qubit();
        b.ccx(f, u[0], z);
        b.ccx(z, v[0], m_i);
        b.ccx(f, u[0], z); // uncompute z
        b.free(z);
    }
    b.x(v[0]);
    b.cx(a_f, b_f);
    b.cx(m_i, b_f); // b_f = a_f XOR m_i

    // STEP 2: l = (u > v); a_f ^= f AND l AND NOT b_f; m_i ^= same.
    {
        let l_gt = b.alloc_qubit();
        cmp_lt_into(b, v, u, l_gt); // l_gt = (v < u) = (u > v)
        let t = b.alloc_qubit();
        b.x(b_f);
        b.ccx(f, l_gt, t); // t = f AND l_gt (b_f already negated below)
        let t2 = b.alloc_qubit();
        b.ccx(t, b_f, t2); // t2 = f AND l_gt AND NOT b_f_orig
        b.cx(t2, a_f);
        b.cx(t2, m_i);
        b.ccx(t, b_f, t2); // uncompute t2
        b.free(t2);
        b.ccx(f, l_gt, t); // uncompute t
        b.free(t);
        b.x(b_f);
        cmp_lt_into(b, v, u, l_gt); // uncompute l_gt
        b.free(l_gt);
    }

    // STEP 3: controlled on a_f: swap(u,v); swap(r,s).
    for j in 0..n {
        cswap(b, a_f, u[j], v[j]);
    }
    for j in 0..n {
        cswap(b, a_f, r[j], s[j]);
    }

    // STEP 4: add_f ^= f AND NOT b_f; controlled on add_f: v -= u; s += r.
    b.x(b_f);
    b.ccx(f, b_f, add_f); // add_f = f AND NOT b_f_orig
    b.x(b_f);
    {
        // v -= (add_f ? u : 0)  (mod 2^n; in-branch v >= u so exact)
        let tmp = b.alloc_qubits(n);
        for i in 0..n {
            b.ccx(add_f, u[i], tmp[i]);
        }
        let cin = b.alloc_qubit();
        cuccaro_sub(b, &tmp, v, cin);
        b.free(cin);
        for i in 0..n {
            b.ccx(add_f, u[i], tmp[i]);
        }
        b.free_all(&tmp);
    }
    {
        // s += (add_f ? r : 0), PLAIN add mod 2^n (not reduced mod p): the
        // standard-form parity invariant s[0] = NOT a_f (used to uncompute a_f
        // in STEP 10) requires plain accumulation.
        let tmp = b.alloc_qubits(n);
        for i in 0..n {
            b.ccx(add_f, r[i], tmp[i]);
        }
        let cin = b.alloc_qubit();
        cuccaro_add(b, &tmp, s, cin);
        b.free(cin);
        for i in 0..n {
            b.ccx(add_f, r[i], tmp[i]);
        }
        b.free_all(&tmp);
    }

    // STEP 5: uncompute add_f; uncompute b_f.
    b.x(b_f);
    b.ccx(f, b_f, add_f);
    b.x(b_f);
    b.cx(m_i, b_f);
    b.cx(a_f, b_f); // b_f = 0

    // STEP 6: v := v >> 1 (v[0] guaranteed 0 here). Rotate-up chain.
    for i in 0..n - 1 {
        b.swap(v[i], v[i + 1]);
    }

    // STEP 7/8: r := 2r mod p.
    mod_double_p(b, r, p);

    // STEP 9: controlled on a_f: swap(u,v); swap(r,s) again.
    for j in 0..n {
        cswap(b, a_f, u[j], v[j]);
    }
    for j in 0..n {
        cswap(b, a_f, r[j], s[j]);
    }

    // STEP 10: uncompute a_f via invariant a_f == NOT s[0].
    b.x(s[0]);
    b.cx(s[0], a_f);
    b.x(s[0]);

    b.free(add_f);
    b.free(b_f);
    b.free(a_f);
}

/// Forward Kaliski: init state and run `KAL_ITERS` iterations. Leaves
/// `st.r = -v_in^{-1} * 2^KAL_ITERS mod p`; all other state dirty (cleaned by
/// the backward pass). `v_in` preserved.
fn kaliski_forward(b: &mut B, st: &KalState, v_in: &[QubitId], p: U256) {
    let n = v_in.len();
    xor_const(b, &st.u, p); // u = p
    for i in 0..n {
        b.cx(v_in[i], st.v[i]); // v = v_in
    }
    b.x(st.s[0]); // s = 1
    b.x(st.f); // f = 1
    for i in 0..KAL_ITERS {
        kal_iter(b, &st.u, &st.v, &st.r, &st.s, st.m[i], st.f, p);
    }
}

/// DEBUG: copy the raw post-forward `r` coefficient into `out` (zeroed), then
/// uncompute. Used to characterize the Kaliski standard-form scale factor.
pub fn kaliski_raw_r(b: &mut B, v_in: &[QubitId], out: &[QubitId], p: U256) {
    let n = v_in.len();
    let st = KalState {
        u: b.alloc_qubits(n),
        v: b.alloc_qubits(n),
        r: b.alloc_qubits(n),
        s: b.alloc_qubits(n),
        m: b.alloc_qubits(KAL_ITERS),
        f: b.alloc_qubit(),
    };
    kaliski_forward(b, &st, v_in, p);
    for i in 0..n {
        b.cx(st.r[i], out[i]);
    }
    emit_inverse(b, |b| kaliski_forward(b, &st, v_in, p));
    b.free(st.f);
    b.free_all(&st.m);
    b.free_all(&st.s);
    b.free_all(&st.r);
    b.free_all(&st.v);
    b.free_all(&st.u);
}

/// DEBUG: run only the forward pass; return all persistent-state qubit ids so
/// a test can verify every *other* (local scratch) qubit ended at |0>.
pub fn kaliski_forward_only(b: &mut B, v_in: &[QubitId], p: U256) -> Vec<QubitId> {
    let n = v_in.len();
    let st = KalState {
        u: b.alloc_qubits(n),
        v: b.alloc_qubits(n),
        r: b.alloc_qubits(n),
        s: b.alloc_qubits(n),
        m: b.alloc_qubits(KAL_ITERS),
        f: b.alloc_qubit(),
    };
    kaliski_forward(b, &st, v_in, p);
    let mut ids = Vec::new();
    ids.extend_from_slice(&st.u);
    ids.extend_from_slice(&st.v);
    ids.extend_from_slice(&st.r);
    ids.extend_from_slice(&st.s);
    ids.extend_from_slice(&st.m);
    ids.push(st.f);
    ids
}

/// `out ^= v_in^{-1} mod p` (out zeroed), v_in preserved, all scratch clean.
/// Closure-free reference form.
pub fn kaliski_inv_into(b: &mut B, v_in: &[QubitId], out: &[QubitId], p: U256) {
    let n = v_in.len();
    let st = KalState {
        u: b.alloc_qubits(n),
        v: b.alloc_qubits(n),
        r: b.alloc_qubits(n),
        s: b.alloc_qubits(n),
        m: b.alloc_qubits(KAL_ITERS),
        f: b.alloc_qubit(),
    };
    kaliski_forward(b, &st, v_in, p);
    let alpha = (p - modpow(U256::from(2u64), U256::from(KAL_SCALE_EXP), p)) % p;
    let c = modinv(alpha, p);
    const_modmul_into(b, out, &st.r, c, p);
    emit_inverse(b, |b| kaliski_forward(b, &st, v_in, p));
    b.free(st.f);
    b.free_all(&st.m);
    b.free_all(&st.s);
    b.free_all(&st.r);
    b.free_all(&st.v);
    b.free_all(&st.u);
}

/// Run `body` with a transient register holding `v_in^{-1} mod p`. `v_in`
/// preserved; all scratch (including the inverse) returns to |0> afterwards.
pub fn with_inv<F: FnOnce(&mut B, &[QubitId])>(b: &mut B, v_in: &[QubitId], p: U256, body: F) {
    let n = v_in.len();
    let st = KalState {
        u: b.alloc_qubits(n),
        v: b.alloc_qubits(n),
        r: b.alloc_qubits(n),
        s: b.alloc_qubits(n),
        m: b.alloc_qubits(KAL_ITERS),
        f: b.alloc_qubit(),
    };

    kaliski_forward(b, &st, v_in, p);

    // After KAL_ITERS=512 iterations the standard-form coefficient satisfies
    // r * v_in ≡ α (mod p) with the fixed, input-independent scale
    // α = -2^384 mod p (measured; net r-channel doublings over the run). So
    // C = α^{-1} recovers inv = C * r = v_in^{-1}.
    let alpha = (p - modpow(U256::from(2u64), U256::from(KAL_SCALE_EXP), p)) % p;
    let c = modinv(alpha, p);

    let inv = b.alloc_qubits(n);
    const_modmul_into(b, &inv, &st.r, c, p);

    body(b, &inv);

    let invv = inv.clone();
    let rv = st.r.clone();
    emit_inverse(b, move |b| const_modmul_into(b, &invv, &rv, c, p));
    b.free_all(&inv);

    emit_inverse(b, |b| kaliski_forward(b, &st, v_in, p));

    b.free(st.f);
    b.free_all(&st.m);
    b.free_all(&st.s);
    b.free_all(&st.r);
    b.free_all(&st.v);
    b.free_all(&st.u);
}

// ---- affine point addition -----------------------------------------------

/// In-place affine point addition: `(px, py) += (qx, qy)` on the curve, all
/// registers quantum (n=256), `qx, qy` preserved. On return `px, py` hold the
/// sum `R`. Generic case only (distinct x, neither point at infinity).
pub fn point_add_affine(
    b: &mut B,
    px: &[QubitId],
    py: &[QubitId],
    qx: &[QubitId],
    qy: &[QubitId],
    p: U256,
) {
    let n = px.len();

    // Phase 1: px = dx, py = dy, then lam = dy * dx^{-1} = λ.
    mod_sub_p(b, px, qx, p);
    mod_sub_p(b, py, qy, p);
    let lam = b.alloc_qubits(n);
    {
        let pyv = py.to_vec();
        let lamv = lam.clone();
        with_inv(b, px, p, move |b, inv| {
            modmul_acc(b, &lamv, &pyv, inv, p);
        });
    }

    // Phase 2: py = dy - λ*dx = 0.
    modmul_sub(b, py, &lam, px, p);

    // Phase 3: px = λ² - dx - 2·qx = Rx.
    mod_neg_p(b, px, p); // px = -dx (dx != 0)
    modmul_acc(b, px, &lam, &lam, p); // px = λ² - dx
    mod_sub_p(b, px, qx, p);
    mod_sub_p(b, px, qx, p);

    // Phase 4: py = λ(qx - Rx) - qy = Ry  (py currently 0).
    modmul_acc(b, py, &lam, qx, p);
    modmul_sub(b, py, &lam, px, p);
    mod_sub_p(b, py, qy, p);

    // Phase 5: zero lam using λ = (Ry + Qy)/(Qx - Rx).
    let denom = b.alloc_qubits(n);
    mod_add_p(b, &denom, qx, p);
    mod_sub_p(b, &denom, px, p); // denom = qx - Rx
    {
        let pyv = py.to_vec();
        let qyv = qy.to_vec();
        let lamv = lam.clone();
        with_inv(b, &denom, p, move |b, inv| {
            modmul_sub(b, &lamv, &pyv, inv, p);
            modmul_sub(b, &lamv, &qyv, inv, p);
        });
    }
    mod_add_p(b, &denom, px, p);
    mod_sub_p(b, &denom, qx, p); // denom = 0
    b.free_all(&denom);
    b.free_all(&lam); // lam = 0
}

/// Entry point called by the trusted `build_circuit` binary. Declares the four
/// contract registers (target_x, target_y qubit; offset_x, offset_y classical
/// bits), loads the classical offset into quantum scratch for free, runs the
/// affine addition in place, then uncomputes the scratch.
pub fn build() -> Vec<Op> {
    let mut b = B::new();
    let n = 256;
    let p = secp_p();
    let tx = b.alloc_qubits(n);
    let ty = b.alloc_qubits(n);
    let ox = b.alloc_bits(n);
    let oy = b.alloc_bits(n);
    b.declare_qubit_register(&tx);
    b.declare_qubit_register(&ty);
    b.declare_bit_register(&ox);
    b.declare_bit_register(&oy);

    // Load classical offset (Qx, Qy) into quantum scratch; X conditioned on a
    // classical bit is free (not charged as Toffoli).
    let qx = b.alloc_qubits(n);
    let qy = b.alloc_qubits(n);
    for i in 0..n {
        b.x_if(qx[i], ox[i]);
    }
    for i in 0..n {
        b.x_if(qy[i], oy[i]);
    }

    point_add_affine(&mut b, &tx, &ty, &qx, &qy, p);

    // Uncompute the offset load (qx, qy preserved by the law → back to |0>).
    for i in 0..n {
        b.x_if(qy[i], oy[i]);
    }
    for i in 0..n {
        b.x_if(qx[i], ox[i]);
    }
    b.free_all(&qy);
    b.free_all(&qx);
    b.ops
}
