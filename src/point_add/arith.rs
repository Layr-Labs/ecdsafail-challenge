//! froghop-double primitives: in-place ripple ladders (Cuccaro majority form with a mid hook), counters, zero tests,
//! controlled rotation and swap networks.
//!
//! Ladder convention: target T (D side) and source S (V side, already aligned), LSB first, equal length, one
//! carry-in ancilla c0 = |0>. `up` complements T and runs the majority ladder, leaving the carry out
//! [S > T] (strictly greater) on S[L-1]. `down(g)` returns to the original lanes and, where g = 1, leaves
//! T - S in T (valid only when S <= T). Both are recordings, so a pass can be played inverted.

use super::builder::{B, G};
use crate::circuit::QubitId;

/// Majority ladder over complemented T. After it, S[L-1] holds [S > T].
pub fn up(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId) -> Vec<G> {
    up_m(b, t, s, c0, true)
}

/// Majority ladder; with `cmpl` T is complemented first (subtract/compare form), otherwise it is the add form
/// and S[L-1] ends holding the carry out of T + S.
pub fn up_m(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, cmpl: bool) -> Vec<G> {
    assert_eq!(t.len(), s.len());
    let l = t.len();
    b.begin();
    if cmpl {
        for &q in t {
            b.x(q);
        }
    }
    for i in 0..l {
        let x = if i == 0 { c0 } else { s[i - 1] };
        // MAJ(x = carry_i, y = T_i, z = S_i)
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    b.end()
}

/// Return pass. With `g = Some(q)`, T becomes T - S where q = 1 (requires S <= T there) and stays T elsewhere;
/// with `None` it is the exact inverse of `up`. 2 Toffoli per lane (+1 per lane when conditional).
pub fn down(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, g: Option<QubitId>) -> Vec<G> {
    down_m(b, t, s, c0, if let Some(q) = g { Dm::Cond(q) } else { Dm::Restore }, true)
}

#[derive(Clone, Copy)]
pub enum Dm {
    /// exact inverse of the up pass
    Restore,
    /// write the sum (T + S in add form, T - S in subtract form)
    Sum,
    /// write the sum where q = 1, restore elsewhere
    Cond(QubitId),
}

pub fn down_m(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, mode: Dm, cmpl: bool) -> Vec<G> {
    let l = t.len();
    b.begin();
    if let Dm::Sum = mode {
        for i in (0..l).rev() {
            let x = if i == 0 { c0 } else { s[i - 1] };
            b.ccx(x, t[i], s[i]);
            b.cx(s[i], x);
            b.cx(x, t[i]); // UMA: sum bit
        }
        if cmpl {
            for &q in t {
                b.x(q);
            }
        }
        return b.end();
    }
    let g = if let Dm::Cond(q) = mode { Some(q) } else { None };
    for i in (0..l).rev() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]); // z = S_i restored
        b.cx(s[i], x); // x = carry_i
        b.cx(s[i], t[i]); // y = T_i (complemented T)
        if let Some(gq) = g {
            b.cx(s[i], x); // x = carry_i ^ S_i
            b.ccx(gq, x, t[i]); // y ^= g (S_i ^ carry_i)  -> sum bit of ~T + S
            b.cx(s[i], x);
        }
    }
    if cmpl {
        for &q in t {
            b.x(q);
        }
    }
    b.end()
}

/// Controlled increment of a little-endian counter (n-1 Toffoli, n-1 transient ancillas from the pool).
pub fn inc(b: &mut B, ctrl: QubitId, bits: &[QubitId], anc: &[QubitId]) {
    let n = bits.len();
    if n == 0 {
        return;
    }
    // carries c[i] = ctrl & b0 & ... & b_{i-1}, i = 1..n-1, held in anc[i-1]
    let mut prev = ctrl;
    for i in 1..n {
        b.and_c(prev, bits[i - 1], anc[i - 1]);
        prev = anc[i - 1];
    }
    for i in (1..n).rev() {
        b.cx(anc[i - 1], bits[i]);
        let p = if i == 1 { ctrl } else { anc[i - 2] };
        b.and_u(p, bits[i - 1], anc[i - 1]);
    }
    b.cx(ctrl, bits[0]);
}

/// Controlled decrement (complement, increment, complement).
pub fn dec(b: &mut B, ctrl: QubitId, bits: &[QubitId], anc: &[QubitId]) {
    for &q in bits {
        b.x(q);
    }
    inc(b, ctrl, bits, anc);
    for &q in bits {
        b.x(q);
    }
}

/// AND of literals (qubit, negated?) into `out` (|0>), using `anc` (len >= n-2) for the chain.
/// Returns the recording so it can be uncomputed by playing it inverted (all ANDs measurement-uncomputed).
pub fn and_lits(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, anc: &[QubitId]) -> Vec<G> {
    let n = lits.len();
    assert!(n >= 2 && anc.len() >= n - 2);
    b.begin();
    for &(q, neg) in lits {
        if neg {
            b.x(q);
        }
    }
    let mut acc = lits[0].0;
    for i in 1..n {
        let tgt = if i == n - 1 { out } else { anc[i - 1] };
        b.and_c(acc, lits[i].0, tgt);
        acc = tgt;
    }
    for &(q, neg) in lits {
        if neg {
            b.x(q);
        }
    }
    b.end()
}

/// Cyclic rotation of `t` as three controlled reflections (1.5n - 2 Fredkins for even n):
/// content moves UP by e = k1 + 2 k2 (lane i ends holding what lane i - e held).
pub fn rot4_up(b: &mut B, k1: QubitId, k2: QubitId, t: &[QubitId]) {
    let n = t.len() as isize;
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..n)
            .filter_map(|i| {
                let j = (x - i).rem_euclid(n);
                (i < j).then_some((i as usize, j as usize))
            })
            .collect()
    };
    // out[i] = in[i + e] composed of rho_1 (k1), rho_0 (k1 ^ k2), rho_-2 (k2) moves content DOWN by e;
    // to move UP we apply the same network to the reversed lane order.
    let tr: Vec<QubitId> = t.iter().rev().copied().collect();
    for (x, kind) in [(1isize, 1u8), (0, 2), (-2, 3)] {
        let ctrl = if kind == 1 { k1 } else { k2 };
        if kind == 2 {
            b.cx(k1, k2);
        }
        for (i, j) in refl(x) {
            b.cswap(ctrl, tr[i], tr[j]);
        }
        if kind == 2 {
            b.cx(k1, k2);
        }
    }
}

/// Controlled cyclic rotation of `t` with content moving UP by 2 (lane i ends holding lane i - 2):
/// n - gcd(n, 2) Fredkins.
pub fn rot2_up(b: &mut B, c: QubitId, t: &[QubitId]) {
    let n = t.len();
    let g = if n % 2 == 0 { 2 } else { 1 };
    for start in 0..g {
        let cyc: Vec<usize> = (0..n / g).map(|k| (start + 2 * k) % n).collect();
        for k in (1..cyc.len()).rev() {
            b.cswap(c, t[cyc[k]], t[cyc[k - 1]]);
        }
    }
}

/// Controlled swap of two equal registers (n Fredkins).
pub fn cswap_regs(b: &mut B, c: QubitId, a: &[QubitId], d: &[QubitId]) {
    for (&x, &y) in a.iter().zip(d) {
        b.cswap(c, x, y);
    }
}

/// Controlled shift of a stack register by one position. up: s[i] -> s[i+1] (top s[n-1] must be 0);
/// down: s[i+1] -> s[i] (s[0] must be 0).
pub fn cshift(b: &mut B, c: QubitId, s: &[QubitId], up_dir: bool) {
    let n = s.len();
    if up_dir {
        for i in (0..n - 1).rev() {
            b.cswap(c, s[i], s[i + 1]);
        }
    } else {
        for i in 0..n - 1 {
            b.cswap(c, s[i], s[i + 1]);
        }
    }
}
