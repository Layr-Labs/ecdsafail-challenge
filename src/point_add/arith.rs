//! froghop-double primitives: in-place ripple ladders (Cuccaro majority form with a mid hook), counters, zero tests,
//! controlled rotation and swap networks.
//!
//! Ladder convention: target T (D side) and source S (V side, already aligned), LSB first, equal length, one
//! carry-in ancilla c0 = |0>. `up` complements T and runs the majority ladder, leaving the carry out
//! [S > T] (strictly greater) on S[L-1]. `down(g)` returns to the original lanes and, where g = 1, leaves
//! T - S in T (valid only when S <= T). Both are recordings, so a pass can be played inverted.

use super::builder::{B, G};
use crate::circuit::QubitId;

/// out ^= AND of literals (qubit, negated) using borrowed lanes in any state, which come back unchanged (Barenco et al.
/// 1995, Lemma 7.2): 4 (n - 2) Toffoli and n - 2 borrowed lanes for n >= 3, no allocation.
thread_local! {
    /// R6-ROOM799 R6_MIX: the live-qubit cap under which `and_dirty` may take clean lanes (0: never; set by greedyfrog)
    pub static R6_MIX_CAP: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}
#[track_caller]
pub fn and_dirty(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, dirty: &[QubitId]) {
    let n = lits.len();
    assert!(n >= 1);
    // R6_MIX (exact): r clean lanes (r < n - 2) carry the AND of the first r + 1 literals by a measured-uncompute
    // chain (r Toffoli), and the remaining n - r literals go through the borrowed-lane form: r + 4 (n - r - 2) Toffoli
    // instead of 4 (n - 2). Never inside a recording (its lanes are taken at record time).
    let cap = R6_MIX_CAP.with(|c| c.get());
    if n >= 3 && cap > 0 && !b.recording() {
        let r = (cap.saturating_sub(b.live) as usize).min(n - 2);
        if r >= 1 {
            let anc = b.alloc_n(r);
            and_mixed_on(b, lits, out, &anc, dirty);
            b.free_n(&anc);
            return;
        }
    }
    and_dirty_plain(b, lits, out, dirty)
}
/// R6_MIX (exact): out ^= AND of literals with r = min(clean.len(), n - 2) clean |0> lanes (restored |0>) and
/// borrowed lanes: the clean lanes carry the AND of the first r + 1 literals by a measured-uncompute chain (r Toffoli),
/// the remaining n - r literals go through the borrowed-lane form: r + 4 (n - r - 2) Toffoli (n - 1 when r = n - 2).
#[track_caller]
pub fn and_mixed_on(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, clean: &[QubitId], dirty: &[QubitId]) {
    let n = lits.len();
    let r = clean.len().min(n.saturating_sub(2));
    if r == 0 { return and_dirty_plain(b, lits, out, dirty); }
    if r < n - 2 && r8_cc() { return and_cc(b, lits, Some(out), &clean[..r], dirty); }
    let anc = &clean[..r];
    for &(q, ng) in &lits[..r + 1] { if ng { b.x(q); } }
    b.and_c(lits[0].0, lits[1].0, anc[0]);
    for i in 2..=r { b.and_c(anc[i - 2], lits[i].0, anc[i - 1]); }
    let brk = cfg!(test) && std::env::var("R6_BREAK").map_or(false, |v| v.trim() == "mix");
    let mut rest = if brk { vec![] } else { vec![(anc[r - 1], false)] };
    rest.extend_from_slice(&lits[r + 1..]);
    if rest.len() == 1 { b.cx(rest[0].0, out); if rest[0].1 { b.x(out); } } else { and_dirty_plain(b, &rest, out, dirty); }
    for i in (2..=r).rev() { b.and_u(anc[i - 2], lits[i].0, anc[i - 1]); }
    b.and_u(lits[0].0, lits[1].0, anc[0]);
    for &(q, ng) in &lits[..r + 1] { if ng { b.x(q); } }
}
#[track_caller]
fn and_dirty_plain(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, dirty: &[QubitId]) {
    let n = lits.len();
    if n >= 3 { super::builder::r8idle::note("and", 3 * (n as u64 - 2)); }
    if n >= 3 && std::env::var_os("R6_DBG").is_some() {
        eprintln!("R6AD {} {} {} {} {} {}", std::panic::Location::caller(), super::builder::i5::SECT.with(|c| c.get()), n, 4 * (n - 2), R6_MIX_CAP.with(|c| c.get()).saturating_sub(b.live), if b.recording() { -1 } else { b.cdepth });
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else if n == 2 {
        b.ccx(lits[0].0, lits[1].0, out);
    } else {
        assert!(dirty.len() >= n - 2, "and_dirty: {} literals need {} borrowed lanes, have {}", n, n - 2, dirty.len());
        let c: Vec<QubitId> = lits.iter().map(|l| l.0).collect();
        let a = &dirty[..n - 2];
        for _ in 0..2 {
            b.ccx(c[n - 1], a[n - 3], out);
            for i in (3..n).rev() {
                b.ccx(c[i - 1], a[i - 3], a[i - 2]);
            }
            b.ccx(c[0], c[1], a[0]);
            for i in 3..n {
                b.ccx(c[i - 1], a[i - 3], a[i - 2]);
            }
        }
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// R8-ROOM0 R8_CC switch (callers are already under R6_MIX's cap guard)
pub fn r8_cc() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R8_CC").map_or(false, |v| v.trim() == "1"));
    *E
}
/// R8-ROOM0 R8_CC (exact): out ^= AND(lits) (or, with `out` None, the phase (-1)^AND(lits)) with 1 <= r < n - 2 clean
/// |0> lanes and conditionally clean lanes. The clean chain holds a = AND(c[0..=r]) (r Toffoli, measured uncompute);
/// where a = 1 every c[0..=r] is 1, so after an X each of those r + 1 literal lanes is |0>: they carry a CCX chain
/// L_1 = c[r+1] c[r+2], L_i = L_(i-1) c[r+1+i] (k <= r + 1 lanes, exact where a = 1, garbage elsewhere), and the target
/// takes a & L_k & (the R = n - r - k - 2 literals left) (one CCX / CZ when R = 0, the borrowed-lane form on R + 2
/// literals otherwise: 4R / 4R - 2). The chain is undone by the same CCX (exact on every shot), then the X and the clean
/// chain. Toffoli: r + 2k + (1 | 4R) for the XOR, r + 2k + (0 | 4R - 2) for the phase, against r + 4(n - r - 2) and
/// r + 4(n - r) - 10 for R6_MIX / R8_PHB. The literal lanes are restored; R borrowed lanes.
#[track_caller]
pub fn and_cc(b: &mut B, lits: &[(QubitId, bool)], out: Option<QubitId>, clean: &[QubitId], dirty: &[QubitId]) {
    let n = lits.len();
    let r = clean.len().min(n - 2);
    assert!(r >= 1 && r < n - 2, "and_cc: n {n} r {r}");
    let brk = cfg!(test) && std::env::var("R8_BREAK").map_or(false, |v| v.trim() == "cc");
    for &(q, ng) in lits { if ng { b.x(q); } }
    let c: Vec<QubitId> = lits.iter().map(|l| l.0).collect();
    let anc = &clean[..r];
    b.and_c(c[0], c[1], anc[0]);
    for i in 2..=r { b.and_c(anc[i - 2], c[i], anc[i - 1]); }
    let a = anc[r - 1];
    for i in 0..=r { if !(brk && i == 0) { b.x(c[i]); } }
    let rest = &c[r + 1..];
    let k = (r + 1).min(rest.len() - 1);
    let lanes = &c[..k];
    let mut ch = vec![(rest[0], rest[1], lanes[0])];
    for i in 2..=k { ch.push((lanes[i - 2], rest[i], lanes[i - 1])); }
    for &(x, y, t) in &ch { b.ccx(x, y, t); }
    let mut fl = vec![(a, false), (lanes[k - 1], false)];
    fl.extend(rest[k + 1..].iter().map(|&q| (q, false)));
    if std::env::var_os("R6_DBG").is_some() {
        eprintln!("R8CC {} {} {} {} {}", std::panic::Location::caller(), n, r, fl.len() - 2, if b.recording() { -1 } else { b.cdepth });
    }
    match out {
        Some(o) => if fl.len() == 2 { b.ccx(a, lanes[k - 1], o) } else { and_dirty_plain(b, &fl, o, dirty) },
        None => if fl.len() == 2 { b.cz(a, lanes[k - 1]) } else { phase_dirty(b, &fl, dirty) },
    }
    for &(x, y, t) in ch.iter().rev() { b.ccx(x, y, t); }
    for i in 0..=r { if !(brk && i == 0) { b.x(c[i]); } }
    for i in (2..=r).rev() { b.and_u(anc[i - 2], c[i], anc[i - 1]); }
    b.and_u(c[0], c[1], anc[0]);
    for &(q, ng) in lits { if ng { b.x(q); } }
}

/// R8-ROOM0 R8_PHB (exact): phase (-1)^AND(lits) on borrowed lanes in any state (restored): Barenco's Lemma 7.2 form
/// of `and_dirty_plain` with its two target CCX (out ^= c[n-1] a[n-3]) replaced by CZ(c[n-1], a[n-3]) (conjugate the
/// target by H and fix it at |1>: CCX -> CCZ -> CZ). 4n - 10 Toffoli and n - 2 borrowed lanes for n >= 3, against
/// 8(n - 3) for two (n-1)-literal ANDs into a borrowed lane around a CZ.
#[track_caller]
pub fn phase_dirty(b: &mut B, lits: &[(QubitId, bool)], dirty: &[QubitId]) {
    let n = lits.len();
    assert!(n >= 3 && dirty.len() >= n - 2, "phase_dirty: {} literals, {} borrowed lanes", n, dirty.len());
    if std::env::var_os("R6_DBG").is_some() {
        eprintln!("R8PD {} {} {} {}", std::panic::Location::caller(), n, 4 * n - 10, if b.recording() { -1 } else { b.cdepth });
    }
    let brk = cfg!(test) && std::env::var("R8_BREAK").map_or(false, |v| v.trim() == "phb");
    for &(q, ng) in lits { if ng { b.x(q); } }
    let c: Vec<QubitId> = lits.iter().map(|l| l.0).collect();
    let a = &dirty[..n - 2];
    for pass in 0..2 {
        if !(brk && pass == 1) { b.cz(c[n - 1], a[n - 3]); }
        for i in (3..n).rev() { b.ccx(c[i - 1], a[i - 3], a[i - 2]); }
        b.ccx(c[0], c[1], a[0]);
        for i in 3..n { b.ccx(c[i - 1], a[i - 3], a[i - 2]); }
    }
    for &(q, ng) in lits { if ng { b.x(q); } }
}

/// bits += ctrl (mod 2^n) using borrowed lanes in any state (restored): bit i flips under ctrl & bits[0..i], highest
/// bit first, each through `and_dirty` (n - 2 borrowed lanes at most).
pub fn inc_dirty(b: &mut B, ctrl: QubitId, bits: &[QubitId], dirty: &[QubitId]) {
    for i in (0..bits.len()).rev() {
        let mut lits = vec![(ctrl, false)];
        lits.extend(bits[..i].iter().map(|&q| (q, false)));
        and_dirty(b, &lits, bits[i], dirty);
    }
}

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
