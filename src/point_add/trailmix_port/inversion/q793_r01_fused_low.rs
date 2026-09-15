//! Exact fused restoring R01 with three virtual low residual bits.
//! Own Q793 integration component; not a packed-cargo adapter or whole-Q claim.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use super::length_recompute::mixed_mcx;

pub(super) fn residual(code: usize) -> usize {
    let (t, b, v, q) = (code & 7, code >> 3 & 7, code >> 6 & 7, code >> 9 & 7);
    if t & 1 != 0 {
        (7usize.wrapping_sub(b * v).wrapping_mul(t).wrapping_sub(q * v)) & 7
    } else { b }
}
pub(super) fn valid(code: usize) -> bool { code & 1 != 0 || code & 64 != 0 }

fn seed_terms(shift: usize) -> &'static Vec<usize> {
    static TERMS: std::sync::OnceLock<[Vec<usize>; 3]> = std::sync::OnceLock::new();
    &TERMS.get_or_init(|| std::array::from_fn(|s| {
        let mut anf: Vec<bool> = (0..4096).map(|c| residual(c) < (((c >> 6 & 7) << s) & 7)).collect();
        for bit in 0..12 { for mask in 0..4096 {
            if mask >> bit & 1 != 0 { anf[mask] ^= anf[mask ^ (1 << bit)]; }
        }}
        let terms: Vec<_> = anf.into_iter().enumerate().filter_map(|(m, b)| b.then_some(m)).collect();
        // All 4096 codes, including the declared even-t invalid extension.
        for c in 0..4096 {
            let actual = terms.iter().filter(|&&m| c & m == m).count() & 1 != 0;
            assert_eq!(actual, residual(c) < (((c >> 6 & 7) << s) & 7));
        }
        terms
    }))[shift]
}

/// XOR the exact low-three-bit borrow into arbitrary HA. No controls changed.
pub(super) fn seed(circ: &mut Circuit, word: [&QReg; 12], ha: &QReg, dirty: &[QReg], shift: usize) {
    if shift >= 3 { return; }
    for &m in seed_terms(shift) {
        let controls: Vec<_> = (0..12).filter(|&i| m >> i & 1 != 0).map(|i| (word[i], true)).collect();
        mixed_mcx(circ, &controls, ha, dirty);
    }
}

fn maj(circ: &mut Circuit, source: &QReg, target: &QReg, ha: &QReg, inverse: bool) {
    if inverse { circ.ccx(target, source, ha); circ.cx(ha, source); circ.cx(source, target); }
    else { circ.cx(source, target); circ.cx(ha, source); circ.ccx(target, source, ha); }
}

/// Update b=r in the even-t chart and qpre after the old low seed was erased.
/// All terms use INPUT lower b/q bits, hence the high-before-low ordering.
pub(super) fn low_update(circ: &mut Circuit, word: [&QReg; 12], decision: &QReg, g: &QReg,
                        dirty: &[QReg], shift: usize) {
    if shift >= 3 { return; }
    let mut change_b = |target: usize, factors: &[(&QReg, bool)]| {
        let mut cs = vec![(g, true), (decision, true), (word[0], false)];
        cs.extend_from_slice(factors);
        mixed_mcx(circ, &cs, word[3 + target], dirty);
    };
    if shift == 0 {
        // borrow2 = x1*!b1 XOR x0*!b0*!b1 XOR x0*!b0*x1.
        change_b(2, &[(word[8], true)]);
        change_b(2, &[(word[7], true), (word[4], false)]);
        change_b(2, &[(word[6], true), (word[3], false), (word[4], false)]);
        change_b(2, &[(word[6], true), (word[3], false), (word[7], true)]);
        change_b(1, &[(word[7], true)]);
        change_b(1, &[(word[6], true), (word[3], false)]);
        change_b(0, &[(word[6], true)]);
    } else if shift == 1 {
        change_b(2, &[(word[7], true)]);
        change_b(2, &[(word[6], true), (word[4], false)]);
        change_b(1, &[(word[6], true)]);
    } else { change_b(2, &[(word[6], true)]); }
    // Increment the actual semantic qpre residue, not a guessed packed prefix.
    for bit in (shift..3).rev() {
        let mut cs = vec![(g, true), (decision, true)];
        cs.extend((shift..bit).map(|i| (word[9 + i], true)));
        mixed_mcx(circ, &cs, word[9 + bit], dirty);
    }
}

/// word=[t0,t1,t2,b0,b1,b2,v0,v1,v2,qpre0,qpre1,qpre2].
/// source is an n-bit X=v*2^shift, with implicit zero bit n; target_high is
/// y[3..n]. Low source bits must equal (v*2^shift) mod8. n>=3, so the no-high
/// n=3 endpoint is also exact. Widths1/2 require a different overflow chart.
///
/// Word v_i may alias source[shift+i], only when that position is in range.
/// All remaining physical IDs are pairwise distinct, including dirty lenders.
/// On g1 HA=0 and decision=h: decision becomes h XOR [y>=X] and y becomes
/// y-decision*X modulo2^n. On g0 the complete map is identity for arbitrary
/// HA,h and work data, even for invalid chart codes. Source/lenders restore.
pub(super) fn emit(circ: &mut Circuit, word: [&QReg; 12], source: &[QReg], target_high: &[QReg],
                   decision: &QReg, g: &QReg, ha: &QReg, dirty: &[QReg], shift: usize) {
    let n = source.len();
    assert!(n >= 3 && target_high.len() == n-3);
    assert!(dirty.len() >= 6, "wide exact seed needs six existing dirty lenders");
    let mut unique: Vec<_> = source.iter().chain(target_high).chain(dirty).map(QReg::id).collect();
    unique.extend([decision.id(), g.id(), ha.id()]);
    for (i, q) in word.iter().enumerate() {
        if (6..9).contains(&i) {
            if let Some(at) = source.iter().position(|s| s.id() == q.id()) {
                assert_eq!(at, shift+i-6, "v/source alias at wrong shifted bit");
                continue;
            }
        }
        unique.push(q.id());
    }
    unique.sort_unstable();
    assert!(unique.windows(2).all(|x| x[0] != x[1]), "Q793 R01 alias contract");
    let before = (circ.b.next_qubit, circ.b.active_qubits);
    let at = circ.b.ops.len();
    seed(circ, word, ha, dirty, shift);
    let unseed = circ.b.ops[at..].to_vec();
    for bit in 3..n { maj(circ, &source[bit], &target_high[bit-3], ha, false); }
    circ.cx(g, decision);
    circ.ccx(g, ha, decision);
    for bit in (3..n).rev() {
        maj(circ, &source[bit], &target_high[bit-3], ha, true);
        circ.cx(ha, &source[bit]);
        mixed_mcx(circ, &[(g, true), (decision, true), (&source[bit], true)], &target_high[bit-3], dirty);
        circ.cx(ha, &source[bit]);
    }
    // Source v and the low input chart are restored before exact HA unseeding.
    circ.b.ops.extend(unseed.into_iter().rev());
    low_update(circ, word, decision, g, dirty, shift);
    assert_eq!((circ.b.next_qubit, circ.b.active_qubits), before, "Q793 R01 allocated a rail");
}

#[path="q793_r01_fused_low_check.rs"] mod check;
pub fn run() { check::run(); }
