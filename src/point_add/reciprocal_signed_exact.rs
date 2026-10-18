//! Exact signed half-remainder kernel ported from signed-noflag-v4.
//! Private to midg; this overlay has no fresh compile or correctness result.
use super::super::builder::B;
use crate::circuit::QubitId;

/// Signed half-remainder step without a separate flag. `h` is the logical
/// register AFTER a cyclic left shift: h[0] holds the old sign. Its write is
/// delayed until the middle/top addition has finished, so it serves as the
/// complement of the old sign throughout that addition. The source has a
/// virtual leading one and virtual top zero. All physical source bits return.
/// For every k-bit input H, output is 2H-A if H>=0, else 2H+A+1, modulo2^k,
/// where A=2^(k-2)+slow. The active recurrence also stays in the signed range.
pub(crate) fn signed_step_vh1(b: &mut B, h: &[QubitId], slow: &[QubitId]) {
    let k = h.len();
    assert!(k >= 4 && slow.len() + 2 == k);
    assert!(!slow.iter().any(|q| h.contains(q)));
    let f = h[0];
    b.x(f);
    for &a in slow { b.cx(f, a); }
    let up = super::super::arith::up_m(b, &h[1..k - 2], &slow[1..], slow[0], false);
    let down = super::super::arith::down_m(b, &h[1..k - 2], &slow[1..], slow[0], super::super::arith::Dm::Sum, false);
    b.play(&up, false);
    let (u, x, z) = (slow[k - 3], h[k - 2], h[k - 1]);
    b.cx(f, x); b.cx(f, u); b.ccx(x, u, z);
    b.cx(f, u); b.cx(f, x); b.cx(x, z); b.cx(u, z);
    b.cx(f, x); b.cx(u, x); b.x(x);
    b.play(&down, false);
    for &a in slow { b.cx(f, a); }
    // Complete the deferred bit-zero sum after its old sign has finished
    // controlling all operations: new_H0 = old_sign XOR original_A0.
    b.x(f);
    b.cx(slow[0], f);
}

