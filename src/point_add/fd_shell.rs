//! FD pane: signed-digit Horner rounds (zuiris's ZFOR idea on frogdrop's lazy Ms arithmetic).
//!
//! A round z = 2z + a (bit 1) or 2z - a (bit 0) makes the add uncontrolled: the bit lane complements z around one
//! plain lazy modular add (z - a = ~(~z + a)). With m signed rounds after a seed value S a, one plain round first
//! gives (2S + 1) a, the rounds give 2 (S 2^m + L) a + a, then subtract a and halve: (S 2^m + L) a.
use super::builder::B;
use super::modp_frogdrop::{add_small, mod_double, mod_halve, Ms, C, CMPT};
use crate::circuit::QubitId;

/// t += a mod 2^n (TTK ripple, a restored), k ^= carry_out. 2n - 1 Toffoli.
fn ttk_add_unc(b: &mut B, a: &[QubitId], t: &[QubitId], k: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    for i in 1..n { b.cx(a[i], t[i]); }
    b.cx(a[n - 1], k);
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    b.ccx(t[n - 1], a[n - 1], k);
    for i in (1..n).rev() { b.cx(a[i], t[i]); b.ccx(t[i - 1], a[i - 1], a[i]); }
    for i in 1..n - 1 { b.cx(a[i], a[i + 1]); }
    b.cx(a[0], t[0]);
    for i in 1..n { b.cx(a[i], t[i]); }
}

/// k ^= carry_out(t + a), t and a restored. 2n - 1 Toffoli.
fn ttk_carry_unc(b: &mut B, a: &[QubitId], t: &[QubitId], k: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    b.begin();
    for i in 1..n { b.cx(a[i], t[i]); }
    let s1 = b.end();
    b.play(&s1, false);
    b.cx(a[n - 1], k);
    b.begin();
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    let s23 = b.end();
    b.play(&s23, false);
    b.ccx(t[n - 1], a[n - 1], k);
    b.play(&s23, true);
    b.play(&s1, true);
}

/// z += y mod p, lazy (as modp_frogdrop::ctrl_modadd with the control removed); y 256 lanes, restored.
pub fn modadd_unc(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    assert!(z.len() == 256 && y.len() == 256);
    ttk_add_unc(b, y, z, ms.k);
    add_small(b, ms, z, 0, Some(ms.k), C, y);
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    for &q in zt { b.x(q); }
    ttk_carry_unc(b, yt, zt, ms.k);
    for &q in zt { b.x(q); }
}

/// z += a mod p, lazy, for a 255-lane a (as pointadd_frogdrop::ctrl_modadd255 with the control removed);
/// `d` borrowed (outside z, a, k).
pub fn modadd255_unc(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], d: QubitId) {
    assert!(z.len() == 256 && a.len() == 255);
    let k = ms.k;
    ttk_add_unc(b, a, &z[..255], k);
    b.cx(k, z[255]);
    let at = &a[255 - CMPT..255];
    let rt = &z[255 - CMPT..255];
    let lt = |b: &mut B| {
        // k ^= z[255] & [rt < at] = z255 & carry(~rt + at)
        for &q in rt { b.x(q); }
        super::arith::ttk_carry(b, at, rt, z[255], k, d);
        for &q in rt { b.x(q); }
    };
    lt(b);
    add_small(b, ms, z, 0, Some(k), C, a);
    b.x(z[255]);
    lt(b);
    b.x(z[255]);
}

fn plain_add(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], d: QubitId) {
    if a.len() == 256 { modadd_unc(b, ms, z, a) } else { modadd255_unc(b, ms, z, a, d) }
}

/// z = 2z + a (bit 1) or 2z - a (bit 0); `bit` restored; `d` borrowed (outside z, a, bit, k).
pub fn sround(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], bit: QubitId, d: QubitId) {
    mod_double(b, ms, z, a);
    b.x(bit);
    for &q in z.iter() { b.cx(bit, q); }
    plain_add(b, ms, z, a, d);
    for &q in z.iter() { b.cx(bit, q); }
    b.x(bit);
}

/// Before the signed rounds: z = 2z + a.
pub fn pre(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], d: QubitId) {
    mod_double(b, ms, z, a);
    plain_add(b, ms, z, a, d);
}

/// After the signed rounds: z = (z - a) / 2.
pub fn post(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], d: QubitId) {
    for &q in z.iter() { b.x(q); }
    plain_add(b, ms, z, a, d);
    for &q in z.iter() { b.x(q); }
    mod_halve(b, ms, z, a);
}
