//! TRACK1 (pane so-A): clean-lane arithmetic for the x' square (V1.md section 5, step 1).
//!
//! During the square x' = lambda^2 - dx - 3 ox the circuit has 250 clean lanes. Here they carry AND-cell ripples
//! (`and_c` compute, `and_u` measured uncompute: one Toffoli per carry), so a 256-bit add costs 255 + 4 (expected) instead of
//! 511, a fold of c (or c - 1) is one controlled constant add over t[0..67) (66 / 62 Toffoli instead of 700 / 560), and the
//! overflow-flag erase is a measured erase whose compare runs only when the outcome bit is 1 (about 20 instead of 79).
//! Same failure class as the parent: a carry leaving t[0..FW) is dropped (<= 2^-34 per fold, parent 5 x 2^-35), and the
//! flag erase compares the top CMPT lanes (differs w.p. <= 2^-40, as the parent).
use super::builder::B;
use super::modp_frogdrop::{Ms, C, CMPT};
use crate::circuit::QubitId;

/// fold window: carries beyond t[FW - 1] are dropped (parent: 32 + 35 = 67 for the top digit)
pub const FW: usize = 67;
/// low segment of the 256-bit add whose boundary carry is erased by measurement
pub const SEG: usize = 8;
/// clean lanes needed by `sq_horner_c`
pub const BANK: usize = 256 - SEG - 1 + 1;

pub fn xclean() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_XCLEAN").map(|v| v.trim() != "0").unwrap_or(true))
}

/// t += ctl * k (neg: -=) mod 2^w for a constant k < 2^64, carries beyond t[w - 1] dropped; ctl restored. AND-cell ripple on
/// `bank` (>= w - 1 - tz(k) clean lanes, returned clean). w - 1 - tz(k) Toffoli.
pub fn const_add_ctl(b: &mut B, t: &[QubitId], k: u64, ctl: QubitId, neg: bool, bank: &[QubitId]) {
    let w = t.len();
    let f = k.trailing_zeros() as usize;
    assert!(k != 0 && f + 1 < w && w <= 64 + 8 && bank.len() >= w - 1 - f);
    assert!(!t[f..].contains(&ctl));
    let kb = |i: usize| i < 64 && (k >> i) & 1 == 1;
    let l = |i: usize| bank[i - 1 - f];
    if neg { for i in f..w { b.x(t[i]); } }
    for i in f..w - 1 {
        if i == f {
            b.and_c(ctl, t[i], l(i + 1));
        } else if !kb(i) {
            b.and_c(l(i), t[i], l(i + 1));
        } else {
            b.cx(l(i), ctl); b.cx(l(i), t[i]);
            b.and_c(ctl, t[i], l(i + 1));
            b.cx(l(i), l(i + 1)); b.cx(l(i), ctl);
        }
    }
    for i in (f..w).rev() {
        if i == w - 1 {
            b.cx(l(i), t[i]);
            if kb(i) { b.cx(ctl, t[i]); }
        } else if i == f {
            b.and_u(ctl, t[i], l(i + 1));
            b.cx(ctl, t[i]);
        } else if !kb(i) {
            b.and_u(l(i), t[i], l(i + 1));
            b.cx(l(i), t[i]);
        } else {
            b.cx(l(i), l(i + 1)); b.cx(l(i), ctl);
            b.and_u(ctl, t[i], l(i + 1));
            b.cx(l(i), ctl); b.cx(ctl, t[i]);
        }
    }
    if neg { for i in f..w { b.x(t[i]); } }
}

#[cfg(test)]
thread_local! { pub static SABOTAGE: std::cell::Cell<bool> = std::cell::Cell::new(false); }

/// majority cell: T ^= carry out of (z_i + y_i + c) with T clean; c = None for bit 0. z_i and y_i are toggled by c (undone by `uncell`).
fn cell(b: &mut B, z: QubitId, y: QubitId, c: Option<QubitId>, t: QubitId) {
    match c {
        None => b.and_c(z, y, t),
        Some(c) => {
            b.cx(c, z); b.cx(c, y);
            b.and_c(z, y, t);
            b.cx(c, t);
        }
    }
}
/// inverse of `cell` (T measured away); `sum`: also turn z_i into the sum bit z ^ y ^ c; keep: leave T (and the toggles) alone
fn uncell(b: &mut B, z: QubitId, y: QubitId, c: Option<QubitId>, t: Option<QubitId>, sum: bool) {
    match c {
        None => { if let Some(t) = t { b.and_u(z, y, t); } if sum { b.cx(y, z); } }
        Some(c) => {
            if let Some(t) = t { b.cx(c, t); b.and_u(z, y, t); }
            #[cfg(test)]
            { if SABOTAGE.with(|s| s.get()) && t.is_some() { b.cx(c, z); return; } }
            b.cx(c, y);
            if sum { b.cx(y, z); } else { b.cx(c, z); }
        }
    }
}

/// z += y mod 2^256 (y restored), flag ^= carry out (flag clean on entry). `bank`: >= 248 clean lanes (returned clean).
/// The low SEG bits are added first and their boundary carry P = c_SEG is kept in a lane while the rest is added, then
/// erased by an X-basis measurement whose phase is repaired by a compare of the low segment run only when the outcome is 1.
pub fn add_flag(b: &mut B, y: &[QubitId], z: &[QubitId], flag: QubitId, bank: &[QubitId]) {
    assert!(y.len() == 256 && z.len() == 256 && bank.len() >= BANK);
    let s = SEG;
    let pl = bank[s - 1];
    let la = |i: usize| bank[i - 1]; // c_i for 1 <= i <= s (A phase)
    let lb = |i: usize| { let j = i - s - 1; bank[if j < s - 1 { j } else { j + 1 }] }; // c_i for s < i <= 255
    let cin = |i: usize| -> Option<QubitId> { if i == 0 { None } else if i <= s { Some(la(i)) } else { Some(lb(i)) } };
    let cin_b = |i: usize| -> Option<QubitId> { if i == s { Some(pl) } else { cin(i) } };
    for i in 0..s { cell(b, z[i], y[i], cin(i), la(i + 1)); }
    for i in (0..s).rev() { uncell(b, z[i], y[i], cin(i), if i == s - 1 { None } else { Some(la(i + 1)) }, true); }
    for i in s..256 {
        let t = if i == 255 { flag } else { lb(i + 1) };
        cell(b, z[i], y[i], cin_b(i), t);
    }
    for i in (s..256).rev() {
        uncell(b, z[i], y[i], cin_b(i), if i == 255 { None } else { Some(lb(i + 1)) }, true);
    }
    // erase P = [sum_A < y_A]
    let m = b.fresh_bits(1)[0];
    b.hmr_to(pl, m);
    b.push_cond(m);
    for i in 0..s { b.x(z[i]); }
    for i in 0..s { cell(b, z[i], y[i], if i == 0 { None } else { Some(la(i)) }, la(i + 1)); }
    b.z_if(la(s), m);
    for i in (0..s).rev() { uncell(b, z[i], y[i], if i == 0 { None } else { Some(la(i)) }, Some(la(i + 1)), false); }
    for i in 0..s { b.x(z[i]); }
    b.pop_cond();
}

/// flag (= [z < y] up to the top CMPT lanes) erased by measurement; the compare of the top lanes runs only if the outcome is 1.
pub fn erase_flag(b: &mut B, flag: QubitId, z: &[QubitId], y: &[QubitId], bank: &[QubitId]) {
    let n = CMPT;
    let (zt, yt) = (&z[256 - n..], &y[256 - n..]);
    let m = b.fresh_bits(1)[0];
    b.hmr_to(flag, m);
    b.push_cond(m);
    for q in zt { b.x(*q); }
    for i in 0..n { cell(b, zt[i], yt[i], if i == 0 { None } else { Some(bank[i - 1]) }, bank[i]); }
    b.z_if(bank[n - 1], m);
    for i in (0..n).rev() { uncell(b, zt[i], yt[i], if i == 0 { None } else { Some(bank[i - 1]) }, Some(bank[i]), false); }
    for q in zt { b.x(*q); }
    b.pop_cond();
}

/// z += y mod p, lazy (as fd_shell::modadd_unc): add with carry flag, fold c under the flag, measured flag erase.
pub fn modadd_c(b: &mut B, z: &[QubitId], y: &[QubitId], flag: QubitId, bank: &[QubitId]) {
    add_flag(b, y, z, flag, bank);
    const_add_ctl(b, &z[..FW], C, flag, false, bank);
    erase_flag(b, flag, z, y, bank);
}

/// z <- 2 z mod p (relabel, then add h (c - 1) with h the old top bit now on lane 0)
pub fn double_c(b: &mut B, z: &mut Vec<QubitId>, bank: &[QubitId]) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    const_add_ctl(b, &z[..FW], C - 1, h, false, bank);
}
pub fn halve_c(b: &mut B, z: &mut Vec<QubitId>, bank: &[QubitId]) {
    let h = z[0];
    const_add_ctl(b, &z[..FW], C - 1, h, true, bank);
    let low = z.remove(0);
    z.push(low);
}

fn sround_c(b: &mut B, z: &mut Vec<QubitId>, a: &[QubitId], bit: QubitId, flag: QubitId, bank: &[QubitId]) {
    double_c(b, z, bank);
    b.x(bit);
    for &q in z.iter() { b.cx(bit, q); }
    modadd_c(b, z, a, flag, bank);
    for &q in z.iter() { b.cx(bit, q); }
    b.x(bit);
}

/// x <- lambda^2 - x (mod p, lazy) in place, lambda untouched: the signed-digit Horner of `sq_horner` on clean lanes.
pub(crate) fn sq_horner_c(b: &mut B, x: &[QubitId], lam: &[QubitId]) {
    let ms = Ms::alloc(b);
    let c = b.alloc();
    let flag = ms.k;
    super::modp_frogdrop::ctrl_neg(b, &ms, x, None, lam);
    let bank = b.alloc_n(BANK);
    let mut xv = x.to_vec();
    for _ in 0..256 { halve_c(b, &mut xv, &bank); }
    double_c(b, &mut xv, &bank);
    modadd_c(b, &xv, lam, flag, &bank);
    for i in (0..256).rev() {
        b.cx(lam[i], c);
        sround_c(b, &mut xv, lam, c, flag, &bank);
        b.cx(lam[i], c);
    }
    for &q in xv.iter() { b.x(q); }
    modadd_c(b, &xv, lam, flag, &bank);
    for &q in xv.iter() { b.x(q); }
    halve_c(b, &mut xv, &bank);
    assert_eq!(xv, x.to_vec());
    b.free_n(&bank);
    b.free(c);
    ms.release(b);
}

#[cfg(test)]
#[path = "fd_clean_tests.rs"]
mod tests;

/// phase (-1)^(product of lanes) for 1..4 lanes; d, d2 dirty (restored), only used for 3 / 4 lanes
fn phase_prod(b: &mut B, l: &[QubitId], d: QubitId, d2: QubitId, m: crate::circuit::BitId) {
    let ph3 = |b: &mut B, x: QubitId, y: QubitId, z: QubitId, dd: QubitId| { b.cz(x, dd); b.ccx(y, z, dd); b.cz(x, dd); b.ccx(y, z, dd); };
    match l.len() {
        1 => b.z_if(l[0], m),
        2 => b.cz(l[0], l[1]),
        3 => ph3(b, l[0], l[1], l[2], d),
        4 => { ph3(b, l[2], l[3], d, d2); b.ccx(l[0], l[1], d); ph3(b, l[2], l[3], d, d2); b.ccx(l[0], l[1], d); }
        _ => panic!("phase_prod"),
    }
}

/// STEP 2 (V1 5 row 2): erase `k` = ctl... & carry_out(~t + a) (top-CMPT-lane compare, as ttk_carry) by an X-basis measurement; the
/// phase (-1)^(m k) is repaired by the same ripple with the two carry-out terms turned into phases, run only if m = 1.
/// Straight-line code only (HMR and the condition block are not allowed inside a recording). t and a restored; k |0> on exit.
/// 2n + 2..6 Toffoli when the outcome is 1, none otherwise. d, d2 borrowed (d2 only with two controls).
pub fn measured_erase(b: &mut B, k: QubitId, a: &[QubitId], t: &[QubitId], ctl: &[QubitId], d: QubitId, d2: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n && ctl.len() <= 2 && !b.fusion_recording());
    let m = b.fresh_bits(1)[0];
    b.hmr_to(k, m);
    b.push_cond(m);
    for &q in t { b.x(q); }
    b.begin();
    for i in 1..n { b.cx(a[i], t[i]); }
    let s1 = b.end();
    b.play(&s1, false);
    let mut l1 = ctl.to_vec(); l1.push(a[n - 1]);
    phase_prod(b, &l1, d, d2, m);
    b.begin();
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    let s23 = b.end();
    b.play(&s23, false);
    let mut l2 = ctl.to_vec(); l2.push(t[n - 1]); l2.push(a[n - 1]);
    phase_prod(b, &l2, d, d2, m);
    b.play(&s23, true);
    b.play(&s1, true);
    for &q in t { b.x(q); }
    b.pop_cond();
}

pub fn measured_ok(b: &B) -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("FD_MERASE").map(|v| v.trim() != "0").unwrap_or(true)) && !b.fusion_recording()
}
