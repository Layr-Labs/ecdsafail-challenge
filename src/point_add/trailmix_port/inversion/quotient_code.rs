//! Exact, opt-in pending-quotient codec. See quotient_code_proof.md for support
//! and finite-width obligations. No coefficient or remainder copy is allocated.

use super::{midq_flush_quotient, xor_const};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{
    borrow_compare_refs, ctrl_add, ctrl_sub,
};

const Q_BITS: usize = 18;
const CODE_BITS: usize = 5;

pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_QUOTIENT_CODE").ok().as_deref() == Some("1")
}

// Small, explicitly unitary AND ladder. At most 16 temporary bits, all counted.
fn xor_and(c: &mut Circuit, controls: &[&QReg], out: &QReg) {
    match controls.len() {
        0 => c.x(out),
        1 => c.cx(controls[0], out),
        2 => c.ccx(controls[0], controls[1], out),
        n => {
            let anc = c.alloc_qreg_bits("qcode.and", n - 2);
            c.ccx(controls[0], controls[1], &anc[0]);
            for i in 1..anc.len() {
                c.ccx(&anc[i - 1], controls[i + 1], &anc[i]);
            }
            c.ccx(&anc[n - 3], controls[n - 1], out);
            for i in (1..anc.len()).rev() {
                c.ccx(&anc[i - 1], controls[i + 1], &anc[i]);
            }
            c.ccx(controls[0], controls[1], &anc[0]);
            for bit in anc {
                c.zero_and_free(bit);
            }
        }
    }
}

fn xor_equal(c: &mut Circuit, reg: &[QReg], value: usize, out: &QReg) {
    for (i, bit) in reg.iter().enumerate() {
        if value >> i & 1 == 0 {
            c.x(bit);
        }
    }
    xor_and(c, &reg.iter().collect::<Vec<_>>(), out);
    for (i, bit) in reg.iter().enumerate() {
        if value >> i & 1 == 0 {
            c.x(bit);
        }
    }
}

fn xor_code(c: &mut Circuit, q: &[QReg], code: &[QReg]) {
    assert!(q.len() < 1 << code.len());
    xor_const(c, code, q.len());
    let hit = c.alloc_qreg("qcode.hit");
    for i in 0..q.len() {
        for bit in &q[..i] {
            c.x(bit);
        }
        let controls: Vec<_> = q[..=i].iter().collect();
        xor_and(c, &controls, &hit);
        for (j, bit) in code.iter().enumerate() {
            if (q.len() ^ i) >> j & 1 != 0 {
                c.cx(&hit, bit);
            }
        }
        xor_and(c, &controls, &hit);
        for bit in &q[..i] {
            c.x(bit);
        }
    }
    c.zero_and_free(hit);
}

fn divide(c: &mut Circuit, a: &[QReg], b: &[QReg], quotient: &[QReg], inverse: bool) {
    // floor(a/2^i) >= b is exactly a >= b*2^i, even if b*2^i exceeds
    // n bits. Lower quotient bits are unwritten zero in the forward sweep,
    // already cleared zero in reverse. The compare restores these borrowed bits.
    let br_full: Vec<_> = b.iter().collect();
    let step = |c: &mut Circuit, i: usize| {
        let ar: Vec<_> = a[i..].iter().collect();
        let br: Vec<_> = b[..a.len() - i].iter().collect();
        let compare_a: Vec<_> = a[i..].iter().chain(quotient[..i].iter()).collect();
        let compare = |c: &mut Circuit| {
            borrow_compare_refs(c, &compare_a, &br_full, &quotient[i]);
            c.x(&quotient[i]);
        };
        if inverse {
            ctrl_add(c, &quotient[i], &ar, &br);
            compare(c);
        } else {
            compare(c);
            ctrl_sub(c, &quotient[i], &ar, &br);
        }
    };
    if inverse {
        for i in 0..quotient.len() {
            step(c, i);
        }
    } else {
        for i in (0..quotient.len()).rev() {
            step(c, i);
        }
    }
}

// q ^= recovered_q, preserving a, b and code. The 18 decision bits are the ONLY
// temporary quotient; a itself holds the remainder until divide is reversed.
fn xor_recovered(c: &mut Circuit, a: &[QReg], b: &[QReg], code: &[QReg], q: &[QReg]) {
    assert_eq!(a.len(), b.len());
    assert!(q.len() <= a.len());
    let section = c.push_section("midq.quotient.extract");
    let quotient = c.alloc_qreg_bits("qcode.quotient", q.len());
    divide(c, a, b, &quotient, false);
    let keep = c.alloc_qreg("qcode.keep");
    for i in 0..q.len() {
        // Equality predicates are disjoint: XOR is exactly [code <= i].
        // Sentinel q.len() (18 in the real codec) never enables a copy.
        for k in 0..=i {
            xor_equal(c, code, k, &keep);
        }
        c.ccx(&keep, &quotient[i], &q[i]);
        for k in (0..=i).rev() {
            xor_equal(c, code, k, &keep);
        }
    }
    c.zero_and_free(keep);
    divide(c, a, b, &quotient, true);
    for bit in quotient {
        c.zero_and_free(bit);
    }
    c.pop_section(&section);
}

pub(super) fn compress(c: &mut Circuit, ca: &[QReg], cb: &[QReg], q: &mut Vec<QReg>) -> Vec<QReg> {
    assert_eq!(
        q.len(),
        Q_BITS,
        "quotient codec is sealed to the inherited q18 handoff"
    );
    assert_eq!(ca.len(), 257);
    assert_eq!(cb.len(), 257);
    let code = c.alloc_qreg_bits("qcode.k", CODE_BITS);
    xor_code(c, q, &code);
    xor_recovered(c, ca, cb, &code, q);
    for bit in std::mem::take(q) {
        c.zero_and_free(bit);
    }
    code
}

pub(super) fn restore(
    c: &mut Circuit,
    ca: &[QReg],
    cb: &[QReg],
    q: &mut Vec<QReg>,
    code: Vec<QReg>,
) {
    assert!(q.is_empty());
    assert_eq!(code.len(), CODE_BITS);
    *q = c.alloc_qreg_bits("qcode.restored_q", Q_BITS);
    xor_recovered(c, ca, cb, &code, q);
    xor_code(c, q, &code);
    for bit in code {
        c.zero_and_free(bit);
    }
}

#[path = "quotient_code_selftest.rs"]
pub(super) mod selftest;
