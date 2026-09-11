//! Component-only D alignment preparation. Never dispatched by production PZ.
//! See analyses/variable-shift-target.md for the conditional support contract.
use super::*;
use crate::point_add::trailmix_port::arith::cuccaro::add_cuccaro_3n_uncontrolled_refs_with_carry;

fn add(c: &mut Circuit, dst: &[QReg], src: &[QReg], zeros: &[QReg], carry: &QReg, sub: bool) {
    assert!(src.len() <= dst.len());
    let a: Vec<_> = dst.iter().collect();
    let b: Vec<_> = src
        .iter()
        .chain(zeros.iter().take(dst.len() - src.len()))
        .collect();
    assert_eq!(a.len(), b.len());
    if sub {
        for bit in dst {
            c.x(bit);
        }
    }
    add_cuccaro_3n_uncontrolled_refs_with_carry(c, &a, &b, carry);
    if sub {
        for bit in dst {
            c.x(bit);
        }
    }
}

fn clamp_xor(c: &mut Circuit, pa: &[QReg], pb: &[QReg], out: &[QReg], carry: &QReg) {
    assert_eq!(pa.len(), 9);
    assert_eq!(pb.len(), 9);
    assert_eq!(out.len(), 5);
    add(c, pa, pb, &[], carry, true);
    // The 9-bit difference is signed and exact for true positions 0..255.
    // It is not a subtraction of the baseline's wrapped 5-bit positions.
    c.x(&pa[8]);
    for (a, b) in pa.iter().zip(out) {
        c.ccx(&pa[8], a, b);
    }
    c.x(&pa[8]);
    add(c, pa, pb, &[], carry, false);
}

fn cycle(c: &mut Circuit, word: &[QReg], amount: usize, control: Option<&QReg>, inverse: bool) {
    let n = word.len();
    let amount = amount % n;
    let mut visited = vec![false; n];
    let mut pairs = Vec::new();
    for first in 0..n {
        if visited[first] {
            continue;
        }
        visited[first] = true;
        let mut next = (first + amount) % n;
        while next != first {
            visited[next] = true;
            pairs.push((first, next));
            next = (next + amount) % n;
        }
    }
    if inverse {
        pairs.reverse();
    }
    for (a, b) in pairs {
        if let Some(control) = control {
            c.cswap(control, &word[a], &word[b]);
        } else {
            c.swap(&word[a], &word[b]);
        }
    }
}

fn rotate_delta(c: &mut Circuit, word: &[QReg], delta: &[QReg], inverse: bool) {
    assert_eq!(delta.len(), 6);
    let section = c.push_section("prototype.d_align.shift");
    if !inverse {
        cycle(c, word, 32, None, true);
    }
    let order: Vec<_> = if inverse {
        (0..6).rev().collect()
    } else {
        (0..6).collect()
    };
    for i in order {
        cycle(c, word, 1 << i, Some(&delta[i]), inverse);
    }
    if inverse {
        cycle(c, word, 32, None, false);
    }
    c.pop_section(&section);
}

pub(super) fn frame_xor(c: &mut Circuit, q: &[QReg], role: &QReg, out: &[QReg]) {
    assert!(!q.is_empty() && q.len() <= 32);
    assert_eq!(out.len(), 5);
    // Exact R*[q!=0]*ctz(q), including q=0. Each prefix includes role.
    // This first bounded component uses up to q.len() clean prefix wires.
    for bit in q {
        c.x(bit);
    }
    let mut chain = Vec::new();
    for (i, bit) in q.iter().enumerate() {
        let flag = c.alloc_qreg("d_align.qprefix");
        c.ccx(chain.last().unwrap_or(role), bit, &flag);
        let mask = if i + 1 < q.len() {
            i ^ (i + 1)
        } else {
            q.len() - 1
        };
        for (j, dst) in out.iter().enumerate() {
            if mask >> j & 1 != 0 {
                c.cx(&flag, dst);
            }
        }
        chain.push(flag);
    }
    for i in (0..chain.len()).rev() {
        c.clear_and(&chain[i], if i == 0 { role } else { &chain[i - 1] }, &q[i]);
    }
    for flag in chain {
        c.zero_and_free(flag);
    }
    for bit in q {
        c.x(bit);
    }
}

fn offset_xor(
    c: &mut Circuit,
    role_m: &QReg,
    pa: &[QReg],
    pb: &[QReg],
    phi: &[QReg],
    offset: &QReg,
) {
    c.x(role_m);
    for bit in [&pa[0], &pb[0], &phi[0]] {
        c.ccx(role_m, bit, offset);
    }
    c.x(role_m);
}

fn predicate_pair(c: &mut Circuit, a: &[QReg], b: &[QReg], phi: &[QReg]) -> (QReg, QReg) {
    let less = c.alloc_qreg("d_align.less");
    let zero = c.alloc_qreg("d_align.zero");
    borrow_compare_refs(
        c,
        &a.iter().collect::<Vec<_>>(),
        &b.iter().collect::<Vec<_>>(),
        &less,
    );
    or_is_zero(c, phi, &zero);
    (less, zero)
}

fn clear_pair(c: &mut Circuit, a: &[QReg], b: &[QReg], phi: &[QReg], less: QReg, zero: QReg) {
    clear_borrow_compare_refs(
        c,
        &a.iter().collect::<Vec<_>>(),
        &b.iter().collect::<Vec<_>>(),
        &less,
    );
    clear_zero_predicate(c, phi, &zero, false);
    c.zero_and_free(less);
    c.zero_and_free(zero);
}

/// Forward boundary: R=[ca<cb], phi=R*[q!=0]*ctz(q), Bphys=B0<<phi.
/// Inverse boundary: the corresponding forward PREP image (A/ca/cb/q unchanged).
/// True max(0,msb(A)-msb(B0))<=31, both embeddings fit, B0>0, width<=256.
/// With lo>0, Blogic>=2^lo is additionally required. Pa is its clamped relative
/// position; Pb is its exact relative position. A below the floor forces M, so
/// the clamp and the gated offset parity remain exact. No width shrink here.
#[allow(clippy::too_many_arguments)]
fn apply_with_floor(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    phi: &[QReg],
    role: &QReg,
    srot: &[QReg],
    offset: &QReg,
    inverse: bool,
    lo: usize,
) {
    assert!((2..=256).contains(&a.len()) && a.len() == b.len());
    assert!(!ca.is_empty() && ca.len() == cb.len());
    assert_eq!(phi.len(), 5);
    assert_eq!(srot.len(), 5);
    let all: Vec<_> = a
        .iter()
        .chain(b)
        .chain(ca)
        .chain(cb)
        .chain(q)
        .chain(phi)
        .chain([role])
        .chain(srot)
        .chain([offset])
        .map(QReg::id)
        .collect();
    assert_eq!(
        all.len(),
        all.iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
    );
    let carry = c.alloc_qreg("d_align.carry");
    let zeros = c.alloc_qreg_bits("d_align.pad", 4);
    assert!(lo < a.len());
    let pa = clz_deposit_a(c, a, 9, lo);
    let pb = clz_deposit_a(c, b, 9, lo);
    add(c, &pb, phi, &zeros, &carry, true);
    let car: Vec<_> = ca.iter().collect();
    let cbr: Vec<_> = cb.iter().collect();
    if !inverse {
        clamp_xor(c, &pa, &pb, srot, &carry);
        let delta = c.alloc_qreg_bits("d_align.delta", 6);
        c.x(&delta[5]);
        add(c, &delta, srot, &zeros, &carry, false);
        add(c, &delta, phi, &zeros, &carry, true);
        rotate_delta(c, b, &delta, false);
        add(c, &delta, phi, &zeros, &carry, false);
        add(c, &delta, srot, &zeros, &carry, true);
        c.x(&delta[5]);
        for bit in delta {
            c.zero_and_free(bit);
        }
        frame_xor(c, q, role, phi);
        for (a, b) in srot.iter().zip(phi) {
            c.cx(a, b);
            c.cx(b, a);
        }
        clear_borrow_compare_refs(c, &car, &cbr, role);
        let (less, zero) = predicate_pair(c, a, b, phi);
        c.ccx(&less, &zero, role);
        c.cx(&less, offset);
        c.cx(role, offset);
        clear_pair(c, a, b, phi, less, zero);
        cycle(c, b, 1, Some(offset), true);
        ctrl_dec(c, offset, phi);
        offset_xor(c, role, &pa, &pb, phi, offset);
    } else {
        offset_xor(c, role, &pa, &pb, phi, offset);
        cycle(c, b, 1, Some(offset), false);
        ctrl_inc(c, offset, phi);
        let (less, zero) = predicate_pair(c, a, b, phi);
        c.cx(&less, offset);
        c.cx(role, offset);
        c.ccx(&less, &zero, role);
        clear_pair(c, a, b, phi, less, zero);
        borrow_compare_refs(c, &car, &cbr, role);
        frame_xor(c, q, role, srot);
        let delta = c.alloc_qreg_bits("d_align.delta", 6);
        c.x(&delta[5]);
        add(c, &delta, phi, &zeros, &carry, false);
        add(c, &delta, srot, &zeros, &carry, true);
        rotate_delta(c, b, &delta, true);
        add(c, &delta, srot, &zeros, &carry, false);
        add(c, &delta, phi, &zeros, &carry, true);
        c.x(&delta[5]);
        for bit in delta {
            c.zero_and_free(bit);
        }
        clamp_xor(c, &pa, &pb, phi, &carry);
        for (a, b) in srot.iter().zip(phi) {
            c.cx(a, b);
        }
        frame_xor(c, q, role, srot);
    }
    add(c, &pb, phi, &zeros, &carry, false);
    clz_undeposit_a(c, pa, a, lo);
    clz_undeposit_a(c, pb, b, lo);
    for bit in zeros {
        c.zero_and_free(bit);
    }
    c.zero_and_free(carry);
}

/// Original full-scan entry. This path emits the parent's exact operation stream.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    phi: &[QReg],
    role: &QReg,
    srot: &[QReg],
    offset: &QReg,
    inverse: bool,
) {
    apply_with_floor(c, a, b, ca, cb, q, phi, role, srot, offset, inverse, 0);
}

/// Existing field-PZ support implies Blogic >= 2^lo. The explicit true-shift
/// and exact determinant premises are not inferred from these allocations.
pub(super) fn profile_floor(n: usize, m: usize) -> usize {
    let lo = 223usize.saturating_sub(m);
    if m == 0 || lo >= n {
        0
    } else {
        lo
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_profile(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    phi: &[QReg],
    role: &QReg,
    srot: &[QReg],
    offset: &QReg,
    inverse: bool,
) {
    let lo = if std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref() == Some("1") {
        profile_floor(a.len(), ca.len())
    } else {
        0
    };
    apply_with_floor(c, a, b, ca, cb, q, phi, role, srot, offset, inverse, lo);
}

#[path = "d_alignment_common_window_selftest.rs"]
mod common_window_checks;
pub(crate) fn common_window_selftest() {
    common_window_checks::run();
}

#[path = "d_alignment_prep_selftest.rs"]
mod checks;
pub(crate) fn selftest() {
    checks::run();
}
