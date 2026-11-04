//! Private native check of the alternating multiplier and quadratic eraser.
use super::builder::Builder;
use crate::circuit::{BitId, QubitId};
#[derive(Clone, Copy)]
enum S {
    Q(QubitId),
    One,
}
fn xor(c: &mut Builder, a: &[S], q: QubitId) {
    for s in a {
        match *s {
            S::Q(x) => c.cx(x, q),
            S::One => c.x(q),
        }
    }
}
fn source(b: &[QubitId], i: isize, odd: bool) -> Vec<S> {
    if i < 0 {
        vec![]
    } else if (i as usize) < b.len() {
        vec![S::Q(b[i as usize])]
    } else if odd {
        vec![S::Q(*b.last().unwrap())]
    } else {
        vec![]
    }
}
fn product(c: &mut Builder, a: &[S], b: &[S], q: QubitId, qa: QubitId, qb: QubitId) {
    xor(c, a, qa);
    xor(c, b, qb);
    c.ccx(qa, qb, q);
    xor(c, b, qb);
    xor(c, a, qa);
}
fn erase_branch(c: &mut Builder, t: QubitId, s0: QubitId, s1: QubitId) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(s0, s1, m);
    c.free_bit(m);
    c.release_clean(t);
}
pub(crate) struct Plan {
    pub(crate) out: Vec<QubitId>,
    pub(crate) t: QubitId,
    odd: bool,
}
// Odd signed mode: P=alpha*B. Arbitrary unsigned mode: P=alpha*B-t.
pub(crate) fn construct(c: &mut Builder, b: &[QubitId], s0: QubitId, s1: QubitId, odd: bool) -> Plan {
    let n = b.len();
    assert!(!odd || (n >= 3 && n % 2 == 1));
    let t = c.alloc_qubit();
    c.ccx(s0, s1, t);
    let qa = c.alloc_qubit();
    let qb = c.alloc_qubit();
    let mut w = c.alloc_qubit();
    let mut out = Vec::new();
    if odd {
        let p0 = c.alloc_qubit();
        c.x(p0);
        out.push(p0);
        c.cx(s0, w);
    } else {
        c.cx(t, w);
    }
    let start = usize::from(odd);
    let end = n + if odd { 2 } else { 3 };
    for i in start..end {
        let x = source(b, i as isize, odd);
        let h1 = source(b, i as isize - 1, odd);
        let h2 = source(b, i as isize - 2, odd);
        if (i - start) % 2 == 0 {
            let nw = c.alloc_qubit();
            let mut a = vec![S::Q(w), S::Q(s0), S::Q(s1)];
            a.extend_from_slice(&h2);
            let mut bb = x.clone();
            bb.extend_from_slice(&h2);
            bb.extend([S::Q(s0), S::Q(t)]);
            product(c, &a, &bb, nw, qa, qb);
            xor(c, &x, w);
            xor(c, &h2, w);
            xor(c, &h2, nw);
            c.cx(s0, nw);
            out.push(w);
            w = nw;
        } else {
            let y = c.alloc_qubit();
            let mut hh = h1.clone();
            hh.extend_from_slice(&h2);
            product(c, &[S::Q(s1)], &hh, y, qa, qb);
            xor(c, &x, y);
            xor(c, &h2, y);
            c.cx(w, y);
            let mut a = vec![S::Q(y)];
            a.extend_from_slice(&x);
            a.push(S::Q(s0));
            let mut bb = x.clone();
            bb.extend_from_slice(&h2);
            bb.extend([S::Q(s0), S::Q(t)]);
            product(c, &a, &bb, w, qa, qb);
            c.cx(s0, w);
            c.cx(y, w);
            xor(c, &x, w);
            out.push(y);
        }
    }
    if odd {
        c.cx(*b.last().unwrap(), w);
    }
    c.cx(t, w);
    let top = c.alloc_qubit();
    if odd {
        c.cx(*b.last().unwrap(), top);
    }
    c.cx(t, top);
    out.push(top);
    assert_eq!(out.len(), n + if odd { 3 } else { 4 });
    c.release_clean(w);
    c.release_clean(qa);
    c.release_clean(qb);
    Plan { out, t, odd }
}
fn phase_linear(c: &mut Builder, a: &[S], m: BitId, spare: QubitId) {
    for s in a {
        match *s {
            S::Q(q) => c.z_if(q, m),
            S::One => {
                c.z_if(spare, m);
                c.x(spare);
                c.z_if(spare, m);
                c.x(spare);
            }
        }
    }
}
fn phase_product(c: &mut Builder, a: &[S], b: &[S], m: BitId, qa: QubitId, qb: QubitId) {
    xor(c, a, qa);
    xor(c, b, qb);
    c.cz_if(qa, qb, m);
    xor(c, b, qb);
    xor(c, a, qa);
}
pub(crate) fn erase(c: &mut Builder, b: &[QubitId], s0: QubitId, s1: QubitId, p: Plan, negative: bool) {
    let qa = c.alloc_qubit();
    let qb = c.alloc_qubit();
    let n = p.out.len();
    if p.odd {
        c.cx(*b.last().unwrap(), p.out[n - 1]);
    }
    c.cx(p.t, p.out[n - 1]);
    c.release_clean(p.out[n - 1]);
    let first = if p.odd { 2 } else { 1 };
    let start = usize::from(p.odd);
    for j in (first..n - 1).rev() {
        let i = j - 1;
        let x = source(b, i as isize, p.odd);
        let h1 = source(b, i as isize - 1, p.odd);
        let h2 = source(b, i as isize - 2, p.odd);
        let xn = source(b, j as isize, p.odd);
        let aclock = (i - start) % 2 == 0;
        let m = c.alloc_bit();
        c.hmr(p.out[j], m);
        let mut ll = xn;
        ll.extend_from_slice(&h1);
        ll.extend_from_slice(&h2);
        ll.push(S::Q(s0));
        phase_linear(c, &ll, m, qa);
        let mut uu = if aclock { x.clone() } else { h1.clone() };
        uu.extend_from_slice(if aclock { &h1 } else { &h2 });
        phase_product(c, &[S::Q(s1)], &uu, m, qa, qb);
        let mut aa = vec![S::Q(p.out[i])];
        aa.extend_from_slice(&x);
        aa.push(S::Q(s0));
        if aclock {
            aa.push(S::Q(s1));
        }
        let mut bb = x;
        bb.extend_from_slice(&h2);
        bb.extend([S::Q(s0), S::Q(p.t)]);
        if !(negative && j == 3) {
            phase_product(c, &aa, &bb, m, qa, qb);
        }
        c.release_clean(p.out[j]);
        c.free_bit(m);
    }
    if p.odd {
        c.cx(b[1], p.out[1]);
        c.cx(s0, p.out[1]);
        c.release_clean(p.out[1]);
        c.x(p.out[0]);
        c.release_clean(p.out[0]);
    } else {
        c.cx(b[0], p.out[0]);
        c.cx(p.t, p.out[0]);
        c.release_clean(p.out[0]);
    }
    erase_branch(c, p.t, s0, s1);
    c.release_clean(qa);
    c.release_clean(qb);
}
