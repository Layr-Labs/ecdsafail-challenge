//! Inert research header gate. Mutated query sources require a retained move receipt.
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
#[derive(Clone, Copy, Debug)]
pub enum Cleanup {
    Unitary,
    Hmr,
}
fn erase(c: &mut Builder, a: Q, b: Q, q: Q) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.free(q);
}
fn tree(c: &mut Builder, x: &[Q]) -> Vec<(Q, Q, Q)> {
    assert!(x.len() >= 2);
    c.x_all(x);
    let mut v = Vec::new();
    let q = c.alloc_qubit();
    c.ccx(x[0], x[1], q);
    v.push((x[0], x[1], q));
    for &b in &x[2..] {
        let a = v.last().unwrap().2;
        let q = c.alloc_qubit();
        c.ccx(a, b, q);
        v.push((a, b, q));
    }
    c.x_all(x);
    v
}
fn clear(c: &mut Builder, x: &[Q], v: Vec<(Q, Q, Q)>, mode: Cleanup) {
    c.x_all(x);
    for (a, b, q) in v.into_iter().rev() {
        match mode {
            Cleanup::Unitary => {
                c.ccx(a, b, q);
                c.free(q)
            }
            Cleanup::Hmr => erase(c, a, b, q),
        }
    }
    c.x_all(x);
}
fn swap(c: &mut Builder, m: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(m, a, b);
    c.cx(b, a);
}
fn dec(c: &mut Builder, h: &[Q], m: Q) {
    assert_eq!(h.len(), 3);
    let w = c.alloc_qubit();
    c.x(h[0]);
    c.x(h[1]);
    c.ccx(m, h[0], w);
    c.ccx(w, h[1], h[2]);
    c.ccx(m, h[0], w);
    c.x(h[1]);
    c.x(h[0]);
    c.x(h[0]);
    c.ccx(m, h[0], h[1]);
    c.x(h[0]);
    c.cx(m, h[0]);
    c.free(w);
}
fn inc(c: &mut Builder, h: &[Q], m: Q) {
    assert_eq!(h.len(), 3);
    let w = c.alloc_qubit();
    c.ccx(m, h[0], w);
    c.ccx(w, h[1], h[2]);
    c.ccx(m, h[0], w);
    c.ccx(m, h[0], h[1]);
    c.cx(m, h[0]);
    c.free(w);
}
fn migrate(c: &mut Builder, l: &[Q], r: &[Q], h: &[Q], m: Q, inverse: bool) {
    assert_eq!(l.len(), r.len());
    if inverse {
        inc(c, h, m);
    }
    for (&a, &b) in l.iter().zip(r) {
        swap(c, m, a, b);
    }
    if !inverse {
        dec(c, h, m);
    }
}
/// Exact 3w+2 (unitary) or 2w+3 (HMR) CCX for width/stride w.
/// Query controls must be disjoint from all mutated registers.
pub fn readonly(c: &mut Builder, x: &[Q], l: &[Q], r: &[Q], h: &[Q], mode: Cleanup, inverse: bool) {
    assert!(
        x.iter()
            .all(|q| !l.contains(q) && !r.contains(q) && !h.contains(q)),
        "aliased query requires a retained move receipt"
    );
    let v = tree(c, x);
    let m = v.last().unwrap().2;
    migrate(c, l, r, h, m, inverse);
    clear(c, x, v, mode);
}
fn zero_xor(c: &mut Builder, x: &[Q], out: Q) {
    assert!(x.len() >= 2);
    c.x_all(x);
    let mut v = Vec::new();
    if x.len() == 2 {
        c.ccx(x[0], x[1], out);
    } else {
        let q = c.alloc_qubit();
        c.ccx(x[0], x[1], q);
        v.push((x[0], x[1], q));
        for &b in &x[2..x.len() - 1] {
            let a = v.last().unwrap().2;
            let q = c.alloc_qubit();
            c.ccx(a, b, q);
            v.push((a, b, q));
        }
        c.ccx(v.last().unwrap().2, *x.last().unwrap(), out);
        for (a, b, q) in v.into_iter().rev() {
            erase(c, a, b, q);
        }
    }
    c.x_all(x);
}
pub struct MoveReceipt {
    pub move_bit: Q,
}
/// Aliased source version is exact at 2w+3 CCX, but its move bit remains live.
pub fn aliased_forward(c: &mut Builder, x: &[Q], l: &[Q], r: &[Q], h: &[Q]) -> MoveReceipt {
    let m = c.alloc_qubit();
    zero_xor(c, x, m);
    migrate(c, l, r, h, m, false);
    MoveReceipt { move_bit: m }
}
/// Independent inverse restores query controls before phase-clean receipt erasure.
pub fn aliased_inverse(c: &mut Builder, x: &[Q], l: &[Q], r: &[Q], h: &[Q], receipt: MoveReceipt) {
    migrate(c, l, r, h, receipt.move_bit, true);
    zero_xor(c, x, receipt.move_bit);
    c.free(receipt.move_bit);
}

pub struct Fixture {
    pub left: Vec<Q>,
    pub right: Vec<Q>,
    pub header: Vec<Q>,
    pub query: Vec<Q>,
    pub passenger: Vec<Q>,
    pub foreign: Vec<Q>,
    pub ops: Vec<crate::circuit::Op>,
    pub begin: usize,
    pub mid: usize,
    pub dimensions: (usize, usize),
    pub peak: usize,
    pub forward_live: usize,
}
/// Standalone research emitter; no production callers. The 961 standing wires include passenger256.
pub fn fixture(w: usize, aliased: bool, mode: Cleanup) -> Fixture {
    fixture_standing(w, aliased, mode, 961)
}
pub fn fixture_standing(w: usize, aliased: bool, mode: Cleanup, standing: usize) -> Fixture {
    let mut c = Builder::new();
    let left = c.alloc_qubits(w);
    let right = c.alloc_qubits(w);
    let header = c.alloc_qubits(3);
    let query = if aliased {
        left.clone()
    } else {
        c.alloc_qubits(w)
    };
    let passenger = c.alloc_qubits(256);
    let foreign = c.alloc_qubits(standing - c.active_qubits() as usize);
    let begin = c.op_count();
    let receipt = if aliased {
        Some(aliased_forward(&mut c, &query, &left, &right, &header))
    } else {
        readonly(&mut c, &query, &left, &right, &header, mode, false);
        None
    };
    let mid = c.op_count();
    let forward_live = c.active_qubits() as usize;
    if let Some(v) = receipt {
        aliased_inverse(&mut c, &query, &left, &right, &header, v);
    } else {
        readonly(&mut c, &query, &left, &right, &header, mode, true);
    }
    assert_eq!(c.active_qubits() as usize, standing);
    let peak = c.peak_total() as usize;
    let dimensions = c.i13_dims();
    let ops = c.take_ops();
    Fixture {
        left,
        right,
        header,
        query,
        passenger,
        foreign,
        ops,
        begin,
        mid,
        dimensions,
        peak,
        forward_live,
    }
}
