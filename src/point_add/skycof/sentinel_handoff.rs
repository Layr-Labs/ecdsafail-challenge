//! Research sentinel history + shared Hcount/odometer. Inert in production.
use super::decoder::{self, DecCfg, Hreg, TickIo};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

fn fredkin(c: &mut Builder, g: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(g, a, b);
    c.cx(b, a);
}
fn and_erase(c: &mut Builder, a: Q, b: Q, q: Q) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.free(q);
}
/// Counter += enabled, with a clean HMR carry tree. Exactly n-1 CCX.
pub fn increment(c: &mut Builder, count: &[Q], enabled: Q) {
    let mut carries = Vec::new();
    let mut previous = enabled;
    for &bit in &count[..count.len() - 1] {
        let q = c.alloc_qubit();
        c.ccx(bit, previous, q);
        carries.push(q);
        previous = q;
    }
    for (i, &bit) in count.iter().enumerate() {
        c.cx(if i == 0 { enabled } else { carries[i - 1] }, bit);
    }
    for i in (0..carries.len()).rev() {
        let prev = if i == 0 { enabled } else { carries[i - 1] };
        let m = c.alloc_bit();
        c.hmr(carries[i], m);
        c.z_if(prev, m);
        c.cz_if(prev, count[i], m);
        c.free_bit(m);
        c.free(carries[i]);
    }
}
pub fn decrement(c: &mut Builder, count: &[Q], enabled: Q) {
    c.x_all(count);
    increment(c, count, enabled);
    c.x_all(count);
}
/// The sentinel is a topmost1, so count=bitlen(H)-1 even for all-zero data.
/// Same native decoder as push/pop; no copied ambiguity output or count bank.
pub fn push_count(c: &mut Builder, io: &TickIo, h: &Hreg, count: &[Q], cfg: DecCfg) {
    assert!(io.park.is_none() && io.cflag.is_none());
    let sc = decoder::open(c, io, cfg);
    decoder::shift_in(c, sc.amb, io.typ, &h.wires);
    increment(c, count, sc.amb);
    c.cx(sc.d, io.typ);
    c.cx(sc.amb, io.typ);
    decoder::close(c, io, sc);
}
pub fn pop_count(c: &mut Builder, io: &TickIo, h: &Hreg, count: &[Q], cfg: DecCfg) {
    assert!(io.park.is_none() && io.cflag.is_none());
    let sc = decoder::open(c, io, cfg);
    c.cx(sc.amb, io.typ);
    c.cx(sc.d, io.typ);
    decrement(c, count, sc.amb);
    decoder::shift_out(c, sc.amb, io.typ, &h.wires);
    decoder::close(c, io, sc);
}
fn newpark(c: &mut Builder, z: Q, typ: Q) -> Q {
    let g = c.alloc_qubit();
    c.x(typ);
    c.ccx(z, typ, g);
    c.x(typ);
    g
}
fn clear_newpark(c: &mut Builder, z: Q, typ: Q, g: Q) {
    c.x(typ);
    and_erase(c, z, typ, g);
    c.x(typ);
}
/// Reuse existing middle r bits64..71, outside decoder top64, r0 and park top14.
/// On NEW park r=p; afterwards its retained record is p XOR Hcount in these bits.
/// Forward and inverse are independently emitted. Every eligible public tick costs9CCX.
pub fn deferred(c: &mut Builder, r: &[Q], p: &[bool], role: &[Q], z: Q, typ: Q, inverse: bool) {
    assert_eq!(role.len(), 8);
    assert!(r.len() >= 256);
    assert_eq!(p.len(), r.len());
    let g = newpark(c, z, typ);
    let _ = inverse; // controlled swap is self-inverse; call order is independent.
    for j in 0..8 {
        if p[64 + j] {
            c.cx(g, r[64 + j]);
        }
    }
    for j in 0..8 {
        fredkin(c, g, role[j], r[64 + j]);
    }
    for j in 0..8 {
        if p[64 + j] {
            c.cx(g, r[64 + j]);
        }
    }
    clear_newpark(c, z, typ, g);
}
/// Exact highest-one-position XOR query. Input must contain a sentinel.
/// Telescoping prefix ORs remove redundant output CNOTs. Full fresh workspace is
/// available at the public endpoint after the known r bank's other248 wires retire.
pub fn index_xor(c: &mut Builder, h: &[Q], out: &[Q]) {
    assert!(h.len() >= 2);
    let mut previous = h[h.len() - 1];
    let mut nodes = Vec::new();
    for pos in (0..h.len() - 1).rev() {
        let q = c.alloc_qubit();
        c.cx(h[pos], q);
        c.cx(previous, q);
        c.ccx(h[pos], previous, q);
        nodes.push((h[pos], previous, q));
        previous = q;
    }
    let prefix = |pos: usize| {
        if pos == h.len() - 1 {
            h[pos]
        } else {
            nodes[h.len() - 2 - pos].2
        }
    };
    for pos in 1..h.len() {
        for (j, &target) in out.iter().enumerate() {
            if pos % (1usize << j) == 0 {
                c.cx(prefix(pos), target);
            }
        }
    }
    for (a, b, q) in nodes.into_iter().rev() {
        c.cx(a, q);
        c.cx(b, q);
        and_erase(c, a, b, q);
    }
}
/// Wide immediate handoff, priced as rejection comparator. Borrow r nodes only
/// unitarily (their values are foreign when !newpark); never HMR foreign r.
pub fn immediate(
    c: &mut Builder,
    h: &[Q],
    r: &[Q],
    p: &[bool],
    role: &[Q],
    z: Q,
    typ: Q,
    inverse: bool,
) {
    let g = newpark(c, z, typ);
    assert!(h.len() - 1 <= r.len());
    for (j, &q) in r.iter().enumerate() {
        if p[j] {
            c.cx(g, q);
        }
    }
    let mut previous = h[h.len() - 1];
    let mut nodes = Vec::new();
    for pos in (0..h.len() - 1).rev() {
        let q = r[h.len() - 2 - pos];
        c.cx(h[pos], q);
        c.cx(previous, q);
        c.ccx(h[pos], previous, q);
        nodes.push((h[pos], previous, q));
        previous = q;
    }
    let prefix = |pos: usize| {
        if pos == h.len() - 1 {
            h[pos]
        } else {
            nodes[h.len() - 2 - pos].2
        }
    };
    if inverse {
        for pos in 1..h.len() {
            for (j, &out) in role.iter().enumerate() {
                if pos % (1usize << j) == 0 {
                    c.ccx(g, prefix(pos), out);
                }
            }
        }
    } else {
        let q = c.alloc_qubit();
        for (j, &bit) in role.iter().enumerate() {
            fredkin(c, g, bit, q);
            let m = c.alloc_bit();
            c.hmr(q, m);
            for pos in 1..h.len() {
                if pos % (1usize << j) == 0 {
                    c.cz_if(g, prefix(pos), m);
                }
            }
            c.free_bit(m);
        }
        c.free(q);
    }
    for (a, b, q) in nodes.into_iter().rev() {
        c.ccx(a, b, q);
        c.cx(b, q);
        c.cx(a, q);
    }
    for (j, &q) in r.iter().enumerate() {
        if p[j] {
            c.cx(g, q);
        }
    }
    clear_newpark(c, z, typ, g);
}

pub struct Probe {
    pub h: Vec<Q>,
    pub r: Vec<Q>,
    pub role: Vec<Q>,
    pub split: Vec<Q>,
    pub z: Q,
    pub typ: Q,
    pub passenger: Vec<Q>,
    pub foreign: Vec<Q>,
    pub ops: Vec<crate::circuit::Op>,
    pub dims: (usize, usize),
    pub begin: usize,
    pub mid: usize,
    pub epoch: usize,
    pub peak: usize,
    pub standing: usize,
}
pub fn handoff_probe(n: usize, wide_immediate: bool, check_parked_decoder: bool) -> Probe {
    let mut c = Builder::new();
    let h = c.alloc_qubits(n);
    let r = c.alloc_qubits(256);
    let role = c.alloc_qubits(8);
    let split = c.alloc_qubits(5);
    let z = c.alloc_qubit();
    let typ = c.alloc_qubit();
    let passenger = c.alloc_qubits(256);
    let foreign = c.alloc_qubits(985 - c.active_qubits() as usize);
    let p = (0..256)
        .map(|j| crate::point_add::SECP256K1_P.bit(j))
        .collect::<Vec<_>>();
    let begin = c.op_count();
    if wide_immediate {
        immediate(&mut c, &h, &r, &p, &role, z, typ, false)
    } else {
        deferred(&mut c, &r, &p, &role, z, typ, false)
    }
    let mid = c.op_count();
    if check_parked_decoder {
        let s = foreign[..256].to_vec();
        let q = c.alloc_qubit();
        c.x(z);
        let io = TickIo {
            s: &s,
            r: &r,
            e: 256,
            en: Some(z),
            typ: q,
            cflag: None,
            park: None,
        };
        let hh = Hreg { wires: h.clone() };
        let cfg = DecCfg { w: 64, room: 13 };
        decoder::push(&mut c, &io, &hh, cfg);
        decoder::pop(&mut c, &io, &hh, cfg);
        c.x(z);
        c.free(q);
    }
    let epoch = c.op_count();
    if wide_immediate {
        immediate(&mut c, &h, &r, &p, &role, z, typ, true)
    } else {
        deferred(&mut c, &r, &p, &role, z, typ, true)
    }
    assert_eq!(c.active_qubits(), 985);
    let dims = c.i13_dims();
    let peak = c.peak_total() as usize;
    let ops = c.take_ops();
    Probe {
        h,
        r,
        role,
        split,
        z,
        typ,
        passenger,
        foreign,
        ops,
        dims,
        begin,
        mid,
        epoch,
        peak,
        standing: 985,
    }
}
pub struct CountProbe {
    pub s: Vec<Q>,
    pub r: Vec<Q>,
    pub h: Vec<Q>,
    pub count: Vec<Q>,
    pub typ: Q,
    pub en: Q,
    pub foreign: Vec<Q>,
    pub ops: Vec<crate::circuit::Op>,
    pub dims: (usize, usize),
    pub begin: usize,
    pub mid: usize,
    pub peak: usize,
    pub baseline: bool,
}
pub fn decoder_probe(e: usize, baseline: bool) -> CountProbe {
    let mut c = Builder::new();
    let s = c.alloc_qubits(e);
    let r = c.alloc_qubits(e);
    let h = c.alloc_qubits(if e == 256 {
        if baseline {
            201
        } else {
            202
        }
    } else {
        7
    });
    let count = c.alloc_qubits(8);
    let typ = c.alloc_qubit();
    let en = c.alloc_qubit();
    let standing = if baseline && e == 256 { 984 } else { 985 };
    let foreign = c.alloc_qubits(standing - c.active_qubits() as usize);
    let hh = Hreg { wires: h.clone() };
    let io = TickIo {
        s: &s,
        r: &r,
        e,
        en: Some(en),
        typ,
        cflag: None,
        park: None,
    };
    let cfg = DecCfg {
        w: 64,
        room: if baseline { 15 } else { 7 },
    };
    let begin = c.op_count();
    if baseline {
        decoder::push(&mut c, &io, &hh, cfg);
    } else {
        push_count(&mut c, &io, &hh, &count, cfg);
    }
    let mid = c.op_count();
    if baseline {
        decoder::pop(&mut c, &io, &hh, cfg);
    } else {
        pop_count(&mut c, &io, &hh, &count, cfg);
    }
    assert_eq!(c.active_qubits() as usize, standing);
    let dims = c.i13_dims();
    let peak = c.peak_total() as usize;
    let ops = c.take_ops();
    CountProbe {
        s,
        r,
        h,
        count,
        typ,
        en,
        foreign,
        ops,
        dims,
        begin,
        mid,
        peak,
        baseline,
    }
}
pub struct EndpointProbe {
    pub h: Vec<Q>,
    pub role: Vec<Q>,
    pub split: Vec<Q>,
    pub r_initial: Vec<Q>,
    pub r_restored: Vec<Q>,
    pub foreign: Vec<Q>,
    pub ops: Vec<crate::circuit::Op>,
    pub dims: (usize, usize),
    pub begin: usize,
    pub mid: usize,
    pub peak: usize,
}
pub fn endpoint_probe(n: usize) -> EndpointProbe {
    let mut c = Builder::new();
    let h = c.alloc_qubits(n);
    let r = c.alloc_qubits(256);
    let role = c.alloc_qubits(8);
    let split = c.alloc_qubits(5);
    let foreign = c.alloc_qubits(985 - c.active_qubits() as usize);
    let p = crate::point_add::SECP256K1_P;
    let begin = c.op_count();
    // All lanes are parked at this public endpoint. Release the known p padding,
    // leaving the8 record wires live; no new count bank is allocated.
    for j in 0..256 {
        if p.bit(j) {
            c.x(r[j]);
        }
        if !(64..72).contains(&j) {
            c.free(r[j]);
        }
    }
    let record = r[64..72].to_vec();
    index_xor(&mut c, &h, &record);
    let mid = c.op_count();
    index_xor(&mut c, &h, &record);
    let mut restored = vec![record[0]; 256];
    for j in 0..256 {
        restored[j] = if (64..72).contains(&j) {
            record[j - 64]
        } else {
            c.alloc_qubit()
        };
        if p.bit(j) {
            c.x(restored[j]);
        }
    }
    let dims = c.i13_dims();
    let peak = c.peak_total() as usize;
    let ops = c.take_ops();
    EndpointProbe {
        h,
        role,
        split,
        r_initial: r,
        r_restored: restored,
        foreign,
        ops,
        dims,
        begin,
        mid,
        peak,
    }
}
