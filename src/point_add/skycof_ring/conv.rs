//! Switch from the public layout (Skywalk rails, separate cofactor fields) to the ring layout at a tick
//! before any park, and back.
//!
//! On the public walk the rails are `{+-u, u + v}`: the `u + v` rail is never negative, it is `R2` after an
//! A step and `R1` after a B or C step, and the sign of the `u` rail is the parity of the C steps so far
//! (the ring's `sign` wire). So the switch is:
//! 1. swap the rails when the last letter is not A (`R1 = +-u`, `R2 = u + v`);
//! 2. dispose of the last letter with the public decoder;
//! 3. `R1`'s sign wire becomes `sign`; `u = |R1|` on the low wires; `R2`'s top wire is free (0);
//!    `v = (u + v) - u`;
//! 4. `KA = bits(s)` and `VB = bits(v)` by leading-one deposits (constant cut);
//! 5. merge the fields into `A = [u | s]` and `B = [v | r]`: where the public fields overlap, the cofactor
//!    cell is XORed into the value cell and then cleared under `[j < KA]` (A) or `[256 - j >= VB]` (B),
//!    which holds exactly where the cell belongs to the cofactor. The cleared cells are released.
//! The odometer's wires (all zero before the park window) are released for the boundary registers; the
//! ring walk allocates its odometer again before its park window.
use super::lod::{lod_deposit, Room};
use super::mc::Thr;
use super::ring::{kbits, Ring};
use super::rwalk::WEnv;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::skycof::adder;
use crate::point_add::skycof::decoder::Hreg;
use crate::point_add::skycof::tick::Cof;
use crate::point_add::skycof::walk::{self as pw, Envelope, Prefix, WalkParams};
use crate::point_add::skycof_mm as mm;

/// Ring state right after the switch, plus what the walk back needs to rebuild the public layout.
pub struct Switched {
    pub ring: Ring,
    pub sign: Q,
    pub h: Hreg,
    meta: Meta,
}

/// Classical shape of the public layout at the switch.
pub struct Meta {
    prev: Vec<crate::point_add::skycof::tick::PrevWidths>,
    w: usize,
    cw: usize,
    odo_bits: usize,
}

impl Switched {
    pub fn split(self) -> (Ring, Q, Hreg, Meta) {
        (self.ring, self.sign, self.h, self.meta)
    }
    pub fn join(ring: Ring, sign: Q, h: Hreg, meta: Meta) -> Switched {
        Switched { ring, sign, h, meta }
    }
}

fn ctrace(c: &mut Builder, what: &str, t: usize) {
    if crate::point_add::skycof::pointadd::knob_flag("SKYCOF_STEP_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_CONV t={t} {what} live={} peak={pk}", c.active_qubits());
    }
}

fn room(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

fn fredkin(c: &mut Builder, ctl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctl, a, b);
    c.cx(b, a);
}

/// `tgt ^= [reg > k]`: the XOR of the exclusive terms "highest differing bit i has reg_i = 1, k_i = 0",
/// each a multi-controlled X (clean ladder when the room allows, borrowed wires otherwise).
fn gt_const(c: &mut Builder, reg: &[Q], k: usize, tgt: Q, dirty: &[Q], cap: usize) {
    use crate::point_add::skycof::k2dec::{mcx, L};
    let len = reg.len();
    if k >= (1usize << len) - 1 {
        return;
    }
    for i in (0..len).rev() {
        if (k >> i) & 1 == 1 {
            continue;
        }
        let mut lits = vec![L(reg[i], false)];
        for jj in i + 1..len {
            lits.push(L(reg[jj], (k >> jj) & 1 == 0));
        }
        mcx(c, &lits, tgt, dirty, cap);
    }
}

/// `x <- (x xor g) + g` on the low wires (conditional negation, an involution), with borrowed wires `bw`
/// (any state, restored; `bw.len() >= x.len()`) and a wire `z` holding 0 as carry-in:
/// `+ g = - g (bw) - g (NOT bw)` (mod 2^len), two controlled subtractions.
fn cneg(c: &mut Builder, x: &[Q], g: Q, bw: &[Q], z: Q, cap: usize) {
    for &q in x {
        c.cx(g, q);
    }
    let bw = &bw[..x.len()];
    adder::sub(c, Some(g), bw, x, Some(z), Some(cap));
    c.x_all(bw);
    adder::sub(c, Some(g), bw, x, Some(z), Some(cap));
    c.x_all(bw);
}

/// `out ^= bits(x)` for `bits(x) >= rlo` (cells below `rlo` never read).
fn deposit_bits(c: &mut Builder, x: &[Q], rlo: usize, out: &[Q], cap: usize) {
    let top = Thr { reg: &[], pairs: vec![(0, x.len())] };
    lod_deposit(c, x, &top, rlo, out, &|r| r, None, Room::Cap(cap));
}

/// Zone of overlapping cells: cofactor indices `j` in `[257 - (w-1), cw)` (value cell `256 - j`).
fn zone(n: usize, wv: usize, cw: usize) -> std::ops::Range<usize> {
    let lo = n - wv;
    lo.min(cw)..cw
}

pub fn fwd(c: &mut Builder, renv: &WEnv, p: &WalkParams, penv: &Envelope, pf: Prefix, t1: usize) -> Switched {
    let n = renv.n;
    let cap = p.cap;
    let Prefix { rails, cof, mut h, odo, typ, prev } = pf;
    let Rails { r1, r2 } = rails;
    let w = r1.len();
    assert_eq!(r2.len(), w);
    let Cof { s, r } = cof;
    let cw = s.len();
    assert_eq!(r.len(), cw);
    let wv = w - 1;
    // 1. R1 = +-u, R2 = u + v
    c.x(typ);
    for i in 0..w {
        fredkin(c, typ, r1[i], r2[i]);
    }
    c.x(typ);
    // 2. the last letter
    {
        let cofr = Cof { s: s.clone(), r: r.clone() };
        let dirty: Vec<Q> = r1.iter().chain(r2.iter()).copied().collect();
        pw::dispose_fwd(c, p, penv, t1 - 1, typ, &cofr, &mut h, &odo, &dirty);
    }
    ctrace(c, "conv.f.disposed", t1);
    // 3. sign, u, v
    let sign = r1[w - 1];
    assert!(r.len() >= wv, "switch: cofactor register narrower than the rails");
    cneg(c, &r1[..wv], sign, &r, r2[w - 1], cap);
    adder::sub(c, None, &r1[..wv], &r2[..wv], Some(r2[w - 1]), Some(cap));
    c.free(r2[w - 1]);
    c.free_vec(&odo);
    let z = renv.z[t1].expect("switch tick needs a ring window");
    ctrace(c, "conv.f.uv", t1);
    // 4./5. A: KA = bits(s), merge
    let kb = kbits(n);
    let ka = c.alloc_qubits(kb);
    deposit_bits(c, &s, z.ka.lo.max(1), &ka, cap);
    for j in zone(n, wv, cw) {
        let pos = n - 1 - j;
        let hold = r1[pos];
        c.cx(s[j], hold);
        let th = c.alloc_qubit();
        gt_const(c, &ka, j, th, &r2[..wv], cap);
        c.ccx(th, hold, s[j]);
        gt_const(c, &ka, j, th, &r2[..wv], cap);
        c.release_clean(th);
        c.free(s[j]);
    }
    let a: Vec<Q> = (0..n).map(|i| if i < wv { r1[i] } else { s[n - 1 - i] }).collect();
    ctrace(c, "conv.f.A", t1);
    // B: VB = bits(v), merge
    let vb = c.alloc_qubits(kb);
    deposit_bits(c, &r2[..wv], z.vb.lo.max(1), &vb, cap);
    for j in zone(n, wv, cw) {
        let pos = n - 1 - j;
        let hold = r2[pos];
        c.cx(r[j], hold);
        let th = c.alloc_qubit();
        gt_const(c, &vb, pos, th, &a[..wv], cap); // th = [VB > pos]: the cell is v's
        c.x(th);
        c.ccx(th, hold, r[j]);
        c.x(th);
        gt_const(c, &vb, pos, th, &a[..wv], cap);
        c.release_clean(th);
        c.free(r[j]);
    }
    let b: Vec<Q> = (0..n).map(|i| if i < wv { r2[i] } else { r[n - 1 - i] }).collect();
    let ring = Ring { n, cap: Some(cap), a, b, ka, vb, gate: None };
    ctrace(c, "conv.f.B", t1);
    Switched { ring, sign, h, meta: Meta { prev, w, cw, odo_bits: p.odo_bits } }
}

/// Exact inverse of [`fwd`].
pub fn rev(c: &mut Builder, renv: &WEnv, p: &WalkParams, penv: &Envelope, sw: Switched, t1: usize) -> Prefix {
    let n = renv.n;
    let cap = p.cap;
    let Switched { ring, sign, mut h, meta } = sw;
    let Meta { prev, w, cw, odo_bits } = meta;
    let wv = w - 1;
    let Ring { a, b, ka, vb, .. } = ring;
    let z = renv.z[t1].expect("switch tick needs a ring window");
    // B back
    let mut r: Vec<Option<Q>> = vec![None; cw];
    let mut r2: Vec<Q> = b[..wv].to_vec();
    for j in 0..cw {
        let pos = n - 1 - j;
        if pos >= wv {
            r[j] = Some(b[pos]);
        }
    }
    for j in zone(n, wv, cw).rev() {
        let pos = n - 1 - j;
        let hold = r2[pos];
        let rj = c.alloc_qubit();
        let th = c.alloc_qubit();
        gt_const(c, &vb, pos, th, &a[..wv], cap);
        c.x(th);
        c.ccx(th, hold, rj);
        c.x(th);
        gt_const(c, &vb, pos, th, &a[..wv], cap);
        c.release_clean(th);
        c.cx(rj, hold);
        r[j] = Some(rj);
    }
    ctrace(c, "conv.r.Bun", t1);
    deposit_bits(c, &r2, z.vb.lo.max(1), &vb, cap);
    c.free_vec(&vb);
    ctrace(c, "conv.r.VB", t1);
    // A back
    let mut s: Vec<Option<Q>> = vec![None; cw];
    let mut r1: Vec<Q> = a[..wv].to_vec();
    for j in 0..cw {
        let pos = n - 1 - j;
        if pos >= wv {
            s[j] = Some(a[pos]);
        }
    }
    for j in zone(n, wv, cw).rev() {
        let pos = n - 1 - j;
        let hold = r1[pos];
        let sj = c.alloc_qubit();
        let th = c.alloc_qubit();
        gt_const(c, &ka, j, th, &r2, cap);
        c.ccx(th, hold, sj);
        gt_const(c, &ka, j, th, &r2, cap);
        c.release_clean(th);
        c.cx(sj, hold);
        s[j] = Some(sj);
    }
    let s: Vec<Q> = s.into_iter().map(|x| x.unwrap()).collect();
    let r: Vec<Q> = r.into_iter().map(|x| x.unwrap()).collect();
    ctrace(c, "conv.r.Aun", t1);
    deposit_bits(c, &s, z.ka.lo.max(1), &ka, cap);
    c.free_vec(&ka);
    ctrace(c, "conv.r.KA", t1);
    // 3 back
    let odo = c.alloc_qubits(odo_bits);
    let top2 = c.alloc_qubit();
    adder::add(c, None, &r1, &r2, Some(top2), Some(cap));
    cneg(c, &r1, sign, &r, top2, cap);
    r2.push(top2);
    r1.push(sign);
    // 2 back: recreate the last letter
    let cof = Cof { s, r };
    let dirty: Vec<Q> = r1.iter().chain(r2.iter()).copied().collect();
    ctrace(c, "conv.r.uv", t1);
    let typ = pw::dispose_rev(c, p, penv, t1 - 1, &cof, &mut h, &odo, &dirty);
    ctrace(c, "conv.r.typ", t1);
    // 1 back
    c.x(typ);
    for i in 0..w {
        fredkin(c, typ, r1[i], r2[i]);
    }
    c.x(typ);
    Prefix { rails: Rails { r1, r2 }, cof, h, odo, typ, prev }
}
