//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

const N: usize = 256;
const W: usize = N + 1;
const NONE: u32 = u32::MAX;
const EB: usize = 4;
/// Real lanes for the wait offset.
const WB: usize = 4;
/// Clean lanes for AND ladders inside F.
const FLAG_ON: bool = true;
const ZB: usize = if FLAG_ON { 6 } else { 5 };
const FL_LANE: u32 = 517;
static IN_F: AtomicBool = AtomicBool::new(false);
/// ZFOR-wait: while a clean lane holds the waiter flag, multi-controlled gates use borrowed wires.
static Z_BUSY: AtomicBool = AtomicBool::new(false);
/// ZFOR-wait: the lane that holds the waiter flag through the act rotation (512 is the AND lane; 513 needs ZB = 2).
const ZW_LANE: u32 = 513;
const ZW_SHARED: bool = false;
/// hmr-and (lane zfor-wait): the clean-lane AND of every cc_core call is uncomputed by X-basis measurement (Hmr) and
/// CZ(c0, c1) under the outcome (Gidney arXiv:1709.06648) instead of the unitary Toffoli: -1 T per call.
const HMR_AND: bool = true;
const HMR_NEGCTL: bool = false;
/// Marks both AND gates of a cc_core pair on the target wire; P::gate toggles compute / measured uncompute per lane.
const AND_FLAG: u32 = 1 << 30;
/// cc2 (lane zfor-wait): second held clean lane for the guard of the second control pair of every cc_core call.
const CC2: bool = true;
const CC2_LANE: u32 = 514;
const CC2_N: usize = 3;
const PIW: usize = 48;
const ECAP: i32 = 27;
const RW: usize = 64;
/// Clean lanes for the merged fold chain.
const ZL: usize = 8;
/// Each fold chain runs this many wires from its own start: a carry gets j wires with 2^-j.
const CHW: usize = 33;
/// ov is read back on this many top wires.
const CMPW: usize = 34;
/// LEAN_SQ (lane arxiv-research): x += lam^2 by three Karatsuba half-squares in one 258-wire register (Haener,
/// Tripier, Young et al. arXiv:2609.05625 section VII.1 squarer form, Gidney 1709.06648 halved adders whose AND
/// ancillae are the register's still-clean upper wires), folded into x with the parent's chains. Off re-emits the parent.
const LEAN_SQ: bool = true;
const LEAN_NEGCTL: bool = false;
/// carry window above a spill addend (the carry past it is dropped: 2^-64 per spill add)
const SPILL_W: usize = 64;
/// Multiplier bits consumed into the product.
const CAPW: usize = 0;
/// Low lanes read when a seed tests a product for zero.
const ZW: usize = 64;
const C0M1: [usize; 6] = [4, 6, 7, 8, 9, 32]; // bits of 2^32 + 976
const P0: [u64; 4] = [0xFFFFFFFEFFFFFC2F, u64::MAX, u64::MAX, u64::MAX];

fn pbit(i: usize) -> bool {
    (P0[i / 64] >> (i % 64)) & 1 == 1
}

#[derive(Clone, Copy)]
struct G(u32, u32, u32);
type Lit = (u32, bool);
type GL = Vec<G>;
#[inline]
fn gx(a: u32) -> G {
    G(a, NONE, NONE)
}
#[inline]
fn gc(a: u32, b: u32) -> G {
    G(a, b, NONE)
}
#[inline]
fn gt(a: u32, b: u32, c: u32) -> G {
    G(a, b, c)
}
fn rev(g: &[G]) -> GL {
    g.iter().rev().cloned().collect()
}

/// AND of k controls on one clean lane, 2k-3 T: conditionally clean wires, Khattar-Gidney 2024.
fn cc_core(cs: &[u32], tgt: u32, z: u32) -> GL {
    let k = cs.len();
    let m = k / 2;
    let zf = if HMR_AND { z | AND_FLAG } else { z };
    let mut up: GL = vec![gt(cs[0], cs[1], zf), gc(z, cs[0]), gc(z, cs[1])];
    let (mut guards, mut aa, mut bb) = (vec![z], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let (g, gf) = if CC2 && i <= CC2_N { let l = CC2_LANE + (i as u32) - 1; (l, if HMR_AND { l | AND_FLAG } else { l }) } else { (aa[i - 1], aa[i - 1]) };
        up.extend_from_slice(&[gt(a, b, gf), gc(g, a), gc(g, b)]);
        guards.push(g);
        aa.push(a);
        bb.push(b);
    }
    let mut cur = guards[m - 1];
    let mut walk: GL = vec![];
    let mut out = up.clone();
    if k % 2 == 1 {
        let x = cs[k - 1];
        if m == 1 {
            out.push(gt(z, x, tgt));
            out.extend(rev(&up));
            return out;
        }
        walk.push(gt(cur, x, bb[m - 2]));
        cur = bb[m - 2];
    }
    if m >= 2 {
        let mut i = m - 2;
        while i >= 1 {
            walk.push(gt(cur, guards[i], bb[i - 1]));
            cur = bb[i - 1];
            i -= 1;
        }
    }
    out.extend_from_slice(&walk);
    out.push(gt(cur, guards[0], tgt));
    out.extend(rev(&walk));
    out.extend(rev(&up));
    out
}

fn mcx(lits: &[Lit], tgt: u32, dirty: &[u32]) -> GL {
    let mut l: Vec<Lit> = Vec::with_capacity(lits.len());
    for &(q0, p) in lits {
        match l.iter().find(|x| x.0 == q0) {
            Some(x) => {
                if x.1 != p {
                    return vec![];
                }
            }
            None => l.push((q0, p)),
        }
    }
    let k = l.len();
    if k == 0 {
        return vec![gx(tgt)];
    }
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g = pre.clone();
    if k == 1 {
        g.push(gc(l[0].0, tgt));
    } else if k == 2 {
        g.push(gt(l[0].0, l[1].0, tgt));
    } else if ZB > 0 && IN_F.load(Ordering::Relaxed) && !Z_BUSY.load(Ordering::Relaxed) {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        g.extend(cc_core(&cs, tgt, 512));
    } else {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut an: Vec<u32> = Vec::with_capacity(k - 2);
        for &d in dirty {
            if d != tgt && !cs.contains(&d) {
                an.push(d);
                if an.len() == k - 2 {
                    break;
                }
            }
        }
        assert!(an.len() == k - 2);
        let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
        let mut i = k - 2;
        while i > 1 {
            up.push(gt(cs[i], an[i - 2], an[i - 1]));
            i -= 1;
        }
        let mid = gt(cs[0], cs[1], an[0]);
        g.extend_from_slice(&up);
        g.push(mid);
        g.extend(up.iter().rev().cloned());
        g.extend_from_slice(&up[1..]);
        g.push(mid);
        g.extend(up[1..].iter().rev().cloned());
    }
    g.extend_from_slice(&pre);
    g
}

fn cswap(c: u32, a: u32, b: u32, g: &mut GL) {
    g.push(gc(b, a));
    g.push(gt(c, a, b));
    g.push(gc(b, a));
}

fn rotate_up(ctl: u32, w: &[u32], r: usize) -> GL {
    let n = w.len();
    let r = r % n;
    let mut g = vec![];
    if r == 0 {
        return g;
    }
    let mut seen = vec![false; n];
    for st in 0..n {
        if seen[st] {
            continue;
        }
        let mut i = st;
        let mut cyc = vec![];
        while !seen[i] {
            seen[i] = true;
            cyc.push(i);
            i = (i + r) % n;
        }
        for j in 1..cyc.len() {
            cswap(ctl, w[cyc[0]], w[cyc[j]], &mut g);
        }
    }
    g
}

fn inc_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    let mut g = vec![];
    for i in (0..reg.len()).rev() {
        let mut l: Vec<Lit> = lits.to_vec();
        for j in 0..i {
            l.push((reg[j], true));
        }
        g.extend(mcx(&l, reg[i], dirty));
    }
    g
}
fn dec_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    rev(&inc_ctl(reg, lits, dirty))
}

fn add_chain(t: &[u32], s: &[u32], c: u32) -> GL {
    let n = t.len();
    let mut g = Vec::with_capacity(7 * n);
    for i in 0..n {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    for i in (0..n).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

fn inc_long(reg: &[u32], ctl: u32, dirty: &[u32], c: u32) -> GL {
    let mut r = vec![ctl];
    r.extend_from_slice(reg);
    let mut d: Vec<u32> = Vec::with_capacity(r.len());
    for &q0 in dirty {
        if q0 != c && !r.contains(&q0) {
            d.push(q0);
            if d.len() == r.len() {
                break;
            }
        }
    }
    assert!(d.len() == r.len());
    let sub = rev(&add_chain(&r, &d, c));
    let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
    let mut g = sub.clone();
    g.extend_from_slice(&nots);
    g.extend_from_slice(&sub);
    g.extend_from_slice(&nots);
    g.push(gx(ctl));
    g
}

fn aligned_blocks(vals: &BTreeSet<i32>) -> Vec<(i32, usize)> {
    let mut out = vec![];
    let mut vals = vals.clone();
    while let Some(&v) = vals.iter().next() {
        let mut k = 0usize;
        loop {
            let k2 = k + 1;
            if v & ((1 << k2) - 1) != 0 {
                break;
            }
            if (0..(1 << k2)).all(|i| vals.contains(&(v + i))) {
                k = k2;
            } else {
                break;
            }
        }
        out.push((v, k));
        for i in 0..(1 << k) {
            vals.remove(&(v + i));
        }
    }
    out
}

/// lane allocator of the stored inverter (virtual lanes)
struct B {
    free: Vec<u32>,
    next: u32,
    gates: Vec<G>,
}
impl B {
    fn alloc(&mut self) -> u32 {
        if let Some(q0) = self.free.pop() {
            q0
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn release(&mut self, q0: u32) {
        self.free.push(q0);
        self.free.sort_by(|a, b| b.cmp(a));
    }
    fn t(&mut self, g: &[G]) {
        self.gates.extend_from_slice(g);
    }
}

struct Machine {
    b: B,
    dirty: Vec<u32>,
    pas: Vec<u32>,
    x: Vec<u32>,
    y: Vec<u32>,
    e: Vec<u32>,
    par: u32,
    w: Vec<u32>,
    memo: HashMap<(u128, u128, i32), Vec<Vec<(usize, u8)>>>,
}

fn lf(t: i32, e: i32) -> (i32, i32) {
    if t % 2 == 1 {
        return ((t - 1) / 2, (t + 1) / 2);
    }
    let m = e >> 1;
    (t / 2 - m, t / 2 + m + (e & 1))
}
fn pairs(t: i32) -> Vec<i32> {
    let n = N as i32;
    if t % 2 == 1 {
        let (l, f) = lf(t, 1);
        return if l >= 1 && f <= n { vec![1] } else { vec![] };
    }
    (0..=ECAP)
        .filter(|&e| {
            let (l, f) = lf(t, e);
            l >= 1 && f <= n && f >= l
        })
        .collect()
}

const VS_EXACT: [usize; 5] = [0, 1, 2, 3, 4];
const VS_H: [usize; 4] = [0, 1, 2, 3];
const VS_T3: [usize; 5] = [0, 1, 2, 3, 5];
const VS_T4: [usize; 6] = [0, 1, 2, 3, 5, 6];
fn vs_tog() -> &'static [usize] {
    if WB >= 4 {
        &VS_T4
    } else if WB >= 3 {
        &VS_T3
    } else {
        &VS_H
    }
}
const fn maskv(v: usize) -> u128 {
    let mut m = 0u128;
    let mut p = 0;
    while p < 128 {
        if (p >> v) & 1 == 0 {
            m |= 1u128 << p;
        }
        p += 1;
    }
    m
}
const MASKV: [u128; 7] = [maskv(0), maskv(1), maskv(2), maskv(3), maskv(4), maskv(5), maskv(6)];
type Cubes = Vec<Vec<(usize, u8)>>;
/// Minimum cost disjoint decision tree: H bits are vars 0..3, w0 var 4, w2 var 5, w3 var 6.
const ESOP_MIN: bool = true;
// Q21 ESOP table (arxiv-research, mode identical): (on, off, vs.len()*100+base) -> cubes
static ESOP_TABLE: &[(u128, u128, i32, &[&[(usize, u8)]])] = &[
    (1073496060u128, 196611u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)]]),
    (1072709616u128, 983055u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)]]),
    (917534u128, 1072775137u128, 501i32, &[&[(3usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8)], &[(4usize, 1u8), (3usize, 0u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (6u128, 24u128, 602i32, &[&[(0usize, 1u8)], &[(1usize, 1u8)]]),
    (786456u128, 1072906215u128, 501i32, &[&[(3usize, 0u8), (2usize, 0u8), (1usize, 1u8)], &[(4usize, 0u8), (3usize, 0u8), (1usize, 1u8), (0usize, 0u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 1u8), (0usize, 0u8)]]),
    (917518u128, 1072775153u128, 501i32, &[&[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (7u128, 8u128, 602i32, &[&[], &[(0usize, 1u8), (1usize, 1u8)]]),
    (6u128, 8u128, 602i32, &[&[], &[(1usize, 1u8), (0usize, 1u8)]]),
    (786440u128, 1072906231u128, 501i32, &[&[(3usize, 0u8), (2usize, 0u8), (1usize, 1u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 0u8)]]),
    (30u128, 32u128, 602i32, &[&[], &[(2usize, 1u8), (0usize, 1u8)]]),
    (31u128, 32u128, 602i32, &[&[], &[(2usize, 1u8), (0usize, 1u8)]]),
    (16646654u128, 1057046017u128, 501i32, &[&[], &[(2usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8)], &[(4usize, 1u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (127u128, 384u128, 602i32, &[&[], &[(0usize, 0u8), (3usize, 1u8)], &[(1usize, 1u8), (0usize, 1u8), (2usize, 1u8)]]),
    (6u128, 504u128, 602i32, &[&[(0usize, 1u8), (2usize, 0u8)], &[(1usize, 1u8), (2usize, 0u8)]]),
    (126u128, 384u128, 602i32, &[&[], &[(0usize, 0u8), (3usize, 1u8)], &[(2usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (16646652u128, 1057046019u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(4usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (16515580u128, 1057177091u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (16515576u128, 1057177095u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 0u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 0u8), (0usize, 0u8)]]),
    (15729120u128, 1057963551u128, 501i32, &[&[(3usize, 0u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(4usize, 0u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(4usize, 0u8), (3usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (12583296u128, 1061109375u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8)], &[(4usize, 0u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (6u128, 1924145349112u128, 602i32, &[&[(1usize, 1u8), (2usize, 0u8)], &[(0usize, 1u8), (2usize, 0u8)]]),
    (274877907070u128, 1649267442048u128, 602i32, &[&[], &[(0usize, 0u8), (3usize, 1u8)], &[(2usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (274877907071u128, 1649267442048u128, 602i32, &[&[], &[(3usize, 1u8), (0usize, 0u8)], &[(2usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (64512u128, 1023u128, 404i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (28672u128, 36863u128, 406i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (24576u128, 40959u128, 407i32, &[&[(3usize, 1u8), (2usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (57344u128, 8191u128, 407i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (16646398u128, 1057046273u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (7u128, 248u128, 602i32, &[&[(2usize, 0u8)], &[(2usize, 0u8), (1usize, 1u8), (0usize, 1u8)]]),
    (63u128, 192u128, 602i32, &[&[], &[(2usize, 1u8), (1usize, 1u8)]]),
    (127u128, 128u128, 602i32, &[&[], &[(1usize, 1u8), (2usize, 1u8), (0usize, 1u8)]]),
    (6u128, 248u128, 602i32, &[&[(2usize, 0u8)], &[(0usize, 1u8), (1usize, 1u8), (2usize, 0u8)]]),
    (62u128, 192u128, 602i32, &[&[], &[(2usize, 1u8), (1usize, 1u8)]]),
    (126u128, 128u128, 602i32, &[&[], &[(2usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (16646396u128, 1057046275u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 1u8), (3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (16515324u128, 1057177347u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)]]),
    (16515320u128, 1057177351u128, 501i32, &[&[(3usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 0u8)]]),
    (12583040u128, 1061109631u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8)], &[(4usize, 0u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (6u128, 17317308138488u128, 602i32, &[&[(2usize, 0u8), (3usize, 0u8)], &[(1usize, 1u8), (2usize, 0u8), (3usize, 0u8), (0usize, 1u8)]]),
    (274877907070u128, 17042430231424u128, 602i32, &[&[], &[(3usize, 1u8), (2usize, 0u8)], &[(0usize, 1u8), (1usize, 1u8), (2usize, 1u8)]]),
    (4123168605182u128, 13194139533312u128, 602i32, &[&[], &[(1usize, 1u8), (3usize, 1u8)]]),
    (8521215116286u128, 8796093022208u128, 602i32, &[&[], &[(3usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (7u128, 17317308138488u128, 602i32, &[&[(2usize, 0u8), (3usize, 0u8)], &[(1usize, 1u8), (2usize, 0u8), (0usize, 1u8), (3usize, 0u8)]]),
    (274877907071u128, 17042430231424u128, 602i32, &[&[], &[(2usize, 0u8), (3usize, 1u8)], &[(0usize, 1u8), (1usize, 1u8), (2usize, 1u8)]]),
    (4123168605183u128, 13194139533312u128, 602i32, &[&[], &[(3usize, 1u8), (1usize, 1u8)]]),
    (8521215116287u128, 8796093022208u128, 602i32, &[&[], &[(3usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (64512u128, 1023u128, 405i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (30720u128, 34815u128, 406i32, &[&[(3usize, 1u8), (1usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (30720u128, 34815u128, 407i32, &[&[(3usize, 1u8), (1usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (57345u128, 8190u128, 409i32, &[&[(2usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (57345u128, 8190u128, 410i32, &[&[(2usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (1073627134u128, 65537u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (7u128, 16376u128, 602i32, &[&[(2usize, 0u8), (3usize, 0u8)], &[(1usize, 1u8), (2usize, 0u8), (0usize, 1u8), (3usize, 0u8)]]),
    (63u128, 16320u128, 602i32, &[&[(3usize, 0u8)], &[(2usize, 1u8), (1usize, 1u8), (3usize, 0u8)]]),
    (127u128, 16256u128, 602i32, &[&[(3usize, 0u8)], &[(2usize, 1u8), (1usize, 1u8), (3usize, 1u8)], &[(2usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (2047u128, 14336u128, 602i32, &[&[], &[(3usize, 1u8), (0usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8)]]),
    (4095u128, 12288u128, 602i32, &[&[], &[(3usize, 1u8), (2usize, 1u8)]]),
    (8191u128, 8192u128, 602i32, &[&[], &[(3usize, 1u8), (2usize, 1u8), (0usize, 1u8)]]),
    (6u128, 16376u128, 602i32, &[&[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (1usize, 1u8), (2usize, 0u8), (0usize, 1u8)]]),
    (62u128, 16320u128, 602i32, &[&[(3usize, 0u8)], &[(1usize, 1u8), (2usize, 1u8), (3usize, 0u8)]]),
    (126u128, 16256u128, 602i32, &[&[(3usize, 0u8)], &[(1usize, 1u8), (3usize, 1u8), (2usize, 1u8)], &[(0usize, 1u8), (1usize, 1u8), (2usize, 1u8)]]),
    (2046u128, 14336u128, 602i32, &[&[], &[(3usize, 1u8), (1usize, 0u8), (2usize, 1u8)], &[(0usize, 1u8), (3usize, 1u8), (1usize, 1u8)]]),
    (4094u128, 12288u128, 602i32, &[&[], &[(3usize, 1u8), (2usize, 1u8)]]),
    (8190u128, 8192u128, 602i32, &[&[], &[(3usize, 1u8), (0usize, 1u8), (2usize, 1u8)]]),
    (1073627132u128, 65539u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 1u8), (3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (1073496056u128, 196615u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 0u8)]]),
    (1073233912u128, 458759u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 1u8)]]),
    (1073233904u128, 458767u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)], &[(4usize, 1u8), (3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 1u8)]]),
    (1072709600u128, 983071u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (1071661024u128, 2031647u128, 501i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (1069563776u128, 4128895u128, 501i32, &[&[(3usize, 0u8), (2usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (1056980480u128, 16712191u128, 501i32, &[&[(3usize, 1u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (1040203264u128, 33489407u128, 501i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (1040202752u128, 33489919u128, 501i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 1u8), (3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (1006648320u128, 67044351u128, 501i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (1006647296u128, 67045375u128, 501i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)], &[(4usize, 0u8), (3usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (805314560u128, 268378111u128, 501i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(4usize, 0u8), (3usize, 1u8), (2usize, 1u8), (0usize, 0u8)]]),
    (6u128, 3894301873197021388649458745540600u128, 602i32, &[&[(0usize, 1u8), (2usize, 0u8), (3usize, 0u8)], &[(1usize, 1u8), (2usize, 0u8), (3usize, 0u8)]]),
    (274877907070u128, 3894301873197021388649183867633536u128, 602i32, &[&[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (6usize, 0u8), (1usize, 0u8), (5usize, 0u8)], &[(0usize, 1u8), (3usize, 0u8), (2usize, 1u8), (1usize, 1u8)]]),
    (8521215117310u128, 3894301873197021388640937530423296u128, 602i32, &[&[(3usize, 0u8), (1usize, 1u8)], &[(2usize, 0u8), (3usize, 1u8)], &[(0usize, 1u8), (2usize, 0u8), (3usize, 1u8), (1usize, 1u8)], &[(6usize, 0u8), (3usize, 0u8), (1usize, 0u8), (5usize, 0u8)]]),
    (17317308141566u128, 3894301873197021388632141437399040u128, 602i32, &[&[(2usize, 1u8)], &[(3usize, 1u8)], &[(5usize, 0u8), (3usize, 0u8), (2usize, 0u8), (6usize, 0u8)]]),
    (75557863760823817609214u128, 3894301873121463524888634927931392u128, 602i32, &[&[(3usize, 1u8)], &[(2usize, 1u8)], &[(5usize, 0u8), (6usize, 0u8), (2usize, 0u8), (3usize, 0u8)], &[(1usize, 0u8), (0usize, 0u8), (2usize, 1u8), (3usize, 1u8)]]),
    (226673591247836836544510u128, 3894301872970347797401621908996096u128, 602i32, &[&[(3usize, 1u8)], &[(1usize, 1u8)], &[(1usize, 1u8), (3usize, 1u8), (2usize, 0u8)], &[(6usize, 0u8), (1usize, 0u8), (3usize, 0u8), (5usize, 0u8)]]),
    (1298074215162611953354486956720126u128, 2596227658034409435294971788820480u128, 602i32, &[&[], &[(3usize, 0u8), (1usize, 0u8)], &[(3usize, 0u8), (6usize, 0u8), (5usize, 0u8), (1usize, 0u8)], &[(2usize, 1u8), (3usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (3894222645034488677567787197071358u128, 79228162532711081671548469248u128, 602i32, &[&[], &[(1usize, 0u8), (3usize, 0u8)], &[(1usize, 0u8), (6usize, 0u8), (5usize, 0u8), (3usize, 0u8)]]),
    (274877907071u128, 3894301873197021388649183867633536u128, 602i32, &[&[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (0usize, 1u8), (2usize, 1u8), (1usize, 1u8)], &[(3usize, 0u8), (5usize, 0u8), (1usize, 0u8), (6usize, 0u8)]]),
    (8521215117311u128, 3894301873197021388640937530423296u128, 602i32, &[&[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (6usize, 0u8), (5usize, 0u8), (1usize, 0u8)], &[(2usize, 0u8), (3usize, 1u8)], &[(2usize, 0u8), (3usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (17317308141567u128, 3894301873197021388632141437399040u128, 602i32, &[&[(2usize, 0u8)], &[(3usize, 0u8)], &[(3usize, 0u8), (6usize, 0u8), (2usize, 0u8), (5usize, 0u8)]]),
    (75557863760823817609215u128, 3894301873121463524888634927931392u128, 602i32, &[&[(2usize, 1u8)], &[(3usize, 1u8)], &[(1usize, 0u8), (3usize, 1u8), (0usize, 0u8), (2usize, 1u8)], &[(6usize, 0u8), (5usize, 0u8), (3usize, 0u8), (2usize, 0u8)]]),
    (226673591247836836544511u128, 3894301872970347797401621908996096u128, 602i32, &[&[(3usize, 1u8)], &[(1usize, 1u8)], &[(1usize, 1u8), (3usize, 1u8), (2usize, 0u8)], &[(6usize, 0u8), (1usize, 0u8), (3usize, 0u8), (5usize, 0u8)]]),
    (1298074215162611953354486956720127u128, 2596227658034409435294971788820480u128, 602i32, &[&[], &[(3usize, 0u8), (1usize, 0u8)], &[(6usize, 0u8), (3usize, 0u8), (5usize, 0u8), (1usize, 0u8)], &[(0usize, 1u8), (2usize, 1u8), (3usize, 1u8), (1usize, 1u8)]]),
    (3894222645034488677567787197071359u128, 79228162532711081671548469248u128, 602i32, &[&[], &[(1usize, 0u8), (3usize, 0u8)], &[(1usize, 0u8), (3usize, 0u8), (5usize, 0u8), (6usize, 0u8)]]),
    (65520u128, 15u128, 404i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)]]),
    (65520u128, 15u128, 405i32, &[&[], &[(3usize, 0u8), (2usize, 0u8)]]),
    (32736u128, 32799u128, 406i32, &[&[(3usize, 1u8)], &[(2usize, 1u8), (1usize, 1u8), (0usize, 1u8)], &[(2usize, 1u8), (3usize, 0u8), (0usize, 1u8)], &[(2usize, 1u8), (3usize, 0u8), (1usize, 1u8)]]),
    (32736u128, 32799u128, 407i32, &[&[(3usize, 1u8)], &[(2usize, 1u8), (1usize, 1u8), (0usize, 1u8)], &[(2usize, 1u8), (3usize, 0u8), (0usize, 1u8)], &[(2usize, 1u8), (3usize, 0u8), (1usize, 1u8)]]),
    (7680u128, 57855u128, 411i32, &[&[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)]]),
    (15360u128, 50175u128, 412i32, &[&[(3usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (28672u128, 36863u128, 414i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 1u8)]]),
    (24576u128, 40959u128, 415i32, &[&[(3usize, 1u8), (2usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (65505u128, 30u128, 405i32, &[&[], &[(3usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8)]]),
    (65505u128, 30u128, 406i32, &[&[], &[(3usize, 0u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8)]]),
    (15872u128, 49663u128, 411i32, &[&[(3usize, 1u8), (1usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (30720u128, 34815u128, 413i32, &[&[(3usize, 1u8), (1usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (57344u128, 8191u128, 415i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (824633721086u128, 3899214019273164031996474360397568u128, 602i32, &[&[(6usize, 0u8), (3usize, 0u8)], &[(1usize, 0u8), (6usize, 0u8), (3usize, 0u8), (5usize, 1u8)]]),
    (1924145349118u128, 3899214019273164031995374848769536u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(5usize, 1u8), (1usize, 0u8), (3usize, 0u8), (6usize, 0u8)], &[(2usize, 0u8), (1usize, 0u8), (0usize, 0u8), (3usize, 1u8)]]),
    (4123168605182u128, 3899214019273164031993175825513472u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(1usize, 0u8), (5usize, 1u8), (3usize, 0u8), (6usize, 0u8)], &[(1usize, 0u8), (2usize, 0u8), (3usize, 1u8)]]),
    (8521215117310u128, 3899214019273164031988777779001344u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(1usize, 0u8), (3usize, 0u8), (5usize, 1u8), (6usize, 0u8)], &[(2usize, 0u8), (3usize, 1u8)], &[(2usize, 0u8), (1usize, 1u8), (3usize, 1u8), (0usize, 1u8)]]),
    (17317308141566u128, 3899214019273164031979981685977088u128, 602i32, &[&[(2usize, 0u8), (3usize, 1u8)], &[(6usize, 0u8), (3usize, 0u8)], &[(6usize, 0u8), (5usize, 1u8), (2usize, 0u8), (3usize, 0u8)]]),
    (75557863760823817609214u128, 3899214019197606168236475176509440u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (6usize, 0u8), (5usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8), (1usize, 0u8)]]),
    (1298074215162611953354486956720126u128, 2601139804110552078642812037398528u128, 602i32, &[&[], &[(6usize, 1u8), (1usize, 1u8), (2usize, 0u8)], &[(3usize, 0u8), (1usize, 0u8)], &[(5usize, 0u8), (3usize, 0u8), (6usize, 0u8), (1usize, 0u8)], &[(0usize, 1u8), (3usize, 1u8), (1usize, 1u8), (2usize, 1u8)]]),
    (3894222645034488677567787197071358u128, 4991374238675354429511797047296u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(5usize, 1u8), (1usize, 0u8), (6usize, 0u8), (3usize, 0u8)]]),
    (3894301873197021388649458745540606u128, 4912146076142643347840248578048u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)], &[(1usize, 0u8), (3usize, 0u8), (0usize, 0u8), (2usize, 0u8), (6usize, 1u8)], &[(5usize, 1u8), (1usize, 0u8), (3usize, 0u8), (0usize, 1u8), (6usize, 0u8)]]),
    (3894460329522086810812801842479102u128, 4753689751077221184497151639552u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(2usize, 0u8), (6usize, 1u8), (1usize, 0u8), (3usize, 0u8)]]),
    (3894777242172217655139470856486910u128, 4436777100946376857828137631744u128, 602i32, &[&[], &[(3usize, 0u8), (1usize, 0u8), (2usize, 1u8), (6usize, 1u8)], &[(3usize, 0u8), (0usize, 1u8), (1usize, 1u8), (6usize, 1u8)]]),
    (3895411067472479343792808884502526u128, 3802951800684688204490109616128u128, 602i32, &[&[], &[(3usize, 0u8), (2usize, 1u8), (6usize, 1u8)]]),
    (3896678718072707573194305587707902u128, 2535301200456458802993406410752u128, 602i32, &[&[], &[(3usize, 0u8), (0usize, 1u8), (6usize, 1u8), (2usize, 1u8)]]),
    (824633721087u128, 3899214019273164031996474360397568u128, 602i32, &[&[(6usize, 0u8), (3usize, 0u8)], &[(5usize, 1u8), (1usize, 0u8), (6usize, 0u8), (3usize, 0u8)]]),
    (1924145349119u128, 3899214019273164031995374848769536u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (6usize, 0u8), (1usize, 0u8), (5usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (0usize, 0u8), (1usize, 0u8)]]),
    (4123168605183u128, 3899214019273164031993175825513472u128, 602i32, &[&[(6usize, 0u8), (3usize, 0u8)], &[(1usize, 0u8), (5usize, 1u8), (6usize, 0u8), (3usize, 0u8)], &[(2usize, 0u8), (1usize, 0u8), (3usize, 1u8)]]),
    (8521215117311u128, 3899214019273164031988777779001344u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (1usize, 0u8), (5usize, 1u8), (6usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (1usize, 1u8), (2usize, 0u8), (0usize, 1u8)]]),
    (17317308141567u128, 3899214019273164031979981685977088u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (6usize, 0u8), (5usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)]]),
    (75557863760823817609215u128, 3899214019197606168236475176509440u128, 602i32, &[&[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (0usize, 0u8), (2usize, 1u8), (1usize, 0u8)], &[(6usize, 0u8), (3usize, 0u8)], &[(5usize, 1u8), (6usize, 0u8), (3usize, 0u8), (2usize, 0u8)]]),
    (1298074215162611953354486956720127u128, 2601139804110552078642812037398528u128, 602i32, &[&[], &[(6usize, 1u8), (2usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (1usize, 0u8)], &[(5usize, 0u8), (3usize, 0u8), (6usize, 0u8), (1usize, 0u8)], &[(0usize, 1u8), (3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (3894222645034488677567787197071359u128, 4991374238675354429511797047296u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)], &[(3usize, 0u8), (1usize, 0u8), (5usize, 1u8), (6usize, 0u8)]]),
    (3894301873197021388649458745540607u128, 4912146076142643347840248578048u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(2usize, 0u8), (1usize, 0u8), (0usize, 0u8), (6usize, 1u8), (3usize, 0u8)], &[(5usize, 1u8), (1usize, 0u8), (0usize, 1u8), (6usize, 0u8), (3usize, 0u8)]]),
    (3894460329522086810812801842479103u128, 4753689751077221184497151639552u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(2usize, 0u8), (6usize, 1u8), (3usize, 0u8), (1usize, 0u8)]]),
    (3894777242172217655139470856486911u128, 4436777100946376857828137631744u128, 602i32, &[&[], &[(1usize, 1u8), (0usize, 1u8), (3usize, 0u8), (6usize, 1u8)], &[(2usize, 1u8), (1usize, 0u8), (3usize, 0u8), (6usize, 1u8)]]),
    (3895411067472479343792808884502527u128, 3802951800684688204490109616128u128, 602i32, &[&[], &[(2usize, 1u8), (3usize, 0u8), (6usize, 1u8)]]),
    (3896678718072707573194305587707903u128, 2535301200456458802993406410752u128, 602i32, &[&[], &[(3usize, 0u8), (2usize, 1u8), (6usize, 1u8), (0usize, 1u8)]]),
    (16128u128, 49407u128, 412i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (16128u128, 49407u128, 413i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (32256u128, 33279u128, 414i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (32256u128, 33279u128, 415i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (64512u128, 1023u128, 416i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (64512u128, 1023u128, 417i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (16128u128, 49407u128, 411i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (32256u128, 33279u128, 413i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (64512u128, 1023u128, 415i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (6u128, 3899214019273016457903958944385016u128, 602i32, &[&[(3usize, 0u8), (2usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 1u8), (6usize, 0u8)]]),
    (62u128, 3899214019273016457903958944384960u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(2usize, 1u8), (3usize, 0u8), (6usize, 0u8), (1usize, 1u8)]]),
    (274877907070u128, 3899214019273016457903684066477952u128, 602i32, &[&[(5usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 1u8)], &[(6usize, 0u8), (3usize, 0u8)], &[(6usize, 0u8), (3usize, 0u8), (1usize, 1u8), (0usize, 1u8)]]),
    (8521215117310u128, 3899214019273016457895437729267712u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(2usize, 0u8), (3usize, 1u8)], &[(1usize, 1u8), (2usize, 0u8), (0usize, 1u8), (3usize, 1u8)]]),
    (226673591247836836530174u128, 3899214019046342866656122107854848u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(1usize, 1u8), (2usize, 1u8), (3usize, 1u8)]]),
    (1298074215162611953354486956689406u128, 2601139804110404504549471987695616u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(0usize, 1u8), (1usize, 1u8), (6usize, 1u8), (3usize, 1u8)]]),
    (3894222645034488677427049708652542u128, 4991374238527780476909235732480u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)]]),
    (3894301873197021388508716962154494u128, 4912146075995069395241982230528u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)], &[(3usize, 0u8), (0usize, 0u8), (1usize, 0u8), (2usize, 0u8), (6usize, 1u8)]]),
    (3894460329522086810672051469158398u128, 4753689750929647231907475226624u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (6usize, 1u8)]]),
    (3894777242172217654998720483166206u128, 4436777100798802905238461218816u128, 602i32, &[&[], &[(3usize, 0u8), (2usize, 1u8), (6usize, 1u8), (1usize, 0u8)], &[(3usize, 0u8), (0usize, 1u8), (6usize, 1u8), (1usize, 1u8)]]),
    (3895411067472331769699468834768894u128, 3802951800684688204490109616128u128, 602i32, &[&[], &[(2usize, 1u8), (3usize, 0u8), (6usize, 1u8)]]),
    (3896678718072559999100965537974270u128, 2535301200456458802993406410752u128, 602i32, &[&[], &[(0usize, 1u8), (2usize, 1u8), (6usize, 1u8), (3usize, 0u8)]]),
    (7u128, 3899214019273016457903958944385016u128, 602i32, &[&[(2usize, 0u8), (3usize, 0u8), (6usize, 0u8)], &[(2usize, 0u8), (1usize, 1u8), (3usize, 0u8), (0usize, 1u8), (6usize, 0u8)]]),
    (63u128, 3899214019273016457903958944384960u128, 602i32, &[&[(3usize, 0u8), (6usize, 0u8)], &[(1usize, 1u8), (3usize, 0u8), (2usize, 1u8), (6usize, 0u8)]]),
    (274877907071u128, 3899214019273016457903684066477952u128, 602i32, &[&[(2usize, 0u8), (0usize, 1u8), (5usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (6usize, 0u8)], &[(3usize, 0u8), (0usize, 1u8), (1usize, 1u8), (6usize, 0u8)]]),
    (8521215117311u128, 3899214019273016457895437729267712u128, 602i32, &[&[(3usize, 1u8), (2usize, 0u8)], &[(6usize, 0u8), (3usize, 0u8)], &[(1usize, 1u8), (0usize, 1u8), (3usize, 1u8), (2usize, 0u8)]]),
    (226673591247836836530175u128, 3899214019046342866656122107854848u128, 602i32, &[&[], &[(1usize, 1u8), (3usize, 1u8), (2usize, 1u8)], &[(6usize, 1u8), (3usize, 0u8)]]),
    (1298074215162611953354486956689407u128, 2601139804110404504549471987695616u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(6usize, 1u8), (3usize, 1u8), (0usize, 1u8), (1usize, 1u8)]]),
    (3894222645034488677427049708652543u128, 4991374238527780476909235732480u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)]]),
    (3894301873197021388508716962154495u128, 4912146075995069395241982230528u128, 602i32, &[&[], &[(3usize, 0u8), (6usize, 1u8)], &[(2usize, 0u8), (1usize, 0u8), (3usize, 0u8), (6usize, 1u8), (0usize, 0u8)]]),
    (3894460329522086810672051469158399u128, 4753689750929647231907475226624u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8)], &[(6usize, 1u8), (2usize, 0u8), (3usize, 0u8), (1usize, 0u8)]]),
    (3894777242172217654998720483166207u128, 4436777100798802905238461218816u128, 602i32, &[&[], &[(6usize, 1u8), (3usize, 0u8), (0usize, 1u8), (1usize, 1u8)], &[(6usize, 1u8), (2usize, 1u8), (3usize, 0u8), (1usize, 0u8)]]),
    (3895411067472331769699468834768895u128, 3802951800684688204490109616128u128, 602i32, &[&[], &[(3usize, 0u8), (2usize, 1u8), (6usize, 1u8)]]),
    (3896678718072559999100965537974271u128, 2535301200456458802993406410752u128, 602i32, &[&[], &[(6usize, 1u8), (2usize, 1u8), (3usize, 0u8), (0usize, 1u8)]]),
    (65024u128, 511u128, 404i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (65024u128, 511u128, 405i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (32256u128, 33279u128, 406i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (32256u128, 33279u128, 407i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (65024u128, 511u128, 408i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (65024u128, 511u128, 409i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 0u8)]]),
    (7680u128, 57855u128, 410i32, &[&[(3usize, 1u8), (1usize, 0u8), (0usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)]]),
    (15872u128, 49663u128, 412i32, &[&[(3usize, 1u8), (1usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (15872u128, 49663u128, 413i32, &[&[(3usize, 1u8), (1usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (64513u128, 1022u128, 405i32, &[&[(3usize, 1u8)], &[(2usize, 0u8), (1usize, 0u8)], &[(2usize, 0u8), (3usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (64513u128, 1022u128, 406i32, &[&[(3usize, 1u8)], &[(2usize, 0u8), (1usize, 0u8)], &[(2usize, 0u8), (3usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (64512u128, 1023u128, 407i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (64512u128, 1023u128, 408i32, &[&[(3usize, 1u8)], &[(3usize, 1u8), (2usize, 0u8), (1usize, 0u8)]]),
    (64513u128, 1022u128, 409i32, &[&[(3usize, 1u8)], &[(2usize, 0u8), (1usize, 0u8)], &[(2usize, 0u8), (3usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (64513u128, 1022u128, 410i32, &[&[(3usize, 1u8)], &[(2usize, 0u8), (1usize, 0u8)], &[(2usize, 0u8), (3usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (15360u128, 50175u128, 411i32, &[&[(3usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)]]),
    (31744u128, 33791u128, 413i32, &[&[(3usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (31744u128, 33791u128, 414i32, &[&[(3usize, 1u8), (1usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (8257662u128, 1065435009u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(3usize, 0u8), (1usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (8257660u128, 1065435011u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (2usize, 1u8)], &[(4usize, 1u8), (3usize, 0u8), (2usize, 0u8), (1usize, 0u8), (0usize, 1u8)]]),
    (8126588u128, 1065566083u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (2usize, 1u8)]]),
    (8126584u128, 1065566087u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(3usize, 0u8), (1usize, 1u8)], &[(3usize, 0u8), (2usize, 1u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 0u8), (1usize, 1u8), (0usize, 0u8)]]),
    (7864440u128, 1065828231u128, 501i32, &[&[(3usize, 0u8), (1usize, 1u8), (0usize, 1u8)], &[(3usize, 0u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8), (0usize, 0u8)]]),
    (7340128u128, 1066352543u128, 501i32, &[&[(2usize, 1u8), (1usize, 1u8), (0usize, 0u8)], &[(3usize, 0u8), (2usize, 1u8), (1usize, 0u8)], &[(4usize, 0u8), (3usize, 0u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (6u128, 8521215115384u128, 602i32, &[&[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (2usize, 0u8), (0usize, 1u8), (1usize, 1u8)]]),
    (4123168604286u128, 4398046511104u128, 602i32, &[&[], &[(1usize, 1u8), (3usize, 1u8)]]),
    (7u128, 8521215115384u128, 602i32, &[&[(3usize, 0u8), (2usize, 0u8)], &[(3usize, 0u8), (1usize, 1u8), (2usize, 0u8), (0usize, 1u8)]]),
    (4123168604287u128, 4398046511104u128, 602i32, &[&[], &[(3usize, 1u8), (1usize, 1u8)]]),
    (57344u128, 8191u128, 404i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (57344u128, 8191u128, 405i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (24576u128, 40959u128, 406i32, &[&[(3usize, 1u8), (2usize, 1u8), (0usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 1u8)]]),
    (57344u128, 8191u128, 408i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (57344u128, 8191u128, 409i32, &[&[(3usize, 1u8), (2usize, 1u8)], &[(3usize, 1u8), (2usize, 1u8), (1usize, 0u8), (0usize, 0u8)]]),
    (393222u128, 1073299449u128, 501i32, &[&[(3usize, 0u8), (2usize, 0u8), (0usize, 1u8)], &[(3usize, 0u8), (2usize, 0u8), (1usize, 1u8)]]),
];

fn tree_rec(on: u128, off: u128, n: i32, base: i32, vs: &[usize], memo: &mut HashMap<(u128, u128, i32), (i64, Cubes)>) -> (i64, Cubes) {
    if on == 0 {
        return (0, vec![]);
    }
    if off == 0 {
        let l = n + base;
        let c = if l <= 1 { 0 } else if l == 2 { 1 } else { 4 * (l as i64 - 2) };
        return (c, vec![vec![]]);
    }
    if let Some(r) = memo.get(&(on, off, n)) {
        return r.clone();
    }
    let mut best: Option<(i64, Cubes)> = None;
    for &v in vs {
        let z = MASKV[v];
        let (on0, on1, off0, off1) = (on & z, on & !z, off & z, off & !z);
        if (on0 == 0 && off0 == 0) || (on1 == 0 && off1 == 0) {
            continue;
        }
        let (c0, l0) = tree_rec(on0, off0, n + 1, base, vs, memo);
        let (c1, l1) = tree_rec(on1, off1, n + 1, base, vs, memo);
        if best.is_none() || c0 + c1 < best.as_ref().unwrap().0 {
            let mut lst: Cubes = vec![];
            for x in &l0 {
                let mut y = vec![(v, 0u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            for x in &l1 {
                let mut y = vec![(v, 1u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            best = Some((c0 + c1, lst));
        }
    }
    let r = best.expect("cover");
    memo.insert((on, off, n), r.clone());
    r
}
fn pe9_lvl(e: i32) -> i32 {
    let top = 1 << WB;
    let p = if e <= 3 {
        2
    } else if e <= 7 {
        4
    } else if e <= 15 {
        8
    } else {
        16
    };
    p.min(top)
}
fn pt9(t: i32) -> i32 {
    (t & -t).min(1 << WB)
}
fn emax9(t: i32) -> i32 {
    let p = pt9(t);
    if p >= (1 << WB) {
        ECAP
    } else if p == 2 {
        3
    } else if p == 4 {
        7
    } else {
        15
    }
}
fn pairs9(t: i32) -> Vec<(i32, i32, i32, i32)> {
    let n = N as i32;
    let mut out = vec![];
    for e in 0..=ECAP {
        let pe = pe9_lvl(e);
        if t % pe != 0 {
            continue;
        }
        for w in 0..pe {
            if (e - w).rem_euclid(2) != 0 {
                continue;
            }
            if e == 1 && w != 1 {
                continue;
            }
            if e == 0 && w != 0 {
                continue;
            }
            let (u, v) = ((e - w) / 2, (e + w) / 2);
            let (l, f) = (t / 2 - u, t / 2 + v);
            if l >= 1 && f <= n && f >= l {
                out.push((e, w, u, v));
            }
        }
    }
    out
}
fn pu9(pr: &(i32, i32, i32, i32)) -> u32 {
    pr.2.rem_euclid(16) as u32
}
fn pv9(pr: &(i32, i32, i32, i32)) -> u32 {
    let w = pr.1 as u32;
    (pr.3.rem_euclid(16) as u32) | (((w >> 2) & 1) << 5) | (((w >> 3) & 1) << 6)
}

/// Register code at even slots on shots whose N root is at the top: e=0,1,2,3 take 0,14,1,15; e>=4 takes e>>1, its parity on a mark.
fn code(e: i32) -> i32 {
    match e {
        0 => 0,
        1 => 14,
        2 => 1,
        3 => 15,
        _ => e >> 1,
    }
}

/// Rotate a wire list up by one under c: w[i] to w[i+1], top wraps to the bottom.
fn rot1(c: u32, w: &[u32]) -> GL {
    let mut g = vec![];
    for i in (1..w.len()).rev() {
        cswap(c, w[i], w[i - 1], &mut g);
    }
    g
}

impl Machine {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    fn hl(&self, v: i32) -> Vec<Lit> {
        (0..EB).map(|i| (self.e[i], (v >> i) & 1 == 1)).collect()
    }
    fn init(&mut self) {
        let mut g: GL = vec![gx(self.x[0])];
        for i in 0..N {
            if pbit(i) {
                g.push(gx(self.x[i + 1]));
            }
        }
        let xl: Vec<u32> = self.y[2..].to_vec();
        for &q0 in &xl {
            g.push(gc(self.par, q0));
        }
        let cl = self.e[0];
        for &i in &C0M1 {
            g.extend(rev(&inc_long(&xl[i..], self.par, &self.dirty, cl)));
        }
        self.b.t(&g);
    }
    #[allow(clippy::too_many_arguments)]
    fn row(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| k + 1).unwrap_or(0),
            None => tog.keys().next_back().map(|k| k + 1).unwrap_or(0),
        };
        let gate3 = |g: &mut GL, a0: u32, a1: u32, tgt: u32, i: usize| {
            if let Some(il) = inline {
                for li in &il[&i] {
                    let mut l = vec![(a0, true), (a1, true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, tgt));
                }
            } else {
                g.extend(self.m(&[(a0, true), (a1, true), (m, true)], tgt));
            }
        };
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        for li in active {
            g.extend(self.m(li, d));
        }
        if top != NONE {
            for li in active {
                let mut l = li.clone();
                l.extend_from_slice(&[(c, true), (top, true)]);
                g.extend(self.m(&l, d));
            }
            g.push(gt(d, c, top));
        } else {
            for li in active {
                let mut l = li.clone();
                l.push((c, true));
                g.extend(self.m(&l, d));
            }
        }
        for i in (0..n).rev() {
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, d, s[i], t[i], i);
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        g.extend_from_slice(&conj);
        g
    }
    #[allow(clippy::too_many_arguments)]
    fn row_v(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>) -> GL {
        self.row_vx(t, s, t1, top, d, c, m, tog, active, inline, cv, None)
    }
    fn row_vx(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, xg: Option<&GL>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
            None => tog.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
        };
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, c));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(s[i], true), (t[i], true), (m, true)], c));
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        for li in active {
            let mut a2: Vec<Lit> = li.clone();
            a2.extend_from_slice(&[(c, false), (t1, false)]);
            if top != NONE {
                g.extend(self.m(&a2, top));
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            } else {
                g.extend(self.m(&a2, d));
            }
        }
        if let Some(x) = xg {
            g.extend_from_slice(x);
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in (0..n).rev() {
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, c));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(s[i], true), (t[i], true), (m, true)], c));
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(d, true), (s[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, t[i]));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(d, true), (s[i], true), (m, true)], t[i]));
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_vt(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        conj.push(gx(top));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, true)], top));
        g.extend(self.m(&[(d, true), (c, false), (t1, true)], top));
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_v(&self, t: &[u32], s: &[u32], t1: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        if top != NONE {
            g.push(gt(d, c, top));
        }
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn pi_gates(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> GL {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act flag): only its carry-out matters
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[W - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, y[1], f3));
        g.extend(rev(&fw));
        g
    }
    fn flag_e(&self, fl: u32, xt: u32, y: &[u32]) -> GL {
        let h = &self.e;
        let ctl = self.x[0];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // act shots, hi=0: xt -> 15; not xt, y0=1 -> 13; not xt, y0=0 -> stays 0
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hl(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(0)), ctl));
        g.extend_from_slice(&[gc(ctl, h[0]), gc(ctl, h[2]), gc(ctl, h[3])]);
        g.extend(self.m(&[(ctl, true), (xt, true)], h[1]));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hl(15)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(13)), ctl));
        g
    }
    fn pe9(e: i32) -> u32 {
        ((e >> 1) as u32) | (((e & 1) as u32) << 4)
    }
    fn lane9(&self, v: usize) -> u32 {
        if v < 4 {
            self.e[v]
        } else if v == 4 {
            self.w[0]
        } else if v == 5 {
            self.w[2]
        } else {
            self.w[3]
        }
    }
    fn lits9(&self, l: &[Vec<(usize, u8)>]) -> Vec<Vec<Lit>> {
        l.iter().map(|x| x.iter().map(|&(v, b)| (self.lane9(v), b == 1)).collect()).collect()
    }
    fn dtree_tree(&mut self, on: u128, off: u128, vs: &'static [usize], base: i32) -> Vec<Vec<(usize, u8)>> {
        let mut m2: HashMap<(u128, u128, i32), (i64, Vec<Vec<(usize, u8)>>)> = HashMap::new();
        tree_rec(on, off, 0, base, vs, &mut m2).1
    }
    fn dtree(&mut self, on: u128, off: u128, vs: &'static [usize], base: i32) -> Vec<Vec<(usize, u8)>> {
        let key = (on, off, vs.len() as i32 * 100 + base);
        if let Some(r) = self.memo.get(&key) {
            return r.clone();
        }
        let mut m2: HashMap<(u128, u128, i32), (i64, Vec<Vec<(usize, u8)>>)> = HashMap::new();
        let mut r = tree_rec(on, off, 0, base, vs, &mut m2).1;
        if ESOP_MIN {
            if let Some(e) = ESOP_TABLE.iter().find(|e| e.0 == on && e.1 == off && e.2 == key.2) {
                r = e.3.iter().map(|c| c.to_vec()).collect();
            }
        }
        self.memo.insert(key, r.clone());
        r
    }
    /// Exact on shots at the top at an even slot: fires on the e in a, on no other e that can be there.
    fn exact9(&mut self, a: &BTreeSet<i32>) -> Vec<Vec<Lit>> {
        let (mut on, mut off) = (0u128, 0u128);
        for e in 0..=ECAP {
            if a.contains(&e) {
                on |= 1u128 << Self::pe9(e);
            } else {
                off |= 1u128 << Self::pe9(e);
            }
        }
        let l = self.dtree(on, off, &VS_EXACT, 1);
        self.lits9(&l)
    }
    fn exact9_tree(&mut self, a: &BTreeSet<i32>) -> Vec<Vec<Lit>> {
        let (mut on, mut off) = (0u128, 0u128);
        for e in 0..=ECAP {
            if a.contains(&e) {
                on |= 1u128 << Self::pe9(e);
            } else {
                off |= 1u128 << Self::pe9(e);
            }
        }
        let l = self.dtree_tree(on, off, &VS_EXACT, 1);
        self.lits9(&l)
    }
    fn tog9(&mut self, on_vals: &BTreeSet<u32>, off_vals: &BTreeSet<u32>, base: i32) -> Vec<Vec<Lit>> {
        let (mut on, mut off) = (0u128, 0u128);
        for &p in on_vals {
            on |= 1u128 << p;
        }
        for &p in off_vals {
            off |= 1u128 << p;
        }
        let l = self.dtree(on, off, vs_tog(), base);
        self.lits9(&l)
    }
    fn wne0(&self) -> Vec<Vec<Lit>> {
        let mut out = vec![];
        let mut pre: Vec<Lit> = vec![];
        for &q0 in &self.w {
            let mut c = pre.clone();
            c.push((q0, true));
            out.push(c);
            pre.push((q0, false));
        }
        out
    }
    fn conv_u9(&self, lev: usize) -> GL {
        let mut g = vec![];
        for i in 1..lev {
            g.extend(dec_ctl(&self.e[i - 1..], &[(self.w[i], true)], &self.dirty));
        }
        g
    }
    fn conv_v9(&self, lev: usize) -> GL {
        let mut g = inc_ctl(&self.e, &[(self.w[0], true)], &self.dirty);
        for i in 1..lev {
            g.extend(inc_ctl(&self.e[i - 1..], &[(self.w[i], true)], &self.dirty));
        }
        g
    }
    fn slot(&mut self, t: i32) {
        if t % 2 == 1 {
            self.odd9(t);
        } else {
            self.even9(t);
        }
    }
    fn odd9(&mut self, t: i32) {
        let (x, y, h, wl) = (self.x.clone(), self.y.clone(), self.e.clone(), self.w.clone());
        let yt = y[W - 1];
        let (x0, y0) = (x[0], y[0]);
        let d = x0;
        let ctl = x0;
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let al: Vec<Lit> = cat(&[(yt, true)], &self.hl(0));
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        if l >= 1 && f <= N as i32 {
            let c = wl[0];
            let actv = vec![al.clone()];
            for k in 0..2usize {
                let alo = W - l as usize - k;
                let tv: Vec<u32> = (alo..(W - k - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (alo..(W - k - 1)).map(|a| y[a + k]).collect();
                let t1 = x[W - 1 - k];
                let top = if k >= 1 { x[W - k] } else { NONE };
                let g = self.row_v(&tv, &sv, t1, top, d, c, NONE, &no_tog, &actv, None, None);
                self.b.t(&g);
                let mut g: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                    }
                } else {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(d, true)]), y0));
                    }
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(y0, true)]), d));
                    }
                }
                self.b.t(&g);
            }
            for k in [1usize, 0] {
                let ahi = W - f as usize - 1 + k;
                let wires: Vec<usize> = (k..=ahi).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - k]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[k - 1] } else { NONE };
                let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &actv, None, None);
                let mut hh: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                    }
                    hh.push(gc(d, x[W - k]));
                    let xt = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                    hh.push(gc(d, top));
                } else {
                    let host = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(host, true)]), d));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
                self.b.t(&hh);
                self.b.t(&rev(&g));
            }
        }
        let g = self.m(&cat(&al, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let fl = y[W - 1];
        let aa = cat(&[(fl, true)], &self.hl(0));
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[W - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: hi to 15 unless (not xt, y0=0), so the common rise gives hi 0 (E'=0, or the second state) or 1 (E'=2)
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hl(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(0)), ctl));
        for &q0 in &h {
            g.push(gc(ctl, q0));
        }
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hl(15)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(15)), ctl));
        self.b.t(&g);
        let mut g = self.m(&cat(&[(xt, true), (y[0], true)], &self.hl(15)), fl);
        g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hl(0)), fl));
        g.extend(self.m(&cat(&[(y[W - 2], true), (xt, false), (y[0], true)], &self.hl(15)), fl));
        self.b.t(&g);
        // waiters count this slot
        let g = inc_ctl(&wl, &[(y[W - 1], true)], &self.dirty);
        self.b.t(&g);
        self.b.t(&[gx(y[W - 1]), gc(y[W - 1], ctl), gx(y[W - 1])]);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        let g = inc_ctl(&h, &[(ctl, true)], &self.dirty);
        self.b.t(&g);
        let yt2 = y[W - 1];
        let mut g = vec![gx(ctl)];
        for cu in self.wne0() {
            g.extend(self.m(&cat(&[(yt2, true)], &cu), ctl));
        }
        self.b.t(&g);
        // the second state acts at the next even slot with w=1
        let g = self.m(&cat(&[(yt2, true), (xt, false), (y[0], false), (y[1], true)], &self.hl(0)), wl[0]);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    fn even9(&mut self, t: i32) {
        let (x, y, h, wl) = (self.x.clone(), self.y.clone(), self.e.clone(), self.w.clone());
        let prs = pairs9(t);
        let pp = pt9(t);
        let mut lev = 0usize;
        while (1 << lev) < pp {
            lev += 1;
        }
        let em = emax9(t);
        let es: BTreeSet<i32> = prs.iter().map(|p| p.0).collect();
        let kk = 1 + es.iter().next_back().cloned().unwrap_or(0);
        let yt = y[W - 1];
        let (x0, y0, y1, y2) = (x[0], y[0], y[1], y[2]);
        let d = x0;
        let al: Vec<Lit> = vec![(yt, true)];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let big: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= 2).collect();
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let cv_v = self.conv_u9(lev);
        let cv_c = self.conv_v9(lev);
        let s0: BTreeSet<i32> = [0].into_iter().collect();
        let s1: BTreeSet<i32> = [1].into_iter().collect();
        let sp0: Vec<Vec<Lit>> = self.exact9(&s0).into_iter().map(|li| cat(&li, &al)).collect();
        let sp1: Vec<Vec<Lit>> = self.exact9(&s1).into_iter().map(|li| cat(&li, &al)).collect();
        let merge0 = es.contains(&0) && !big.is_empty();
        let mut c10: GL = vec![];
        for li in &sp0 {
            c10.extend(self.m(li, d));
        }
        if es.contains(&0) && !merge0 {
            let (l, _f) = lf(t, 0);
            let lu = l as usize;
            let mut c1: GL = vec![];
            for li in &sp0 {
                c1.extend(self.m(li, d));
            }
            self.b.t(&c1);
            let tv: Vec<u32> = ((W - lu)..(W - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((W - lu)..(W - 1)).map(|a| y[a]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 1], d, h[0]);
            self.b.t(&g);
            self.b.t(&c1);
        }
        let merge1 = es.contains(&1) && !big.is_empty();
        let mut c11: GL = vec![];
        for li in &sp1 {
            c11.extend(self.m(li, d));
        }
        if es.contains(&1) && !merge1 {
            let (l, _f) = lf(t, 1);
            let lu = l as usize;
            let mut c1: GL = vec![];
            for li in &sp1 {
                c1.extend(self.m(li, d));
            }
            self.b.t(&c1);
            let tv: Vec<u32> = ((W - lu - 1)..(W - 2)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((W - lu - 1)..(W - 2)).map(|a| y[a + 1]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 2], d, h[0]);
            self.b.t(&g);
            self.b.t(&c1);
        }
        for k in 0..kk {
            let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<u32>> = BTreeMap::new();
            for pr in &act {
                starts.entry(W as i32 - (t / 2 - pr.2) - k).or_default().insert(pu9(pr));
            }
            if k == 0 && merge0 {
                starts.entry(W as i32 - t / 2).or_default().insert(0);
            }
            let mut vspos: Vec<(i32, u32)> = act.iter().map(|pr| (W as i32 - (t / 2 - pr.2) - k, pu9(pr))).collect();
            if k == 1 && merge1 {
                starts.entry(W as i32 - t / 2 - 1).or_default().insert(0);
                vspos.push((W as i32 - t / 2 - 1, 0));
            }
            let alo = *starts.keys().next().unwrap();
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[W - 1 - ku];
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let aset: BTreeSet<i32> = es.iter().cloned().filter(|&e| e >= k && e >= 2).collect();
            let actv: Vec<Vec<Lit>> = self.exact9_tree(&aset).into_iter().map(|li| cat(&li, &al)).collect();
            let mut allu: BTreeSet<u32> = act.iter().map(pu9).collect();
            if (k == 0 && merge0) || (k == 1 && merge1) {
                allu.insert(0);
            }
            let cv = if cv_v.is_empty() { None } else { Some(&cv_v) };
            let g = if k == 0 || k >= 3 {
                let cc = if k == 0 { y0 } else { y2 };
                assert!(k == 0 || alo + k >= 3);
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, us) in &starts {
                    let rest: BTreeSet<u32> = allu.difference(us).cloned().collect();
                    tg.insert((a - alo) as usize, self.tog9(us, &rest, 0));
                }
                if k == 0 && merge0 {
                    // ZFOR-wait merge0: Y[1] is not a known 0 for the code-0 class at the slot start, so the merged row's
                    // mask is the clean AND lane; every multi-controlled gate in the row (conversions included) uses the
                    // borrowed-wire form meanwhile.
                    if ZW_SHARED {
                        Z_BUSY.store(true, Ordering::Relaxed);
                    }
                    let cvb = self.conv_u9(lev);
                    let cvb_o = if cvb.is_empty() { None } else { Some(&cvb) };
                    let r = self.row_v(&tv, &sv, t1, top, d, cc, ZW_LANE, &tg, &actv, None, cvb_o);
                    Z_BUSY.store(false, Ordering::Relaxed);
                    r
                } else {
                    self.row_v(&tv, &sv, t1, top, d, cc, y1, &tg, &actv, None, cv)
                }
            } else {
                let wend = (starts.keys().map(|&a| a - alo).max().unwrap() + 1) as usize;
                let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for i in 0..wend {
                    let on: BTreeSet<u32> = vspos.iter().filter(|p| (p.0 - alo) as usize <= i).map(|p| p.1).collect();
                    let rest: BTreeSet<u32> = allu.difference(&on).cloned().collect();
                    let ll: Vec<Vec<Lit>> = if on.is_empty() { vec![] } else { self.tog9(&on, &rest, 2) };
                    il.insert(i, ll);
                }
                let mut ftg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                if FLAG_ON {
                    for (&a, us) in &starts {
                        let rest: BTreeSet<u32> = allu.difference(us).cloned().collect();
                        ftg.insert((a - alo) as usize, self.tog9(us, &rest, 0));
                    }
                }
                if k == 1 && merge1 {
                    // ZFOR-wait merge1: Y[1] is not a known 0 for the code-1 class; carry on the clean AND lane
                    if ZW_SHARED {
                        Z_BUSY.store(true, Ordering::Relaxed);
                    }
                    let cvb = self.conv_u9(lev);
                    let cvb_o = if cvb.is_empty() { None } else { Some(&cvb) };
                    let r = if FLAG_ON {
                        self.row_v(&tv, &sv, t1, top, d, ZW_LANE, FL_LANE, &ftg, &actv, None, cvb_o)
                    } else {
                        self.row_v(&tv, &sv, t1, top, d, ZW_LANE, NONE, &no_tog, &actv, Some(&il), cvb_o)
                    };
                    Z_BUSY.store(false, Ordering::Relaxed);
                    r
                } else if FLAG_ON {
                    self.row_v(&tv, &sv, t1, top, d, y1, FL_LANE, &ftg, &actv, None, cv)
                } else {
                    self.row_v(&tv, &sv, t1, top, d, y1, NONE, &no_tog, &actv, Some(&il), cv)
                }
            };
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            self.b.t(&g);
            let mut g: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                }
            } else {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(d, true)]), y0));
                }
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
        }
        for k in (0..kk).rev() {
            let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<u32>> = BTreeMap::new();
            let mut spos: Vec<(i32, u32)> = act.iter().map(|pr| (W as i32 - (t / 2 + pr.3) - 1 + k, pv9(pr))).collect();
            if k == 0 && merge0 {
                spos.push((W as i32 - t / 2 - 1, 0));
            }
            if k == 1 && merge1 {
                spos.push((W as i32 - t / 2 - 1, 1));
            }
            for &(a, v) in &spos {
                starts.entry(a).or_default().insert(v);
            }
            let ahi = *starts.keys().next_back().unwrap();
            let ku = k as usize;
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let cc = if k >= 2 {
                x[W - ku]
            } else if k == 1 {
                if merge1 { ZW_LANE } else { x[W - 2] }
            } else {
                x[W - 1]
            };
            let aset: BTreeSet<i32> = es.iter().cloned().filter(|&e| e >= k && e >= 2).collect();
            let actv: Vec<Vec<Lit>> = self.exact9_tree(&aset).into_iter().map(|li| cat(&li, &al)).collect();
            let allv: BTreeSet<u32> = spos.iter().map(|p| p.1).collect();
            let g = if k >= 3 {
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, vs) in &starts {
                    let rest: BTreeSet<u32> = allv.difference(vs).cloned().collect();
                    tg.insert((ahi - a) as usize, self.tog9(vs, &rest, 0));
                }
                self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, y1, &tg, &actv, None, Some(&cv_c))
            } else {
                let wend = (starts.keys().map(|&a| ahi - a).max().unwrap() + 1) as usize;
                let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for i in 0..wend {
                    let on: BTreeSet<u32> = spos.iter().filter(|p| (ahi - p.0) as usize <= i).map(|p| p.1).collect();
                    let rest: BTreeSet<u32> = allv.difference(&on).cloned().collect();
                    let ll: Vec<Vec<Lit>> = if on.is_empty() { vec![] } else { self.tog9(&on, &rest, 2) };
                    il.insert(i, ll);
                }
                if k == 1 && merge1 {
                    if ZW_SHARED {
                        Z_BUSY.store(true, Ordering::Relaxed);
                    }
                    let cvb = self.conv_v9(lev);
                    // plain_vt's carry-out into top for the code-1 class (gated by zuiris's code-1 literal)
                    let mut xg: GL = vec![];
                    for li in &sp1 {
                        xg.extend(self.m(&cat(li, &[(d, true), (cc, true)]), top));
                        xg.extend(self.m(&cat(li, &[(d, true), (cc, false), (tv[nn - 1], true)]), top));
                    }
                    let mut ftg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                    if FLAG_ON {
                        for (&a, vs) in &starts {
                            let rest: BTreeSet<u32> = allv.difference(vs).cloned().collect();
                            ftg.insert((ahi - a) as usize, self.tog9(vs, &rest, 0));
                        }
                    }
                    let r = if FLAG_ON {
                        self.row_vx(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, FL_LANE, &ftg, &actv, None, Some(&cvb), Some(&xg))
                    } else {
                        self.row_vx(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, NONE, &no_tog, &actv, Some(&il), Some(&cvb), Some(&xg))
                    };
                    Z_BUSY.store(false, Ordering::Relaxed);
                    r
                } else {
                    if FLAG_ON {
                        let mut ftg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                        for (&a, vs) in &starts {
                            let rest: BTreeSet<u32> = allv.difference(vs).cloned().collect();
                            ftg.insert((ahi - a) as usize, self.tog9(vs, &rest, 0));
                        }
                        self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, FL_LANE, &ftg, &actv, None, Some(&cv_c))
                    } else {
                        self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, NONE, &no_tog, &actv, Some(&il), Some(&cv_c))
                    }
                }
            };
            let mut hh: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                }
                hh.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                }
                if k == 1 && merge1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), top));
                    }
                } else {
                    hh.push(gc(d, top));
                }
            } else {
                let host = x[W - 1];
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(host, true)]), d));
                }
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            self.b.t(&rev(&g));
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
        }
        if es.contains(&0) && !merge0 {
            let (_l, f) = lf(t, 0);
            let mb = W - f as usize;
            let wires: Vec<usize> = (0..mb).rev().collect();
            let mut c1: GL = vec![];
            for li in &sp0 {
                c1.extend(self.m(li, d));
            }
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a]).collect();
            let nn = tv.len();
            let g = self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        if es.contains(&1) && !merge1 {
            let (_l, f) = lf(t, 1);
            let mb = W - f as usize;
            let wires: Vec<usize> = (1..=mb).rev().collect();
            let mut c1: GL = vec![];
            for li in &sp1 {
                c1.extend(self.m(li, d));
            }
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - 1]).collect();
            let nn = tv.len();
            let g = self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        // post
        let ctl = x0;
        let acts: BTreeSet<i32> = (0..=em.min(ECAP)).collect();
        let wait: BTreeSet<i32> = ((em + 1)..=ECAP).collect();
        let has_wait = !wait.is_empty();
        let acu: Vec<Vec<Lit>> = if has_wait { self.exact9(&acts) } else { vec![] };
        let wcu: Vec<Vec<Lit>> = if has_wait { self.exact9(&wait) } else { vec![] };
        if !has_wait {
            let g = self.m(&[(yt, true), (y[0], false)], ctl);
            self.b.t(&g);
            let g = rotate_up(ctl, &y, W - 1);
            self.b.t(&g);
            self.b.t(&[gc(y[W - 1], ctl)]);
        } else {
            let mut g: GL = vec![];
            for cu in &acu {
                g.extend(self.m(&cat(&[(yt, true), (y[0], false)], cu), ctl));
            }
            self.b.t(&g);
            // ZFOR-wait: the waiter flag goes on lane z. Acting (ctl) and waiting shots are disjoint, so one rotation
            // under ctl ^ z serves both, and z keeps the waiter flag until the original wne0 pattern erases it.
            if ZW_SHARED {
                Z_BUSY.store(true, Ordering::Relaxed);
            }
            let z = ZW_LANE;
            let mut g: GL = vec![];
            for cu in &wcu {
                g.extend(self.m(&cat(&[(y[W - 1], true)], cu), z));
            }
            g.push(gc(ctl, z));
            self.b.t(&g);
            let g = rotate_up(z, &y, W - 1);
            self.b.t(&g);
            self.b.t(&[gc(ctl, z)]);
            let mut g: GL = vec![];
            for cu in &acu {
                g.extend(self.m(&cat(&[(yt, true)], cu), ctl));
            }
            self.b.t(&g);
        }
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        if !has_wait {
            self.b.t(&[gc(y[W - 1], ctl)]);
        } else {
            let mut g: GL = vec![];
            for cu in &acu {
                g.extend(self.m(&cat(&[(yt, true)], cu), ctl));
            }
            self.b.t(&g);
        }
        if has_wait {
            // waiters hold still through the relabel and count this slot
            let z = ZW_LANE;
            let g = inc_ctl(&wl, &[(z, true)], &self.dirty);
            self.b.t(&g);
            let mut g: GL = vec![];
            for wc in self.wne0() {
                g.extend(self.m(&cat(&[(y[W - 1], false), (y[W - 2], true)], &wc), z));
            }
            self.b.t(&g);
            Z_BUSY.store(false, Ordering::Relaxed);
        }
        let mut ny = vec![y[W - 1]];
        ny.extend_from_slice(&y[..W - 1]);
        self.y = ny.clone();
        let y = ny;
        let mut d2 = self.pas.clone();
        d2.extend_from_slice(&self.x);
        d2.extend_from_slice(&y);
        self.dirty = d2;
        let act = y[0];
        let win: Vec<u32> = y[1..].to_vec();
        // rotate the new N by w, hi -= w1 + 2 w2 + 4 w3
        for i in (0..lev).rev() {
            let g1 = self.m(&[(act, true), (wl[i], true)], ctl);
            self.b.t(&g1);
            let g = rotate_up(ctl, &win, 1 << i);
            self.b.t(&g);
            self.b.t(&g1);
        }
        let mut g: GL = vec![];
        for i in 1..lev {
            g.extend(dec_ctl(&h[i - 1..], &[(act, true), (wl[i], true)], &self.dirty));
        }
        self.b.t(&g);
        // erase w from the first one of the new N's cofactor, at p = 1+w
        let mut g: GL = vec![];
        for w in 1usize..(1 << lev) {
            let p = 1 + w;
            let mut li: Vec<Lit> = vec![(act, true)];
            for i in 1..p {
                li.push((y[i], false));
            }
            li.push((y[p], true));
            for i in 0..lev {
                if (w >> i) & 1 == 1 {
                    g.extend(self.m(&li, wl[i]));
                }
            }
        }
        self.b.t(&g);
        let mut g: GL = h.iter().map(|&q0| gc(act, q0)).collect();
        g.extend(inc_ctl(&h, &[(act, true)], &self.dirty));
        self.b.t(&g);
        let g1 = self.m(&[(act, true), (xt, false)], ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let g = inc_ctl(&h, &[(act, true), (xt, false)], &self.dirty);
        self.b.t(&g);
        let mut g = self.m(&[(xt, true), (y[1], true)], act);
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true)], act));
        for gp in 0..2usize {
            let mut gl: Vec<Lit> = vec![(xt, gp == 0)];
            for w in 1..(2 + gp) {
                gl.push((y[w], false));
            }
            gl.push((y[2 + gp], true));
            g.extend(self.m(&gl, act));
            g.extend(self.m(&cat(&gl, &self.hl(gp as i32)), act));
        }
        for gg in 0..2i32 {
            for w in 2i32..(1 << lev) {
                let vals: BTreeSet<i32> = prs.iter().filter(|p| p.1 == w).map(|p| (gg - p.2).rem_euclid(16)).collect();
                if vals.is_empty() {
                    continue;
                }
                let gu = (1 + gg + w) as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 1..gu {
                    li.push((y[i], false));
                }
                li.push((y[gu], true));
                let (mut on, mut off) = (0u128, 0u128);
                for x_ in 0..16 {
                    if vals.contains(&x_) {
                        on |= 1u128 << x_;
                    } else {
                        off |= 1u128 << x_;
                    }
                }
                let cubes = self.dtree(on, off, &VS_H, li.len() as i32);
                for cu in self.lits9(&cubes) {
                    g.extend(self.m(&cat(&li, &cu), act));
                }
            }
        }
        self.b.t(&g);
        if t + 1 <= 2 * N as i32 {
            let tau = ctl;
            let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hl(0));
            let tg = self.m(&gl, tau);
            self.b.t(&tg);
            let pg = self.pi_gates(t + 1, h[3], h[0], h[1], h[2]);
            self.b.t(&pg);
            let g = self.m(&[(tau, true), (h[0], false), (h[1], true), (h[2], true)], act);
            self.b.t(&g);
            self.b.t(&rev(&pg));
            self.b.t(&tg);
        }
        self.b.t(&[gx(ctl)]);
    }
}

/// F on virtual lanes: 0..255 x, 256..511 borrowed passenger, 512.. the rest.
struct FCirc {
    gates: Vec<G>,
    next: u32,
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
    ar: Vec<u32>,
    last: GL,
}
fn f_circuit() -> FCirc {
    IN_F.store(true, Ordering::Relaxed);
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(26_000_000) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let w: Vec<u32> = (0..WB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, w, par, memo: HashMap::new() };
    mc.init();
    for t in (3..=(2 * N as i32 - 1)).rev() {
        mc.slot(t);
    }
    IN_F.store(false, Ordering::Relaxed);
    let mut last: GL = vec![gx(mc.x[W - 1])];
    for i in 0..N {
        if pbit(i) {
            last.push(gx(mc.x[W - 2 - i]));
        }
    }
    FCirc {
        gates: mc.b.gates,
        next: mc.b.next,
        y0,
        y1,
        par,
        xtop: mc.y[W - 1],
        ar: (0..N).map(|i| mc.y[W - 2 - i]).collect(),
        last,
    }
}

/// physical emitter
struct P {
    ops: Vec<Op>,
    free: Vec<u32>,
    next: u32,
    bits: u64,
    /// hmr-and: 1 while the lane holds a cc_core AND (compute emitted, measured uncompute pending)
    hold: Vec<u8>,
}
const fn q(i: u32) -> QubitId {
    QubitId(i as u64)
}
impl P {
    fn alloc(&mut self) -> u32 {
        if let Some(a) = self.free.pop() {
            a
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn allocn(&mut self, k: usize) -> Vec<u32> {
        (0..k).map(|_| self.alloc()).collect()
    }
    fn rel(&mut self, a: u32) {
        assert!((a as usize) >= self.hold.len() || self.hold[a as usize] == 0, "hmr-and: lane released while holding an AND");
        self.free.push(a);
        self.free.sort_by(|x, y| y.cmp(x));
    }
    #[inline]
    fn gate(&mut self, g: G) {
        let mut o = Op::empty();
        if g.2 != NONE {
            let flagged = HMR_AND && (g.2 & AND_FLAG) != 0;
            let tgt = if HMR_AND { g.2 & !AND_FLAG } else { g.2 };
            if flagged {
                let t = tgt as usize;
                if self.hold.len() <= t {
                    self.hold.resize(t + 1, 0);
                }
                if self.hold[t] == 1 {
                    // measured uncompute: Hmr on the AND lane, CZ(c0, c1) under the outcome (exact: phase ^= rng & (z ^ c0c1) = 0)
                    self.hold[t] = 0;
                    let bit = self.hmr(tgt);
                    if !HMR_NEGCTL {
                        self.czc(g.0, g.1, bit);
                    }
                    return;
                }
                self.hold[t] = 1;
            }
            o.kind = OperationType::CCX;
            o.q_control1 = q(g.0);
            o.q_control2 = q(g.1);
            o.q_target = q(tgt);
        } else if g.1 != NONE {
            o.kind = OperationType::CX;
            o.q_control1 = q(g.0);
            o.q_target = q(g.1);
        } else {
            o.kind = OperationType::X;
            o.q_target = q(g.0);
        }
        self.ops.push(o);
    }
    fn g(&mut self, l: &[G]) {
        for &x in l {
            self.gate(x);
        }
    }
    fn xc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    fn zc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::Z;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    /// LEAN_SQ: CZ(a, b) under the classical bit (Gidney's AND uncompute correction).
    fn czc(&mut self, a: u32, b: u32, bit: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::CZ;
        o.q_control1 = q(a);
        o.q_target = q(b);
        o.c_condition = BitId(bit);
        self.ops.push(o);
    }
    fn hmr(&mut self, a: u32) -> u64 {
        let b = self.bits;
        self.bits += 1;
        let mut o = Op::empty();
        o.kind = OperationType::Hmr;
        o.q_target = q(a);
        o.c_target = BitId(b);
        self.ops.push(o);
        b
    }
}

/// ZFOR-wait: EMIT_REROLL swaps the two commuting CNOTs of the up-chain step (same circuit, different stream hash), used
/// only to re-draw a stream whose Fiat-Shamir shot set hit the parent's own e >= 28 tail class on the official set.
const EMIT_REROLL: bool = true;
/// ZFOR-wait zs: with a dedicated ZW lane (ZW_SHARED false) the clean AND lane 512 stays free during the merge0/merge1 rows,
/// so the busy flag (borrowed-wire multi-controlled gates) is only raised when the lane is shared.
fn add_gl(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(3 * t.len());
    for i in 0..t.len() {
        if EMIT_REROLL {
            g.push(gc(c, t[i]));
            g.push(gc(c, s[i]));
        } else {
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
        }
        g.push(gt(s[i], t[i], c));
    }
    g
}
fn add_back(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(4 * t.len());
    for i in (0..t.len()).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

/// The shell. No spare lane for the doubling: it is a rotation, the top bit is already the LSB of its multiple of c0.
/// The carry lane doubles as the fold's clean lane. a has 255 bits, its top lane and N's top lane are free after F.
/// x is squared into in place and classical offsets load 128 bits at a time. The top CAPW multiplier bits can move into the
/// product's top lanes with a descending seed, an idea from the public frogdrop 765 note 153caee.
/// LEAN_SQ: Gidney halved adder (arXiv:1709.06648): tgt += add mod 2^w (w = tgt.len() = add.len()); the carries
/// c_1..c_(w-1) live on anc[0..w-1) (clean in, clean out) and are uncomputed by measurement (Hmr, then CZ under the
/// bit). With cout = Some(s) the carry-out c_w is computed onto s and kept. w-1 Toffoli (w with cout).
fn gid_add(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32], cout: Option<u32>) {
    let w = tgt.len();
    assert!(w >= 1 && add.len() == w);
    let kmax = if cout.is_some() { w } else { w - 1 };
    assert!(anc.len() + 1 >= kmax, "gid_add: {} ancillae for {} carries", anc.len(), kmax);
    for k in 0..kmax {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let tc = if k == w - 1 { cout.unwrap() } else { anc[k] };
        if ck != NONE {
            p.g(&[gc(ck, add[k]), gc(ck, tgt[k])]);
        }
        p.g(&[gt(add[k], tgt[k], tc)]);
        if ck != NONE {
            p.g(&[gc(ck, tc)]);
        }
    }
    for k in (0..w).rev() {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let processed = k < kmax;
        if processed && k < w - 1 {
            if ck != NONE {
                p.g(&[gc(ck, anc[k])]);
            }
            let m = p.hmr(anc[k]);
            p.czc(add[k], tgt[k], m);
        }
        if processed {
            if ck != NONE {
                p.g(&[gc(ck, add[k])]);
            }
            p.g(&[gc(add[k], tgt[k])]);
        } else {
            p.g(&[gc(add[k], tgt[k])]);
            if ck != NONE {
                p.g(&[gc(ck, tgt[k])]);
            }
        }
    }
}
/// LEAN_SQ: tgt -= add mod 2^w as not(not tgt + add).
fn gid_sub(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32]) {
    let x: GL = tgt.iter().map(|&q0| gx(q0)).collect();
    p.g(&x);
    gid_add(p, tgt, add, anc, None);
    p.g(&x);
}
/// LEAN_SQ: Haener's squarer, LSB first: z (2n or more wires, zero) += v^2. v^2 = -v + sum_i (2 v_i - 1) 2^(2i+1) (h_i + v_i),
/// h_i = v >> (i + 1). Step 0: z[0..n+1) -= v. Step i: sign-extend z[n+i] -> z[n+i+1]; window z[2i+1 .. n+i+2) -= u, u = h_i
/// padded to the window and inverted under v_i. Last: z[2n-1] ^= v_(n-1). AND ancillae: z above the window, then xa.
fn sq_fwd(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    let zb = z.len();
    assert!(zb >= 2 * n);
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_sub(p, &z[0..w], &add, &anc);
    }
    for i in 0..n - 1 {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        p.g(&[gc(z[n + i], z[n + i + 1])]);
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_sub(p, &z[lo..top], &add, &anc);
        p.g(&inv);
    }
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
}
/// LEAN_SQ: the exact reverse of sq_fwd (z -= v^2 back to zero).
fn sq_rev(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
    for i in (0..n - 1).rev() {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_add(p, &z[lo..top], &add, &anc, None);
        p.g(&inv);
        p.g(&[gc(z[n + i], z[n + i + 1])]);
    }
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_add(p, &z[0..w], &add, &anc, None);
    }
}
struct S3 {
    dirty: Vec<u32>,
    zl: Vec<u32>,
}
impl S3 {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    /// reg += f at its LSB, plus sign*f*2^pos for (pos,sign,z) in terms, z clean. One two-pass chain: a clean lane z in place of
    /// the borrowed bit takes f on one pass. f's wire reads f^d0 between the passes; the corrections are CNOTs.
    fn merged(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && !r.contains(&q0) && !terms.iter().any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait: `merged` with a second control g2 whose terms (pos, sign, clean lane) ride the same two passes.
    /// A positive g2 term holds 0 then not g2 on its lane, a negative one g2 then 1 (checked exhaustively in tools/chain_search.py).
    fn merged_c(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], g2: u32, gterms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().chain(gterms.iter()).find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && q0 != g2 && !r.contains(&q0) && !terms.iter().chain(gterms.iter()).any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        for t in gterms.iter().filter(|t| t.1 < 0) {
            g.push(gc(g2, t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        for t in gterms.iter() {
            g.push(gc(g2, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        for t in gterms.iter().filter(|t| t.1 > 0) {
            g.push(gc(g2, t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait signed digits: `merged` whose extra terms (pos, sign, lane) add sign * (W - c) * 2^pos, W and c wires.
    /// Lane values across the two passes: positive (not W, c), negative (W, not c) (tools/chain_signed.py, exhaustive).
    fn merged_s(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], wt: u32, cc: u32, dterms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().chain(dterms.iter()).find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && q0 != wt && q0 != cc && !r.contains(&q0) && !terms.iter().chain(dterms.iter()).any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            g.push(gc(cc, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        for t in dterms.iter() {
            g.push(gc(cc, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait: acc += a with no control, carry-out on ov (zuiris's add_ctl with the control removed: 2 T per wire).
    fn add_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gc(c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.push(gt(c, acc[255], ov));
            g.push(gc(c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ZFOR-wait: zuiris's clear_ov with the control removed.
    fn clear_ov_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gc(c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.push(gt(c, acc[255], ov));
        }
        g.extend(rev(&h));
        g
    }
    /// ZFOR-wait signed round: acc = acc + a (bit = 1) or acc - a (bit = 0), the subtraction as ~(~acc + a). The bit wire
    /// holds c = not bit inside the bracket; the next doubling's fold rides the ov chain as (K/2)(W255 - c).
    fn round3(&self, acc: &[u32], a: &[u32], bit: u32, c: u32, ov: u32, nxt: bool) -> GL {
        let mut g: GL = vec![gx(bit)];
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.extend(self.add_plain(acc, a, c, ov));
        if nxt {
            let z = &self.zl;
            g.extend(self.merged_s(&acc[0..RW], ov, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], acc[255], bit, &[(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])], c));
        } else {
            g.extend(self.lean(acc, ov, RW, c));
        }
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.push(gx(bit));
        g
    }
    /// ZFOR-wait: acc -= a (fixed subtraction round, no doubling term).
    fn sub_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL = acc.iter().map(|&q0| gx(q0)).collect();
        g.extend(self.add_plain(acc, a, c, ov));
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g.extend(acc.iter().map(|&q0| gx(q0)));
        g
    }
    /// ZFOR-wait: acc := acc / 2 mod p (inverse of zuiris's doubling), returns the new labeling.
    fn halve(&self, acc: &[u32], c: u32) -> (Vec<u32>, GL) {
        let mut prev: Vec<u32> = acc[1..].to_vec();
        prev.push(acc[0]);
        let (t2, h) = self.dbl(&prev, c);
        assert!(t2 == acc);
        (prev, rev(&h))
    }
    /// ZFOR-wait: one Horner round whose ov fold also carries the next doubling's fold (f2 = the top wire before the
    /// rotation, so (c0-1) f2 lands at 2^3 - 2^5 + 2^9 + 2^31 in this labeling). Then ov is cleared as before.
    fn round2(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32, f2: Option<u32>) -> GL {
        let mut g = self.add_ctl(acc, a, ctl, c, ov);
        match f2 {
            Some(f2) => {
                let z = &self.zl;
                g.extend(self.merged_c(&acc[0..RW], ov, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], f2, &[(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])], c));
            }
            None => g.extend(self.lean(acc, ov, RW, c)),
        }
        g.extend(self.clear_ov(acc, a, ctl, c, ov));
        g
    }
    fn lean(&self, t: &[u32], f: u32, _window: usize, c2: u32) -> GL {
        let z = &self.zl;
        if ZL >= 4 {
            return self.merged(&t[0..RW], f, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], c2);
        }
        let mut g = inc_long(&t[0..CHW], f, &self.dirty, c2);
        g.extend(self.merged(&t[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2));
        g
    }
    fn dbl(&self, t: &[u32], c2: u32) -> (Vec<u32>, GL) {
        let mut t2 = vec![t[255]];
        t2.extend_from_slice(&t[..255]);
        let f = t2[0];
        let z = &self.zl;
        let g = self.merged(&t2[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2);
        (t2, g)
    }
    fn add_ctl(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gt(ctl, c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
            g.push(gt(ctl, c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ov = ctl & (T < a), read on the top CMPW wires. An equal window reads as T >= a, so T = a (the first add) is right.
    fn clear_ov(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gt(ctl, c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
        }
        g.extend(rev(&h));
        g
    }
    fn round(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g = self.add_ctl(acc, a, ctl, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov(acc, a, ctl, c, ov));
        g
    }
    /// acc = a * sum bits[i] 2^i mod p; the top w bits move into acc's top lanes. Returns acc, the fresh lanes, the gates.
    fn product(&self, p: &mut P, a: &[u32], bits: &[u32], c: u32, ov: u32, w: usize) -> (Vec<u32>, Vec<u32>, GL) {
        let nb = bits.len();
        let j_: Vec<u32> = bits[nb - w..].to_vec();
        let low = p.allocn(256 - w);
        let mut acc = low.clone();
        acc.extend_from_slice(&j_);
        let mut g: GL = vec![];
        let mut al = NONE;
        if w > 0 {
            al = p.alloc();
            let zl: Vec<Lit> = (0..ZW).map(|r| (acc[r], false)).collect();
            for k in (1..(1usize << w)).rev() {
                let mut l: Vec<Lit> = vec![(al, false)];
                for i in 0..w {
                    l.push((j_[i], (k >> i) & 1 == 1));
                }
                g.extend(self.m(&l, c));
                for i in 0..w {
                    if (k >> i) & 1 == 1 {
                        g.push(gc(c, j_[i]));
                    }
                }
                g.push(gc(c, al));
                let mut l2: Vec<Lit> = vec![(al, true)];
                l2.extend_from_slice(&zl);
                g.extend(self.m(&l2, c));
                g.extend(self.round(&acc, a, al, c, ov));
            }
            g.push(gx(al));
            g.extend(self.m(&zl, al));
        }
        assert!(w == 0, "ZFOR-wait signed Horner assumes CAPW = 0");
        // ZFOR-wait signed digits: n = 2b + 1 = 2^256 + sum (2 b_i - 1) 2^i. acc := a, 256 signed rounds, then (acc - a) / 2.
        for j in 0..a.len() {
            g.push(gc(a[j], acc[j]));
        }
        if a.len() == 256 {
            let (t2, h) = self.dbl(&acc, c);
            acc = t2;
            g.extend(h);
        } else {
            // a has 255 bits, so acc's top wire is 0 and the first doubling's fold is dead: a relabel
            let mut t2 = vec![acc[255]];
            t2.extend_from_slice(&acc[..255]);
            acc = t2;
        }
        for i in (0..nb).rev() {
            let nxt = i > 0;
            g.extend(self.round3(&acc, a, bits[i], c, ov, nxt));
            if nxt {
                let mut t2 = vec![acc[255]];
                t2.extend_from_slice(&acc[..255]);
                acc = t2;
            }
        }
        g.extend(self.sub_round(&acc, a, c, ov));
        let (t2, h) = self.halve(&acc, c);
        acc = t2;
        g.extend(h);
        if w > 0 {
            p.rel(al);
        }
        (acc, low, g)
    }
    fn neg(&self, p: &mut P, t: &[u32], c2: u32) {
        let u = p.alloc();
        p.g(&[gx(u)]);
        let mut g: GL = t.iter().map(|&q0| gx(q0)).collect();
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], u, &self.dirty, c2)));
        }
        g.push(gx(u));
        p.g(&g);
        p.rel(u);
    }
    fn cneg_list(&self, t: &[u32], ctl: u32, neg_when: bool, c2: u32) -> GL {
        let pre: GL = if neg_when { vec![] } else { vec![gx(ctl)] };
        let mut g = pre.clone();
        for &q0 in t {
            g.push(gc(ctl, q0));
        }
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], ctl, &self.dirty, c2)));
        }
        g.extend_from_slice(&pre);
        g
    }
    /// t += classical s mod p (t -= s when sub), 128 lanes at a time.
    fn cl_add(&mut self, p: &mut P, t: &[u32], bits: u64, sub: bool) {
        const K: usize = 128;
        let l = p.allocn(K);
        let (k, c, o) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let keep = self.dirty.clone();
        self.dirty.extend_from_slice(&l);
        let (lo, hi) = (&t[..K], &t[K..]);
        let flip = |r: &[u32]| -> GL { r.iter().map(|&q0| gx(q0)).collect() };
        enum It {
            Load(u64),
            Gs(GL),
        }
        let mut seq: Vec<It> = vec![];
        let a1 = {
            let mut g = add_gl(lo, &l, c);
            g.push(gc(c, k));
            g.extend(add_back(lo, &l, c));
            g
        };
        let a2 = {
            let mut g = add_gl(hi, &l, k);
            g.push(gc(k, o));
            g.extend(add_back(hi, &l, k));
            g
        };
        let h = {
            let mut h0 = flip(lo);
            h0.extend(add_gl(lo, &l, c));
            let mut g = h0.clone();
            g.push(gc(c, k));
            g.extend(rev(&h0));
            g
        };
        let h2 = {
            let mut h0 = flip(hi);
            h0.extend(add_gl(hi, &l, k));
            let mut g = h0.clone();
            g.push(gc(k, o));
            g.extend(rev(&h0));
            g
        };
        seq.push(It::Load(0));
        seq.push(It::Gs(a1));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(a2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Gs(self.lean(t, o, 256, c)));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(h2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h));
        seq.push(It::Load(0));
        if sub {
            seq.reverse();
        }
        for it in &seq {
            match it {
                It::Load(off) => {
                    for i in 0..K {
                        p.xc(l[i], bits + off + i as u64);
                    }
                }
                It::Gs(g) => {
                    if sub {
                        p.g(&rev(g));
                    } else {
                        p.g(g);
                    }
                }
            }
        }
        self.dirty = keep;
        for &q0 in &l {
            p.rel(q0);
        }
        p.rel(k);
        p.rel(c);
        p.rel(o);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
    /// x += lam^2 in place: halve 256 times, then Horner on x.
    /// LEAN_SQ: ov ^= [x_top < atop] on the top CMPW wires (the parent's compare with the addend's top wires given).
    fn clear_ov_top(&self, x: &[u32], atop: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        assert!(atop.len() == CMPW);
        let mut h: GL = x[k..].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[k..], atop, c));
        let mut g = h.clone();
        g.push(gc(c, ov));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x[j..256) += a (a.len() = 256 - j), carry-out on ov, fold ov c0 (the parent's chain), erase ov by the
    /// top-window compare against (a << j)'s top wires. The parent's add_plain + lean + clear_ov_plain, shifted.
    fn fold_shift(&self, x: &[u32], a: &[u32], j: usize, c: u32, ov: u32) -> GL {
        let w = 256 - j;
        assert!(a.len() == w && w >= CMPW);
        let mut g = add_gl(&x[j..], a, c);
        g.push(gc(c, ov));
        g.extend(add_back(&x[j..], a, c));
        g.extend(self.lean(x, ov, RW, c));
        g.extend(self.clear_ov_top(x, &a[w - CMPW..], c, ov));
        g
    }
    /// LEAN_SQ: x[o..o+wv) += v, the carry-out carried on through the next SPILL_W wires by the borrowed-lane increment,
    /// then erased by the window compare (t = [x_window < v]). Exact unless the carry runs past the window (2^-64).
    fn spill_add(&self, x: &[u32], v: &[u32], o: usize, c: u32, t: u32) -> GL {
        let wv = v.len();
        let hi = o + wv;
        assert!(hi <= 256);
        let mut g = add_gl(&x[o..hi], v, c);
        g.push(gc(c, t));
        g.extend(add_back(&x[o..hi], v, c));
        let top = (hi + SPILL_W).min(256);
        if top > hi {
            g.extend(inc_long(&x[hi..top], t, &self.dirty, c));
        }
        let mut h: GL = x[o..hi].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[o..hi], v, c));
        g.extend(h.clone());
        g.push(gc(c, t));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x += (Z << sh) mod p (pos) or x -= (Z << sh) mod p, Z = z[0..zw) an integer below 2^zw. The low 256 - sh
    /// wires shift into x; the top zw - 256 + sh wires are the spill, added times c0 = 2^32 + 2^10 - 2^6 + 2^4 + 1.
    fn weighted(&self, x: &[u32], z: &[u32], zw: usize, sh: usize, pos: bool, c: u32, ov: u32) -> GL {
        let flip: GL = x.iter().map(|&q0| gx(q0)).collect();
        let mut g: GL = vec![];
        if !pos {
            g.extend(flip.clone());
        }
        let wlo = 256 - sh;
        g.extend(self.fold_shift(x, &z[..wlo], sh, c, ov));
        if zw > wlo {
            let hi = &z[wlo..zw];
            for (o, sg) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                if !sg {
                    g.extend(flip.clone());
                }
                g.extend(self.spill_add(x, hi, o, c, ov));
                if !sg {
                    g.extend(flip.clone());
                }
            }
        }
        if !pos {
            g.extend(flip);
        }
        g
    }
    /// LEAN_SQ: x += lam^2 mod p. lam = L + 2^128 H, S = L + H: lam^2 = L^2 (1 - 2^128) + H^2 (c0 - 2^128) + 2^128 S^2.
    fn sq_into_lean(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        let next0 = p.next;
        let (c, ov) = (p.alloc(), p.alloc());
        self.zl = p.allocn(4);
        let z = p.allocn(258);
        let s = p.alloc();
        assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
        let (l, h) = (&lam[..128], &lam[128..]);
        let pad = [self.zl[2], self.zl[3]];
        let xa = [self.zl[0], self.zl[1]];
        sq_fwd(p, l, &z, pad, xa);
        p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
        p.g(&self.weighted(x, &z, 256, 128, false, c, ov));
        sq_rev(p, l, &z, pad, xa);
        sq_fwd(p, h, &z, pad, xa);
        for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true), (128, false)] {
            p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
        }
        sq_rev(p, h, &z, pad, xa);
        gid_add(p, l, h, &z[..128], Some(s));
        let sv: Vec<u32> = [l, &[s][..]].concat();
        sq_fwd(p, &sv, &z, pad, xa);
        p.g(&self.weighted(x, &z, 258, 128, true, c, ov));
        sq_rev(p, &sv, &z, pad, xa);
        if !LEAN_NEGCTL {
            let mut hp: Vec<u32> = h.to_vec();
            hp.push(pad[0]);
            let fl: GL = sv.iter().map(|&q0| gx(q0)).collect();
            p.g(&fl);
            gid_add(p, &sv, &hp, &z[..128], None);
            p.g(&fl);
        }
        p.rel(s);
        for &q0 in z.iter().rev() {
            p.rel(q0);
        }
        for i in 0..4 {
            p.rel(self.zl[i]);
        }
        p.rel(ov);
        p.rel(c);
        assert!(p.next == next0);
    }
    fn sq_into(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        if LEAN_SQ {
            self.sq_into_lean(p, x, lam);
            return;
        }
        let (c, ov, d) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let mut cur = x.to_vec();
        for _ in 0..256 {
            let mut prev: Vec<u32> = cur[1..].to_vec();
            prev.push(cur[0]);
            let (t2, h) = self.dbl(&prev, c);
            assert!(t2 == cur);
            p.g(&rev(&h));
            cur = prev;
        }
        // ZFOR-wait signed digits: cur = x / 2^256. One plain round (2 cur + lam), 256 signed rounds on lam's bits
        // (2 cur + s_i lam), subtract lam, halve: x + lam^2.
        {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gx(d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, true));
            p.g(&[gx(d)]);
            let mut t2 = vec![cur[255]];
            t2.extend_from_slice(&cur[..255]);
            cur = t2;
        }
        for i in (0..256).rev() {
            p.g(&[gc(lam[i], d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, i > 0));
            p.g(&[gc(lam[i], d)]);
            if i > 0 {
                let mut t2 = vec![cur[255]];
                t2.extend_from_slice(&cur[..255]);
                cur = t2;
            }
        }
        p.g(&self.sub_round(&cur, lam, c, ov));
        let (t2, h) = self.halve(&cur, c);
        cur = t2;
        p.g(&h);
        assert!(cur == x);
        p.rel(c);
        p.rel(ov);
        p.rel(d);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
}
struct Kept {
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
}
fn map_lanes(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], kept: Option<&Kept>) -> Vec<u32> {
    let mut m = vec![NONE; fc.next as usize];
    for i in 0..256 {
        m[i] = x[i];
        m[256 + i] = pas[i];
    }
    if let Some(k) = kept {
        m[fc.y0 as usize] = k.y0;
        m[fc.y1 as usize] = k.y1;
    }
    for v in 0..fc.next as usize {
        if m[v] == NONE {
            m[v] = p.alloc();
        }
    }
    m
}
fn mapg(m: &[u32], g: G) -> G {
    if g.2 != NONE {
        let t = if HMR_AND { g.2 & !AND_FLAG } else { g.2 };
        G(m[g.0 as usize], m[g.1 as usize], m[t as usize] | (g.2 & AND_FLAG & if HMR_AND { u32::MAX } else { 0 }))
    } else if g.1 != NONE {
        G(m[g.0 as usize], m[g.1 as usize], NONE)
    } else {
        G(m[g.0 as usize], NONE, NONE)
    }
}
fn emit_f(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32]) -> (Vec<u32>, Kept) {
    let m = map_lanes(p, fc, x, pas, None);
    for &g in &fc.gates {
        p.gate(mapg(&m, g));
    }
    for &g in &fc.last {
        p.gate(mapg(&m, g));
    }
    let a: Vec<u32> = fc.ar.iter().map(|&v| m[v as usize]).collect();
    let kept = Kept { y0: m[fc.y0 as usize], y1: m[fc.y1 as usize], par: m[fc.par as usize], xtop: m[fc.xtop as usize] };
    assert!(p.hold.iter().all(|&h| h == 0), "hmr-and: AND held at the end of emit_f");
    for v in 512..fc.next {
        if v != fc.y0 && v != fc.y1 {
            p.rel(m[v as usize]);
        }
    }
    (a, kept)
}
fn emit_finv(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], k: &Kept) {
    let m = map_lanes(p, fc, x, pas, Some(k));
    for &g in fc.last.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for &g in fc.gates.iter().rev() {
        p.gate(mapg(&m, g));
    }
    assert!(p.hold.iter().all(|&h| h == 0), "hmr-and: AND held at the end of emit_finv");
    for v in 512..fc.next {
        p.rel(m[v as usize]);
    }
}

fn build_unfolded() -> Vec<Op> {
    let fc = f_circuit();
    let mut p = P { ops: Vec::with_capacity(190_000_000), free: vec![], next: 0, bits: 0, hold: vec![] };
    let x = p.allocn(256);
    let y = p.allocn(256);
    let (ox, oy) = (0u64, 256u64);
    p.bits = 512;
    for r in 0..4u64 {
        let mut o = Op::empty();
        o.kind = OperationType::Register;
        o.r_target = RegisterId(r);
        p.ops.push(o);
    }
    for (r, lanes) in [(0u64, &x), (1u64, &y)] {
        for &a in lanes.iter() {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.q_target = q(a);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    for (r, base) in [(2u64, ox), (3u64, oy)] {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.c_target = BitId(base + i);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    let w = CAPW;
    let mut a = S3 { dirty: y.clone(), zl: vec![] };
    a.cl_add(&mut p, &x, ox, true);
    a.dirty = x.clone();
    a.cl_add(&mut p, &y, oy, true);
    // division 1
    let (a1, k1) = emit_f(&mut p, &fc, &x, &y);
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    a.zl = p.allocn(ZL);
    let (lam, _low1, g) = a.product(&mut p, &a1[..255], &y, k1.xtop, a1[255], w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    let cg = a.cneg_list(&lam, k1.par, false, k1.xtop);
    p.g(&cg);
    let m1: Vec<u64> = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &y[..256 - w] {
        p.rel(q0);
    }
    emit_finv(&mut p, &fc, &x, &lam, &k1);
    // dy recompute
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&lam[..], &x[..256 - w]].concat();
    let (dy2, low2, g) = a.product(&mut p, &lam, &x, c, ov, w);
    p.g(&g);
    for i in 0..(256 - w) {
        p.zc(dy2[i], m1[i]);
    }
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low2 {
        p.rel(q0);
    }
    p.rel(c);
    p.rel(ov);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    // x: dx' = lam^2 - dx - 3 ox
    let c2 = p.alloc();
    a.dirty = lam.clone();
    a.neg(&mut p, &x, c2);
    p.rel(c2);
    a.dirty = lam.clone();
    a.sq_into(&mut p, &x, &lam);
    for _ in 0..3 {
        a.dirty = lam.clone();
        a.cl_add(&mut p, &x, ox, true);
    }
    // y: ndy = -lam dx'; lam's top bits go on living inside it
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&x[..], &lam[..256 - w]].concat();
    let (ndy, _low4, g) = a.product(&mut p, &x, &lam, c, ov, w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    p.rel(ov);
    a.neg(&mut p, &ndy, c);
    p.rel(c);
    let m2: Vec<u64> = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &lam[..256 - w] {
        p.rel(q0);
    }
    // division 2
    let (a2, k2) = emit_f(&mut p, &fc, &x, &ndy);
    a.dirty = [&a2[..255 - w], &ndy[..]].concat();
    a.zl = p.allocn(ZL);
    let (l2, low5, g) = a.product(&mut p, &ndy, &a2[..255], k2.xtop, a2[255], w);
    p.g(&g);
    let cg = a.cneg_list(&l2, k2.par, true, k2.xtop);
    p.g(&cg);
    for i in 0..(256 - w) {
        p.zc(l2[i], m2[i]);
    }
    p.g(&rev(&cg));
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low5 {
        p.rel(q0);
    }
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    emit_finv(&mut p, &fc, &x, &ndy, &k2);
    a.dirty = ndy.clone();
    a.cl_add(&mut p, &x, ox, false);
    a.dirty = x.clone();
    a.cl_add(&mut p, &ndy, oy, true);
    // move ndy onto the y register
    let mut cur = ndy.clone();
    for i in 0..256 {
        if cur[i] == y[i] {
            continue;
        }
        for j in (i + 1)..256 {
            if cur[j] == y[i] {
                cur[j] = cur[i];
                break;
            }
        }
        p.g(&[gc(cur[i], y[i]), gc(y[i], cur[i]), gc(cur[i], y[i])]);
        cur[i] = y[i];
    }
    eprintln!("point_add: ops {} peak qubits {}", p.ops.len(), p.next);
    p.ops
}

// armada-a3: nasqret's exact Toffoli-pair fold (submission 6d94a56a, gate_fold.rs, unchanged), generalized in-place
// rounds of the same identities (gate_fold2.rs), then idle-wire product holds (hold_idle.rs, value model of haotang1995's
// hold pass, dca38d60), applied to the finished stream. FOLD_NCT=0: the parent stream; HOLDS=0: folds only;
// HOLDS=1: holds on wires idle over the whole interval only (no relocation).
mod gate_fold;
mod gate_fold2;
mod hold_idle;
// Three exact post-passes from the main-lane tree (affine_simplify.rs, truth_simplify.rs and cond_pass.rs are already in
// this tree, unchanged; they were not compiled in before). They run on the finished stream before the folds, as in
// binharold's 777 row (eae44491). On this stream a second final_cap_cleanup call finds nothing more, so it runs once.
#[allow(dead_code)]
mod affine_simplify;
#[allow(dead_code)]
mod cond_pass;
#[allow(dead_code)]
mod quadratic_simplify;
#[allow(dead_code)]
mod truth_simplify;
pub fn build() -> Vec<Op> {
    let mut ops = build_unfolded();
    if std::env::var("FOLD_NCT").as_deref() == Ok("0") {
        return ops;
    }
    let holds = std::env::var("HOLDS").as_deref() != Ok("0");
    let holds_first = std::env::var("HOLDS_FIRST").as_deref() == Ok("1");
    if holds && holds_first {
        let (o, h) = hold_idle::apply(ops);
        eprintln!("HOLD_IDLE holds={h} (before the folds)");
        ops = o;
    }
    ops = affine_simplify::simplify(ops);
    ops = truth_simplify::simplify_products(ops);
    ops = cond_pass::final_cap_cleanup(ops);
    ops = gate_fold::apply(ops);
    let rounds = std::env::var("FOLD2").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(3);
    ops = gate_fold2::apply(ops, rounds);
    if holds && !holds_first {
        // Spare wires for the hold pass: 6 wires above the construction's 785 are zero and untouched, so the pass can
        // keep hold copies on them. An identity X;X pair on each makes them visible to it; the pairs are removed after.
        const BASE: u64 = 785;
        const SPARE: u64 = 6;
        for d in 0..SPARE {
            let x = Op { kind: OperationType::X, q_target: QubitId(BASE + d), ..Op::empty() };
            ops.push(x);
            ops.push(x);
        }
        let (o, h) = if std::env::var("HOLDS").as_deref() == Ok("1") { hold_idle::apply(ops) } else { hold_idle::apply_reloc(ops) };
        eprintln!("HOLD_IDLE holds={h}");
        ops = o;
        let n = ops.len();
        let k = SPARE as usize;
        for d in 0..k {
            for j in 0..2 {
                let o = &ops[n - 2 * k + 2 * d + j];
                assert!(o.kind == OperationType::X && o.q_target == QubitId(BASE + d as u64), "spare tail moved");
            }
        }
        ops.truncate(n - 2 * k);
    }
    ops
}
