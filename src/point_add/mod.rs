//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

const N: usize = 256;
const D: usize = 3;
const W: usize = N + 1 - D;
const CW: usize = N + 1;
const BE: i32 = 9 + D as i32;

#[allow(dead_code)]
const T4_TYN1: &[(u32, u8)] = &[(20,1),(12,0),(4,1),(4,0)];
#[allow(dead_code)]
const T4_TYT1_1: &[(u32, u8)] = &[(0,1),(0,0)];
#[allow(dead_code)]
const T4_TYT1_2: &[(u32, u8)] = &[(4,1)];
#[allow(dead_code)]
const T4_TYT1_3: &[(u32, u8)] = &[(12,0),(4,0)];
#[allow(dead_code)]
const T4_TYA1: &[(u32, u8)] = &[(8,1),(4,0),(0,1),(0,0)];
#[allow(dead_code)]
const T4_TYN2: &[(u32, u8)] = &[(10,0),(2,0)];
#[allow(dead_code)]
const T4_TYT2_1: &[(u32, u8)] = &[(0,0)];
#[allow(dead_code)]
const T4_TYT2_2: &[(u32, u8)] = &[(2,0)];
#[allow(dead_code)]
const T4_TYT2_3: &[(u32, u8)] = &[];
#[allow(dead_code)]
const T4_TYA2: &[(u32, u8)] = &[(4,0),(0,0)];
#[allow(dead_code)]
const A4_INV2_1: &[u32] = &[0,1];
#[allow(dead_code)]
const A4_TB2_1: &[u32] = &[0];
#[allow(dead_code)]
const T4_INVZ5: &[(u32, u8)] = &[];
#[allow(dead_code)]
const T4_KV2_0Q: &[(u32, u8)] = &[(62,0),(61,1),(58,2),(58,0),(57,2),(57,1),(62,0),(56,2),(56,0),(55,3),(61,1),(54,3),(60,1),(52,3),(56,2),(51,2),(53,1),(50,3),(50,2),(60,1),(48,3),(48,1),(45,1),(44,0),(43,2),(40,1),(40,0),(39,3),(45,1),(38,3),(38,0),(37,3),(41,2),(40,0),(36,3),(36,1),(35,3),(42,0),(34,3),(34,0),(33,3),(33,2),(33,1),(46,0),(32,0),(29,1),(30,0),(28,1),(28,0),(27,2),(30,0),(26,2),(25,2),(25,1),(30,0),(24,2),(24,1),(23,3),(27,2),(21,3),(21,1),(27,2),(26,0),(19,2),(21,1),(17,3),(17,1),(26,0)];
#[allow(dead_code)]
const A4_KQ2_0: &[u32] = &[17,21,23,25,29,31,32,37,38,41,42,43,44,47,48,49,54,55,58,59,60,61];
#[allow(dead_code)]
const T4_KV2_1: &[(u32, u8)] = &[(241,3),(240,3),(225,3),(224,3),(181,3),(180,3),(179,3),(178,3),(177,3),(177,2),(176,3),(176,2),(165,3),(164,3),(163,3),(162,3),(161,2),(160,2),(117,3),(116,3),(115,3),(114,3),(113,3),(113,1),(112,3),(112,1),(101,3),(100,3),(99,3),(98,3),(97,1),(96,1),(62,0),(60,1),(60,0),(58,2),(57,2),(60,0),(56,0),(52,3),(56,2),(50,2),(52,1),(49,3),(49,1),(45,1),(46,0),(43,2),(46,0),(42,0),(41,2),(40,1),(40,0),(39,3),(37,3),(37,1),(43,2),(42,0),(36,3),(36,1),(35,3),(35,2),(45,1),(44,0),(34,3),(34,2),(34,0),(33,3),(33,2),(33,1),(29,1),(30,0),(28,1),(28,0),(27,2),(30,0),(26,2),(25,2),(25,1),(30,0),(24,2),(24,1),(23,3),(27,2),(21,3),(21,1),(27,2),(26,0),(19,2),(21,1),(17,3),(17,1),(26,0)];
#[allow(dead_code)]
const A4_KF2_1_0: &[u32] = &[17,25,27,32,37,38,43,44,46,48,49,53,54,57,60,62,81,83,89,99,100,101,102,105,106,107,108,109,111,113,116,117,118,122,123,124,125,127];
#[allow(dead_code)]
const A4_KU2_1_0_0: &[u32] = &[17,19,25,35,36,37,38,41,42,43,44,45,47,49,52,53,54,58,59,60,61,63];
#[allow(dead_code)]
const A4_KF2_1_1: &[u32] = &[17,21,23,25,29,31,32,37,38,41,42,43,44,47,48,49,54,55,58,59,60,61,81,83,85,87,89,91,93,95,98,99,100,111,113,114,116,117,119,121,123,125];
#[allow(dead_code)]
const A4_IE0_0: &[u32] = &[];
#[allow(dead_code)]
const A4_IE0_1: &[u32] = &[11,14,15];
#[allow(dead_code)]
const A4_IE0_2: &[u32] = &[11,14,15,21,27];
#[allow(dead_code)]
const A4_IE1_0: &[u32] = &[];
#[allow(dead_code)]
const A4_IE1_1: &[u32] = &[11];
#[allow(dead_code)]
const A4_IE2_0: &[u32] = &[];
#[allow(dead_code)]
const T4_LK2_1_END: &[(u32, u8)] = &[(31,5),(29,5),(15,5),(15,4),(13,5),(13,4),(7,5),(7,3),(5,5),(5,3)];
#[allow(dead_code)]
const A4_LK2_1_F0: &[u32] = &[1,3,5,7,22,23,25,27,29,30,37,39,41,43,49,51,53,55,61,62,73,75,86,87,93,94,97,99,101,103,117,118,125,126];
#[allow(dead_code)]
const T4_LK2_1_U0: &[(u32, u8)] = &[(71,5),(69,5),(67,5),(65,5),(23,5),(21,5),(19,5),(17,5),(15,5),(13,5),(11,5),(9,5),(7,5),(7,3),(5,5),(5,3),(3,5),(3,3),(1,5),(1,3)];
#[allow(dead_code)]
const A4_LK2_1_F1: &[u32] = &[1,3,5,7,22,23,25,27,37,38,49,51,53,54,57,59,81,83,85,86,89,91,101,102,105,107,109,111,113,115,125,127];
#[allow(dead_code)]
const A4_LK2_1_R1_0: &[u32] = &[22,23,25,27,33,35,38,39,41,43,45,47,49,51,61,63];
#[allow(dead_code)]
const T4_LK2_1_U1: &[(u32, u8)] = &[(23,5),(21,5),(19,5),(17,5),(15,5),(13,5),(11,5),(9,5),(7,5),(7,4),(5,5),(5,4),(3,5),(3,4),(1,5),(1,4)];
#[allow(dead_code)]
const T4_LK2_2_END: &[(u32, u8)] = &[(31,5),(29,5),(15,5),(15,4),(13,5),(13,4),(7,5),(7,3),(5,5),(5,3)];
#[allow(dead_code)]
const A4_LK2_2_F0: &[u32] = &[1,3,5,7,22,23,25,27,29,30,37,39,41,43,49,51,53,55,61,62,73,75,86,87,93,94,97,99,101,103,117,118,125,126,157,159,173,174,205,207,221,222];
#[allow(dead_code)]
const T4_LK2_2_U0: &[(u32, u8)] = &[(71,5),(69,5),(67,5),(65,5),(23,5),(21,5),(19,5),(17,5),(15,5),(13,5),(11,5),(9,5),(7,5),(7,3),(5,5),(5,3),(3,5),(3,3),(1,5),(1,3)];
#[allow(dead_code)]
const A4_LK2_2_F1: &[u32] = &[1,3,5,7,22,23,25,27,37,38,49,51,53,54,57,59,81,83,85,86,89,91,101,102,105,107,109,111,113,115,125,127,158,159,190,191,222,223];
#[allow(dead_code)]
const A4_LK2_2_R1_0: &[u32] = &[22,23,25,27,33,35,38,39,41,43,45,47,49,51,61,63,158,159];
#[allow(dead_code)]
const T4_LK2_2_U1: &[(u32, u8)] = &[(23,5),(21,5),(19,5),(17,5),(15,5),(13,5),(11,5),(9,5),(7,5),(7,4),(5,5),(5,4),(3,5),(3,4),(1,5),(1,4)];
#[allow(dead_code)]
const A4_LK2_2_F2: &[u32] = &[1,3,5,7,13,15,21,22,29,31,37,38,45,47,53,54,57,59,77,79,85,86,89,91,94,95,109,111,113,115,118,119,125,126,141,143,145,147,150,151,157,159,165,166,169,171,189,191,201,203,213,214,221,222,225,227,229,231,237,239];
#[allow(dead_code)]
const A4_LK2_2_R2_0: &[u32] = &[1,3,5,7,9,11,21,22,29,30,33,35,37,39,45,47];
#[allow(dead_code)]
const A4_LK2_2_R2_1: &[u32] = &[1,3,5,7,17,19,21,23,30,31,33,35,38,39,41,43,45,47,61,63,65,67,69,71,73,75,85,86,93,94,97,99,101,103,109,111];
#[allow(dead_code)]
const T4_LK2_2_U2: &[(u32, u8)] = &[(7,5),(5,5),(3,5),(1,5)];
#[allow(dead_code)]
const T4_LQ2_END: &[(u32, u8)] = &[(31,5),(29,5),(15,5),(15,4),(13,5),(13,4),(7,5),(7,3),(5,5),(5,3)];
#[allow(dead_code)]
const A4_LQ2_F: &[u32] = &[1,3,5,7,22,23,25,27,29,30,37,39,41,43,49,51,53,55,61,62];
#[allow(dead_code)]
const T4_LQ2_U: &[(u32, u8)] = &[(23,5),(21,5),(19,5),(17,5),(15,5),(13,5),(11,5),(9,5),(7,5),(7,3),(5,5),(5,3),(3,5),(3,3),(1,5),(1,3)];
#[allow(dead_code)]
const A4_P2_3: &[u32] = &[33,35];
#[allow(dead_code)]
const A4_P3_3: &[u32] = &[32,34];
#[allow(dead_code)]
const A4_P2_4: &[u32] = &[74,75,89,90,104,105,120,129,131,133,135,137,139,141,142,144,146,148,150,152,154,157,158,170,171,176,177,180,181,188,189,193,196,197,198,201,202,203,205,208,210,212,214,221,222,234,235,240,244,245,248,249,252,253];
#[allow(dead_code)]
const A4_P3_4: &[u32] = &[74,75,89,90,104,105,120,128,130,132,134,136,138,139,140,156,157,170,171,176,177,180,181,188,189,194,196,201,202,203,205,216,240,241,244,249,252];
#[allow(dead_code)]
const T4_L2C: &[(u32, u8)] = &[];
#[allow(dead_code)]
const A4_L2R0: &[u32] = &[];
#[allow(dead_code)]
const A4_L2R1: &[u32] = &[];
#[allow(dead_code)]
const A4_L2S0: &[u32] = &[];
#[allow(dead_code)]
const A4_L2S1: &[u32] = &[];
#[allow(dead_code)]
const T4_L2V2: &[(u32, u8)] = &[];
#[allow(dead_code)]
const T4_L2V3: &[(u32, u8)] = &[];
#[allow(dead_code)]
const T4_L2Q: &[(u32, u8)] = &[];
const ONE: u32 = u32::MAX - 1;
fn t4_kf(m: usize, e: i32, k: i32) -> &'static [u32] {
    match (m, e, k) {
        (2, 1, 0) => A4_KF2_1_0,
        (2, 1, 1) => A4_KF2_1_1,
        _ => panic!("t4_kf"),
    }
}
fn t4_ku(m: usize, e: i32, k: i32, j: usize) -> &'static [u32] {
    match (m, e, k, j) {
        (2, 1, 0, 0) => A4_KU2_1_0_0,
        _ => panic!("t4_ku"),
    }
}
fn t4_kv(m: usize, e: i32, q: bool) -> &'static [(u32, u8)] {
    match (m, e, q) {
        (2, 0, true) => T4_KV2_0Q,
        (2, 1, false) => T4_KV2_1,
        _ => panic!("t4_kv"),
    }
}
fn t4_kq(m: usize, e: i32) -> &'static [u32] {
    match (m, e) {
        (2, 0) => A4_KQ2_0,
        _ => panic!("t4_kq"),
    }
}
fn t4_ie(w: i32, nq: usize) -> &'static [u32] {
    match (w, nq) {
        (0, 0) => A4_IE0_0,
        (0, 1) => A4_IE0_1,
        (0, 2) => A4_IE0_2,
        (1, 0) => A4_IE1_0,
        (1, 1) => A4_IE1_1,
        (2, 0) => A4_IE2_0,
        _ => panic!("t4_ie"),
    }
}
fn t4_il(_w: i32, _nq: usize) -> &'static [u32] {
    panic!("il")
}
fn t4_lkf(l: i32, e: i32, w: i32) -> &'static [u32] {
    match (l, e, w) {
        (2, 1, 0) => A4_LK2_1_F0,
        (2, 1, 1) => A4_LK2_1_F1,
        (2, 2, 0) => A4_LK2_2_F0,
        (2, 2, 1) => A4_LK2_2_F1,
        (2, 2, 2) => A4_LK2_2_F2,
        _ => panic!("t4_lkf"),
    }
}
fn t4_lkr(l: i32, e: i32, w: i32, j: usize) -> &'static [u32] {
    match (l, e, w, j) {
        (2, 1, 1, 0) => A4_LK2_1_R1_0,
        (2, 2, 1, 0) => A4_LK2_2_R1_0,
        (2, 2, 2, 0) => A4_LK2_2_R2_0,
        (2, 2, 2, 1) => A4_LK2_2_R2_1,
        _ => panic!("t4_lkr"),
    }
}
fn t4_lku(l: i32, e: i32, w: i32) -> &'static [(u32, u8)] {
    match (l, e, w) {
        (2, 1, 0) => T4_LK2_1_U0,
        (2, 1, 1) => T4_LK2_1_U1,
        (2, 2, 0) => T4_LK2_2_U0,
        (2, 2, 1) => T4_LK2_2_U1,
        (2, 2, 2) => T4_LK2_2_U2,
        _ => panic!("t4_lku"),
    }
}
fn t4_lke(l: i32, e: i32) -> &'static [(u32, u8)] {
    match (l, e) {
        (2, 1) => T4_LK2_1_END,
        (2, 2) => T4_LK2_2_END,
        _ => panic!("t4_lke"),
    }
}
fn t4_lqf(l: i32) -> &'static [u32] {
    match l {
        2 => A4_LQ2_F,
        _ => panic!("t4_lqf"),
    }
}
fn t4_lqu(l: i32) -> &'static [(u32, u8)] {
    match l {
        2 => T4_LQ2_U,
        _ => panic!("t4_lqu"),
    }
}
fn t4_lqe(l: i32) -> &'static [(u32, u8)] {
    match l {
        2 => T4_LQ2_END,
        _ => panic!("t4_lqe"),
    }
}
fn t4_l2t(_j: usize) -> &'static [u32] {
    panic!("l2t")
}
fn t4_tyn(v: usize) -> &'static [(u32, u8)] {
    match v {
        1 => T4_TYN1,
        2 => T4_TYN2,
        _ => panic!("t4_tyn"),
    }
}
fn t4_tyt(v: usize, m: usize) -> &'static [(u32, u8)] {
    match (v, m) {
        (1, 1) => T4_TYT1_1,
        (1, 2) => T4_TYT1_2,
        (1, 3) => T4_TYT1_3,
        (2, 1) => T4_TYT2_1,
        (2, 2) => T4_TYT2_2,
        (2, 3) => T4_TYT2_3,
        _ => panic!("t4_tyt"),
    }
}
fn t4_tya(v: usize) -> &'static [(u32, u8)] {
    match v {
        1 => T4_TYA1,
        2 => T4_TYA2,
        _ => panic!("t4_tya"),
    }
}
fn t4_inv(w: usize, j: usize) -> &'static [u32] {
    match (w, j) {
        (2, 1) => A4_INV2_1,
        _ => panic!("t4_inv"),
    }
}
fn t4_tb(w: usize, j: usize) -> &'static [u32] {
    match (w, j) {
        (2, 1) => A4_TB2_1,
        _ => panic!("t4_tb"),
    }
}
fn t4_p2(mp: usize) -> &'static [u32] {
    match mp {
        3 => A4_P2_3,
        4 => A4_P2_4,
        _ => panic!("t4_p2"),
    }
}
fn t4_p3(mp: usize) -> &'static [u32] {
    match mp {
        3 => A4_P3_3,
        4 => A4_P3_4,
        _ => panic!("t4_p3"),
    }
}
const NONE: u32 = u32::MAX;
const EB: usize = 2;
/// Clean lane for the AND of many controls inside F.
const ZB: usize = 1;
/// hmr-and (lane zfor-wait): the clean-lane AND of every cc_core call is uncomputed by X-basis measurement (Hmr) and
/// CZ(c0, c1) under the outcome (Gidney arXiv:1709.06648) instead of the unitary Toffoli: -1 T per call.
const HMR_AND: bool = true;
const HMR_NEGCTL: bool = false;
/// Marks both AND gates of a cc_core pair on the target wire; P::gate toggles compute / measured uncompute per lane.
const AND_FLAG: u32 = 1 << 30;
static IN_F: AtomicBool = AtomicBool::new(false);
const PIW: usize = 48;
const ECAP: i32 = 26;
const RW: usize = 64;
/// Clean lanes for the merged fold chain.
const ZL: usize = 4;
/// Each fold chain runs this many wires from its own start: a carry gets j wires with 2^-j.
const CHW: usize = 33;
/// ov is read back on this many top wires.
const CMPW: usize = 34;
/// Multiplier bits consumed into the product.
const CAPW: usize = 5;
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
        let g = aa[i - 1];
        up.extend_from_slice(&[gt(a, b, g), gc(g, a), gc(g, b)]);
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
    } else if ZB > 0 && IN_F.load(Ordering::Relaxed) {
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
/// Minimum cost disjoint decision tree over the hi bits (vars 0..3) and the parity (var 4).
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
fn dtree(on: u128, off: u128, vs: &[usize], base: i32) -> Cubes {
    let mut memo = HashMap::new();
    tree_rec(on, off, 0, base, vs, &mut memo).1
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
    s: Vec<u32>,
    xl: Vec<u32>,
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
            l >= 1 && f <= n && f >= l && !(e == 1 && f == n)
        })
        .collect()
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
        let mut v: Vec<Lit> = Vec::with_capacity(l.len());
        for &(q0, c) in l {
            if let Some(x_) = v.iter().find(|y_| y_.0 == q0) {
                if x_.1 != c {
                    return vec![];
                }
            } else {
                v.push((q0, c));
            }
        }
        mcx(&v, t, &self.dirty)
    }
    fn tvl(&self, a: i32) -> u32 {
        if a <= 0 {
            self.s[(a + D as i32 - 1) as usize]
        } else {
            self.x[a as usize]
        }
    }
    fn tcl(&self, a: usize) -> u32 {
        if a >= W - 1 {
            self.s[D - 1 - (a - (W - 1))]
        } else {
            self.y[a]
        }
    }
    fn tm(&self, lanes: &[u32], tab: &[(u32, u8)], lits: &[Lit]) -> GL {
        let mut g = vec![];
        for &(c, t) in tab {
            let mut l = lits.to_vec();
            for (i, &q0) in lanes.iter().enumerate() {
                if (c >> i) & 1 == 1 {
                    l.push((q0, true));
                }
            }
            g.extend(self.m(&l, lanes[t as usize]));
        }
        g
    }
    fn lm(&self, a: &[Lit], b: &[Lit]) -> Vec<Lit> {
        [a, b].concat()
    }
    fn cadd(&self, z: &[u32], v: &[u32], lits: &[Lit]) -> GL {
        // Z += V through V's own lanes: the ladder runs on every shot and is undone, only the writes are controlled
        let n = z.len();
        let inl = |q: u32| lits.iter().any(|x| x.0 == q);
        let clash = v.iter().skip(1).any(|&q| inl(q)) || z.iter().skip(1).any(|&q| inl(q));
        if n >= 2 && v.len() == n && !clash && (!inl(z[0]) || lits.contains(&(v[0], false))) {
            let mut g: GL = vec![];
            for i in 0..n {
                g.push(gc(v[i], z[i]));
            }
            for i in (1..n).rev() {
                g.push(gc(v[i - 1], v[i]));
            }
            for i in 0..n - 1 {
                g.push(gt(z[i], v[i], v[i + 1]));
            }
            for i in (0..n).rev() {
                g.extend(self.m(&self.lm(lits, &[(v[i], true)]), z[i]));
                if i > 0 {
                    g.push(gt(z[i - 1], v[i - 1], v[i]));
                }
            }
            for i in 1..n {
                g.push(gc(v[i - 1], v[i]));
            }
            for i in 0..n {
                g.push(gc(v[i], z[i]));
            }
            return g;
        }
        self.cadd_mono(z, v, lits)
    }
    fn cadd_mono(&self, z: &[u32], v: &[u32], lits: &[Lit]) -> GL {
        let mut g = vec![];
        for j in (0..z.len()).rev() {
            if j < v.len() {
                g.extend(self.m(&self.lm(lits, &[(v[j], true)]), z[j]));
            }
            for k in 0..j {
                if k >= v.len() {
                    continue;
                }
                let ls: Vec<usize> = ((k + 1)..j).collect();
                for ch in 0..(1usize << ls.len()) {
                    let mut mon: Vec<Lit> = vec![(v[k], true), (z[k], true)];
                    let mut ok = true;
                    for (ii, &lv) in ls.iter().enumerate() {
                        if (ch >> ii) & 1 == 0 {
                            if lv >= v.len() {
                                ok = false;
                                break;
                            }
                            mon.push((v[lv], true));
                        } else {
                            mon.push((z[lv], true));
                        }
                    }
                    if ok {
                        g.extend(self.m(&self.lm(lits, &mon), z[j]));
                    }
                }
            }
        }
        g
    }
    fn addmul(&self, z: &[u32], u: &[u32], v: &[u32], lits: &[Lit]) -> GL {
        let mut g = vec![];
        let dd = z.len();
        for i in 0..dd {
            if i < u.len() {
                let vv = &v[..v.len().min(dd - i)];
                g.extend(self.cadd(&z[i..], vv, &self.lm(lits, &[(u[i], true)])));
            }
        }
        g
    }
    fn mul(&self, z: &[u32], u: &[u32], lits: &[Lit]) -> GL {
        let mut g = vec![];
        let dd = z.len();
        for i in (0..dd.saturating_sub(1)).rev() {
            g.extend(self.cadd(&z[i + 1..], &u[1..(dd - i)], &self.lm(lits, &[(z[i], true)])));
        }
        g
    }
    fn addc(&self, z: &[u32], c: u64, lits: &[Lit]) -> GL {
        let mut g = vec![];
        let dd = z.len();
        for i in 0..dd {
            if (c >> i) & 1 == 1 {
                for j in ((i + 1)..dd).rev() {
                    let mut l = lits.to_vec();
                    for q0 in &z[i..j] {
                        l.push((*q0, true));
                    }
                    g.extend(self.m(&l, z[j]));
                }
                g.extend(self.m(lits, z[i]));
            }
        }
        g
    }
    fn neg(&self, z: &[u32], lits: &[Lit]) -> GL {
        let mut g = vec![];
        for &q0 in z {
            g.extend(self.m(lits, q0));
        }
        g.extend(self.addc(z, 1, lits));
        g
    }
    fn swapr(&self, p: &[u32], q0: &[u32], lits: &[Lit]) -> GL {
        let mut g = vec![];
        for (&a, &b) in p.iter().zip(q0.iter()) {
            g.extend(self.m(&self.lm(lits, &[(b, true)]), a));
            g.extend(self.m(&self.lm(lits, &[(a, true)]), b));
            g.extend(self.m(&self.lm(lits, &[(b, true)]), a));
        }
        g
    }
    fn rv(&self, r: &[u32], lits: &[Lit]) -> GL {
        let rr: Vec<u32> = r.iter().rev().cloned().collect();
        let h = r.len() / 2;
        self.swapr(&r[..h], &rr[..h], lits)
    }
    fn mulc(&self, z: &[u32], c: u64, lits: &[Lit]) -> GL {
        let mut g = vec![];
        let dd = z.len();
        for i in (0..dd.saturating_sub(1)).rev() {
            let md = 1u64 << (dd - i - 1);
            g.extend(self.addc(&z[i + 1..], (c >> 1) % md, &self.lm(lits, &[(z[i], true)])));
        }
        g
    }
    fn psub(&self, z: &[u32], lits: &[Lit]) -> GL {
        // Z = p - Z: ~Z + (p + 1), and p + 1 has zero low bits
        let md = 1u64 << z.len();
        let mut g = vec![];
        for &q0 in z {
            g.extend(self.m(lits, q0));
        }
        g.extend(self.addc(z, P0[0].wrapping_add(1) % md, lits));
        g
    }
    fn mulk(&self, z: &[u32], xr: &[u32], yr: &[u32], lits: &[Lit], yeven: bool) -> GL {
        // Z *= (p - X Y), Z odd, X0 & Y0 = 0: Z (X Y - p) by bit i of Z from the top with ripples of Y, then negate
        let dd = z.len();
        let e = P0[0].wrapping_add(1) % (1u64 << dd);
        let mut g: GL = vec![];
        for i in (0..dd.saturating_sub(1)).rev() {
            let li = self.lm(lits, &[(z[i], true)]);
            let md = 1u64 << (dd - i - 1);
            let c = (md - (e >> 1) % md) % md;
            if c != 0 {
                g.extend(self.addc(&z[i + 1..], c, &li));
            }
            for u in 0..dd {
                let (base, vv): (usize, &[u32]) = if yeven || u == 0 { (i + u + 1, &yr[1..]) } else { (i + u, yr) };
                if base >= dd {
                    continue;
                }
                let n = dd - base;
                g.extend(self.cadd(&z[base..], &vv[..n.min(vv.len())], &self.lm(&li, &[(xr[u], true)])));
            }
        }
        for &q0 in &z[1..] {
            g.extend(self.m(lits, q0));
        }
        g
    }
    fn qs(&self, e: i32) -> Vec<u32> {
        let mut o = vec![];
        for i in 0..(D as i32) {
            let k = e - i;
            if k >= 1 {
                o.push(self.x[W - k as usize]);
            } else if k == 0 {
                o.push(self.y[0]);
            }
        }
        o
    }
    fn liv0(&self, e: i32, cl: &[Lit]) -> Vec<Lit> {
        let mut v = cl.to_vec();
        if e >= 3 {
            for j in 1..(e as usize - 1) {
                v.push((self.y[j], false));
            }
        }
        v.push((self.s[0], e & 1 == 1));
        v
    }
    fn pk(&self, i: usize) -> bool {
        pbit(i)
    }
    fn ninv(&self, w: usize) -> usize {
        match w {
            1 | 2 | 3 => 1,
            4 => 3,
            _ => 7,
        }
    }
    fn invz(&self, z: &[u32], lits: &[Lit]) -> GL {
        if z.len() <= 3 {
            return vec![];
        }
        if z.len() == 5 {
            return self.tm(&z[1..], T4_INVZ5, lits);
        }
        let mut g = self.m(&self.lm(lits, &[(z[1], true)]), z[3]);
        g.extend(self.m(&self.lm(lits, &[(z[2], true)]), z[3]));
        g
    }
    fn addmul_q(&self, z: &[u32], u: &[u32], v: &[u32], lits: &[Lit], lowq: bool) -> GL {
        let mut g = vec![];
        let dd = z.len();
        for i in 0..dd {
            if i < u.len() {
                let vv = &v[..v.len().min(dd - i)];
                let mut l = self.lm(lits, &[(u[i], true)]);
                if lowq && i >= 3 {
                    for j in 1..(i - 1) {
                        l.push((self.y[j], false));
                    }
                }
                g.extend(self.cadd(&z[i..], vv, &l));
            }
        }
        g
    }
    fn br_tog(&self, cls: &[Vec<Lit>], x: &[Lit]) -> GL {
        let d = self.x[0];
        let mut g: GL = vec![];
        for l in cls {
            g.extend(self.m(&self.lm(l, x), d));
        }
        g
    }
    fn br_to(&self, cls: &[Vec<Lit>], cur: &mut Vec<Lit>, x: &[Lit]) -> GL {
        // d holds class AND the current branch, recomputed from the class literals
        let y = cur.clone();
        *cur = x.to_vec();
        if y[..] == x[..] {
            return vec![];
        }
        if y.len() == x.len() {
            let dif: Vec<usize> = (0..x.len()).filter(|&i| x[i] != y[i]).collect();
            if dif.len() == 1 && x[dif[0]].0 == y[dif[0]].0 {
                let rest: Vec<Lit> = (0..x.len()).filter(|&i| i != dif[0]).map(|i| x[i]).collect();
                return self.br_tog(cls, &rest);
            }
        }
        [&self.br_tog(cls, &y)[..], &self.br_tog(cls, x)[..]].concat()
    }
    fn usable(&self, cls: Option<&[Vec<Lit>]>, a: &[u32], b: &[u32], s: &[u32]) -> bool {
        match cls {
            None => false,
            Some(c) => !c.is_empty() && !c.iter().any(|l| l.iter().any(|x| a.contains(&x.0) || b.contains(&x.0) || s.contains(&x.0))),
        }
    }
    fn v2c_nof(&self, a: &[u32], b: &[u32], s: &[u32], q: &[u32], qone: bool) -> GL {
        self.v2c_nofq(a, b, s, q, qone, false, None)
    }
    fn v2c_nofq(&self, a: &[u32], b: &[u32], s: &[u32], q: &[u32], qone: bool, lowq: bool, cls: Option<&[Vec<Lit>]>) -> GL {
        let d = self.x[0];
        let mut g: GL = vec![];
        let addq = |ss: &Self, zz: &[u32], li: &[Lit]| -> GL {
            if qone {
                ss.cadd(zz, b, li)
            } else {
                ss.addmul_q(zz, q, b, li, lowq)
            }
        };
        let subq = |ss: &Self, zz: &[u32], li: &[Lit]| -> GL {
            if qone {
                rev(&ss.cadd(zz, s, li))
            } else {
                rev(&ss.addmul_q(zz, q, s, li, lowq))
            }
        };
        let l0: Vec<Lit> = vec![(d, true)];
        if self.usable(cls, a, b, s) {
            let c = cls.unwrap();
            let mut cur: Vec<Lit> = vec![];
            g.extend(self.br_to(c, &mut cur, &[(b[0], true), (s[0], true)]));
            g.extend(addq(self, a, &l0));
            g.extend(self.mul(a, s, &l0));
            g.extend(self.psub(a, &l0));
            g.extend(rev(&self.mul(a, b, &l0)));
            g.extend(self.br_to(c, &mut cur, &[(b[0], true), (s[0], false)]));
            g.extend(self.invz(b, &l0));
            g.extend(self.mulk(b, a, s, &l0, true));
            g.extend(subq(self, b, &l0));
            g.extend(self.br_to(c, &mut cur, &[(b[0], false)]));
            g.extend(addq(self, a, &l0));
            g.extend(self.invz(a, &l0));
            g.extend(self.mulk(a, s, b, &l0, true));
            g.extend(self.br_to(c, &mut cur, &[(b[0], true)]));
            g.extend(self.swapr(a, s, &l0));
            g.extend(self.br_to(c, &mut cur, &[(a[0], true)]));
            g.extend(self.swapr(b, s, &l0));
            g.extend(self.br_to(c, &mut cur, &[]));
            g.extend(self.rv(a, &l0));
            g.extend(self.rv(b, &l0));
            return g;
        }
        let l1: Vec<Lit> = vec![(d, true), (b[0], true), (s[0], true)];
        let l2: Vec<Lit> = vec![(d, true), (b[0], true), (s[0], false)];
        let l3: Vec<Lit> = vec![(d, true), (b[0], false)];
        g.extend(addq(self, a, &l1));
        g.extend(self.mul(a, s, &l1));
        g.extend(self.psub(a, &l1));
        g.extend(rev(&self.mul(a, b, &l1)));
        g.extend(self.invz(b, &l2));
        g.extend(self.mulk(b, a, s, &l2, true));
        g.extend(subq(self, b, &l2));
        g.extend(addq(self, a, &l3));
        g.extend(self.invz(a, &l3));
        g.extend(self.mulk(a, s, b, &l3, true));
        g.extend(self.swapr(a, s, &[(d, true), (b[0], true)]));
        g.extend(self.swapr(b, s, &[(d, true), (a[0], true)]));
        g.extend(self.rv(a, &l0));
        g.extend(self.rv(b, &l0));
        g
    }
    fn c2v_nof(&self, a: &[u32], b: &[u32], s: &[u32]) -> GL {
        self.c2v_nofc(a, b, s, None)
    }
    fn c2v_nofc(&self, a: &[u32], b: &[u32], s: &[u32], cls: Option<&[Vec<Lit>]>) -> GL {
        let d = self.x[0];
        let tb: Vec<u32> = a.iter().rev().cloned().collect();
        let tt: Vec<u32> = b.iter().rev().cloned().collect();
        let l0: Vec<Lit> = vec![(d, true)];
        let mut g: GL = vec![];
        if self.usable(cls, a, b, s) {
            let c = cls.unwrap();
            let mut cur: Vec<Lit> = vec![];
            g.extend(self.br_to(c, &mut cur, &[(tb[0], true), (tt[0], true), (s[0], true)]));
            g.extend(self.swapr(&tb[1..], &tt[1..], &l0));
            g.extend(self.br_to(c, &mut cur, &[(tt[0], true), (s[0], true)]));
            g.extend(self.mul(&tb, s, &l0));
            g.extend(self.psub(&tb, &l0));
            g.extend(rev(&self.mul(&tb, &tt, &l0)));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], true), (s[0], false)]));
            g.extend(self.invz(&tb, &l0));
            g.extend(self.mulk(&tb, &tt, s, &l0, true));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], true), (s[0], true), (tt[0], false)]));
            g.extend(self.invz(&tb, &l0));
            g.extend(self.mulk(&tb, s, &tt, &l0, true));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], false), (tt[0], true), (s[0], false)]));
            g.extend(self.invz(&tt, &l0));
            g.extend(self.mulk(&tt, s, &tb, &l0, true));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], true), (tt[0], true), (s[0], true)]));
            g.extend(self.swapr(&tb[1..], &s[1..], &l0));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], false), (tt[0], true), (s[0], false)]));
            g.extend(self.swapr(&tb[1..], &s[1..], &l0));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], false), (s[0], true)]));
            g.extend(self.swapr(&tt[1..], &s[1..], &l0));
            g.extend(self.br_to(c, &mut cur, &[(tb[0], true)]));
            g.extend(self.swapr(&tt[1..], &s[1..], &l0));
            g.extend(self.swapr(&tt[..1], &s[..1], &l0));
            g.extend(self.br_to(c, &mut cur, &[]));
            g.extend(self.rv(a, &l0));
            g.extend(self.rv(b, &l0));
            return g;
        }
        g.extend(self.swapr(&tb[1..], &tt[1..], &[(d, true), (tb[0], true), (tt[0], true), (s[0], true)]));
        let lu: Vec<Lit> = vec![(d, true), (tt[0], true), (s[0], true)];
        g.extend(self.mul(&tb, s, &lu));
        g.extend(self.psub(&tb, &lu));
        g.extend(rev(&self.mul(&tb, &tt, &lu)));
        let la1: Vec<Lit> = vec![(d, true), (tb[0], true), (s[0], false)];
        g.extend(self.invz(&tb, &la1));
        g.extend(self.mulk(&tb, &tt, s, &la1, true));
        let la2: Vec<Lit> = vec![(d, true), (tb[0], true), (s[0], true), (tt[0], false)];
        g.extend(self.invz(&tb, &la2));
        g.extend(self.mulk(&tb, s, &tt, &la2, true));
        let ld: Vec<Lit> = vec![(d, true), (tb[0], false), (tt[0], true), (s[0], false)];
        g.extend(self.invz(&tt, &ld));
        g.extend(self.mulk(&tt, s, &tb, &ld, true));
        g.extend(self.swapr(&tb[1..], &s[1..], &[(d, true), (tb[0], true), (tt[0], true), (s[0], true)]));
        g.extend(self.swapr(&tb[1..], &s[1..], &[(d, true), (tb[0], false), (tt[0], true), (s[0], false)]));
        g.extend(self.swapr(&tt[1..], &s[1..], &[(d, true), (tb[0], true)]));
        g.extend(self.swapr(&tt[1..], &s[1..], &[(d, true), (tb[0], false), (s[0], true)]));
        g.extend(self.swapr(&tt[..1], &s[..1], &[(d, true), (tb[0], true)]));
        g.extend(self.rv(a, &l0));
        g.extend(self.rv(b, &l0));
        g
    }
    fn anf_z(&self, lanes: &[u32], mons: &[u32], tgt: u32) -> GL {
        // carry table where d is clean on every shot: 2k-3 T per monomial
        let mut g = vec![];
        for &mk in mons {
            let mut l: Vec<Lit> = vec![];
            for (i, &q0) in lanes.iter().enumerate() {
                if (mk >> i) & 1 == 1 {
                    l.push((q0, true));
                }
            }
            g.extend(self.mz(&l, tgt, self.x[0]));
        }
        g
    }
    fn anf_to(&self, lanes: &[u32], mons: &[u32], tgt: u32, lits: &[Lit]) -> GL {
        let mut g = vec![];
        for &mk in mons {
            let mut l = lits.to_vec();
            for (i, &q0) in lanes.iter().enumerate() {
                if (mk >> i) & 1 == 1 {
                    l.push((q0, true));
                }
            }
            g.extend(self.m(&l, tgt));
        }
        g
    }
    fn mmq(&self, f: i32) -> i32 {
        CW as i32 - f
    }
    fn areg(&self, f: i32) -> Vec<u32> {
        (0..D as i32).map(|i| self.tvl(W as i32 - f + i)).collect()
    }
    fn blr(&self, l: i32) -> Vec<u32> {
        (0..D as i32)
            .map(|i| {
                let a = W as i32 - l + i;
                if a >= 0 && a < W as i32 {
                    self.y[a as usize]
                } else {
                    NONE
                }
            })
            .collect()
    }
    fn bli(&self, cl: &[Lit], e: i32, w: i32, hb: &[u32], a0: u32, a1: u32, a2: u32) -> Vec<Lit> {
        let mut v = cl.to_vec();
        let m = e >> 1;
        for i in 0..4 {
            v.push((hb[i], (m >> i) & 1 == 1));
        }
        v.push((a0, e & 1 == 1));
        v.push((a1, (w >> 1) & 1 == 1));
        v.push((a2, (w >> 2) & 1 == 1));
        v
    }
    fn known(&self, zs: &[(u32, bool)]) -> GL {
        let d = self.x[0];
        let mut g = vec![];
        for &(q0, v) in zs {
            if v {
                g.extend(self.m(&[(d, true)], q0));
            }
        }
        g
    }
    fn near_gates(&self, aa: &[u32], bl: &[u32]) -> GL {
        let d = self.x[0];
        let s = self.s.clone();
        let pm = P0[0] % (1u64 << D);
        let lo: Vec<Lit> = vec![(d, true), (aa[0], true)];
        let mut g = self.swapr(&s, bl, &lo);
        g.extend(self.rv(&s, &lo));
        let lb = self.lm(&lo, &[(bl[0], true)]);
        g.extend(self.mul(&s, bl, &lb));
        g.extend(self.neg(&s, &lb));
        g.extend(self.addc(&s, pm, &lb));
        g.extend(self.invz(aa, &lb));
        g.extend(self.mul(&s, aa, &lb));
        g.extend(self.invz(aa, &lb));
        let ta: Vec<u32> = bl.iter().rev().cloned().collect();
        for v in 1..=D {
            let mut lv: Vec<Lit> = vec![(d, true)];
            for i in 0..v {
                lv.push((aa[i], false));
            }
            if v < D {
                lv.push((aa[v], true));
                let y_: Vec<u32> = s[..D - v].to_vec();
                let lanes: Vec<u32> = [&y_[..], &ta[..]].concat();
                g.extend(self.tm(&lanes, t4_tyn(v), &lv));
                if D - v > 1 {
                    for _ in 0..self.ninv(D - v) {
                        g.extend(self.mul(&y_, &aa[v..], &lv));
                    }
                }
            }
            g.extend(self.rv(bl, &lv));
            g.extend(self.invz(bl, &lv));
            g.extend(self.mulk_s(bl, aa, &s, &lv));
        }
        g
    }
    fn mulk_s(&self, z: &[u32], xr: &[u32], yr: &[u32], lits: &[Lit]) -> GL {
        let dd = z.len();
        let md = 1u64 << dd;
        let pm = P0[0] % md;
        let mut g = self.mulc(z, pm, lits);
        let mut pinv = 1u64;
        for _ in 0..6 {
            pinv = pinv.wrapping_mul(2u64.wrapping_sub(pm.wrapping_mul(pinv)));
        }
        let w = (md - (pinv % md)) % md;
        for i in (0..dd.saturating_sub(1)).rev() {
            for u in 0..dd {
                for v in 0..dd {
                    if u + v == 0 || u + v > dd - 1 - i {
                        continue;
                    }
                    if yr[v] == NONE {
                        continue;
                    }
                    let c = (w << (u + v - 1)) % (1u64 << (dd - i - 1));
                    if c != 0 {
                        let mut l = self.lm(lits, &[(z[i], true), (xr[u], true)]);
                        if yr[v] != ONE {
                            l.push((yr[v], true));
                        }
                        g.extend(self.addc(&z[i + 1..], c, &l));
                    }
                }
            }
        }
        g
    }
    fn mulspec(&self, z: &[u32], u: &[u32], lits: &[Lit]) -> GL {
        let dd = z.len();
        let mut g = vec![];
        for i in (0..dd.saturating_sub(1)).rev() {
            for j in 1..(dd - i) {
                if j >= u.len() || u[j] == NONE {
                    continue;
                }
                let mut l = self.lm(lits, &[(z[i], true)]);
                if u[j] != ONE {
                    l.push((u[j], true));
                }
                g.extend(self.addc(&z[i + j..], 1, &l));
            }
        }
        g
    }
    fn tail_gates(&self, m: usize, l: i32, _f: i32) -> GL {
        let x = &self.x;
        let d = x[0];
        let s = self.s.clone();
        let pm = P0[0] % (1u64 << D);
        let bl = self.blr(l);
        let mut tbl: Vec<u32> = (0..m - 1).map(|j| x[m - 1 - j]).collect();
        tbl.push(ONE);
        while tbl.len() < D {
            tbl.push(NONE);
        }
        let mut lo: Vec<Lit> = vec![(d, true)];
        if m >= 2 {
            lo.push((x[m - 1], true));
        }
        let mut g = self.swapr(&s, &bl, &lo);
        g.extend(self.rv(&s, &lo));
        let lb = self.lm(&lo, &[(bl[0], true)]);
        g.extend(self.mul(&s, &bl, &lb));
        g.extend(self.neg(&s, &lb));
        g.extend(self.addc(&s, pm, &lb));
        for _ in 0..self.ninv(D) {
            g.extend(self.mulspec(&s, &tbl, &lb));
        }
        let klanes = [0usize, 1, 2, 3, 4];
        for v in 1..D {
            let mut lv = lo.clone();
            for i in 0..v {
                lv.push((bl[i], false));
            }
            lv.push((bl[v], true));
            let y_: Vec<u32> = s[..D - v].to_vec();
            if D - v > 1 {
                g.extend(self.mul(&y_, &bl[v..], &lv));
            }
            let mut lanes = y_.clone();
            // lane values of odd t: for m=2 only tB=3, one lane; m=3 two lanes; m=4 three lanes
            for j in 0..klanes[m - 1] {
                lanes.push(x[m - 1 - j]);
            }
            g.extend(self.tm(&lanes, t4_tyt(v, m), &lv));
        }
        if m >= 2 {
            let le: Vec<Lit> = vec![(d, true), (x[m - 1], false)];
            g.extend(self.rv(&bl, &le));
            g.extend(self.invz(&bl, &le));
            g.extend(self.mulk_s(&bl, &s, &tbl, &le));
        }
        g
    }
    fn short_gates(&self, m: usize, l: i32) -> GL {
        let x = &self.x;
        let d = x[0];
        let s = self.s.clone();
        let bl = self.blr(l);
        let wl = W as i32 - l;
        let mut g: GL = vec![];
        let mut lo: Vec<Lit> = vec![(d, true)];
        if m >= 2 {
            lo.push((x[m - 1], true));
        }
        let mut tbs: Vec<u32> = (0..m - 1).map(|j| x[m - 1 - j]).collect();
        tbs.push(ONE);
        while tbs.len() < D {
            tbs.push(NONE);
        }
        for mp in m..=D {
            if (D as i32 - mp as i32) < -wl {
                continue;
            }
            let mut lp: Vec<Lit> = vec![];
            for i in 0..(D - mp) {
                if bl[i] != NONE {
                    lp.push((bl[i], false));
                }
            }
            lp.push((bl[D - mp], true));
            let lit = self.lm(&lo, &lp);
            for i in (D - mp + 1)..D {
                g.extend(self.swapr(&[s[i]], &[bl[i]], &lit));
            }
            g.extend(self.rv(&s, &lit));
            if D - mp >= 1 {
                g.extend(self.rv(&s[mp - 1..], &lit));
            }
            if m >= 2 {
                for w in 1..m {
                    let mut lw: Vec<Lit> = vec![(d, true), (x[m - 1], false)];
                    for j in 1..w {
                        lw.push((x[m - 1 - j], false));
                    }
                    if w < m - 1 {
                        lw.push((x[m - 1 - w], true));
                    }
                    lw.extend_from_slice(&lp);
                    let r: Vec<u32> = (w..D).map(|j| tbs[j]).collect();
                    let y_: Vec<u32> = s[..D - w].to_vec();
                    if D - w > 1 {
                        g.extend(self.mulspec(&y_, &r, &lw));
                    }
                    let tl: Vec<u32> = (0..mp - 1).map(|j| bl[D - 1 - j]).collect();
                    let mut lanes = y_.clone();
                    lanes.extend_from_slice(&tl[..mp - 1]);
                    g.extend(self.tm(&lanes, t4_tyt(w, mp), &lw));
                    for j in 1..w {
                        g.extend(self.anf_to(&tl[1..w], t4_tb(w, j), tl[j], &lw));
                    }
                    // items: (kind, index) -> lane, kind 0 b, 1 t, 2 T
                    let mut items: Vec<((u8, usize), u32)> = vec![];
                    for i in 0..(D - w) {
                        items.push(((0, w + i), s[i]));
                    }
                    for t in 0..w {
                        items.push(((1, t), s[D - w + t]));
                    }
                    for j in 0..(mp - 1) {
                        items.push((if j < w { (0, j) } else { (2, j) }, tl[j]));
                    }
                    let mut fin: Vec<((u8, usize), u32)> = vec![((0, 0), s[0])];
                    for j in w..(mp - 1) {
                        fin.push(((2, j), s[j]));
                    }
                    for t in 0..(w - 1) {
                        fin.push(((1, t), s[1 + t]));
                    }
                    fin.push(((1, w - 1), s[mp - 1]));
                    for i in 1..(D - mp + 1) {
                        fin.push(((0, i), s[mp - 1 + i]));
                    }
                    for i in (D - mp + 1)..D {
                        fin.push(((0, i), bl[i]));
                    }
                    for (k, dst) in fin.iter() {
                        let src = items.iter().find(|it| it.0 == *k).unwrap().1;
                        if src == *dst {
                            continue;
                        }
                        g.extend(self.swapr(&[src], &[*dst], &lw));
                        for it in items.iter_mut() {
                            if it.1 == *dst {
                                it.1 = src;
                            } else if it.1 == src {
                                it.1 = *dst;
                            }
                        }
                    }
                }
            }
        }
        g
    }
    fn v2c_m(&self, m: usize, e: i32, l: i32, f: i32, zs: &[(u32, bool)], qone: bool) -> GL {
        let d = self.x[0];
        let s = self.s.clone();
        let ld: Vec<Lit> = vec![(d, true)];
        let (a, bl) = (self.areg(f), self.blr(l));
        let n_ = D - m + 1;
        let z: Vec<u32> = zs[..n_].iter().map(|x_| x_.0).collect();
        let pre = self.known(&zs[..n_]);
        let b0 = bl[0];
        let mut g = pre.clone();
        g.extend(self.m(&[(d, true), (b0, false), (a[0], true)], z[0]));
        g.extend(self.m(&[(d, true), (b0, false), (z[0], true)], a[0]));
        g.extend(self.m(&[(d, true), (b0, false)], a[0]));
        g.extend(self.m(&[(d, true), (b0, true)], z[0]));
        let q: Vec<u32> = if qone { vec![] } else { self.qs(e) };
        let sg: Vec<u32> = [&s[..m - 1], &z[..]].concat();
        g.extend(self.v2c_nof(&a, &bl, &sg, &q, qone));
        g.extend(self.m(&ld, a[D - m]));
        for j in 0..n_ {
            g.extend(self.swapr(&[a[j]], &[z[j]], &ld));
        }
        g.extend_from_slice(&pre);
        g
    }
    fn v1_gates(&self, e: i32, l: i32) -> GL {
        let d = self.x[0];
        let s = self.s.clone();
        let ld: Vec<Lit> = vec![(d, true)];
        let bl = self.blr(l);
        let q = self.qs(e);
        let mut g: GL = vec![];
        if pbit(0) {
            g.extend(self.m(&ld, s[0]));
        }
        g.extend(self.m(&[(d, true), (q[0], true), (bl[0], true)], s[0]));
        g.extend(self.addmul(&s, &q, &bl, &ld));
        for i in 0..D {
            if pbit(i) {
                g.extend(self.m(&ld, s[i]));
            }
        }
        g.extend(self.swapr(&s, &bl, &ld));
        g
    }
    fn vstart(&self, li: &[Lit], e: i32, l: i32, f: i32, zf: &[(u32, bool)]) -> GL {
        let n = N as i32;
        let d = self.x[0];
        let y = &self.y;
        let s = self.s.clone();
        let ld: Vec<Lit> = vec![(d, true)];
        let m = self.mmq(f);
        if l <= D as i32 {
            return vec![];
        }
        if m == 1 {
            let bl = self.blr(l);
            let mut g = self.m(li, d);
            g.extend(self.swapr(&s, &bl, &ld));
            for i in 1..D {
                if pbit(i) {
                    g.extend(self.m(&ld, s[i]));
                }
            }
            g.extend(self.m(li, d));
            return g;
        }
        if m as usize <= D {
            let c = self.m(li, d);
            let h = self.vstart_gates(m as usize, &self.areg(f), &self.blr(l), zf);
            return [&c[..], &h[..], &c[..]].concat();
        }
        if f >= n - ECAP - D as i32 - 1 {
            let mut z = li.to_vec();
            for j in (e as usize)..(W - l as usize) {
                z.push((y[j], false));
            }
            for &(q0, c0) in &z {
                if z.iter().any(|x_| x_.0 == q0 && x_.1 != c0) {
                    return vec![];
                }
            }
            let c = self.m(&z, d);
            let h = self.near_gates(&self.areg(f), &self.blr(l));
            return [&c[..], &h[..], &c[..]].concat();
        }
        vec![]
    }
    fn v2c(&self, li: &[Lit], e: i32, l: i32, f: i32, qone: bool, zs: &[(u32, bool)]) -> GL {
        let d = self.x[0];
        let s = self.s.clone();
        let m = self.mmq(f);
        let g = self.m(li, d);
        if m == 1 {
            return [&g[..], &self.v1_gates(e, l)[..], &g[..]].concat();
        }
        if l == D as i32 {
            let (aa, bb) = (self.areg(f), self.blr(l));
            let q: Vec<u32> = if qone { vec![] } else { self.qs(e) };
            let fr = self.swapr(&[s[D - 1]], &[bb[D - 1]], &[(d, true), (aa[D - 1], true)]);
            return [&g[..], &self.v2c_nofq(&aa, &bb, &s, &q, qone, false, Some(&[li.to_vec()]))[..], &fr[..], &g[..]].concat();
        }
        if m as usize <= D {
            return [&g[..], &self.v2c_m(m as usize, e, l, f, zs, qone)[..], &g[..]].concat();
        }
        let q: Vec<u32> = if qone { vec![] } else { self.qs(e) };
        [&g[..], &self.v2c_nofq(&self.areg(f), &self.blr(l), &s, &q, qone, false, Some(&[li.to_vec()]))[..], &g[..]].concat()
    }
    fn c2v_any(&self, li: &[Lit], m: usize, l: i32, f: i32) -> GL {
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let s = self.s.clone();
        let ld: Vec<Lit> = vec![(d, true)];
        let bl = self.blr(l);
        let wl = W as i32 - l;
        if wl > 1 {
            let c = self.m(li, d);
            return [&c[..], &self.tail_gates(m, l, f)[..], &c[..]].concat();
        }
        if wl <= 0 {
            let c = self.m(li, d);
            return [&c[..], &self.short_gates(m, l)[..], &c[..]].concat();
        }
        let la = self.lm(li, &[(y[0], true)]);
        let lb = self.lm(li, &[(y[0], false)]);
        let (c, c2) = (self.m(&la, d), self.m(&lb, d));
        [&c[..], &self.tail_gates(m, l, f)[..], &c[..], &c2[..], &self.short_gates(m, l)[..], &c2[..]].concat()
    }
    fn c2v(&self, li: &[Lit], _e: i32, l: i32, f: i32) -> GL {
        let d = self.x[0];
        let s = self.s.clone();
        let m = self.mmq(f);
        if m as usize <= D {
            return self.c2v_any(li, m as usize, l, f);
        }
        let g = self.m(li, d);
        if l == D as i32 {
            let (aa, bb) = (self.areg(f), self.blr(l));
            let fr = self.swapr(&[s[D - 1]], &[bb[D - 1]], &[(d, true), (aa[D - 1], true)]);
            return [&g[..], &fr[..], &self.c2v_nofc(&aa, &bb, &s, Some(&[li.to_vec()]))[..], &g[..]].concat();
        }
        [&g[..], &self.c2v_nofc(&self.areg(f), &self.blr(l), &s, Some(&[li.to_vec()]))[..], &g[..]].concat()
    }
    fn special(&self, l: i32, f: i32) -> bool {
        l <= D as i32 || self.mmq(f) <= D as i32
    }
    fn hsw(&self, d: u32, l: &[u32], l0: &[u32], base: i32, base0: i32, g: &mut GL) {
        let idx: Vec<usize> = if base < base0 { (0..l.len()).rev().collect() } else { (0..l.len()).collect() };
        for i in idx {
            let (u, v) = (l[i], l0[i]);
            if u != v {
                g.push(gc(v, u));
                g.push(gt(d, u, v));
                g.push(gc(v, u));
            }
        }
    }
    fn hub_moves(&self, items: &[(Vec<Lit>, i32, i32, i32)], digits: bool) -> GL {
        let d = self.x[0];
        let wi = W as i32;
        let f0 = items.iter().map(|it| it.3).max().unwrap();
        let l0 = items.iter().map(|it| it.2).min().unwrap();
        let e0 = items.iter().map(|it| it.1).max().unwrap();
        let a0: Vec<u32> = (0..D).map(|i| self.x[W - f0 as usize + i]).collect();
        let b0: Vec<u32> = (0..D).map(|i| self.y[W - l0 as usize + i]).collect();
        let q0 = self.qs(e0);
        let mut mv: GL = vec![];
        for (li, e, l, f) in items {
            let a: Vec<u32> = (0..D).map(|i| self.x[W - *f as usize + i]).collect();
            let bl: Vec<u32> = (0..D).map(|i| self.y[W - *l as usize + i]).collect();
            let mut sw: GL = vec![];
            self.hsw(d, &a, &a0, wi - *f, wi - f0, &mut sw);
            self.hsw(d, &bl, &b0, wi - *l, wi - l0, &mut sw);
            if digits {
                let q = self.qs(*e);
                self.hsw(d, &q, &q0, -*e, -e0, &mut sw);
            }
            if !sw.is_empty() {
                let c = self.m(li, d);
                mv.extend_from_slice(&c);
                mv.extend_from_slice(&sw);
                mv.extend_from_slice(&c);
            }
        }
        mv
    }
    fn hub_v2c(&self, items: &[(Vec<Lit>, i32, i32, i32)], lic: &[Lit], lowq: bool) -> GL {
        let d = self.x[0];
        let f0 = items.iter().map(|it| it.3).max().unwrap();
        let l0 = items.iter().map(|it| it.2).min().unwrap();
        let e0 = items.iter().map(|it| it.1).max().unwrap();
        let a0: Vec<u32> = (0..D).map(|i| self.x[W - f0 as usize + i]).collect();
        let b0: Vec<u32> = (0..D).map(|i| self.y[W - l0 as usize + i]).collect();
        let q0 = self.qs(e0);
        let mv = self.hub_moves(items, true);
        let c = self.m(lic, d);
        let h = self.v2c_nofq(&a0, &b0, &self.s, &q0, false, lowq, Some(&[lic.to_vec()]));
        [&mv[..], &c[..], &h[..], &c[..], &rev(&mv)[..]].concat()
    }
    fn hub_c2v(&self, items: &[(Vec<Lit>, i32, i32, i32)], lic: &[Vec<Lit>]) -> GL {
        let d = self.x[0];
        let f0 = items.iter().map(|it| it.3).max().unwrap();
        let l0 = items.iter().map(|it| it.2).min().unwrap();
        let a0: Vec<u32> = (0..D).map(|i| self.x[W - f0 as usize + i]).collect();
        let b0: Vec<u32> = (0..D).map(|i| self.y[W - l0 as usize + i]).collect();
        let mv = self.hub_moves(items, false);
        let mut c: GL = vec![];
        for l_ in lic {
            c.extend(self.m(l_, d));
        }
        let h = self.c2v_nofc(&a0, &b0, &self.s, Some(lic));
        [&mv[..], &c[..], &h[..], &c[..], &rev(&mv)[..]].concat()
    }
    fn hub_v2c_q(&self, items: &[(Vec<Lit>, i32, i32, i32)]) -> GL {
        let d = self.x[0];
        let wi = W as i32;
        let f0 = items.iter().map(|it| it.3).max().unwrap();
        let l0 = items.iter().map(|it| it.2).min().unwrap();
        let a0: Vec<u32> = (0..D).map(|i| self.x[W - f0 as usize + i]).collect();
        let b0: Vec<u32> = (0..D).map(|i| self.y[W - l0 as usize + i]).collect();
        let mut mv: GL = vec![];
        let mut fl: GL = vec![];
        for (li, _e, l, f) in items {
            let a: Vec<u32> = (0..D).map(|i| self.x[W - *f as usize + i]).collect();
            let bl: Vec<u32> = (0..D).map(|i| self.y[W - *l as usize + i]).collect();
            let mut sw: GL = vec![];
            self.hsw(d, &a, &a0, wi - *f, wi - f0, &mut sw);
            self.hsw(d, &bl, &b0, wi - *l, wi - l0, &mut sw);
            let c = self.m(li, d);
            if !sw.is_empty() {
                mv.extend_from_slice(&c);
                mv.extend_from_slice(&sw);
                mv.extend_from_slice(&c);
            }
            fl.extend_from_slice(&c);
        }
        let clsq: Vec<Vec<Lit>> = items.iter().map(|it| it.0.clone()).collect();
        let h = self.v2c_nofq(&a0, &b0, &self.s, &[], true, false, Some(&clsq));
        [&mv[..], &fl[..], &h[..], &fl[..], &rev(&mv)[..]].concat()
    }
    fn sp_generic(&self, l: i32, f: i32) -> bool {
        self.mmq(f) > D as i32 && l > D as i32
    }
    fn near_ok(&self, li: &[Lit], e: i32, l: i32, f: i32) -> Option<Vec<Lit>> {
        if !(self.mmq(f) > D as i32 && l > D as i32 && f >= N as i32 - ECAP - D as i32 - 1) {
            return None;
        }
        let mut z = li.to_vec();
        for j in (e as usize)..(W - l as usize) {
            z.push((self.y[j], false));
        }
        for &(q0, c0) in &z {
            if z.iter().any(|x_| x_.0 == q0 && x_.1 != c0) {
                return None;
            }
        }
        Some(z)
    }
    fn hub_near(&self, items: &[(Vec<Lit>, i32, i32, i32)]) -> GL {
        let d = self.x[0];
        let wi = W as i32;
        let it: Vec<(Vec<Lit>, i32, i32)> = items.iter().filter_map(|(li, e, l, f)| self.near_ok(li, *e, *l, *f).map(|z| (z, *l, *f))).collect();
        if it.is_empty() {
            return vec![];
        }
        let f0 = it.iter().map(|x_| x_.2).max().unwrap();
        let l0 = it.iter().map(|x_| x_.1).min().unwrap();
        let (a0, b0) = (self.areg(f0), self.blr(l0));
        let mut mv: GL = vec![];
        let mut fl: GL = vec![];
        for (z, l, f) in &it {
            let mut sw: GL = vec![];
            self.hsw(d, &self.areg(*f), &a0, wi - *f, wi - f0, &mut sw);
            self.hsw(d, &self.blr(*l), &b0, wi - *l, wi - l0, &mut sw);
            let c = self.m(z, d);
            if !sw.is_empty() {
                mv.extend_from_slice(&c);
                mv.extend_from_slice(&sw);
                mv.extend_from_slice(&c);
            }
            fl.extend_from_slice(&c);
        }
        let h = self.near_gates(&a0, &b0);
        [&mv[..], &fl[..], &h[..], &fl[..], &rev(&mv)[..]].concat()
    }
    fn vstart_gates(&self, m: usize, a: &[u32], bl: &[u32], zf: &[(u32, bool)]) -> GL {
        let d = self.x[0];
        let ld: Vec<Lit> = vec![(d, true)];
        let sf: Vec<u32> = self.s[..m - 1].to_vec();
        let mut sg = sf.clone();
        sg.push(a[0]);
        let (f2, f3) = (zf[0].0, zf[1].0);
        let pre = self.known(&zf[..2]);
        let pm = P0[0] % (1u64 << D);
        let pg = P0[0] % (1u64 << m);
        let mut tbs = sf.clone();
        tbs.push(ONE);
        while tbs.len() < D {
            tbs.push(NONE);
        }
        let mut asp: Vec<u32> = vec![ONE];
        asp.extend_from_slice(&a[1..]);
        let mut g = pre.clone();
        g.extend(self.rv(bl, &ld));
        g.extend(self.m(&[(d, true), (bl[0], false)], f3));
        for li_ in [vec![(d, true), (bl[0], true), (a[0], false)], vec![(d, true), (bl[0], true), (a[0], true), (sf[0], false)]] {
            g.extend(self.invz(bl, &li_));
            g.extend(self.mulk_s(bl, a, &tbs, &li_));
        }
        g.extend(self.m(&[(d, true), (bl[0], true), (a[0], true), (sf[0], true)], f2));
        let lo: Vec<Lit> = vec![(d, true), (f2, true)];
        for j in 0..m {
            g.extend(self.swapr(&[sg[j]], &[bl[j]], &lo));
        }
        g.extend(self.mulspec(bl, &asp, &lo));
        g.extend(self.neg(bl, &lo));
        g.extend(self.addc(bl, pm, &lo));
        let mut tas = sg.clone();
        while tas.len() < D {
            tas.push(NONE);
        }
        for _ in 0..self.ninv(D) {
            g.extend(self.mulspec(bl, &tas, &lo));
        }
        g.extend(self.m(&[(d, true), (f3, false), (bl[0], false), (sf[0], true)], f2));
        for w in 1..m {
            let mut lw: Vec<Lit> = vec![(d, true), (f3, true), (sf[0], true)];
            for j in 0..w {
                lw.push((bl[j], false));
            }
            lw.push((bl[w], true));
            g.extend(self.m(&lw, f2));
            for j in 1..w {
                g.extend(self.swapr(&[sf[j]], &[bl[j - 1]], &lo));
            }
            g.extend(self.swapr(&[a[0]], &[bl[w - 1]], &lo));
            g.extend(self.m(&lo, a[0]));
            for j in 1..w {
                g.extend(self.anf_to(&a[1..w], t4_inv(w, j), sf[j], &lo));
            }
            for j in w..m {
                g.extend(self.swapr(&[sg[j]], &[bl[j]], &lo));
            }
            for j in 0..w {
                if j == 0 {
                    g.extend(self.m(&lo, sf[0]));
                } else {
                    g.extend(self.anf_to(&a[1..w], t4_inv(w, j), sf[j], &lo));
                }
            }
            let lanes: Vec<u32> = [&bl[w..], &a[1..]].concat();
            g.extend(self.tm(&lanes, t4_tya(w), &lo));
            let rs: Vec<u32> = (w..D).map(|j| if j < m { sg[j] } else { NONE }).collect();
            for _ in 0..self.ninv(D - w) {
                g.extend(self.mulspec(&bl[w..], &rs, &lo));
            }
            for _ in 0..w {
                for j in 0..D - 1 {
                    g.extend(self.swapr(&[bl[j]], &[bl[j + 1]], &lo));
                }
            }
            let mut lc: Vec<Lit> = vec![(d, true), (f3, true)];
            for j in 0..w {
                lc.push((sg[j], false));
            }
            lc.push((sg[w], true));
            g.extend(self.m(&lc, f2));
        }
        let lb: Vec<Lit> = vec![(d, true), (f3, true), (bl[0], true)];
        g.extend(self.mulspec(&sg, bl, &lb));
        g.extend(self.neg(&sg, &lb));
        g.extend(self.addc(&sg, pg, &lb));
        for _ in 0..self.ninv(m) {
            g.extend(self.mulspec(&sg, &asp, &lb));
        }
        g.extend(self.m(&[(d, true), (bl[0], true), (a[0], true), (sf[0], true)], f3));
        g.extend(self.m(&[(d, true), (bl[0], false), (sf[0], false)], f3));
        g.extend_from_slice(&pre);
        g
    }
    fn hub_vs(&self, items: &[(Vec<Lit>, i32, i32, i32)], m: usize, zf: &[(u32, bool)]) -> GL {
        let d = self.x[0];
        let wi = W as i32;
        let f = items[0].3;
        let l0 = items.iter().map(|it| it.2).min().unwrap();
        let b0 = self.blr(l0);
        let mut mv: GL = vec![];
        let mut fl: GL = vec![];
        for (li, _e, l, _f) in items {
            let mut sw: GL = vec![];
            self.hsw(d, &self.blr(*l), &b0, wi - *l, wi - l0, &mut sw);
            let c = self.m(li, d);
            if !sw.is_empty() {
                mv.extend_from_slice(&c);
                mv.extend_from_slice(&sw);
                mv.extend_from_slice(&c);
            }
            fl.extend_from_slice(&c);
        }
        let t = self.vstart_gates(m, &self.areg(f), &b0, zf);
        [&mv[..], &fl[..], &t[..], &fl[..], &rev(&mv)[..]].concat()
    }
    fn solo_v_rows(&mut self, e: i32, l: i32, f: i32, li: &[Lit], c: u32) {
        let (x, y) = (self.x.clone(), self.y.clone());
        let s = self.s.clone();
        let d = x[0];
        let m = self.mmq(f);
        let wi = W as i32;
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        let act = vec![li.to_vec()];
        for k in 0..=e {
            let w = e - k;
            let aa: Vec<i32>;
            let (tv, sv): (Vec<u32>, Vec<u32>);
            if m == 1 {
                aa = ((wi - l - k).max(1)..(wi - k - 1)).collect();
                tv = aa.iter().map(|&a| x[a as usize]).collect();
                sv = aa
                    .iter()
                    .map(|&a| {
                        let i = a - (wi - l - k);
                        if (i as usize) < D {
                            s[i as usize]
                        } else {
                            y[(a + k) as usize]
                        }
                    })
                    .collect();
            } else {
                aa = ((wi - l - k)..(wi - k - 1)).collect();
                tv = aa.iter().map(|&a| self.tvl(a)).collect();
                sv = aa.iter().map(|&a| y[(a + k) as usize]).collect();
            }
            let t1 = self.tvl(wi - 1 - k);
            let top = if k >= 1 { x[W - k as usize] } else { NONE };
            let mut g = self.row_v(&tv, &sv, t1, top, d, c, NONE, &no_tog, &act, None, None);
            if m == 1 && (w as usize) < D {
                let mut ql: Vec<u32> = vec![];
                for wp in (w + 1)..(D as i32).min(e + 1) {
                    let kp = e - wp;
                    ql.push(if kp >= 1 { x[W - kp as usize] } else { y[0] });
                }
                let lanes: Vec<u32> = [&s[..], &ql[..]].concat();
                let inj = self.anf_to(&lanes, t4_ie(w, ql.len()), c, &[]);
                let injz = self.anf_z(&lanes, t4_ie(w, ql.len()), c);
                g = [&injz[..], &g[..], &inj[..]].concat();
            }
            self.b.t(&g);
            let mut h: GL = vec![];
            if k >= 1 {
                h.extend(self.m(&self.lm(li, &[(x[W - k as usize], true)]), d));
            } else {
                h.extend(self.m(&self.lm(li, &[(d, true)]), y[0]));
                h.extend(self.m(&self.lm(li, &[(y[0], true)]), d));
            }
            self.b.t(&h);
        }
    }
    fn keep_rows(&mut self, m: usize, e: i32, li: &[Lit], c: u32) {
        let (x, y) = (self.x.clone(), self.y.clone());
        let s = self.s.clone();
        let d = x[0];
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        let act = vec![li.to_vec()];
        let xw: Vec<u32> = (0..m - 1).map(|i| x[1 + i]).collect();
        let pat: Vec<u32> = (0..m).map(|i| y[e as usize + i]).collect();
        for k in 0..=e {
            let w = e - k;
            let ku = k as usize;
            let aa: Vec<usize> = ((m + w as usize)..(W - ku - 1)).collect();
            let tv: Vec<u32> = aa.iter().map(|&a| x[a]).collect();
            let sv: Vec<u32> = aa.iter().map(|&a| y[a + ku]).collect();
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let g = self.row_v(&tv, &sv, x[W - 1 - ku], top, d, c, NONE, &no_tog, &act, None, None);
            let mut ql: Vec<u32> = vec![];
            for wp in (w + 1)..=(D as i32 - 1).min(e) {
                let kp = e - wp;
                ql.push(if kp >= 1 { x[W - kp as usize] } else { y[0] });
            }
            let real: Vec<u32> = (0..w as usize).map(|j| x[m + j]).collect();
            let lanes: Vec<u32> = [&s[..], &xw[..], &pat[..], &real[..], &ql[..]].concat();
            let inj = self.anf_to(&lanes, t4_kf(m, e, k), c, &[]);
            let injz = self.anf_z(&lanes, t4_kf(m, e, k), c);
            self.b.t(&[&injz[..], &g[..], &inj[..]].concat());
            let mut h: GL = vec![];
            for j in (0..w as usize).rev() {
                h.extend(self.anf_to(&lanes, t4_ku(m, e, k, j), real[j], &[(d, true)]));
            }
            if k >= 1 {
                h.extend(self.m(&self.lm(li, &[(x[W - ku], true)]), d));
            } else {
                h.extend(self.m(&self.lm(li, &[(d, true)]), y[0]));
                h.extend(self.m(&self.lm(li, &[(y[0], true)]), d));
            }
            self.b.t(&h);
        }
    }
    fn keep_v2c_gates(&self, m: usize, e: i32, li: &[Lit], qone: bool) -> GL {
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let xw: Vec<u32> = (0..m - 1).map(|i| x[1 + i]).collect();
        let pat: Vec<u32> = (0..m).map(|i| y[e as usize + i]).collect();
        let q: Vec<u32> = if qone { vec![] } else { self.qs(e) };
        let lanes: Vec<u32> = [&self.s[..], &xw[..], &pat[..], &q[..]].concat();
        let c_ = self.m(li, d);
        [&c_[..], &self.tm(&lanes, t4_kv(m, e, qone), &[(d, true)])[..], &c_[..]].concat()
    }
    fn keep_inj(&self, m: usize, e: i32, c: u32) -> GL {
        let (x, y) = (&self.x, &self.y);
        let xw: Vec<u32> = (0..m - 1).map(|i| x[1 + i]).collect();
        let pat: Vec<u32> = (0..m).map(|i| y[e as usize + i]).collect();
        let lanes: Vec<u32> = [&self.s[..], &xw[..], &pat[..]].concat();
        self.anf_to(&lanes, t4_kq(m, e), c, &[])
    }
    fn late_lists(&self, l: i32, f: i32, k: i32) -> (Vec<u32>, Vec<u32>) {
        let wi = W as i32;
        let ahi = CW as i32 - f - 1 + k;
        let wires: Vec<usize> = (k..=ahi).rev().filter(|&a| a < wi - 1).map(|a| a as usize).collect();
        let tv: Vec<u32> = wires.iter().map(|&a| self.y[a]).collect();
        let sv: Vec<u32> = wires
            .iter()
            .map(|&a| {
                let j = wi + D as i32 - 1 - f - (a as i32 - k);
                if (l == 1 && j < D as i32) || (l == 2 && j < D as i32 - 2) {
                    self.s[j as usize]
                } else {
                    self.x[a - k as usize]
                }
            })
            .collect();
        (tv, sv)
    }
    /// ql: digit lanes of weights above w, ascending, as present
    fn inj_late(&self, l: i32, f: i32, w: i32, ql: &[u32], c: u32, z: bool) -> GL {
        if l == 1 {
            if w as usize >= D {
                return vec![];
            }
            let lanes: Vec<u32> = [&self.s[..], ql].concat();
            return if z { self.anf_z(&lanes, t4_ie(w, ql.len()), c) } else { self.anf_to(&lanes, t4_ie(w, ql.len()), c, &[]) };
        }
        if w as usize >= D - 1 {
            return vec![];
        }
        let s = &self.s;
        let (ta, tb) = (self.x[W - f as usize + 1], self.x[W - f as usize]);
        let mut lanes: Vec<u32> = s[..D - 2].to_vec();
        lanes.extend_from_slice(&[ta, tb, s[D - 2], s[D - 1]]);
        let nq = ql.len().min(D - 2 - w as usize);
        lanes.extend_from_slice(&ql[..nq]);
        if z { self.anf_z(&lanes, t4_il(w, nq), c) } else { self.anf_to(&lanes, t4_il(w, nq), c, &[]) }
    }
    #[allow(clippy::too_many_arguments)]
    fn solo_c_rows(&mut self, e: i32, l: i32, f: i32, li: &[Lit], alone: bool, cfix: u32, moves: Option<&BTreeMap<i32, (u32, bool)>>, zh: &[u32]) {
        let (x, y) = (self.x.clone(), self.y.clone());
        let d = x[0];
        let h0 = self.e[0];
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        let act = vec![li.to_vec()];
        for k in (0..=e).rev() {
            let ku = k as usize;
            let late = l == 1 || (l == 2 && D >= 4);
            let (tv, sv): (Vec<u32>, Vec<u32>);
            if late {
                let r = self.late_lists(l, f, k);
                tv = r.0;
                sv = r.1;
            } else {
                let ahi = CW - f as usize - 1 + ku;
                let wires: Vec<usize> = (ku..=ahi).rev().collect();
                tv = wires.iter().map(|&a| self.tcl(a)).collect();
                sv = wires
                    .iter()
                    .map(|&a| {
                        let i_ = (a - ku) as i32 - (W as i32 - e);
                        if i_ >= 0 && (i_ as usize) < zh.len() && i_ > e - k {
                            zh[i_ as usize]
                        } else {
                            x[a - ku]
                        }
                    })
                    .collect();
            }
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            if let Some(mv) = moves {
                if let Some(&(src, vv)) = mv.get(&k) {
                    if vv {
                        let mut g = self.m(li, x[W - ku - 1]);
                        g.extend(self.m(li, src));
                        self.b.t(&g);
                    }
                }
            }
            let c = if ((e - k) as usize) < zh.len() {
                zh[(e - k) as usize]
            } else if cfix != NONE {
                cfix
            } else if k >= 2 {
                x[W - ku]
            } else if alone {
                h0
            } else {
                x[W - 2]
            };
            let nn = tv.len();
            let mut g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &act, None, None);
            if late {
                let w = e - k;
                let mut ql: Vec<u32> = vec![];
                for wp in (w + 1)..(D as i32) {
                    let kp = e - wp;
                    if kp >= 1 {
                        ql.push(x[W - kp as usize]);
                    } else if kp == 0 {
                        ql.push(if k == 1 { x[W - 1] } else { y[0] });
                    }
                }
                let inj = self.inj_late(l, f, w, &ql, c, false);
                let injz = self.inj_late(l, f, w, &ql, c, true);
                g = [&injz[..], &g[..], &inj[..]].concat();
            }
            let mut h: GL = vec![];
            if k >= 1 {
                h.extend(self.m(&self.lm(li, &[(x[W - ku], true)]), d));
                h.push(gc(d, x[W - ku]));
                if ((e - k) as usize) < zh.len() {
                    let zz = zh[(e - k) as usize];
                    h.extend(self.m(&self.lm(li, &[(zz, true)]), x[W - ku]));
                    h.extend(self.m(&self.lm(li, &[(x[W - ku], true)]), zz));
                }
                if k == 1 {
                    let xt = x[W - 1];
                    h.extend(self.m(&self.lm(li, &[(y[0], true)]), xt));
                    h.extend(self.m(&self.lm(li, &[(xt, true)]), y[0]));
                }
                h.push(gc(d, top));
            } else {
                let host = x[W - 1];
                h.extend(self.m(&self.lm(li, &[(host, true)]), d));
                h.extend(self.m(&self.lm(li, &[(d, true)]), host));
            }
            self.b.t(&h);
            self.b.t(&rev(&g));
        }
    }
    fn host_lanes(&self, l: i32) -> Vec<u32> {
        let h = D - l as usize;
        (0..h).map(|i| self.y[h - i]).collect()
    }
    fn l3_v2c(&self, e: i32, l: i32, f: i32, li: &[Lit], zh: &[u32], z2: &[(u32, bool)]) -> GL {
        let (x, y) = (&self.x, &self.y);
        let s = self.s.clone();
        let d = x[0];
        let yt = y[W - 1];
        let wf = W - f as usize;
        let lu = l as usize;
        let h = D - lu;
        let ld: Vec<Lit> = vec![(d, true)];
        let zb: Vec<u32> = z2.iter().map(|q0| q0.0).collect();
        let mut aa: Vec<u32> = (0..lu).map(|i| x[wf + i]).collect();
        aa.extend_from_slice(zh);
        let mut bb: Vec<u32> = (0..lu - 1).map(|i| y[W - lu + i]).collect();
        bb.push(yt);
        bb.extend_from_slice(&zb);
        let pre = self.known(z2);
        let q = self.qs(e);
        let c = self.m(li, d);
        let mut g = c.clone();
        g.extend_from_slice(&pre);
        g.extend(self.v2c_nof(&aa, &bb, &s, &q, false));
        g.extend(self.swapr(&[s[D - 1]], &[yt], &ld));
        g.extend(self.m(&ld, yt));
        for i in 0..h - 1 {
            g.extend(self.swapr(&[s[D - 2 - i]], &[zb[i]], &ld));
        }
        let t0 = zh[h - 1];
        let l1: Vec<Lit> = vec![(d, true), (t0, true)];
        let l0: Vec<Lit> = vec![(d, true), (t0, false)];
        g.extend(self.m(&l1, s[lu - 1]));
        g.extend(self.swapr(&[s[lu - 1]], &[zb[h - 1]], &l1));
        g.extend(self.m(&l0, zb[h - 1]));
        g.extend_from_slice(&pre);
        g.extend_from_slice(&c);
        g
    }
    fn l3_c2v(&self, l: i32, f: i32, li: &[Lit], z2: &[(u32, bool)]) -> GL {
        let (x, y) = (&self.x, &self.y);
        let s = self.s.clone();
        let d = x[0];
        let yt = y[W - 1];
        let wf = W - f as usize;
        let lu = l as usize;
        let h = D - lu;
        let ld: Vec<Lit> = vec![(d, true)];
        let zb: Vec<u32> = z2.iter().map(|q0| q0.0).collect();
        let aa: Vec<u32> = (0..D).map(|i| x[wf + i]).collect();
        let mut bb: Vec<u32> = (0..lu - 1).map(|i| y[W - lu + i]).collect();
        bb.push(yt);
        bb.extend_from_slice(&zb);
        let t0 = aa[D - 1];
        let pre = self.known(z2);
        let l1: Vec<Lit> = vec![(d, true), (t0, true)];
        let l0: Vec<Lit> = vec![(d, true), (t0, false)];
        let c = self.m(li, d);
        let mut g = c.clone();
        g.extend_from_slice(&pre);
        g.extend(self.m(&ld, yt));
        g.extend(self.swapr(&[s[D - 1]], &[yt], &ld));
        for i in 0..h - 1 {
            g.extend(self.swapr(&[s[D - 2 - i]], &[zb[i]], &ld));
        }
        g.extend(self.swapr(&[s[lu - 1]], &[zb[h - 1]], &l1));
        g.extend(self.m(&l1, s[lu - 1]));
        g.extend(self.m(&l0, zb[h - 1]));
        g.extend(self.c2v_nof(&aa, &bb, &s));
        g.extend_from_slice(&pre);
        g.extend_from_slice(&c);
        g
    }
    fn late_mode(&self, l: i32, e: i32) -> u8 {
        let h = D as i32 - l;
        if l == 1 {
            return 0;
        }
        if D == 4 && l == 2 {
            return 1;
        }
        if l == 2 && D >= 5 {
            return if e <= 4 { 2 } else { 1 };
        }
        if e <= h + 1 {
            2
        } else {
            3
        }
    }
    fn lk_rows(&mut self, e: i32, l: i32, f: i32, li: &[Lit], c: u32, cfix: bool) -> Vec<u32> {
        let (x, y) = (self.x.clone(), self.y.clone());
        let s = self.s.clone();
        let d = x[0];
        let wf = W - f as usize;
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        let act = vec![li.to_vec()];
        let lu = l as usize;
        let mut win: Vec<u32> = (0..lu).map(|i| x[wf + i]).collect();
        for i in 0..lu - 1 {
            win.push(y[W - lu + i]);
        }
        win.extend_from_slice(&s);
        for k in (0..=e).rev() {
            let w = e - k;
            let ku = k as usize;
            let wires: Vec<usize> = (ku..=(W - lu - 1 - w as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let ck = if k < 2 || cfix { c } else { x[W - ku] };
            let nn = tv.len();
            let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, ck, NONE, &no_tog, &act, None, None);
            let real: Vec<u32> = (0..w as usize).map(|j| y[W - lu - 1 - j]).collect();
            let mut h: GL = vec![];
            if k >= 1 {
                h.extend(self.m(&self.lm(li, &[(x[W - ku], true)]), d));
                h.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    h.extend(self.m(&self.lm(li, &[(y[0], true)]), xt));
                    h.extend(self.m(&self.lm(li, &[(xt, true)]), y[0]));
                }
                h.push(gc(d, top));
            } else {
                let host = x[W - 1];
                h.extend(self.m(&self.lm(li, &[(host, true)]), d));
                h.extend(self.m(&self.lm(li, &[(d, true)]), host));
            }
            let mut ql: Vec<u32> = vec![];
            for wp in (w + 1)..((D as i32).min(e + 1)) {
                let kp = e - wp;
                ql.push(if kp >= 1 { x[W - kp as usize] } else if k == 1 { x[W - 1] } else { y[0] });
            }
            let lanes: Vec<u32> = [&win[..], &real[..], &ql[..]].concat();
            for j in (0..w as usize).rev() {
                h.extend(self.anf_to(&lanes, t4_lkr(l, e, w, j), real[j], &[(d, true)]));
            }
            let ulanes: Vec<u32> = [&win[..], &ql[..]].concat();
            h.extend(self.tm(&ulanes, t4_lku(l, e, w), &[(d, true)]));
            let inj = self.anf_to(&lanes, t4_lkf(l, e, w), ck, &[]);
            let injz = self.anf_z(&lanes, t4_lkf(l, e, w), ck);
            self.b.t(&h);
            self.b.t(&[&inj[..], &rev(&g)[..], &injz[..]].concat());
        }
        win
    }
    fn l2_v(&self, e: i32, f: i32, li: &[Lit]) -> GL {
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let wf = W - f as usize;
        let q = self.qs(e);
        let lanes: Vec<u32> = [&[x[wf], x[wf + 1], y[W - 2]][..], &self.s[..], &q[..]].concat();
        let t = if q.len() == 2 { T4_L2V2 } else { T4_L2V3 };
        let c_ = self.m(li, d);
        [&c_[..], &self.tm(&lanes, t, &[(d, true)])[..], &c_[..]].concat()
    }
    fn l2_arith(&self, e: i32, f: i32, li: &[Lit], zs: &[(u32, bool)]) -> GL {
        let (x, y) = (&self.x, &self.y);
        let s = self.s.clone();
        let d = x[0];
        let yt = y[W - 1];
        let wf = W - f as usize;
        let ld: Vec<Lit> = vec![(d, true)];
        let h = D - 2;
        let za: Vec<u32> = zs[..h].iter().map(|q0| q0.0).collect();
        let zb: Vec<u32> = zs[h..2 * h].iter().map(|q0| q0.0).collect();
        let mut aa: Vec<u32> = vec![x[wf], x[wf + 1]];
        aa.extend_from_slice(&za);
        let mut bb: Vec<u32> = vec![y[W - 2], yt];
        bb.extend_from_slice(&zb);
        let q = self.qs(e);
        let pre = self.known(&zs[..2 * h]);
        let c_ = self.m(li, d);
        let mut g = c_.clone();
        g.extend_from_slice(&pre);
        g.extend(self.v2c_nof(&aa, &bb, &s, &q, false));
        let mut tl: Vec<u32> = zb.iter().rev().cloned().collect();
        tl.push(yt);
        let mut tbl: Vec<u32> = za.iter().rev().cloned().collect();
        tbl.push(aa[1]);
        tbl.push(aa[0]);
        g.extend(self.addmul(&tl, &q[..D - 1], &tbl[..D - 1], &ld));
        let k1 = [s[0], s[1], tbl[0], tl[0]];
        let sr = [s[D - 2], s[D - 1]];
        g.extend(self.anf_to(&k1, A4_L2R0, sr[0], &ld));
        g.extend(self.anf_to(&k1, A4_L2R1, sr[1], &ld));
        let k2: Vec<u32> = [&tbl[..], &sr[..]].concat();
        for j in 0..D - 1 {
            g.extend(self.anf_to(&k2, t4_l2t(j), tl[j], &ld));
        }
        g.extend(self.m(&ld, yt));
        let k3 = [sr[0], sr[1], tbl[0]];
        g.extend(self.anf_to(&k3, A4_L2S0, s[0], &ld));
        g.extend(self.anf_to(&k3, A4_L2S1, s[1], &ld));
        for j in 0..D - 2 {
            g.extend(self.swapr(&[s[j]], &[tbl[j]], &ld));
        }
        g.extend_from_slice(&pre);
        g.extend_from_slice(&c_);
        g
    }
    fn l2_c(&self, f: i32, li: &[Lit]) -> GL {
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let wf = W - f as usize;
        let lanes: Vec<u32> = [&[x[wf], x[wf + 1], y[W - 2]][..], &self.s[..]].concat();
        let c_ = self.m(li, d);
        [&c_[..], &self.tm(&lanes, T4_L2C, &[(d, true)])[..], &c_[..]].concat()
    }
    fn finish(&mut self, e: i32, cl: &[Lit], li: &[Lit], alone: bool) {
        let (x, y) = (self.x.clone(), self.y.clone());
        let (h0, h1) = (self.e[0], self.e[1]);
        let eu = e as usize;
        if alone {
            let g = self.m(cl, x[W - eu]);
            self.b.t(&g);
            return;
        }
        let g = self.m(li, x[W - eu]);
        self.b.t(&g);
        let mut tail: Vec<Lit> = vec![(x[W - 1], false)];
        for j in 2..eu {
            tail.push((x[W - j], false));
        }
        tail.push((x[W - eu], true));
        let g = self.m(&self.lm(cl, &tail), h0);
        self.b.t(&g);
        let g = self.m(&self.lm(&[(h1, true)], &tail), y[W - 1]);
        self.b.t(&g);
    }
    fn solo(&mut self, e: i32, l: i32, f: i32, cl: &[Lit], alone: bool) {
        let (x, y, s) = (self.x.clone(), self.y.clone(), self.s.clone());
        let d = x[0];
        let (h0, h1) = (self.e[0], self.e[1]);
        let m = self.mmq(f);
        let yt = y[W - 1];
        let ld: Vec<Lit> = vec![(d, true)];
        let eu = e as usize;
        let mut lv = cl.to_vec();
        for j in 1..(eu.max(2) - 1) {
            lv.push((y[j], false));
        }
        lv.push((y[eu - 1], true));
        let li: Vec<Lit>;
        if alone {
            let g = self.m(cl, y[eu - 1]);
            self.b.t(&g);
            li = cl.to_vec();
        } else {
            let mut g = self.m(&lv, h0);
            g.extend(self.m(&self.lm(cl, &[(h0, true)]), y[eu - 1]));
            self.b.t(&g);
            li = self.lm(cl, &[(h0, true)]);
        }
        let di = D as i32;
        if m >= 2 && (m - di + e <= 0 || (e >= 3 && e + m - di - 1 < 1)) {
            let c = if e == 2 { h0 } else { y[eu - 2] };
            self.keep_rows(m as usize, e, &li, c);
            let g = self.keep_v2c_gates(m as usize, e, &li, false);
            self.b.t(&g);
            self.solo_c_rows(e, l, f, &li, e == 2, NONE, None, &[]);
            let g = self.c2v_any(&li, m as usize, l, f);
            self.b.t(&g);
            self.finish(e, cl, &li, e == 2);
            return;
        }
        let cv;
        if m >= 2 && m < di {
            cv = if alone { h0 } else { y[(e + m - di - 1) as usize] };
            let c_ = self.m(&li, d);
            let g = [&c_[..], &self.vstart_gates(m as usize, &self.areg(f), &self.blr(l), &[(cv, false), (h1, true)])[..], &c_[..]].concat();
            self.b.t(&g);
        } else if m == 1 {
            cv = if alone { h0 } else { y[eu - 1] };
        } else {
            cv = if alone { h0 } else { y[1] };
        }
        self.solo_v_rows(e, l, f, &li, cv);
        if m >= 2 && m < di {
            let zs: Vec<(u32, bool)> = if alone { vec![(h1, true), (yt, true)] } else { vec![(h0, true), (h1, true), (yt, true), (cv, false)] };
            let c_ = self.m(&li, d);
            let g = [&c_[..], &self.v2c_m(m as usize, e, l, f, &zs, false)[..], &c_[..]].concat();
            self.b.t(&g);
            self.solo_c_rows(e, l, f, &li, alone, NONE, None, &[]);
            let g = self.c2v_any(&li, m as usize, l, f);
            self.b.t(&g);
        } else if m == 1 {
            self.solo_c_rows(e, l, f, &li, alone, NONE, None, &[]);
            let g = self.c2v_any(&li, 1, l, f);
            self.b.t(&g);
        } else {
            match self.late_mode(l, e) {
                3 => {
                    let zh = self.host_lanes(l);
                    let z2: Vec<(u32, bool)> = vec![(h1, true), (h0, true)][..(D - l as usize)].to_vec();
                    let g = self.l3_v2c(e, l, f, &li, &zh, &z2);
                    self.b.t(&g);
                    self.solo_c_rows(e, l, f, &li, alone, NONE, None, &zh);
                    let g = self.l3_c2v(l, f, &li, &z2);
                    self.b.t(&g);
                }
                2 => {
                    let cc = if alone { cv } else { x[W - 2] };
                    let win = self.lk_rows(e, l, f, &li, cc, false);
                    let c_ = self.m(&li, d);
                    let g = [&c_[..], &self.tm(&win, t4_lke(l, e), &ld)[..], &c_[..]].concat();
                    self.b.t(&g);
                }
                1 => {
                    let g = if D == 4 && e < 3 {
                        self.l2_v(e, f, &li)
                    } else {
                        let mut zs: Vec<(u32, bool)> = vec![(h0, true), (h1, true)];
                        for j in 0..(2 * (D - 2)).saturating_sub(2) {
                            zs.push((y[1 + j], false));
                        }
                        self.l2_arith(e, f, &li, &zs)
                    };
                    self.b.t(&g);
                    self.solo_c_rows(e, l, f, &li, alone, NONE, None, &[]);
                    let g = self.l2_c(f, &li);
                    self.b.t(&g);
                }
                _ => {
                    self.solo_c_rows(e, l, f, &li, alone, NONE, None, &[]);
                }
            }
        }
        self.finish(e, cl, &li, alone);
    }
    fn restore(&self, emin: i32) -> GL {
        let x = &self.x;
        let mut v: Vec<Lit> = vec![(self.e[1], true), (x[W - 1], false)];
        for j in 2..(emin as usize) {
            v.push((x[W - j], false));
        }
        self.m(&v, self.y[W - 1])
    }
    fn hide_big(&self, e: i32, w: i32, cl: &[Lit], hb: &[u32], a0: u32, a1: u32, a2: u32) -> Vec<Lit> {
        let (x, yt) = (&self.x, self.y[W - 1]);
        let mut li: Vec<Lit> = self.bli(cl, e, w, hb, a0, a1, a2).into_iter().filter(|q0| q0.0 != yt).collect();
        li.extend_from_slice(&[(x[W - 1], false), (x[W - 2], false)]);
        li
    }
    #[allow(clippy::too_many_arguments)]
    fn big_solo(&mut self, e: i32, w: i32, l: i32, f: i32, hb0: &[u32], w0: u32, w1: u32, w2: u32, cv9: u32, cl: &[Lit]) {
        let (x, y) = (self.x.clone(), self.y.clone());
        let d = x[0];
        let (h0, h1) = (self.e[0], self.e[1]);
        let yt = y[W - 1];
        let l0: Vec<Lit> = self.bli(cl, e, w, hb0, w0, w1, w2).into_iter().filter(|q0| q0.0 != h1).collect();
        let g = self.m(&l0, h1);
        self.b.t(&g);
        let li: Vec<Lit> = vec![(yt, true), (h0, true), (h1, false)];
        self.solo_v_rows(e, l, f, &li, cv9);
        let hv = e >> 1;
        let mut mv: BTreeMap<i32, (u32, bool)> = BTreeMap::new();
        mv.insert(9, (hb0[3], (hv >> 3) & 1 == 1));
        mv.insert(8, (hb0[2], (hv >> 2) & 1 == 1));
        mv.insert(7, (w2, (w >> 2) & 1 == 1));
        mv.insert(6, (w1, (w >> 1) & 1 == 1));
        mv.insert(5, (w0, e & 1 == 1));
        mv.insert(4, (hb0[1], (hv >> 1) & 1 == 1));
        mv.insert(3, (hb0[0], hv & 1 == 1));
        match self.late_mode(l, e) {
            3 => {
                let mut zh: Vec<u32> = (0..(D - l as usize - 1)).map(|i| y[10 + i]).collect();
                zh.push(y[1]);
                let z2: Vec<(u32, bool)> = vec![(h1, false), (h0, true)][..(D - l as usize)].to_vec();
                let g = self.l3_v2c(e, l, f, &li, &zh, &z2);
                self.b.t(&g);
                self.solo_c_rows(e, l, f, &li, false, NONE, Some(&mv), &zh);
                let g = self.l3_c2v(l, f, &li, &z2);
                self.b.t(&g);
            }
            1 => {
                let mut zs: Vec<(u32, bool)> = vec![(h0, true), (h1, false), (y[1], false)];
                for j in 0..(2 * (D - 2)).saturating_sub(3) {
                    zs.push((y[10 + j], false));
                }
                let g = self.l2_arith(e, f, &li, &zs);
                self.b.t(&g);
                self.solo_c_rows(e, l, f, &li, false, NONE, Some(&mv), &[]);
                let g = self.l2_c(f, &li);
                self.b.t(&g);
            }
            _ => {
                self.solo_c_rows(e, l, f, &li, false, NONE, Some(&mv), &[]);
            }
        }
        let z: Vec<Lit> = vec![(h0, true), (h1, false), (x[W - 1], false), (x[W - 2], false)];
        let hm = [x[W - 4], x[W - 5], x[W - 9], x[W - 10]];
        let mut lm: Vec<Lit> = self.bli(cl, e, w, &hm, x[W - 6], x[W - 7], x[W - 8]).into_iter().filter(|q0| q0.0 != yt).collect();
        lm.extend_from_slice(&[(yt, false), (x[W - 1], false), (x[W - 2], false)]);
        let mut g = self.m(&z, yt);
        g.extend(self.m(&self.lm(&[(yt, false)], &z), d));
        g.push(gc(d, h1));
        g.extend(self.m(&lm, d));
        self.b.t(&g);
    }
    fn odd_solo(&mut self, l: i32, f: i32, li: &[Lit], c: u32) {
        let d = self.x[0];
        let m = self.mmq(f);
        let ld: Vec<Lit> = vec![(d, true)];
        if m >= 2 && m < D as i32 {
            self.keep_rows(m as usize, 1, li, c);
            let g = self.keep_v2c_gates(m as usize, 1, li, false);
            self.b.t(&g);
            self.solo_c_rows(1, l, f, li, false, c, None, &[]);
            let g = self.c2v_any(li, m as usize, l, f);
            self.b.t(&g);
        } else if m == 1 {
            self.solo_v_rows(1, l, f, li, c);
            self.solo_c_rows(1, l, f, li, false, c, None, &[]);
            let g = self.c2v_any(li, 1, l, f);
            self.b.t(&g);
        } else {
            self.solo_v_rows(1, l, f, li, c);
            match self.late_mode(l, 1) {
                2 => {
                    let win = self.lk_rows(1, l, f, li, c, true);
                    let c_ = self.m(li, d);
                    let g = [&c_[..], &self.tm(&win, t4_lke(l, 1), &ld)[..], &c_[..]].concat();
                    self.b.t(&g);
                }
                1 => {
                    let g = self.l2_v(1, f, li);
                    self.b.t(&g);
                    self.solo_c_rows(1, l, f, li, false, c, None, &[]);
                    let g = self.l2_c(f, li);
                    self.b.t(&g);
                }
                _ => {
                    self.solo_c_rows(1, l, f, li, false, c, None, &[]);
                }
            }
        }
    }
    fn sp_v(&mut self, e: i32, l: i32, f: i32, li: &[Lit], c: u32) {
        let (x, y, s) = (self.x.clone(), self.y.clone(), self.s.clone());
        let d = x[0];
        let m = self.mmq(f);
        let wi = W as i32;
        let c1 = self.m(li, d);
        let ku = e as usize;
        if m >= 2 && m < D as i32 && m - D as i32 + e < 0 {
            let aa: Vec<usize> = (m as usize..(W - ku - 1)).collect();
            let tv: Vec<u32> = aa.iter().map(|&a| x[a]).collect();
            let sv: Vec<u32> = aa.iter().map(|&a| y[a + ku]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 1 - ku], d, c);
            let inj = self.keep_inj(m as usize, e, c);
            self.b.t(&c1);
            self.b.t(&[&inj[..], &g[..], &inj[..]].concat());
            self.b.t(&c1);
            let g = self.keep_v2c_gates(m as usize, e, li, true);
            self.b.t(&g);
            return;
        }
        let rr: Vec<i32> = ((wi - l - e)..(wi - e - 1)).collect();
        if l < D as i32 {
            let tv: Vec<u32> = rr.iter().map(|&a| x[a as usize]).collect();
            let sv: Vec<u32> = rr.iter().map(|&a| y[(a + e) as usize]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 1 - ku], d, c);
            self.b.t(&c1);
            self.b.t(&g);
            self.b.t(&c1);
            if l == 2 && D == 4 {
                let wf = W - f as usize;
                let lanes: Vec<u32> = [&[x[wf], x[wf + 1], y[W - 2]][..], &s[..]].concat();
                let g = [&c1[..], &self.tm(&lanes, T4_L2Q, &[(d, true)])[..], &c1[..]].concat();
                self.b.t(&g);
            }
            return;
        }
        if m <= D as i32 {
            let (h0_, h1_) = (self.e[0], self.e[1]);
            let zf: Vec<(u32, bool)> = if e == 0 { vec![(h0_, false), (h1_, false)] } else { vec![(h1_, false), (h0_, true)] };
            let g = self.vstart(li, e, l, f, &zf);
            self.b.t(&g);
        }
        let tv: Vec<u32> = rr.iter().map(|&a| self.tvl(a)).collect();
        let sv: Vec<u32> = rr.iter().map(|&a| y[(a + e) as usize]).collect();
        let g = self.plain_v(&tv, &sv, x[W - 1 - ku], d, c);
        self.b.t(&c1);
        self.b.t(&g);
        self.b.t(&c1);
        let (h0, h1) = (self.e[0], self.e[1]);
        let zs: Vec<(u32, bool)> = if e == 0 { vec![(h1, false)] } else { vec![(h0, true), (x[W - 1], false)] };
        if !self.sp_generic(l, f) {
            let g = self.v2c(li, e, l, f, true, &zs);
            self.b.t(&g);
        }
    }
    fn sp_c(&mut self, e: i32, l: i32, f: i32, li: &[Lit], c: u32) {
        let (x, y, s) = (self.x.clone(), self.y.clone(), self.s.clone());
        let d = x[0];
        let c1 = self.m(li, d);
        let ld: Vec<Lit> = vec![(d, true)];
        let ku = e as usize;
        let wf = W - f as usize;
        if l < D as i32 && !(l == 2 && D == 4) {
            let lu = l as usize;
            let mut win: Vec<u32> = (0..lu).map(|i| x[wf + i]).collect();
            for i in 0..lu - 1 {
                win.push(y[W - lu + i]);
            }
            win.extend_from_slice(&s);
            let wires: Vec<usize> = (ku..=(W - lu - 1)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let g = if e == 0 { self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, c) } else { self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, c) };
            let inj = self.anf_to(&win, t4_lqf(l), c, &[]);
            self.b.t(&c1);
            let h = self.tm(&win, t4_lqu(l), &ld);
            self.b.t(&h);
            self.b.t(&[&inj[..], &rev(&g)[..], &inj[..]].concat());
            let h = self.tm(&win, t4_lqe(l), &ld);
            self.b.t(&h);
            self.b.t(&c1);
            return;
        }
        if l == 2 && D == 4 {
            let r = self.late_lists(l, f, e);
            let (tv, sv) = (r.0, r.1);
            let inj = self.inj_late(l, f, 0, &[], c, false);
            let nn = tv.len();
            let g = if e == 0 { self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, c) } else { self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, c) };
            self.b.t(&c1);
            self.b.t(&[&inj[..], &rev(&g)[..], &inj[..]].concat());
            self.b.t(&c1);
            let g = self.l2_c(f, li);
            self.b.t(&g);
            return;
        }
        let wires: Vec<usize> = (ku..=(CW - f as usize - 1 + ku)).rev().collect();
        let tv: Vec<u32> = wires.iter().map(|&a| self.tcl(a)).collect();
        let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
        let nn = tv.len();
        let g = if e == 0 { self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, c) } else { self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, c) };
        self.b.t(&c1);
        self.b.t(&rev(&g));
        self.b.t(&c1);
        if !self.sp_generic(l, f) {
            let g = self.c2v(li, e, l, f);
            self.b.t(&g);
        }
    }
    fn hl(&self, v: i32) -> Vec<Lit> {
        (0..EB).map(|i| (self.e[i], (v >> i) & 1 == 1)).collect()
    }
    fn init(&mut self) {
        let mut g: GL = vec![gx(self.x[0])];
        for i in D..N {
            if pbit(i) {
                g.push(gx(self.x[i + 1 - D]));
            }
        }
        let xl: Vec<u32> = self.xl.clone();
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
        self.row_vz(t, s, t1, top, d, c, m, tog, active, inline, cv, false)
    }
    fn row_vz(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool) -> GL {
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
                        g.extend(self.mz(l, m, d));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(if nz { self.m(&l, c) } else { self.mz(&l, c, d) });
                }
            } else if m != NONE && i < wend {
                g.extend(self.mz(&[(s[i], true), (t[i], true), (m, true)], c, d));
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        if top != NONE {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.mz(&a2, top, d));
            }
            for li in active {
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            }
        } else {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.m(&a2, d));
            }
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
            let v: Vec<usize> = (W.saturating_sub(l)..(W - 1)).collect();
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
    /// As m, with z a lane that is clean here: AND of k controls in 2k-3 T.
    fn mz(&self, l0: &[Lit], t: u32, z: u32) -> GL {
        let mut l: Vec<Lit> = Vec::with_capacity(l0.len());
        for &(q0, p) in l0 {
            match l.iter().find(|x| x.0 == q0) {
                Some(x) => {
                    if x.1 != p {
                        return vec![];
                    }
                }
                None => l.push((q0, p)),
            }
        }
        if l.len() < 3 || ZB > 0 {
            return self.m(l0, t);
        }
        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut g = pre.clone();
        g.extend(cc_core(&cs, t, z));
        g.extend_from_slice(&pre);
        g
    }
    fn hc(&self, c: i32) -> Vec<Lit> {
        vec![(self.e[0], c & 1 == 1), (self.e[1], (c >> 1) & 1 == 1)]
    }
    fn slot(&mut self, t: i32) {
        if t % 2 == 1 {
            self.odd11(t);
        } else {
            self.even11(t);
        }
    }
    fn odd11(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let yt = y[W - 1];
        let (x0, y0) = (x[0], y[0]);
        let (d, ctl) = (x0, x0);
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let al: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        // a shot at the top with e odd >= 3 waits one slot: code 11
        let g = self.m(&[(yt, true), (h1, true)], h0);
        self.b.t(&g);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        if l >= 1 && f <= N as i32 {
            let actv: Vec<Vec<Lit>> = vec![vec![(yt, true), (h0, false)]];
            if self.mmq(f) < D as i32 || l < D as i32 {
                self.odd_solo(l, f, &actv[0], h1);
            } else {
            let g = self.vstart(&actv[0], 1, l, f, &[(h1, false), (h0, false)]);
            self.b.t(&g);
            for k in 0..2usize {
                let alo = W as i32 - l - k as i32;
                let aa: Vec<i32> = (alo..(W as i32 - k as i32 - 1)).collect();
                let tv: Vec<u32> = aa.iter().map(|&a| self.tvl(a)).collect();
                let sv: Vec<u32> = aa.iter().map(|&a| y[(a + k as i32) as usize]).collect();
                let t1 = self.tvl(W as i32 - 1 - k as i32);
                let top = if k >= 1 { x[W - k] } else { NONE };
                let g = self.row_v(&tv, &sv, t1, top, d, h1, NONE, &no_tog, &actv, None, None);
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
            let g = self.v2c(&actv[0], 1, l, f, false, &[(h0, false)]);
            self.b.t(&g);
            for k in [1usize, 0] {
                let ahi = CW - f as usize - 1 + k;
                let wires: Vec<usize> = (k..=ahi).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| self.tcl(a)).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - k]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[k - 1] } else { NONE };
                let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, h1, NONE, &no_tog, &actv, None, None);
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
            let g = self.c2v(&actv[0], 1, l, f);
            self.b.t(&g);
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
        let aa = cat(&[(fl, true)], &self.hc(0));
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[W - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: E'=0 and the second state take code 01 (the common rise gives 00); E'=2 stays 00 (the rise gives 10 and a marker)
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hc(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(0)), ctl));
        g.push(gc(ctl, h0));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hc(1)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(1)), ctl));
        self.b.t(&g);
        let mut g = self.m(&cat(&[(xt, true), (y[0], true)], &self.hc(1)), fl);
        g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hc(0)), fl));
        g.extend(self.m(&cat(&[(y[W - 2], true), (xt, false), (y[0], true)], &self.hc(1)), fl));
        self.b.t(&g);
        self.b.t(&[gx(y[W - 1]), gc(y[W - 1], ctl), gx(y[W - 1])]);
        // one slot of rise for every shot not at the top
        let mut g = self.m(&cat(&[(ctl, true)], &self.hc(0)), y[0]);
        g.extend(self.m(&[(ctl, true), (y[0], true), (h0, false)], h1));
        g.extend(self.m(&[(ctl, true), (h1, false)], h0));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, true), (y[W - 3], true)], h1));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, false), (y[W - 4], true)], h1));
        g.extend(self.m(&cat(&[(ctl, true), (xt, true)], &self.hc(1)), y[W - 3]));
        g.extend(self.m(&cat(&[(ctl, true), (xt, false)], &self.hc(1)), y[W - 4]));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        let yt2 = y[W - 1];
        let mut g = vec![gx(ctl)];
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(3)), ctl));
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(1)), ctl));
        self.b.t(&g);
        self.arrive11(t - 1, &y, ctl);
        // the second state acts at the next even slot
        let g = self.m(&[(yt2, true), (xt, false), (y[0], false), (y[1], true), (h1, false)], h0);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    fn even11(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs: Vec<i32> = pairs(t).into_iter().filter(|&e| e < BE).collect();
        let big: Vec<i32> = prs.iter().cloned().filter(|&e| e >= 2).collect();
        let kk = 1 + big.iter().cloned().max().unwrap_or(0);
        let yt = y[W - 1];
        let (x0, y0, y1) = (x[0], y[0], y[1]);
        let (d, ctl) = (x0, x0);
        let cl: Vec<Lit> = vec![(yt, true), (h1, true)];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let mut g: GL = vec![];
        for &e in &big {
            if e & 1 == 1 {
                let mut l = cl.clone();
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(self.m(&l, h0));
            }
        }
        self.b.t(&g);
        let sp0: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let sp1: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(y1, true)]);
        let sp1c: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(x[W - 1], false), (x[W - 2], false)]);
        let mut nit: Vec<(Vec<Lit>, i32, i32, i32)> = vec![];
        for &e in big.iter().filter(|&&e| !(self.mmq(lf(t, e).1) < D as i32 || lf(t, e).0 < D as i32)) {
            let mut v = cl.clone();
            if e >= 3 {
                for j in 1..(e as usize - 1) {
                    v.push((y[j], false));
                }
            }
            v.push((y[e as usize - 1], true));
            nit.push((v, e, lf(t, e).0, lf(t, e).1));
        }
        if prs.contains(&0) {
            nit.push((sp0.clone(), 0, lf(t, 0).0, lf(t, 0).1));
        }
        let g = self.hub_near(&nit);
        self.b.t(&g);
        let merge0 = prs.contains(&0) && self.sp_generic(lf(t, 0).0, lf(t, 0).1) && big.iter().any(|&e| !(self.mmq(lf(t, e).1) < D as i32 || lf(t, e).0 < D as i32));
        if prs.contains(&0) && !merge0 {
            let (l, f_) = lf(t, 0);
            self.sp_v(0, l, f_, &sp0, h0);
        }
        if prs.contains(&1) {
            let (l, f_) = lf(t, 1);
            if l == D as i32 {
                let lq: Vec<Lit> = vec![(yt, true), (h0, true), (h1, true)];
                let g = self.m(&[(yt, true), (h0, true), (y1, true)], h1);
                self.b.t(&g);
                self.sp_v(1, l, f_, &lq, x[W - 1]);
                self.sp_c(1, l, f_, &lq, x[W - 1]);
                let mut g = self.m(&lq, d);
                g.push(gc(d, h1));
                g.extend(self.m(&[(yt, true), (h0, true), (h1, false), (x[W - 1], false), (x[W - 2], false)], d));
                self.b.t(&g);
            } else {
                let lih: Vec<Lit> = if W as i32 - l > 1 && l > D as i32 { sp1.clone() } else { cat(&[(yt, true)], &self.hc(1)) };
                self.sp_v(1, l, f_, &lih, h1);
            }
        }
        let mut sq: Vec<(Vec<Lit>, i32, i32, i32)> = vec![];
        if prs.contains(&0) && self.sp_generic(lf(t, 0).0, lf(t, 0).1) {
            sq.push((sp0.clone(), 0, lf(t, 0).0, lf(t, 0).1));
        }
        if prs.contains(&1) && self.sp_generic(lf(t, 1).0, lf(t, 1).1) {
            let lih: Vec<Lit> = if W as i32 - lf(t, 1).0 > 1 { sp1.clone() } else { cat(&[(yt, true)], &self.hc(1)) };
            sq.push((lih, 1, lf(t, 1).0, lf(t, 1).1));
        }
        if !sq.is_empty() && !merge0 {
            let g = self.hub_v2c_q(&sq);
            self.b.t(&g);
        }
        let allbig = big.clone();
        let solos: Vec<i32> = big.iter().cloned().filter(|&e| self.mmq(lf(t, e).1) < D as i32 || lf(t, e).0 < D as i32).collect();
        let big: Vec<i32> = big.iter().cloned().filter(|e| !solos.contains(e)).collect();
        let kk = 1 + big.iter().cloned().max().unwrap_or(0);
        for &e in solos.iter().rev() {
            let (l, f) = lf(t, e);
            self.solo(e, l, f, &cl, e == 2);
        }
        let likc = |k: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            if k >= 3 {
                for j in 1..(k as usize - 1) {
                    l.push((y[j], false));
                }
            }
            l
        };
        let lik = |k: i32| -> Vec<Lit> { likc(k) };
        let liv = |e: i32| -> Vec<Lit> {
            let mut v = likc(e);
            v.push((y[e as usize - 1], true));
            v
        };
        let lic = |e: i32| -> Vec<Lit> {
            let mut v = cl.clone();
            for j in 2..e {
                v.push((x[W - j as usize], false));
            }
            v.push((x[W - e as usize], true));
            v
        };
        let m4: Vec<(Vec<Lit>, i32, i32, i32)> = big.iter().filter(|&&e| self.mmq(lf(t, e).1) == D as i32).map(|&e| (liv(e), e, lf(t, e).0, lf(t, e).1)).collect();
        if !m4.is_empty() {
            let g = self.hub_vs(&m4, D, &[(h0, false), (h1, true)]);
            self.b.t(&g);
        }
        for k in 0..kk {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let m0 = merge0 && k == 0;
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, W as i32 - lf(t, e).0 - k)).collect();
            let alo1 = starts.iter().map(|p| p.1).min().unwrap();
            let shi = starts.iter().map(|p| p.1).max().unwrap();
            // code-00 shots (e = 0) have L = t/2: their row starts one wire below every big start
            let alo = if m0 { W as i32 - t / 2 } else { alo1 };
            assert!(!m0 || (alo >= 1 && alo < alo1));
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| self.tvl(a as i32)).collect();
            let sv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = self.tvl(W as i32 - 1 - k);
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let li = lik(k);
            let actv: Vec<Vec<Lit>> = vec![li];
            let mn = *act.iter().min().unwrap();
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(shi - alo + 1) {
                let a = alo + i;
                let nx = starts.iter().filter(|p| p.1 > a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if m0 && a < alo1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let lo = (mn - 1).max(1) as usize;
                            let mut ch: Vec<Lit> = if m0 { vec![(h1, true)] } else { vec![] };
                            ch.extend((lo..(n as usize - 1)).map(|j| (y[j], false)));
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vz(&tv, &sv, t1, top, d, h0, NONE, &no_tog, &actv, Some(&il), None, m0);
            let c1 = if m0 { self.m(&sp0, d) } else { vec![] };
            self.b.t(&c1);
            self.b.t(&g);
            let mut g: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(x[W - ku], true)]), d));
                }
            } else {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(d, true)]), y0));
                }
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            self.b.t(&c1);
        }
        if merge0 && !sq.is_empty() {
            let g = self.hub_v2c_q(&sq);
            self.b.t(&g);
        }
        let hubok = !big.is_empty()
            && !big.iter().any(|&e| self.special(lf(t, e).0, lf(t, e).1))
            && big.iter().map(|&e| lf(t, e).1).min().unwrap() - D as i32 + 1 > *big.iter().max().unwrap();
        if hubok {
            let items: Vec<(Vec<Lit>, i32, i32, i32)> = big.iter().map(|&e| (liv(e), e, lf(t, e).0, lf(t, e).1)).collect();
            let g = self.hub_v2c(&items, &cl, true);
            self.b.t(&g);
        } else {
        for &e in big.iter() {
            let (l, f) = lf(t, e);
            let g = self.v2c(&liv(e), e, l, f, false, &[(h1, true)]);
            self.b.t(&g);
        }
        }
        for k in (0..kk).rev() {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            let li = likc(k);
            let actv: Vec<Vec<Lit>> = vec![li.clone()];
            let flag = k >= 2 && big.contains(&k);
            if flag {
                let mut g = self.m(&cat(&li, &[(y[ku - 1], true)]), h0);
                g.extend(self.m(&cat(&li, &[(h0, true)]), y[ku - 1]));
                self.b.t(&g);
            }
            let m0 = merge0 && k == 0;
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, CW as i32 - lf(t, e).1 - 1 + k)).collect();
            let ahi1 = starts.iter().map(|p| p.1).max().unwrap();
            let slo = starts.iter().map(|p| p.1).min().unwrap();
            // code-00 shots have F = t/2: their top wire is one above every big top
            let ahi = if m0 { CW as i32 - t / 2 - 1 } else { ahi1 };
            assert!(!m0 || ahi > ahi1);
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| self.tcl(a)).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let c = if k >= 2 { x[W - ku] } else { h0 };
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(ahi - slo + 1) {
                let a = ahi - i;
                let nx = starts.iter().filter(|p| p.1 < a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if m0 && a > ahi1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let jlo = (k + 1).max(2);
                            let mut ch: Vec<Lit> = if m0 { vec![(h1, true)] } else { vec![] };
                            if k >= 2 {
                                ch.push((h0, false));
                            }
                            for j in jlo..n {
                                ch.push((x[W - j as usize], false));
                            }
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vz(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &actv, Some(&il), None, m0);
            let c1 = if m0 { self.m(&sp0, d) } else { vec![] };
            let mut hh: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(x[W - ku], true)]), d));
                }
                hh.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(y0, true)]), xt));
                    }
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[W - 1];
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(host, true)]), d));
                }
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            self.b.t(&c1);
            self.b.t(&rev(&g));
            self.b.t(&c1);
            if flag {
                let mut g = self.m(&cat(&li, &[(h0, true)]), x[W - ku]);
                g.extend(self.m(&cat(&li, &[(x[W - ku], true)]), h0));
                self.b.t(&g);
            }
        }
        if prs.contains(&0) && !merge0 {
            let (l_, f) = lf(t, 0);
            self.sp_c(0, l_, f, &sp0, h0);
        }
        if prs.contains(&1) && lf(t, 1).0 != D as i32 {
            let (l_, f) = lf(t, 1);
            let spc: Vec<Lit> = if l_ > D as i32 && self.mmq(f) > D as i32 { sp1c.clone() } else { cat(&[(yt, true)], &self.hc(1)) };
            self.sp_c(1, l_, f, &spc, x[W - 1]);
        }
        let mut sq2: Vec<(Vec<Lit>, i32, i32, i32)> = vec![];
        if prs.contains(&0) && self.sp_generic(lf(t, 0).0, lf(t, 0).1) {
            sq2.push((sp0.clone(), 0, lf(t, 0).0, lf(t, 0).1));
        }
        if prs.contains(&1) && self.sp_generic(lf(t, 1).0, lf(t, 1).1) {
            sq2.push((sp1c.clone(), 1, lf(t, 1).0, lf(t, 1).1));
        }
        let shi: Vec<(Vec<Lit>, i32, i32, i32)> = big.iter().map(|&e| (lic(e), e, lf(t, e).0, lf(t, e).1)).collect();
        let fitall = hubok && !sq2.is_empty() && shi.iter().chain(sq2.iter()).map(|it| it.3).min().unwrap() - D as i32 + 1 > shi.iter().chain(sq2.iter()).map(|it| it.1).max().unwrap();
        if fitall {
            let items: Vec<(Vec<Lit>, i32, i32, i32)> = shi.iter().chain(sq2.iter()).cloned().collect();
            let mut ls: Vec<Vec<Lit>> = vec![cl.clone()];
            for x_ in &sq2 {
                ls.push(x_.0.clone());
            }
            let g = self.hub_c2v(&items, &ls);
            self.b.t(&g);
        } else {
            if hubok {
                let g = self.hub_c2v(&shi, &[cl.clone()]);
                self.b.t(&g);
            } else {
                for &e in big.iter() {
                    let (l, f) = lf(t, e);
                    let g = self.c2v(&lic(e), e, l, f);
                    self.b.t(&g);
                }
            }
            if !sq2.is_empty() {
                let ls: Vec<Vec<Lit>> = sq2.iter().map(|x_| x_.0.clone()).collect();
                let g = self.hub_c2v(&sq2, &ls);
                self.b.t(&g);
            }
        }
        if solos.iter().any(|&e| e >= 3) {
            let g = self.restore(3.max(*solos.iter().filter(|&&e| e >= 3).min().unwrap()));
            self.b.t(&g);
        }
        if false {
            let (_l, f) = lf(t, 0);
            let mb = W - f as usize;
            let wires: Vec<usize> = (0..mb).rev().collect();
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a]).collect();
            let nn = tv.len();
            let g = self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        if false {
            let (_l, f) = lf(t, 1);
            let mb = W - f as usize;
            let wires: Vec<usize> = (1..=mb).rev().collect();
            let c1 = self.m(&sp1c, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - 1]).collect();
            let nn = tv.len();
            let g = self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        // waiters step aside: a down-rotation now, the relabel below undoes it
        let hold1: Vec<Lit> = cat(&[(yt, true)], &self.hc(1));
        let mut g = self.m(&cat(&hold1, &[(x[W - 1], true)]), ctl);
        g.extend(self.m(&cat(&hold1, &[(x[W - 1], false), (x[W - 2], true)]), ctl));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&cat(&[(y[W - 1], false), (y[W - 2], true)], &self.hc(1)), ctl);
        self.b.t(&g);
        // post
        let g = self.m(&[(yt, true), (y[0], false)], ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        self.b.t(&[gc(y[W - 1], ctl)]);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        self.b.t(&[gc(y[W - 1], ctl)]);
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
        // parity: rotate the new N by r. The marker sits at W-e+1, everything above it is zero.
        let mut g = self.m(&cat(&[(act, true)], &self.hc(1)), ctl);
        for &e in &allbig {
            if e & 1 == 1 {
                let eu = e as usize;
                let mut l = cat(&[(act, true)], &self.hc(2));
                for i in 0..(eu - 2) {
                    l.push((y[W - 1 - i], false));
                }
                l.push((y[W - eu + 1], true));
                g.extend(self.m(&l, ctl));
            }
        }
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&[(act, true), (y[1], false)], ctl);
        self.b.t(&g);
        // final codes; the marker of a shot that stays in 11 is already in place
        let aa: Vec<Lit> = vec![(act, true)];
        let mut g = self.m(&cat(&aa, &[(h1, false), (y[1], false)]), h0);
        g.extend(self.m(&cat(&aa, &[(h1, true), (y[W - 1], true)]), h0));
        g.extend(self.m(&cat(&aa, &self.hc(3)), y[W - 1]));
        g.extend(self.m(&cat(&aa, &[(h0, true)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, false), (xt, false)]), h0));
        g.extend(self.m(&cat(&aa, &[(h1, true), (xt, false), (y[W - 3], true)]), h0));
        g.extend(self.m(&cat(&cat(&aa, &self.hc(3)), &[(xt, false)]), y[W - 3]));
        g.extend(self.m(&cat(&aa, &[(h0, true), (xt, false)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, true)]), h0));
        self.b.t(&g);
        let g1 = self.m(&[(act, true), (xt, false)], ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let mut g = self.m(&[(xt, true), (y[1], true)], act);
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, false)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, true), (h0, true)], act));
        g.extend(self.m(&[(xt, true), (y[1], false), (y[2], true), (h0, true)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], false), (y[3], true)], act));
        self.b.t(&g);
        if t + 1 <= 2 * N as i32 {
            let tau = ctl;
            let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hc(0));
            let tg = self.m(&gl, tau);
            self.b.t(&tg);
            let p0 = self.pas[0];
            let (p12, p3) = self.pi10(t + 1, h1, h0, y[1], p0);
            self.b.t(&p12);
            let q = self.m(&[(tau, true), (h0, false), (y[1], true), (p0, true)], act);
            self.b.t(&q);
            self.b.t(&p3);
            self.b.t(&q);
            self.b.t(&rev(&p3));
            self.b.t(&rev(&p12));
            self.b.t(&tg);
        }
        if t % 8 == 0 && !self.big_pairs11(t).is_empty() {
            self.big_phase(t);
        }
        self.arrive11(t - 1, &y, ctl);
        self.b.t(&[gx(ctl)]);
    }
    fn big_pairs11(&self, t: i32) -> Vec<(i32, i32, i32, i32)> {
        let mut out = vec![];
        for w in 0..8 {
            for e in BE..=ECAP {
                if (e - w).rem_euclid(2) != 0 {
                    continue;
                }
                let (u, v) = ((e - w) / 2, (e + w) / 2);
                let (l, f) = (t / 2 - u, t / 2 + v);
                if l >= 1 && f <= N as i32 && f >= l {
                    out.push((e, w, u, v));
                }
            }
        }
        out
    }
    /// A shot that has just reached the top with e >= 10 takes code 01 and w = tn mod 8. ctl is clean.
    fn arrive11(&mut self, tn: i32, y: &[u32], ctl: u32) {
        let (h0, h1) = (self.e[0], self.e[1]);
        let w = tn.rem_euclid(8);
        let yt2 = y[W - 1];
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(2));
        for j in 1..(BE as usize - 1) {
            l.push((y[j], false));
        }
        let mut g = self.m(&l, ctl);
        g.push(gc(ctl, h0));
        g.push(gc(ctl, h1));
        for i in 0..3 {
            if (w >> i) & 1 == 1 {
                g.push(gc(ctl, y[4 + i]));
            }
        }
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(1));
        l.push((y[1], false));
        for i in 0..3 {
            l.push((y[4 + i], (w >> i) & 1 == 1));
        }
        g.extend(self.m(&l, ctl));
        self.b.t(&g);
    }
    /// Rows, marker and post of the waiting big shots (code 01) at a tier slot, after the slot's own low work.
    fn big_phase(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs = self.big_pairs11(t);
        let es: BTreeSet<i32> = prs.iter().map(|p| p.0).collect();
        let kk = *es.iter().next_back().unwrap() + 1;
        let yt = y[W - 1];
        let (d, ctl) = (x[0], x[0]);
        let (y0, y1) = (y[0], y[1]);
        let (w0, w1, w2) = (y[4], y[5], y[6]);
        let hb0: Vec<u32> = vec![y[2], y[3], y[7], y[8]];
        let cv9 = y[9];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let g = self.m(&[(yt, true), (h0, true)], h1);
        self.b.t(&g);
        let cl: Vec<Lit> = cat(&[(yt, true)], &self.hc(3));
        let mut g: GL = vec![];
        for &e in &es {
            let mut li = cl.clone();
            for j in (BE as usize - 1)..(e as usize - 1) {
                li.push((y[j], false));
            }
            li.push((y[e as usize - 1], true));
            let m = e >> 1;
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.extend(self.m(&li, hb0[i]));
                }
            }
        }
        for &e in &es {
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb0[i], ((e >> 1) >> i) & 1 == 1));
            }
            li.push((w0, e & 1 == 1));
            g.extend(self.m(&li, y[e as usize - 1]));
        }
        self.b.t(&g);
        let lits = |cubes: &Cubes, lanes: &[u32]| -> Vec<Vec<Lit>> { cubes.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
        let exact = |k: i32, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &e in &es {
                let p_ = (e >> 1) | ((e & 1) << 4);
                if e >= k {
                    on |= 1u128 << p_;
                } else {
                    off |= 1u128 << p_;
                }
            }
            lits(&dtree(on, off, &[0, 1, 2, 3, 4], 1), lanes).into_iter().map(|x_| cat(&x_, &cl)).collect()
        };
        let hterm = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &x_ in vals {
                on |= 1u128 << (x_ % 16);
            }
            for &x_ in others {
                off |= 1u128 << (x_ % 16);
            }
            lits(&dtree(on, off, &[0, 1, 2, 3], 0), lanes)
        };
        let allprs = prs.clone();
        let bsolo: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| t / 2 - p.2 < D as i32).collect();
        let prs: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| t / 2 - p.2 >= D as i32).collect();
        for &(e, w, u, v) in &bsolo {
            self.big_solo(e, w, t / 2 - u, t / 2 + v, &hb0, w0, w1, w2, cv9, &cl);
        }
        for mq in 2..=(D as i32) {
            let it: Vec<(Vec<Lit>, i32, i32, i32)> = prs.iter().filter(|p| self.mmq(t / 2 + p.3) == mq).map(|p| (self.bli(&cl, p.0, p.1, &hb0, w0, w1, w2), p.0, t / 2 - p.2, t / 2 + p.3)).collect();
            if !it.is_empty() {
                let g = self.hub_vs(&it, mq as usize, &[(cv9, false), (h0, true)]);
                self.b.t(&g);
            }
        }
        for &(e, w, u, v) in &prs {
            let mq = self.mmq(t / 2 + v);
            if mq == 1 {
                let li = self.bli(&cl, e, w, &hb0, w0, w1, w2);
                let g = self.vstart(&li, e, t / 2 - u, t / 2 + v, &[]);
                self.b.t(&g);
            }
        }
        let nit: Vec<(Vec<Lit>, i32, i32, i32)> = prs.iter().map(|p| (self.bli(&cl, p.0, p.1, &hb0, w0, w1, w2), p.0, t / 2 - p.2, t / 2 + p.3)).collect();
        let g = self.hub_near(&nit);
        self.b.t(&g);
        let mut cv_v = dec_ctl(&hb0, &[(w1, true)], &self.dirty);
        cv_v.extend(dec_ctl(&hb0[1..], &[(w2, true)], &self.dirty));
        for k in 0..kk {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, u, _v) in &act {
                starts.entry((W as i32 - (t / 2 - u) - k).max(2 - D as i32)).or_default().insert(u);
            }
            let alo = *starts.keys().next().unwrap();
            assert!(alo + k >= 10);
            let ku = k as usize;
            let tv: Vec<u32> = (alo..(W as i32 - k - 1)).map(|a| self.tvl(a)).collect();
            let sv: Vec<u32> = (alo..(W as i32 - k - 1)).map(|a| y[(a + k) as usize]).collect();
            let t1 = self.tvl(W as i32 - 1 - k);
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let actv = exact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], w0]);
            let allu: BTreeSet<i32> = act.iter().map(|p| p.2).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, us) in &starts {
                let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                tg.insert((a - alo) as usize, hterm(us, &rest, &hb0));
            }
            let g = self.row_v(&tv, &sv, t1, top, d, cv9, y1, &tg, &actv, None, Some(&cv_v));
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
        }
        let mv = |me: &Machine, src: u32, dst: u32| -> GL {
            let mut g = me.m(&cat(&cl, &[(src, true)]), dst);
            g.extend(me.m(&cat(&cl, &[(dst, true)]), src));
            g
        };
        let hubb = !prs.is_empty() && !prs.iter().any(|p| self.special(t / 2 - p.2, t / 2 + p.3))
            && prs.iter().map(|p| t / 2 + p.3).min().unwrap() - D as i32 + 1 > prs.iter().map(|p| p.0).max().unwrap();
        if hubb {
            let items: Vec<(Vec<Lit>, i32, i32, i32)> = prs.iter().map(|p| (self.bli(&cl, p.0, p.1, &hb0, w0, w1, w2), p.0, t / 2 - p.2, t / 2 + p.3)).collect();
            let g = self.hub_v2c(&items, &cl, false);
            self.b.t(&g);
        } else {
        for &(e, w, u, v) in &prs {
            let li = self.bli(&cl, e, w, &hb0, w0, w1, w2);
            let g = self.v2c(&li, e, t / 2 - u, t / 2 + v, false, &[(h0, true), (h1, true), (yt, true), (y[10], false)]);
            self.b.t(&g);
        }
        }
        let mut hb = hb0.clone();
        let (mut a0, mut a1, mut a2) = (w0, w1, w2);
        for k in (0..kk).rev() {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            let ku = k as usize;
            if k == 9 {
                let g = mv(self, hb[3], x[W - 10]);
                self.b.t(&g);
                hb[3] = x[W - 10];
            }
            if k == 8 {
                let g = mv(self, hb[2], x[W - 9]);
                self.b.t(&g);
                hb[2] = x[W - 9];
            }
            if k == 7 {
                let g = mv(self, a2, x[W - 8]);
                self.b.t(&g);
                a2 = x[W - 8];
            }
            if k == 6 {
                let g = mv(self, a1, x[W - 7]);
                self.b.t(&g);
                a1 = x[W - 7];
            }
            if k == 5 {
                let g = mv(self, a0, x[W - 6]);
                self.b.t(&g);
                a0 = x[W - 6];
            }
            if k == 4 {
                let g = mv(self, hb[1], x[W - 5]);
                self.b.t(&g);
                hb[1] = x[W - 5];
            }
            if k == 3 {
                let g = mv(self, hb[0], x[W - 4]);
                self.b.t(&g);
                hb[0] = x[W - 4];
            }
            if act.is_empty() {
                continue;
            }
            let mut cv_c = inc_ctl(&hb, &[(a0, true)], &self.dirty);
            cv_c.extend(inc_ctl(&hb, &[(a1, true)], &self.dirty));
            cv_c.extend(inc_ctl(&hb[1..], &[(a2, true)], &self.dirty));
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, _u, v) in &act {
                starts.entry(CW as i32 - (t / 2 + v) - 1 + k).or_default().insert(v);
            }
            let ahi = *starts.keys().next_back().unwrap();
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| self.tcl(a)).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let cc = if k >= 2 {
                x[W - ku]
            } else if k == 1 {
                x[W - 2]
            } else {
                x[W - 1]
            };
            let mask = if k >= 3 { y1 } else { x[W - 3] };
            let actv = exact(k, &[hb[0], hb[1], hb[2], hb[3], a0]);
            let allv: BTreeSet<i32> = act.iter().map(|p| p.3).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, vs) in &starts {
                let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                tg.insert((ahi - a) as usize, hterm(vs, &rest, &hb));
            }
            let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, mask, &tg, &actv, None, Some(&cv_c));
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
        if hubb {
            let items: Vec<(Vec<Lit>, i32, i32, i32)> = prs.iter().map(|p| (self.bli(&cl, p.0, p.1, &hb, a0, a1, a2), p.0, t / 2 - p.2, t / 2 + p.3)).collect();
            let g = self.hub_c2v(&items, &[cl.clone()]);
            self.b.t(&g);
        } else {
        for &(e, w, u, v) in &prs {
            let li = self.bli(&cl, e, w, &hb, a0, a1, a2);
            let g = self.c2v(&li, e, t / 2 - u, t / 2 + v);
            self.b.t(&g);
        }
        }
        for &(e, w, _u, _v) in &bsolo {
            let li = self.hide_big(e, w, &cl, &hb, a0, a1, a2);
            let g = self.m(&li, yt);
            self.b.t(&g);
        }
        let prs = allprs;
        // hi -> marker on X[W-e], largest e first
        let mut g: GL = vec![];
        for &e in es.iter().rev() {
            let m = e >> 1;
            let mk = x[W - e as usize];
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb[i], (m >> i) & 1 == 1));
            }
            li.push((a0, e & 1 == 1));
            g.extend(self.m(&li, ctl));
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.push(gc(ctl, hb[i]));
                }
            }
            g.push(gc(ctl, mk));
            let mut li = cl.clone();
            for i in 0..4 {
                if hb[i] != mk {
                    li.push((hb[i], false));
                }
            }
            li.push((mk, true));
            g.extend(self.m(&li, ctl));
        }
        self.b.t(&g);
        let g = mv(self, a0, x[W - 2]);
        self.b.t(&g);
        let g = mv(self, a1, x[W - 3]);
        self.b.t(&g);
        let g = mv(self, a2, x[W - 4]);
        self.b.t(&g);
        // its own post
        let g = self.m(&cat(&cl, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let fl = y[W - 1];
        let aa: Vec<Lit> = cat(&[(fl, true)], &self.hc(3));
        for &(idx, rot) in &[(W - 4, 4usize), (W - 3, 2), (W - 2, 1)] {
            let mut g = self.m(&cat(&aa, &[(y[idx], true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), y[idx]));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=idx], rot);
            self.b.t(&g);
            let mut g: GL = vec![];
            if rot == 4 {
                g.extend(self.m(&cat(&aa, &[(y[0], false)]), ctl));
            } else if rot == 2 {
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], true)]), ctl));
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], false), (y[4], false)]), ctl));
            } else {
                for &p_ in &[1usize, 3, 5, 7] {
                    let mut l = aa.clone();
                    for i in 0..p_ {
                        l.push((y[i], false));
                    }
                    l.push((y[p_], true));
                    g.extend(self.m(&l, ctl));
                }
            }
            self.b.t(&g);
        }
        // u=2, g=1 ends with E'=-1: no marker, code 01
        let fc1 = cat(&[(fl, true), (xt, false)], &self.hc(1));
        let mut g = self.m(&cat(&aa, &[(xt, false), (y[W - 4], true)]), ctl);
        g.push(gc(ctl, h1));
        g.extend(self.m(&fc1, ctl));
        self.b.t(&g);
        let g = self.m(&fc1, y[W - 4]);
        self.b.t(&g);
        let ab: Vec<Lit> = vec![(fl, true), (h0, true)];
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g1 = self.m(&cat(&ab, &[(xt, false)]), ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let g1 = self.m(&ab, ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        // erase the act flag
        let mut g: GL = vec![];
        for gg in 0..2usize {
            for w in 0..8i32 {
                let sub: Vec<&(i32, i32, i32, i32)> = prs.iter().filter(|p| p.1 == w).collect();
                if sub.is_empty() {
                    continue;
                }
                let gq = 1 + gg + w as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 0..gq {
                    li.push((y[i], false));
                }
                li.push((y[gq], true));
                if sub.iter().any(|p| !(gg == 1 && p.2 == 2)) {
                    let mut l = cat(&li, &self.hc(3));
                    for j in (W + gq + 1 - BE as usize)..(W - 1) {
                        l.push((y[j], false));
                    }
                    g.extend(self.m(&l, fl));
                }
                if sub.iter().any(|p| gg == 1 && p.2 == 2) {
                    g.extend(self.m(&cat(&li, &self.hc(1)), fl));
                }
            }
        }
        self.b.t(&g);
    }
    fn pi10(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> (GL, GL) {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g: GL = vec![];
        let s = &self.s;
        let mp = CW - l;
        if mp <= 2 {
            return (vec![], vec![]);
        }
        // the top lane of this frame is a known zero (it holds the act bit): only its carry-out matters
        let idx = {
            let v: Vec<usize> = (W.saturating_sub(l)..(W - 1)).collect();
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
        if mp <= D + 1 {
            let (wx, hi, t2, t3): (usize, usize, &[u32], &[u32]) = (if mp <= D { mp - 1 } else { D }, mp - 2, t4_p2(mp), t4_p3(mp));
            let mut lanes: Vec<u32> = s.to_vec();
            for i in 0..wx {
                lanes.push(x[1 + i]);
            }
            for i in 0..hi {
                lanes.push(y[W - l + D - hi + i]);
            }
            g.extend(self.anf_to(&lanes, t2, f2, &[]));
            let h = self.anf_to(&lanes, t3, f3, &[]);
            return (g, h);
        }
        let ext: Vec<usize> = (2..(W - l + D)).rev().collect();
        let idx: Vec<usize>;
        if ext.len() <= PIW {
            let a: Vec<u32> = (0..D).map(|i| y[W - l + i]).collect();
            let bl: Vec<u32> = (0..D).map(|i| x[W - l + i]).collect();
            g.extend(rev(&self.c2v_nof(&a, &bl, s)));
            idx = ext;
        } else {
            idx = last((2..(W - l)).rev().collect());
        }
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        let mut h = fw.clone();
        h.push(gt(cc, y[1], f3));
        h.extend(rev(&fw));
        (g, h)
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
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(48_000_000) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[D..N - 1]);
    let s: Vec<u32> = xl[..D].to_vec();
    let xl1: Vec<u32> = xl[..N - 1].to_vec();
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, par, s, xl: xl1 };
    mc.init();
    for t in (3..=(2 * N as i32 - 1)).rev() {
        mc.slot(t);
    }
    IN_F.store(false, Ordering::Relaxed);
    let mut last: GL = vec![gx(mc.x[W - 1])];
    for j in D..N {
        if pbit(j) {
            last.push(gx(mc.x[W + D - 2 - j]));
        }
    }
    FCirc {
        gates: mc.b.gates,
        next: mc.b.next,
        y0,
        y1,
        par,
        xtop: mc.y[W - 1],
        ar: (0..N).map(|i| if i < D { mc.s[i] } else { mc.y[N - 1 - i] }).collect(),
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

fn add_gl(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(3 * t.len());
    for i in 0..t.len() {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
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
    /// +f(2^4 - 2^6 + 2^10 + 2^32): one merged chain with as many clean lanes as there are, plain chains for the rest.
    fn fold_rest(&self, t: &[u32], f: u32, c2: u32) -> GL {
        let terms: [(usize, i32); 3] = [(2, -1), (6, 1), (28, 1)];
        let mut use_t: Vec<(usize, i32, u32)> = vec![];
        for (i, tm) in terms.iter().enumerate() {
            if i < ZL {
                use_t.push((tm.0, tm.1, self.zl[i]));
            }
        }
        let mut g = self.merged(&t[4..RW], f, &use_t, c2);
        for (i, tm) in terms.iter().enumerate() {
            if i >= ZL {
                let st = 4 + tm.0;
                let ch = inc_long(&t[st..(st + CHW).min(RW)], f, &self.dirty, c2);
                if tm.1 < 0 {
                    g.extend(rev(&ch));
                } else {
                    g.extend(ch);
                }
            }
        }
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
    /// ZFOR-wait: acc += a, no control (one plain round).
    fn add_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g = self.add_plain(acc, a, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
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
    fn lean(&self, t: &[u32], f: u32, _window: usize, c2: u32) -> GL {
        let z = &self.zl;
        if ZL >= 4 {
            return self.merged(&t[0..RW], f, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], c2);
        }
        let mut g = inc_long(&t[0..CHW], f, &self.dirty, c2);
        g.extend(self.fold_rest(t, f, c2));
        g
    }
    fn dbl(&self, t: &[u32], c2: u32) -> (Vec<u32>, GL) {
        let mut t2 = vec![t[255]];
        t2.extend_from_slice(&t[..255]);
        let f = t2[0];
        let g = self.fold_rest(&t2, f, c2);
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
        // ZFOR-wait signed digits. With CAPW = w > 0, zuiris's seed loop above leaves acc = S a (S = the top w bits).
        // Then acc := 2 acc + a (one plain round), m = nb - w signed rounds on the low bits give 2ab + a; subtract a, halve.
        if w == 0 {
            for j in 0..a.len() {
                g.push(gc(a[j], acc[j]));
            }
        } else {
            let (t2, h) = self.dbl(&acc, c);
            acc = t2;
            g.extend(h);
            g.extend(self.add_round(&acc, a, c, ov));
        }
        let idx: Vec<usize> = (0..(nb - w)).rev().collect();
        for (j, &i) in idx.iter().enumerate() {
            if j == 0 && w == 0 && a.len() < 256 {
                // acc = a with a 255-bit a: top wire 0, so this doubling's fold is dead
                let mut t2 = vec![acc[255]];
                t2.extend_from_slice(&acc[..255]);
                acc = t2;
            } else {
                let (t2, h) = self.dbl(&acc, c);
                acc = t2;
                g.extend(h);
            }
            g.extend(self.round3(&acc, a, bits[i], c, ov, false));
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
    fn sq_into(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
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
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gx(d)]);
        }
        for i in (0..256).rev() {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gc(lam[i], d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gc(lam[i], d)]);
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

pub fn build() -> Vec<Op> {
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
