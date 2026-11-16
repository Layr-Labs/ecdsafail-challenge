//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

/// BAKED (s21 bake.py): lever set L1_MERGED_C0M1,L2_QBIT_MOVE,L3A_CONV_TRUNC,L3B_LAST_TOGGLE,L4_WAIT_ENVELOPE,L5_H15_UPDATE,L6_HORNER_LAST,L7_CARRY_N0,L8_T3_JUNCTION,L9_D_PAIR,L10_ROW_FLAG,L11_CONV_MID,L12_FLAG_INC,L13_FLAG_K012,P2_E1,P2_B3,P2_B2,P2_B1,P2_D1,P2_B4,L14_O9_FLAG,L15_MASK_SHARE. Nothing below reads DEV_* from the environment; breaks are 0.
/// (original header) carbon-dibs s11 development switches. DEV_<NAME>=0 turns lever <NAME> off (default on); DEV_<NAME>_BREAK=n selects a
/// deliberate breakage of that lever (0 = none, only read while the lever is on). Inert in an empty environment.
fn lv(name: &str) -> bool {
    matches!(name, "L1_MERGED_C0M1" | "L2_QBIT_MOVE" | "L3A_CONV_TRUNC" | "L3B_LAST_TOGGLE" | "L4_WAIT_ENVELOPE" | "L5_H15_UPDATE" | "L6_HORNER_LAST" | "L7_CARRY_N0" | "L8_T3_JUNCTION" | "L9_D_PAIR" | "L10_ROW_FLAG" | "L11_CONV_MID" | "L12_FLAG_INC" | "L13_FLAG_K012" | "L14_O9_FLAG" | "L15_MASK_SHARE")
}
fn brk(_name: &str) -> i64 {
    0
}
/// s18 pass-2 levers (Argon audit 2): DEV_P2_<ID>=0 turns the item off (default ON), DEV_P2_<ID>_BREAK=n numbered deliberate breakage (only read while on).
/// items accepted (replay passed): default ON; every other id is default OFF until DEV_P2_<ID>=1
fn p2(id: &str) -> bool {
    matches!(id, "E1" | "B3" | "B2" | "B1" | "D1" | "B4")
}
/// per-site mask for the S3-phase items (DEV_P2_<ID>_SITES bitmask; default all)
fn p2_site(_id: &str, _bit: u32) -> bool {
    true
}
fn p2brk(_id: &str) -> i64 {
    0
}
/// s26 pass-3 levers (Argon audit 3): DEV_P3_<ID>=1 turns the item on, =0 off; accepted items default ON (P3_ACCEPTED), the rest OFF.
/// DEV_P3_<ID>_BREAK=n numbered deliberate breakage (only read while on).
fn p3(id: &str) -> bool {
    ["G1", "G2", "G3", "G5", "G6", "G7", "H1", "H2", "I1", "J1", "K1"].contains(&id)
}
fn p3brk(_id: &str) -> i64 {
    0
}
const L1: &str = "L1_MERGED_C0M1";
const L2: &str = "L2_QBIT_MOVE";
const L3A: &str = "L3A_CONV_TRUNC";
const L3B: &str = "L3B_LAST_TOGGLE";
const L4: &str = "L4_WAIT_ENVELOPE";
const L5: &str = "L5_H15_UPDATE";
const L6: &str = "L6_HORNER_LAST";
const L7: &str = "L7_CARRY_N0";
const L8: &str = "L8_T3_JUNCTION";
const L9: &str = "L9_D_PAIR";
const L10: &str = "L10_ROW_FLAG";
const L11: &str = "L11_CONV_MID";
const L12: &str = "L12_FLAG_INC";
const L13: &str = "L13_FLAG_K012";
const L14: &str = "L14_O9_FLAG";
const L15: &str = "L15_MASK_SHARE";
const L16: &str = "L16_RESET_FL";
const L17: &str = "L17_RESET_ZW";

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
/// s23 band port: B1 / B2 (conv_clean, inc_ctl_clean) take the clean ladder lanes 512, 514, 515, so 515 must be a cc_core lane and
/// not the flag lane (FL_LANE is the last clean lane: 515 at 783, 516 at 784, 517 at 785 and up). False at 783: B1 / B2 are out by layout.
const W2_CLEAN3: bool = FL_LANE > 515;
/// s28 wave-three band port: lane 515 is a spare cc2 lane (not the flag lane) only when CC2_N >= 2 (784: 515; 785 and up: 515, 516; 783: FL_LANE = 515, off).
/// G3 (literal 515 as a measured AND lane), K1 (515 as a carry lane) and I1 (515 as the k=1 carry) need it.
const W3_LANE515: bool = CC2_N >= 2;
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
const ZL_BASE: usize = 8;
/// P2_B5: six spare lanes for the split chain tops (peak 778 -> 784 in the product phase)
fn zl_n() -> usize {
    if p2("B5") { ZL_BASE + 6 } else { ZL_BASE }
}
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

fn g3_on() -> bool {
    static C: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *C.get_or_init(|| p3("G3") && W3_LANE515)
}
/// AND of k controls on one clean lane, 2k-3 T: conditionally clean wires, Khattar-Gidney 2024.
fn cc_core(cs: &[u32], tgt: u32, z: u32, n5: bool) -> GL {
    let k = cs.len();
    let m = k / 2;
    let zf = if HMR_AND { z | AND_FLAG } else { z };
    let mut up: GL = vec![gt(cs[0], cs[1], zf), gc(z, cs[0]), gc(z, cs[1])];
    let (mut guards, mut aa, mut bb) = (vec![z], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let (g, gf) = if CC2 && i <= (if n5 { CC2_N.min(1) } else { CC2_N }) { let l = CC2_LANE + (i as u32) - 1; (l, if HMR_AND { l | AND_FLAG } else { l }) } else { (aa[i - 1], aa[i - 1]) };
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
        if m == 2 && CC2 && HMR_AND && g3_on() && !n5 {
            // P3_G3: the third held clean lane (CC2_LANE + 1 = 515) takes cur & x (one measured AND) instead of the two-Toffoli dirty walk
            let l = CC2_LANE + 1;
            let b = p3brk("G3");
            up.push(gt(cur, x, l | AND_FLAG));
            out = vec![];
            if b == 1 { out.push(gx(l)); }
            out.extend(up.iter().cloned());
            out.push(gt(l, if b == 2 { cur } else { guards[0] }, tgt));
            out.extend(rev(&up));
            if b == 1 { out.push(gx(l)); }
            return out;
        }
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

mod mac_merge;
const MAC_ON: bool = true;
const MERGE_E1: bool = true;
const MERGE_E2: bool = false;
const MAC: u32 = u32::MAX - 1;
#[derive(Clone)]
struct Mac { lits: Vec<Lit>, tgt: u32, an: Vec<u32>, n5: bool }
/// P3_I1: while set, lane 515 holds a row carry: MACs recorded meanwhile expand with CC2_N = 1 (no scratch on 515), K1 and G3 stay off it.
static NO515: AtomicBool = AtomicBool::new(false);
static MACS: std::sync::Mutex<Vec<Mac>> = std::sync::Mutex::new(Vec::new());
/// Expand one dirty-ancilla MCX (Barenco, the original emission).
fn mac_expand(m: &Mac, out: &mut GL) {
    let l = &m.lits; let k = l.len(); let tgt = m.tgt; let an = &m.an;
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    out.extend_from_slice(&pre);
    let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
    if an.is_empty() { out.extend(cc_core(&cs, tgt, 512, m.n5)); out.extend_from_slice(&pre); return; }
    let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
    let mut i = k - 2;
    while i > 1 { up.push(gt(cs[i], an[i - 2], an[i - 1])); i -= 1; }
    let mid = gt(cs[0], cs[1], an[0]);
    out.extend_from_slice(&up); out.push(mid); out.extend(up.iter().rev().cloned());
    out.extend_from_slice(&up[1..]); out.push(mid); out.extend(up[1..].iter().rev().cloned());
    out.extend_from_slice(&pre);
}
/// Macro-level analysis + expansion of the F gate list.
fn mac_finish(gates: Vec<G>) -> Vec<G> {
    let t = MACS.lock().unwrap().clone();
    let key = |m: &Mac| { let mut v = m.lits.clone(); v.sort(); v };
    let (mut r1, mut r1t, mut adj, mut sw2, mut sw3) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut prev: Option<usize> = None; let mut prev2: Option<usize> = None;
    for g in &gates {
        if g.0 == MAC {
            let id = g.1 as usize;
            if let Some(p) = prev {
                adj += 1;
                let (a, b) = (&t[p], &t[id]);
                if key(a) == key(b) && a.tgt != b.tgt && !b.lits.iter().any(|x| x.0 == a.tgt) && !a.lits.iter().any(|x| x.0 == b.tgt) { r1 += 1; r1t += 4 * (a.lits.len() as u64) - 8; }
                // swap pair: a = MCX(S+b.tgt -> a.tgt), b = MCX(S+a.tgt -> b.tgt)
                let mut ka: Vec<Lit> = a.lits.iter().filter(|x| x.0 != b.tgt).cloned().collect(); ka.sort();
                let mut kb: Vec<Lit> = b.lits.iter().filter(|x| x.0 != a.tgt).cloned().collect(); kb.sort();
                if a.lits.contains(&(b.tgt, true)) && b.lits.contains(&(a.tgt, true)) && ka == kb {
                    sw2 += 1;
                    if let Some(p2) = prev2 { let c = &t[p2]; if c.tgt == a.tgt && key(c) == key(a) { sw3 += 1; } }
                }
            }
            prev2 = prev; prev = Some(id);
        } else { prev = None; prev2 = None; }
    }
    eprintln!("MAC: {} macros, adjacent pairs {adj}, same-controls pairs {r1} (~{r1t} T), swap pairs {sw2}, swap triples {sw3}", t.len());
    // optimize runs of adjacent macros
    let mut opt: Vec<G> = Vec::with_capacity(gates.len());
    let (mut n_sw, mut n_fan, mut n_fan_t) = (0u64, 0u64, 0u64);
    let mut i = 0usize;
    let n = gates.len();
    while i < n {
        let g = gates[i];
        if g.0 != MAC { opt.push(g); i += 1; continue; }
        // (a) swap triple
        if OPT_SWAP && i + 2 < n && gates[i + 1].0 == MAC && gates[i + 2].0 == MAC {
            let (m1, m2, m3) = (&t[g.1 as usize], &t[gates[i + 1].1 as usize], &t[gates[i + 2].1 as usize]);
            let (a, b) = (m1.tgt, m2.tgt);
            let mut s1: Vec<Lit> = m1.lits.iter().filter(|x| x.0 != b).cloned().collect(); s1.sort();
            let mut s2: Vec<Lit> = m2.lits.iter().filter(|x| x.0 != a).cloned().collect(); s2.sort();
            if a != b && m3.tgt == a && key(m1) == key(m3) && m1.lits.contains(&(b, true)) && m2.lits.contains(&(a, true)) && s1 == s2
                && !s1.iter().any(|x| x.0 == a || x.0 == b) {
                opt.push(gc(b, a)); opt.push(gates[i + 1]); opt.push(gc(b, a));
                n_sw += 1; i += 3; continue;
            }
        }
        // (b) same-controls run -> one MCX + CX fanout
        if OPT_FAN {
            let k0 = key(&t[g.1 as usize]);
            let mut j = i + 1;
            let mut tg: Vec<u32> = vec![t[g.1 as usize].tgt];
            while j < n && gates[j].0 == MAC {
                let m = &t[gates[j].1 as usize];
                if key(m) != k0 || tg.contains(&m.tgt) { break; }
                tg.push(m.tgt); j += 1;
            }
            if j - i >= 2 {
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); }
                opt.push(g);
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); }
                n_fan += 1; n_fan_t += (j - i - 1) as u64; i = j; continue;
            }
        }
        opt.push(g); i += 1;
    }
    eprintln!("MAC opt: swap triples {n_sw}, fanout groups {n_fan} removing {n_fan_t} MCX");
    let opt = if MERGE_E1 || MERGE_E2 { mac_merge::run(opt, &t, MERGE_E1, MERGE_E2) } else { opt };
    let mut out = Vec::with_capacity(opt.len() * 3);
    for g in opt { if g.0 == MAC { mac_expand(&t[g.1 as usize], &mut out); } else { out.push(g); } }
    out
}
/// d1-rowripple levers (env switches, default OFF; with all off the stream is the parent's, byte for byte):
/// D1_F: even9 rows with k >= 3 read the activity predicate from the idle clean lane FL_LANE instead of re-testing the
/// actv cubes in the row middle and the digit moves; D1_CVMID: in those rows the rev(cv)/cv pair around the middle is
/// dropped (the middle no longer reads e/w); D1_FINC: FL_LANE keeps the predicate across k and moves by the exact
/// difference tree; D1_F012 (with D1_F): also the k = 0, 1, 2 rows, flag on FL_LANE (forward k = 0) or ZW_LANE (other
/// k < 3 rows; not the merge1 k = 1 rows, whose carry is ZW_LANE). D1_F_BREAK=1|2 (P1 form) and 3|4 (with D1_FINC): deliberate breakages for the replay gate.
static D1_SKIPMID: AtomicBool = AtomicBool::new(false);
/// P3_J1: the mask toggle at i = 0 of two consecutive rows on the same mask lane is merged: the earlier row skips its closing toggle, the later row's opening
/// toggle is replaced by the (cancelled) XOR of the two cube lists. Set by even9 before the row call, consumed (and cleared) by row_vx.
static J1_SKIP_END0: AtomicBool = AtomicBool::new(false);
static J1_FWD0: std::sync::Mutex<Option<Vec<Vec<Lit>>>> = std::sync::Mutex::new(None);
/// backward rows are emitted as rev(g): their time-first toggle is g's closing one (override J1_END0), their time-last is g's opening one (skip).
static J1_SKIP_START0: AtomicBool = AtomicBool::new(false);
static J1_END0: std::sync::Mutex<Option<Vec<Vec<Lit>>>> = std::sync::Mutex::new(None);
fn j1_tgx(tg: &BTreeMap<usize, Vec<Vec<Lit>>>, d: &Option<Vec<Vec<Lit>>>) -> BTreeMap<usize, Vec<Vec<Lit>>> {
    let mut t2 = tg.clone();
    if let Some(d) = d {
        t2.entry(0).or_default().extend(d.iter().cloned());
    }
    t2
}
fn j1_lane(k: i32) -> i32 {
    if k >= 3 { 1 } else if k == 1 || k == 2 { 2 } else { 0 }
}
fn j1_xor(a: &[Vec<Lit>], b: &[Vec<Lit>]) -> Vec<Vec<Lit>> {
    let norm = |c: &Vec<Lit>| { let mut v = c.clone(); v.sort(); v };
    let mut out: Vec<Vec<Lit>> = a.iter().map(norm).collect();
    for c in b.iter().map(norm) {
        if let Some(pos) = out.iter().position(|x| *x == c) { out.remove(pos); } else { out.push(c); }
    }
    out
}
/// L10..L13 switches: D1_F = L10_ROW_FLAG, D1_CVMID = L11_CONV_MID, D1_FINC = L12_FLAG_INC, D1_F012 = L13_FLAG_K012 (L11, L12, L13 need L10).
/// Wave two (round-two of the deep lane): D1_O9F = L14_O9_FLAG, D1_MSHARE = L15_MASK_SHARE, D1_RZ = L16_RESET_FL, D1_RZW = L17_RESET_ZW.
/// Breaks: D1_F_BREAK 1|2 = DEV_L10_ROW_FLAG_BREAK 1|2; 3|4 = DEV_L12_FLAG_INC_BREAK 1|2; D1_O9F_BREAK 1|2 = DEV_L14_O9_FLAG_BREAK 1|2;
/// D1_MSHARE_BREAK 1|2 = DEV_L15_MASK_SHARE_BREAK 1|2; D1_RZ_BREAK 1 = DEV_L16_RESET_FL_BREAK=1, D1_RZ_BREAK 2 = DEV_L17_RESET_ZW_BREAK=2.
fn d1_sw(name: &str) -> bool {
    match name {
        "D1_F" => lv(L10),
        "D1_CVMID" => lv(L11),
        "D1_FINC" => lv(L12),
        "D1_F012" => lv(L13),
        "D1_O9F" => lv(L14),
        "D1_MSHARE" => lv(L15),
        "D1_RZ" => lv(L16),
        "D1_RZW" => lv(L17),
        _ => false,
    }
}
fn d1_brk(name: &str) -> u32 {
    match name {
        "D1_O9F_BREAK" => brk(L14) as u32,
        "D1_MSHARE_BREAK" => brk(L15) as u32,
        "D1_RZ_BREAK" => {
            if brk(L16) == 1 { 1 } else if brk(L17) == 2 { 2 } else { 0 }
        }
        _ => {
            let b = brk(L10);
            if b > 0 {
                return b as u32;
            }
            let c = brk(L12);
            if c > 0 { c as u32 + 2 } else { 0 }
        }
    }
}
/// R3: G(RST, lane, NONE) = reset hint on a lane that is |0> there (emitted as one Hmr into a fresh bit, never read).
const RST: u32 = u32::MAX - 2;
fn grst(a: u32) -> G {
    G(RST, a, NONE)
}
const OPT_SWAP: bool = true;
const OPT_FAN: bool = true;
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
        if MAC_ON {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: Vec::new(), n5: NO515.load(Ordering::Relaxed) });
            #[allow(unused_mut)]
            let mut r = vec![G(MAC, (t.len() - 1) as u32, NONE)];
            //PZ if l.len() == 5 { r.extend(pzero("G3 lane 515 at a k=5 MAC (expect 0)", &[515])); }
            return r;
        }
        g.extend(cc_core(&cs, tgt, 512, false));
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
        if MAC_ON && IN_F.load(Ordering::Relaxed) {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: an.clone(), n5: false });
            return vec![G(MAC, (t.len() - 1) as u32, NONE)];
        }
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

/// P2_B2: reg += AND(lits) with the carries on the clean lanes 512, 514, 515 (touched only by cc_core, whose gates never interleave
/// with a contiguous plain run), AND_FLAG pairs (Hmr + CZ uncompute). r - 1 charged CCX for one literal, r for two (r = reg.len() >= 3).
/// Breaks (DEV_P2_B2_BREAK): 1/2/3 = lane 512/514/515 flipped to |1> around the block (dirty-lane), 4 = top bit never flipped,
/// 5 = a carry is uncomputed after the lower bit it reads was already flipped.
fn inc_ctl_clean(reg: &[u32], lits: &[Lit]) -> GL {
    assert!(W2_CLEAN3, "B2 needs three clean ladder lanes 512/514/515");
    inc_ctl_lanes(reg, lits, &[512u32, 514, 515])
}
/// reg += AND(lits) with the carries on the given clean lanes (lanes.len() >= reg.len() - 2 for one literal)
fn inc_ctl_lanes(reg: &[u32], lits: &[Lit], lanes: &[u32]) -> GL {
    let r = reg.len();
    let brk = if lanes.len() == 3 { p2brk("B2") } else { 0 };
    let pre: GL = lits.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g = pre.clone();
    if (1..=3).contains(&brk) {
        g.push(gx(lanes[(brk - 1) as usize]));
    }
    // cw[i] = wire holding the carry INTO bit i (c_0 = AND(lits)), stored for i = 0..=r-2
    let mut cw: Vec<u32> = vec![];
    let mut nl = 0usize;
    let mut comp: Vec<(u32, u32, u32)> = vec![]; // (a, b, lane) AND computations in order
    if lits.len() == 1 {
        cw.push(lits[0].0);
    } else {
        let ln = lanes[nl];
        nl += 1;
        comp.push((lits[0].0, lits[1].0, ln));
        cw.push(ln);
    }
    for i in 1..=(r - 2) {
        let ln = lanes[nl];
        nl += 1;
        comp.push((cw[i - 1], reg[i - 1], ln));
        cw.push(ln);
    }
    for &(a, b, ln) in &comp {
        g.push(gt(a, b, ln | AND_FLAG));
    }
    // descending: flip reg[j] ^= c_j; before the flip of reg[j-1]... carry c_{j} (stored) is uncomputed after the flip of reg[j]'s reader
    for j in (0..r).rev() {
        // uncompute c_{j+1} (stored when j + 1 <= r - 2) while reg[j] is still old
        if j + 1 <= r - 2 && brk != 5 {
            g.push(gt(cw[j], reg[j], cw[j + 1] | AND_FLAG));
        }
        if j == r - 1 {
            if brk != 4 {
                g.push(gt(cw[r - 2], reg[r - 2], reg[r - 1]));
            }
        } else {
            g.push(gc(cw[j], reg[j]));
        }
        if j + 1 <= r - 2 && brk == 5 {
            g.push(gt(cw[j], reg[j], cw[j + 1] | AND_FLAG));
        }
    }
    // the stored carry c_0 (two literals) is a lane: uncompute it last (controls = the two literals, unchanged)
    if lits.len() == 2 {
        g.push(gt(lits[0].0, lits[1].0, lanes[0] | AND_FLAG));
    }
    if (1..=3).contains(&brk) {
        g.push(gx(lanes[(brk - 1) as usize]));
    }
    g.extend_from_slice(&pre);
    g
}
#[track_caller]
fn inc_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    if IN_F.load(Ordering::Relaxed) && reg.len() >= 3 && (lits.len() == 1 || (lits.len() == 2 && reg.len() <= 4)) && p2("B2") && W2_CLEAN3 {
        let line = std::panic::Location::caller().line();
        let ok = true;
        if ok && reg.len() - 2 + (lits.len() - 1) <= 3 {
            return inc_ctl_clean(reg, lits);
        }
    }
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
#[track_caller]
fn dec_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    rev(&inc_ctl(reg, lits, dirty))
}

/// P3_H2: add_chain on a clean-zero carry wire c: the bottom carry is one measured AND (the CX on a zero carry are dropped), -1 charged CCX per chain.
/// Breaks: 1 = c dirty (|1>) around the chain.
fn add_chain_h2(t: &[u32], s: &[u32], c: u32) -> GL {
    let n = t.len();
    if !p3("H2") || n == 0 || !h2_site_ok() { return add_chain(t, s, c); }
    let mut g = Vec::with_capacity(7 * n);
    if p3brk("H2") == 1 { g.push(gx(c)); }
    g.push(gt(s[0], t[0], c | AND_FLAG));
    for i in 1..n {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    for i in (1..n).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g.push(gt(s[0], t[0], c | AND_FLAG));
    if p3brk("H2") != 2 { g.push(gc(s[0], t[0])); }
    if p3brk("H2") == 1 { g.push(gx(c)); }
    g
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

/// P2_B3: reg -= ctl * (2^32 + 976) (mod 2^n), reg LSB at bit 0, ONE ripple pass with the carries on CLEAN wires anc
/// (anc.len() >= n - 5, all |0> on entry and on exit; each carry is uncomputed by Hmr + CZ (AND_FLAG pairs, Gidney 1709.06648),
/// n - 5 charged CCX). Done as ~(~reg + ctl*K): complement bits 4.., add K = {4,6,7,8,9,32} bit set, complement back.
/// Breaks (P2_B3_BREAK): 1 = bit 32 of the constant missing, 2 = no MAJ transform at the constant bits (carry = plain AND).
fn c0m1_clean(reg: &[u32], ctl: u32, anc: &[u32]) -> GL {
    let n = reg.len();
    let brk = p2brk("B3");
    let kset: Vec<usize> = if brk == 1 { vec![4, 6, 7, 8, 9] } else { vec![4, 6, 7, 8, 9, 32] };
    assert!(anc.len() + 5 >= n && n > 33);
    let cw = |k: usize| -> u32 { anc[k - 5] }; // carry INTO bit k, k >= 5
    let mut g: GL = vec![];
    for i in 4..n {
        g.push(gx(reg[i]));
    }
    // forward: carries
    for k in 4..(n - 1) {
        let isk = kset.contains(&k);
        let tgt = cw(k + 1) | AND_FLAG;
        if k == 4 {
            g.push(gt(reg[4], ctl, tgt));
        } else if isk {
            let c = cw(k);
            if brk != 2 {
                g.push(gc(c, reg[k]));
                g.push(gc(c, ctl));
            }
            g.push(gt(reg[k], ctl, tgt));
            if brk != 2 {
                g.push(gc(c, ctl));
                g.push(gc(c, cw(k + 1)));
            }
        } else {
            g.push(gt(reg[k], cw(k), tgt));
        }
    }
    // backward: uncompute carries, apply sums
    for k in (4..n).rev() {
        let isk = kset.contains(&k);
        if k < n - 1 {
            let tgt = cw(k + 1) | AND_FLAG;
            if k == 4 {
                g.push(gt(reg[4], ctl, tgt));
            } else if isk {
                let c = cw(k);
                if brk != 2 {
                    g.push(gc(c, cw(k + 1)));
                    g.push(gc(c, ctl));
                }
                g.push(gt(reg[k], ctl, tgt));
                if brk != 2 {
                    g.push(gc(c, ctl));
                }
            } else {
                g.push(gt(reg[k], cw(k), tgt));
            }
        }
        // sum bit k: reg[k] ^= (ctl if k in K) ^ carry_k  (reg[k] holds reg[k] ^ c_k after the MAJ transform at constant bits)
        if isk {
            g.push(gc(ctl, reg[k]));
            if k > 4 && brk == 2 {
                g.push(gc(cw(k), reg[k]));
            }
        } else if k > 4 {
            g.push(gc(cw(k), reg[k]));
        }
    }
    for i in 4..n {
        g.push(gx(reg[i]));
    }
    g
}
/// P2_B1: e (n <= 4 bits, LSB first) += sum of the addend wires per position (adds[k] = wires whose value is added at 2^k, at most 2 at
/// position 0 and 1 elsewhere), ONE Gidney ripple on the clean lanes 512, 514, 515 (carries stored, uncomputed by Hmr + CZ). The
/// carry out of position k costs 1 CCX when position k has an addend or a carry in. sub = e -= sum, done as ~(~e + sum).
/// Breaks (DEV_P2_B1_BREAK): 1/2/3 = lane 512/514/515 dirty (|1> around the block), 4 = the addend at position 0 dropped from the carry,
/// 5 = sum bit applied before the carry is uncomputed (reads a changed wire).
fn conv_clean(e: &[u32], adds: &[Vec<u32>], sub: bool) -> GL {
    assert!(W2_CLEAN3, "B1 needs three clean ladder lanes 512/514/515");
    let n = e.len();
    let brk = p2brk("B1");
    let lanes = [512u32, 514, 515];
    assert!(n <= 4);
    let mut g: GL = vec![];
    if (1..=3).contains(&brk) {
        g.push(gx(lanes[(brk - 1) as usize]));
    }
    if sub {
        for &q0 in e {
            g.push(gx(q0));
        }
    }
    // ins[k]: inputs at position k other than e[k] (addends, then the carry lane of position k-1)
    let mut lane_of: Vec<Option<u32>> = vec![None; n + 1]; // carry INTO position k
    let mut ins: Vec<Vec<u32>> = vec![vec![]; n];
    let mut nl = 0usize;
    for k in 0..n {
        if k < adds.len() {
            ins[k].extend_from_slice(&adds[k]);
        }
        if let Some(c) = lane_of[k] {
            ins[k].push(c);
        }
        assert!(ins[k].len() <= 2);
        if k + 1 < n && !ins[k].is_empty() {
            lane_of[k + 1] = Some(lanes[nl]);
            nl += 1;
        }
    }
    // forward: carries
    for k in 0..(n - 1) {
        let m = ins[k].len();
        if m == 0 {
            continue;
        }
        let tgt = lane_of[k + 1].unwrap() | AND_FLAG;
        if m == 1 {
            g.push(gt(e[k], ins[k][0], tgt));
        } else {
            let (y, z) = (ins[k][0], ins[k][1]);
            g.push(gc(z, e[k]));
            g.push(gc(z, y));
            g.push(gt(e[k], y, tgt));
            g.push(gc(z, y));
            g.push(gc(z, lane_of[k + 1].unwrap()));
        }
    }
    // backward: uncompute carries, apply sums
    for k in (0..n).rev() {
        let m = ins[k].len();
        let mut sum: GL = vec![];
        if k + 1 < n && m == 2 {
            sum.push(gc(ins[k][0], e[k])); // e[k] holds e ^ z already: add y
        } else {
            for &w in &ins[k] {
                sum.push(gc(w, e[k]));
            }
        }
        if brk == 4 && k == 0 {
            sum.clear();
        }
        if brk == 5 {
            g.extend_from_slice(&sum);
        }
        if k + 1 < n && m >= 1 {
            let tgt = lane_of[k + 1].unwrap() | AND_FLAG;
            if m == 1 {
                g.push(gt(e[k], ins[k][0], tgt));
            } else {
                let (y, z) = (ins[k][0], ins[k][1]);
                g.push(gc(z, lane_of[k + 1].unwrap()));
                g.push(gc(z, y));
                g.push(gt(e[k], y, tgt));
                g.push(gc(z, y));
            }
        }
        if brk != 5 {
            g.extend_from_slice(&sum);
        }
    }
    if sub {
        for &q0 in e {
            g.push(gx(q0));
        }
    }
    if (1..=3).contains(&brk) {
        g.push(gx(lanes[(brk - 1) as usize]));
    }
    g
}
/// P2_B5: one subtraction pass r -= d of the merged chains (= rev(add_chain(r, d, c))) with the TOP hk = ex.len() + 2 wires of r cut out of
/// the chain: at the midpoint of the pass the carry wire c holds the borrow beta out of the low part; the top part then only sees
/// -beta (pass 1) or +(1 - beta) (pass 2, after the complement of d), done as an increment / decrement by a clean-lane ripple on ex
/// (AND_FLAG pairs). Net on the top part over both passes: +1 - beta1 - beta2, identical to the dirty-d chain (d_hi cancels).
/// Breaks (DEV_P2_B5_BREAK): 1 = pass 2 adds beta instead of 1 - beta, 2 = pass 1 skips the top update, 3 = ex[0] dirty (|1>) around the update.
fn sub_pass(r: &[u32], d: &[u32], c: u32, ex: &[u32], pass: u32) -> GL {
    if ex.is_empty() {
        return rev(&add_chain_h2(r, d, c));
    }
    let hk = ex.len() + 2;
    let nl = r.len() - hk;
    assert!(d.len() == nl);
    let brk = p2brk("B5");
    let mut g: GL = Vec::with_capacity(8 * nl);
    for i in 0..nl {
        g.push(gc(c, d[i]));
        g.push(gc(d[i], r[i]));
        g.push(gc(c, r[i]));
        g.push(gt(d[i], r[i], c));
    }
    let rh = &r[nl..];
    let lits_dec: Vec<Lit> = vec![(c, true)];
    let lits_inc: Vec<Lit> = vec![(c, brk == 1)];
    if brk == 3 {
        g.push(gx(ex[0]));
    }
    if pass == 1 {
        if brk != 2 {
            g.extend(rev(&inc_ctl_lanes(rh, &lits_dec, ex)));
        }
    } else {
        g.extend(inc_ctl_lanes(rh, &lits_inc, ex));
    }
    if brk == 3 {
        g.push(gx(ex[0]));
    }
    for i in (0..nl).rev() {
        g.push(gt(d[i], r[i], c));
        g.push(gc(c, r[i]));
        g.push(gc(c, d[i]));
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
        if p2("B3") {
            // P2_B3 supersedes L1's merged chain here: x is still |0> (the constants are loaded after the chain), x[..250] carry the ripple
            let mut g: GL = vec![];
            for &q0 in &xl {
                g.push(gc(self.par, q0));
            }
            let dirtyx = p2brk("B3") == 3;
            if dirtyx { g.push(gx(self.x[0])); }
            g.extend(c0m1_clean(&xl, self.par, &self.x[..xl.len() - 5]));
            if dirtyx { g.push(gx(self.x[0])); }
            g.push(gx(self.x[0]));
            for i in 0..N {
                if pbit(i) {
                    g.push(gx(self.x[i + 1]));
                }
            }
            self.b.t(&g);
            return;
        }
        if lv(L1) {
            let s3 = S3 { dirty: self.dirty.clone(), zl: vec![] };
            let z = [self.e[1], self.e[2], self.e[3]];
            g.extend(rev(&s3.c0m1(&xl, self.par, &z, cl)));
        } else {
            for &i in &C0M1 {
                g.extend(rev(&inc_long(&xl[i..], self.par, &self.dirty, cl)));
            }
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
        let j1_skip = J1_SKIP_END0.swap(false, Ordering::Relaxed);
        let j1_fwd0: Option<Vec<Vec<Lit>>> = J1_FWD0.lock().unwrap().take();
        let j1_skip_start = J1_SKIP_START0.swap(false, Ordering::Relaxed);
        let j1_end0: Option<Vec<Vec<Lit>>> = J1_END0.lock().unwrap().take();
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        g.extend_from_slice(&conj);
        // L7_CARRY_N0: with an empty carry loop the carry wire is still |0>. Breaks: 1 = also at n == 1 (one iteration too many).
        let c0 = lv(L7) && (n == 0 || (brk(L7) == 1 && n == 1));
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
            None => {
                let skip_last = lv(L3B);
                // L3B break 2: wend one lower (the last group is unmasked one index too early)
                let lower = if skip_last && brk(L3B) == 2 { 1 } else { 0 };
                tog.keys().next_back().map(|&k| if skip_last && tog[&k].is_empty() { k.min(n).saturating_sub(lower) } else { (k + 1).min(n) }).unwrap_or(0)
            }
        };
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        // P3_K1: the top carries of the unmasked tail ripple on idle clean lanes (514 / 515, whichever the middle's multi-controlled
        // gates do not need as cc_core scratch) with a measured uncompute, one Toffoli less per lane bit. Needs the middle free of conversions.
        let skipmid0 = D1_SKIPMID.load(Ordering::Relaxed);
        let mut klanes: Vec<u32> = vec![];
        if p3("K1") && n > wend && (cv.is_none() || skipmid0) && !c0 {
            let mut maxk = 2usize;
            for li in active {
                maxk = maxk.max(li.len() + 2);
            }
            if let Some(x) = xg {
                let t = MACS.lock().unwrap();
                for gg_ in x.iter() {
                    if gg_.0 == MAC {
                        maxk = maxk.max(t[gg_.1 as usize].lits.len());
                    }
                }
            }
            let need514 = maxk >= 4;
            let need515 = maxk >= 6 || (g3_on() && maxk >= 5) || NO515.load(Ordering::Relaxed);
            if !need514 { klanes.push(CC2_LANE); }
            if !need515 && W3_LANE515 { klanes.push(CC2_LANE + 1); }
            klanes.truncate(n - wend);
        }
        let nk = klanes.len();
        let i0 = n - nk;
        let cin = |i: usize| -> u32 { if i == i0 { c } else { klanes[i - i0 - 1] } };
        let cm: u32 = if nk > 0 { klanes[nk - 1] } else { c };
        let k2 = p3("K2") && n > 0 && wend == 0 && i0 > 0 && !c0 && c != NONE;
        //PZ if k2 { g.extend(pzero("K2 carry wire c nonzero on row entry (expect 0)", &[c])); }
        //PZ if nk > 0 { g.extend(pzero("K1 lanes 514/515 before the carry ripple (expect 0)", &klanes)); }
        if nk > 0 && p3brk("K1") == 1 { g.push(gx(klanes[0])); }
        for i in 0..n {
            if i >= i0 && nk > 0 {
                let (ci, ln) = (cin(i), klanes[i - i0]);
                g.push(gc(ci, s[i]));
                g.push(gc(ci, t[i]));
                g.push(gt(s[i], t[i], ln | AND_FLAG));
                if !(p3brk("K1") == 2 && i == i0) { g.push(gc(ci, ln)); }
                continue;
            }
            if k2 && i == 0 {
                // P3_K2 (valid walk states: c = |0> on entry): the bottom carry is one measured AND, the two CX on a zero carry are dropped
                if p3brk("K2") == 1 { g.push(gx(c)); }
                g.push(gt(s[0], t[0], c | AND_FLAG));
                continue;
            }
            if inline.is_none() && !(j1_skip_start && i == 0) {
                let ll0 = if i == 0 && j1_fwd0.is_some() { j1_fwd0.as_ref() } else { tog.get(&i) };
                if let Some(ll) = ll0 {
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
        let skipmid = D1_SKIPMID.load(Ordering::Relaxed);
        if skipmid {
            assert!(xg.is_none() && active.len() == 1 && (active[0] == vec![(FL_LANE, true)] || active[0] == vec![(ZW_LANE, true)]));
        }
        if let Some(cg) = cv {
            if !skipmid {
                g.extend(rev(cg));
            }
        }
        for li in active {
            let mut a2: Vec<Lit> = li.clone();
            if c0 {
                a2.extend_from_slice(&[(t1, false)]);
            } else {
                a2.extend_from_slice(&[(cm, false), (t1, false)]);
            }
            if top != NONE && (!p2("D1") || p2brk("D1") == 3) {
                g.extend(self.m(&a2, top));
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            } else if top != NONE {
                // P2_D1: all `top` gates first, then all `d` gates: exact for ESOP (overlapping, XOR) covers; same gates as the loop above for one cube
                g.extend(self.m(&a2, top));
            } else {
                g.extend(self.m(&a2, d));
            }
        }
        if top != NONE && p2("D1") && p2brk("D1") != 3 {
            for li in active {
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                if p2brk("D1") == 1 {
                    // break 1: the d gates read top again inside the top loop's order for the FIRST cube only (loop not fully split)
                    if std::ptr::eq(li, &active[0]) { continue; }
                }
                g.extend(self.m(&a3, d));
            }
        }
        if let Some(x) = xg {
            g.extend_from_slice(x);
        }
        if c0 {
            g.push(gc(d, t1));
        } else {
            g.extend(self.m(&[(d, true), (cm, false)], t1));
        }
        if let Some(cg) = cv {
            if !skipmid {
                g.extend_from_slice(cg);
            }
        }
        let mshare = d1_sw("D1_MSHARE") && HMR_AND && inline.is_none() && m != NONE;
        for i in (0..n).rev() {
            if k2 && i == 0 {
                g.push(gt(s[0], t[0], c | AND_FLAG));
                g.push(gt(d, s[0], t[0]));
                if p3brk("K2") == 2 { g.push(gx(c)); }
                continue;
            }
            if i >= i0 && nk > 0 {
                let (ci, ln) = (cin(i), klanes[i - i0]);
                g.push(gc(ci, ln));
                g.push(gt(s[i], t[i], ln | AND_FLAG));
                g.push(gc(ci, t[i]));
                g.push(gt(d, s[i], t[i]));
                g.push(gc(ci, s[i]));
                continue;
            }
            if mshare && i < wend {
                let z = 512u32;
                let b = d1_brk("D1_MSHARE_BREAK");
                g.push(gt(s[i], m, z | AND_FLAG));
                g.push(gt(z, t[i], c));
                if b == 2 && i == 0 {
                    g.push(gc(c, t[i]));
                    g.push(gt(z, c, t[i]));
                } else {
                    g.push(gc(c, t[i]));
                    if b != 1 || i != 0 {
                        g.push(gt(z, d, t[i]));
                    }
                }
                g.push(gt(s[i], m, z | AND_FLAG));
                g.push(gc(c, s[i]));
                if !(j1_skip && i == 0) {
                    if let Some(ll) = (if i == 0 && j1_end0.is_some() { j1_end0.as_ref() } else { tog.get(&i) }) {
                        for l in ll {
                            g.extend(self.m(l, m));
                        }
                    }
                }
                continue;
            }
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
            if inline.is_none() && !(j1_skip && i == 0) {
                if let Some(ll) = (if i == 0 && j1_end0.is_some() { j1_end0.as_ref() } else { tog.get(&i) }) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        if nk > 0 && p3brk("K1") == 1 { g.push(gx(klanes[0])); }
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
    /// P2_E1: the comparator part of pi_gates with ripples 1 and 3 left OPEN on their flag wires f1 = h[0], f3 = h[2]
    /// (carry wire = the flag itself, clean at tau = 1; x[W-1] = y_pi[1] = 1 at tau = 1 folds the final CCX into nothing).
    /// The caller emits U, the act gate, rev(U): U act U^-1 is the identity whenever tau = 0, and at tau = 1 the flags carry the same values.
    fn pi_gates_open(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> GL {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let brk = p2brk("E1");
        let mut g = vec![];
        // ripple 2, closed on cc as before
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        // ripple 1 open on f1
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let cw = if brk == 1 { cc } else { f1 };
        for (j, &w) in idx.iter().enumerate() {
            if j > 0 {
                g.extend_from_slice(&[gc(cw, x[w]), gc(cw, y[w])]);
            }
            g.push(gt(x[w], y[w], cw));
        }
        // ripple 3 open on f3
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for (j, &w) in idx.iter().enumerate() {
            if j > 0 {
                if brk != 4 {
                    fw.push(gc(f3, y[w]));
                }
                fw.push(gc(f3, x[w - 1]));
            }
            fw.push(gt(y[w], x[w - 1], f3));
        }
        g.extend_from_slice(&fw);
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
    /// D1_FINC: index cubes of the activity predicate (the same tree exact9_tree / exact9_tree_at builds), the value of a
    /// cube list on a pe9 code, and the gates moving FL_LANE from predicate `old` to `new` (exact on all 32 codes, al = yt).
    fn f_idx(&mut self, a: &BTreeSet<i32>, dom: &BTreeSet<i32>) -> Vec<Vec<(usize, u8)>> {
        let (mut on, mut off) = (0u128, 0u128);
        for &e in dom {
            if a.contains(&e) { on |= 1u128 << Self::pe9(e); } else { off |= 1u128 << Self::pe9(e); }
        }
        if p2("D1") { return self.dtree(on, off, &VS_EXACT, 1); } // P2_D1
        self.dtree_tree(on, off, &VS_EXACT, 1)
    }
    /// P3_I1: f_idx without touching the dtree memo.
    fn f_idx_nm(&mut self, a: &BTreeSet<i32>, dom: &BTreeSet<i32>) -> Vec<Vec<(usize, u8)>> {
        let saved = self.memo.clone();
        let r = self.f_idx(a, dom);
        self.memo = saved;
        r
    }
    fn f_eval(c: &[Vec<(usize, u8)>], code: u32) -> bool {
        c.iter().filter(|cb| cb.iter().all(|&(v, b)| ((code >> v) & 1) as u8 == b)).count() % 2 == 1
    }
    fn f_trans(&mut self, old: &[Vec<(usize, u8)>], new: &[Vec<(usize, u8)>], al: &[Lit]) -> GL {
        let (mut on, mut off) = (0u128, 0u128);
        for code in 0..32u32 {
            if Self::f_eval(old, code) ^ Self::f_eval(new, code) { on |= 1u128 << code; } else { off |= 1u128 << code; }
        }
        let l = if p2("D1") { self.dtree(on, off, &VS_EXACT, 1) } else { self.dtree_tree(on, off, &VS_EXACT, 1) }; // P2_D1
        let lits = self.lits9(&l);
        let mut g = vec![];
        for li in &lits {
            let mut c = li.clone();
            c.extend_from_slice(al);
            g.extend(self.m(&c, FL_LANE));
        }
        g
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
                if p2brk("D1") == 2 && IN_F.load(Ordering::Relaxed) { r.pop(); } // P2_D1 break 2: one cover cube dropped
            }
        }
        self.memo.insert(key, r.clone());
        r
    }
    /// Exact on shots at the top at an even slot: fires on the e in a, on no other e that can be there.
    fn exact9(&mut self, a: &BTreeSet<i32>) -> Vec<Vec<Lit>> {
        self.exact9_at(a, &(0..=ECAP).collect())
    }
    fn exact9_at(&mut self, a: &BTreeSet<i32>, dom: &BTreeSet<i32>) -> Vec<Vec<Lit>> {
        let (mut on, mut off) = (0u128, 0u128);
        for &e in dom {
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
        self.exact9_tree_at(a, &(0..=ECAP).collect())
    }
    /// L4: e values that can wait (be at the top with w > 0) at even slot t, from the pairs9 bounds. Break 2 = one e short.
    fn wait_es(t: i32) -> BTreeSet<i32> {
        let em = emax9(t);
        let mut out = BTreeSet::new();
        for e in (em + 1)..=ECAP {
            let pe = pe9_lvl(e);
            let w_max = (pe - 1) - (t % pe);
            for w in 0..=w_max {
                if (e - w).rem_euclid(2) != 0 {
                    continue;
                }
                if e + w <= 2 * N as i32 - t && e - w <= t - 2 {
                    out.insert(e);
                    break;
                }
            }
        }
        if brk(L4) == 2 {
            if let Some(&m) = out.iter().next_back() {
                out.remove(&m);
            }
        }
        out
    }
    /// L4: bits of the waiter counter that can be nonzero after the increment at slot t. Break 1 = one bit short; 4 = one
    /// bit short at t = 2 mod 16 only (a tight edge).
    fn wb_slot(t: i32) -> usize {
        let s = ((16 - (t % 16)) % 16).min(2 * N as i32 - t);
        let mut wb = if s <= 0 {
            0
        } else if s <= 1 {
            1
        } else if s <= 3 {
            2
        } else if s <= 7 {
            3
        } else {
            4
        };
        let b = brk(L4);
        if (b == 1 || (b == 4 && t % 16 == 2)) && wb > 0 {
            wb -= 1;
        }
        wb
    }
    fn wne0_wb(&self, wb: usize) -> Vec<Vec<Lit>> {
        if p3("G6") && wb >= 2 {
            // P3_G6: OR(w) = 1 ^ AND(~w): two XOR cubes instead of wb disjoint ones. Breaks: 1 = the constant cube dropped, 2 = one literal dropped from the AND cube.
            let b = p3brk("G6");
            let mut all: Vec<Lit> = self.w[..wb].iter().map(|&q0| (q0, false)).collect();
            if b == 2 { all.pop(); }
            return if b == 1 { vec![all] } else { vec![vec![], all] };
        }
        let mut out = vec![];
        let mut pre: Vec<Lit> = vec![];
        for &q0 in &self.w[..wb] {
            let mut c = pre.clone();
            c.push((q0, true));
            out.push(c);
            pre.push((q0, false));
        }
        out
    }
    fn exact9_tree_at(&mut self, a: &BTreeSet<i32>, dom: &BTreeSet<i32>) -> Vec<Vec<Lit>> {
        let (mut on, mut off) = (0u128, 0u128);
        for &e in dom {
            if a.contains(&e) {
                on |= 1u128 << Self::pe9(e);
            } else {
                off |= 1u128 << Self::pe9(e);
            }
        }
        let l = if p2("D1") { self.dtree(on, off, &VS_EXACT, 1) } else { self.dtree_tree(on, off, &VS_EXACT, 1) }; // P2_D1: ESOP cover (table hit) instead of the disjoint tree
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
        if p2("B1") && W2_CLEAN3 && IN_F.load(Ordering::Relaxed) {
            return self.conv_u9_eb(lev, EB, u32::MAX);
        }
        let mut g = vec![];
        for i in 1..lev {
            g.extend(dec_ctl(&self.e[i - 1..], &[(self.w[i], true)], &self.dirty));
        }
        g
    }
    fn conv_v9(&self, lev: usize) -> GL {
        if p2("B1") && W2_CLEAN3 && IN_F.load(Ordering::Relaxed) {
            return self.conv_v9_eb(lev, EB, u32::MAX);
        }
        let mut g = inc_ctl(&self.e, &[(self.w[0], true)], &self.dirty);
        for i in 1..lev {
            g.extend(inc_ctl(&self.e[i - 1..], &[(self.w[i], true)], &self.dirty));
        }
        g
    }
    /// bits of e that the mask toggles read
    fn eb_used(&self, tg: &BTreeMap<usize, Vec<Vec<Lit>>>) -> usize {
        let mut mx = 0usize;
        for ll in tg.values() {
            for c in ll {
                for &(w, _) in c {
                    for j in 0..EB {
                        if w == self.e[j] && j + 1 > mx {
                            mx = j + 1;
                        }
                    }
                }
            }
        }
        mx
    }
    /// L3A: the conversion restricted to e[..eb] and to the w bits some active pair has set. Breaks: 1 = eb one lane short,
    /// 2 = the lowest set bit of w_mask dropped, 3 = (single start) conversion skipped but the mask toggle kept (VACUOUS per s13), 4 = the single-start tg clear also applied to two-start rows (real obligation).
    fn l3_tg(&self, tg: &mut BTreeMap<usize, Vec<Vec<Lit>>>, nstarts: usize, last_key: usize) {
        if lv(L3A) && (nstarts == 1 || (brk(L3A) == 4 && nstarts == 2)) && brk(L3A) != 3 {
            tg.clear();
        }
        if lv(L3B) && nstarts >= 2 {
            let b = brk(L3B);
            tg.insert(last_key, vec![]);
            if b == 1 {
                // the group before the last also loses its toggle
                let prev = tg.range(..last_key).next_back().map(|(&k, _)| k);
                if let Some(k) = prev {
                    tg.insert(k, vec![]);
                }
            }
        }
    }
    fn l3_eb_mask(&self, tg: &BTreeMap<usize, Vec<Vec<Lit>>>, w_mask: u32, nstarts: usize) -> (usize, u32) {
        let mut eb = self.eb_used(tg);
        let mut wm = w_mask;
        let b = brk(L3A);
        if b == 1 && eb > 0 {
            eb -= 1;
        }
        if b == 2 && wm != 0 {
            wm &= wm - 1;
        }
        if b == 3 && nstarts == 1 {
            eb = 0;
        }
        (eb, wm)
    }
    /// P2_B1 form of conv_u9_eb / conv_v9_eb: the same sums as one clean-lane ripple on e[..eb]
    fn conv_adds(&self, lev: usize, eb: usize, w_mask: u32, with_w0: bool) -> Vec<Vec<u32>> {
        let mut adds: Vec<Vec<u32>> = vec![vec![]; eb];
        if with_w0 && (w_mask & 1) != 0 && eb > 0 {
            adds[0].push(self.w[0]);
        }
        for i in 1..lev {
            if i - 1 < eb && ((w_mask >> i) & 1 != 0) {
                adds[i - 1].push(self.w[i]);
            }
        }
        adds
    }
    fn conv_u9_eb(&self, lev: usize, eb: usize, w_mask: u32) -> GL {
        if p2("B1") && W2_CLEAN3 && eb >= 1 && IN_F.load(Ordering::Relaxed) {
            let adds = self.conv_adds(lev, eb, w_mask, false);
            if adds.iter().all(|a| a.is_empty()) {
                return vec![];
            }
            return conv_clean(&self.e[..eb], &adds, true);
        }
        if false {
            return vec![]; // DIAGNOSTIC ONLY (count upper bound of what the conv chains still cost), not a lever
        }
        let mut g = vec![];
        for i in 1..lev {
            if i - 1 < eb && ((w_mask >> i) & 1 != 0) {
                g.extend(dec_ctl(&self.e[i - 1..eb], &[(self.w[i], true)], &self.dirty));
            }
        }
        g
    }
    fn conv_v9_eb(&self, lev: usize, eb: usize, w_mask: u32) -> GL {
        if p2("B1") && W2_CLEAN3 && eb >= 1 && IN_F.load(Ordering::Relaxed) {
            let adds = self.conv_adds(lev, eb, w_mask, true);
            if adds.iter().all(|a| a.is_empty()) {
                return vec![];
            }
            return conv_clean(&self.e[..eb], &adds, false);
        }
        if eb == 0 || false {
            return vec![];
        }
        let mut g = if (w_mask & 1) != 0 { inc_ctl(&self.e[..eb], &[(self.w[0], true)], &self.dirty) } else { vec![] };
        for i in 1..lev {
            if i - 1 < eb && ((w_mask >> i) & 1 != 0) {
                g.extend(inc_ctl(&self.e[i - 1..eb], &[(self.w[i], true)], &self.dirty));
            }
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
        let l4_511 = lv(L4) && (t == 2 * N as i32 - 1 || (brk(L4) == 3 && t == 2 * N as i32 - 3));
        let al: Vec<Lit> = if l4_511 { vec![(yt, true)] } else { cat(&[(yt, true)], &self.hl(0)) };
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        // D1_O9F: hold al (yt & e = 0) on the idle clean lane FL_LANE from here to the first post-block gate.
        let o9f = d1_sw("D1_O9F") && al.len() >= 2 && l >= 1 && f <= N as i32;
        // P3_G2 (unitary only): [h == 0] parked on lane 513 (idle in odd slots) from here to the first L5 gate, which sits before h is touched.
        // Breaks: 1 = lane 513 dirty around the park, 2 = park never uncomputed.
        let g2 = p3("G2") && lv(L5) && !l4_511 && t != 2 * N as i32 - 1 && t != 3 && al.len() >= 2;
        let h0l = self.hl(0);
        let al: Vec<Lit> = if g2 { vec![(yt, true), (ZW_LANE, true)] } else { al };
        if g2 {
            //PZ self.b.t(&pzero("G2 lane 513 before park (expect 0)", &[ZW_LANE]));
            if p3brk("G2") == 1 { self.b.t(&[gx(ZW_LANE)]); }
            let pk = self.m(&h0l, ZW_LANE);
            self.b.t(&pk);
        }
        let o9src: Vec<Lit> = if o9f && d1_brk("D1_O9F_BREAK") == 2 { al[..al.len() - 1].to_vec() } else { al.clone() };
        if o9f {
            let g = self.m(&o9src, FL_LANE);
            self.b.t(&g);
        }
        let o9un: GL = if o9f && d1_brk("D1_O9F_BREAK") != 1 { self.m(&o9src, FL_LANE) } else { vec![] };
        if l >= 1 && f <= N as i32 {
            let c = wl[0];
            let actv = if o9f { vec![vec![(FL_LANE, true)]] } else { vec![al.clone()] };
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
                    if !lv(L9) || brk(L9) == 2 {
                        for li in &actv {
                            g.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                        }
                    }
                } else {
                    if lv(L2) {
                        g.push(gc(d, y0));
                    } else {
                        for li in &actv {
                            g.extend(self.m(&cat(li, &[(d, true)]), y0));
                        }
                    }
                    if !(lv(L2) && brk(L2) == 2) {
                        for li in &actv {
                            g.extend(self.m(&cat(li, &[(y0, true)]), d));
                        }
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
                    if !lv(L9) {
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                        }
                    }
                    hh.push(gc(d, x[W - k]));
                    let xt = x[W - 1];
                    if lv(L2) {
                        hh.push(gc(xt, y0));
                    }
                    if p2("F1B") {
                        hh.push(gc(y0, xt)); // P2_F1B: y0 is 0 outside actv here (audit claim, tested by the replay)
                    } else {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    }
                    if lv(L2) {
                        if brk(L2) != 1 {
                            hh.push(gc(xt, y0));
                        }
                    } else {
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
                    if lv(L2) {
                        if brk(L2) == 4 {
                            hh.push(gc(host, d));
                        } else {
                            hh.push(gc(d, host));
                        }
                    } else {
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(d, true)]), host));
                        }
                    }
                }
                self.b.t(&hh);
                self.b.t(&rev(&g));
            }
        }
        if lv(L8) && t == 3 {
            // L8_T3_JUNCTION (valid walk states only): at t = 3 every shot ends at (L,F) = (1,1), so the rise/rotate gates have a
            // |0> control and the post block only erases ctl and h. Breaks: 1 = h[0] not erased, 2 = no relabel of y, 3 = ctl not cleared.
            let b8 = brk(L8);
            let mut g = if o9f { vec![gc(FL_LANE, ctl)] } else { self.m(&al, ctl) };
            g.extend_from_slice(&o9un);
            if d1_sw("D1_RZ") && o9f {
                g.push(grst(FL_LANE));
            }
            for w in 1..(W - 1) {
                cswap(ctl, x[w], y[w], &mut g);
            }
            g.extend_from_slice(&[gc(ctl, x[W - 1]), gc(ctl, y[W - 1]), gc(ctl, self.par)]);
            for (i, &q0) in h.iter().enumerate() {
                if b8 == 1 && i == 0 {
                    continue;
                }
                g.extend_from_slice(&[gc(ctl, q0), gx(q0)]);
            }
            g.push(gc(y[0], ctl));
            if b8 != 3 {
                g.push(gx(ctl));
            }
            self.b.t(&g);
            if b8 != 2 {
                let mut ny = vec![y[W - 1]];
                ny.extend_from_slice(&y[..W - 1]);
                self.y = ny;
            }
            return;
        }
        let mut g = if o9f { self.m(&[(FL_LANE, true), (y[0], false)], ctl) } else { self.m(&cat(&al, &[(y[0], false)]), ctl) };
        g.extend_from_slice(&o9un);
        if d1_sw("D1_RZ") && o9f {
            g.push(grst(FL_LANE));
        }
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
        let aa = if g2 { vec![(fl, true), (ZW_LANE, true)] } else { cat(&[(fl, true)], &self.hl(0)) };
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[W - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: hi to 15 unless (not xt, y0=0), so the common rise gives hi 0 (E'=0, or the second state) or 1 (E'=2)
        if lv(L5) {
            // L5_H15_UPDATE. Breaks: 1 = fl, y0 merge drops the h == 0 literals at every slot (not only 511); 2 = ctl uncompute
            // reads h1,h2 only (one literal short); 3 = the t = 511 special case also applied at t = 509; 4 = ctl kept live but
            // the xt-gated fl clear uses xt = false (wrong polarity).
            let b5 = brk(L5);
            // CORRECTED FORM (s13-evidence784 T3): the first form (uncompute ctl with h1,h2,h3 only) was refuted by the replay (fails every shot):
            // h is 14 or 15 on idle shots (fl = 0, y0 = 0), so the ctl uncompute needs y0 as an extra literal. Rests on the sampled premise h >= 14 => y0 = 0.
            let t511 = (t == 2 * N as i32 - 1) || (b5 == 3 && t == 2 * N as i32 - 3);
            let mut g = if t511 || b5 == 1 {
                self.m(&[(fl, true), (y[0], true)], ctl)
            } else if g2 {
                self.m(&[(fl, true), (y[0], true), (ZW_LANE, true)], ctl)
            } else {
                self.m(&cat(&[(fl, true), (y[0], true)], &self.hl(0)), ctl)
            };
            if g2 && p3brk("G2") != 2 {
                g.extend(self.m(&h0l, ZW_LANE));
                if p3brk("G2") == 1 { g.push(gx(ZW_LANE)); }
            }
            for &q0 in &h {
                g.push(gc(ctl, q0));
            }
            g.push(gt(ctl, xt, fl));
            g.extend(self.m(&[(ctl, true), (xt, b5 == 4), (y[W - 2], true)], fl));
            if t511 {
                g.push(gc(h[0], ctl));
                g.extend(self.m(&[(xt, false), (y[0], false), (y[1], true), (h[0], false)], fl));
            } else {
                if b5 == 2 {
                    g.extend(self.m(&[(h[1], true), (h[2], true), (h[3], true)], ctl));
                } else {
                    g.extend(self.m(&[(y[0], true), (h[1], true), (h[2], true), (h[3], true)], ctl));
                }
                g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hl(0)), fl));
            }
            self.b.t(&g);
        } else {
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
        }
        // waiters count this slot
        let wb = if !lv(L4) {
            WB
        } else if l4_511 {
            0
        } else {
            Self::wb_slot(t)
        };
        let g = inc_ctl(&wl[..wb], &[(y[W - 1], true)], &self.dirty);
        self.b.t(&g);
        self.b.t(&[gx(y[W - 1]), gc(y[W - 1], ctl), gx(y[W - 1])]);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        let g = inc_ctl(&h, &[(ctl, true)], &self.dirty);
        self.b.t(&g);
        let yt2 = y[W - 1];
        let mut g = vec![gx(ctl)];
        for cu in self.wne0_wb(wb) {
            g.extend(self.m(&cat(&[(yt2, true)], &cu), ctl));
        }
        self.b.t(&g);
        // the second state acts at the next even slot with w=1
        let g = self.m(&cat(&[(yt2, true), (xt, false), (y[0], false), (y[1], true)], &self.hl(0)), wl[0]);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    /// P3_J1: the final i = 0 toggle cube list of forward row k (after L3A / L3B), None when the row has fewer than two starts (no mask at 0) or no pairs.
    fn row_tg0(&mut self, big: &[(i32, i32, i32, i32)], merge1: bool, t: i32, k: i32, kk: i32) -> Option<Vec<Vec<Lit>>> {
        if k < 1 || k >= kk { return None; }
        let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
        if act.is_empty() { return None; }
        let mut starts: BTreeMap<i32, BTreeSet<u32>> = BTreeMap::new();
        for pr in &act {
            starts.entry(W as i32 - (t / 2 - pr.2) - k).or_default().insert(pu9(pr));
        }
        if k == 1 && merge1 {
            starts.entry(W as i32 - t / 2 - 1).or_default().insert(0);
        }
        if starts.len() < 2 { return None; }
        let mut allu: BTreeSet<u32> = act.iter().map(pu9).collect();
        if k == 1 && merge1 { allu.insert(0); }
        let alo = *starts.keys().next().unwrap();
        let us = starts[&alo].clone();
        let rest: BTreeSet<u32> = allu.difference(&us).cloned().collect();
        Some(self.tog9(&us, &rest, 0))
    }
    /// P3_J1 (backward rows): the final i = 0 toggle cubes of backward row k, None when fewer than two starts.
    fn row_tgb0(&mut self, big: &[(i32, i32, i32, i32)], merge0: bool, merge1: bool, t: i32, k: i32) -> Option<Vec<Vec<Lit>>> {
        if k < 0 { return None; }
        let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
        if act.is_empty() { return None; }
        let mut spos: Vec<(i32, u32)> = act.iter().map(|pr| (W as i32 - (t / 2 + pr.3) - 1 + k, pv9(pr))).collect();
        if k == 0 && merge0 { spos.push((W as i32 - t / 2 - 1, 0)); }
        if k == 1 && merge1 { spos.push((W as i32 - t / 2 - 1, 1)); }
        let mut starts: BTreeMap<i32, BTreeSet<u32>> = BTreeMap::new();
        for &(a, v) in &spos { starts.entry(a).or_default().insert(v); }
        if starts.len() < 2 { return None; }
        let allv: BTreeSet<u32> = spos.iter().map(|p| p.1).collect();
        let ahi = *starts.keys().next_back().unwrap();
        let vs = starts[&ahi].clone();
        let rest: BTreeSet<u32> = allv.difference(&vs).cloned().collect();
        Some(self.tog9(&vs, &rest, 0))
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
        let wait: BTreeSet<i32> = if lv(L4) { Self::wait_es(t) } else { ((em + 1)..=ECAP).collect() };
        let dom: BTreeSet<i32> = if lv(L4) { es.union(&wait).cloned().collect() } else { (0..=ECAP).collect() };
        let sp0: Vec<Vec<Lit>> = self.exact9_at(&s0, &dom).into_iter().map(|li| cat(&li, &al)).collect();
        let sp1: Vec<Vec<Lit>> = self.exact9_at(&s1, &dom).into_iter().map(|li| cat(&li, &al)).collect();
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
        let mut fcur: Vec<Vec<(usize, u8)>> = vec![];
        let finc = d1_sw("D1_F") && d1_sw("D1_FINC");
        let dom9: BTreeSet<i32> = dom.clone();
        // P3_I1: one flag on FL_LANE for the forward rows k = 0..2 (aset is the same for k <= 2) and for backward k = 3 -> 2, stepped by f_trans;
        // the mask of the k = 1, 2 rows moves to ZW_LANE and the k = 1 carry to lane 515 (CC2_N = 1 for the MACs of that row). Breaks: 1 = lane 515 dirty
        // before the k = 1 row, 2 = no step at the k = 3 / 2 junction (flag cleared instead).
        let i1 = p3("I1") && W3_LANE515 && merge0 && merge1 && finc && d1_sw("D1_F012") && kk >= 4 && true;
        let aset2: BTreeSet<i32> = es.iter().cloned().filter(|&e| e >= 2).collect();
        let cub2: Vec<Vec<(usize, u8)>> = if i1 { self.f_idx_nm(&aset2, &dom9) } else { vec![] };
        let i1_none: Vec<Vec<(usize, u8)>> = vec![];
        let i1_part: u32 = 3;
        let i1f = i1 && i1_part & 1 != 0;
        let i1b = i1 && i1_part & 2 != 0;
        let j1 = p3("J1") && lv(L3A) && lv(L3B);
        let mut j1_prev: Option<(i32, Vec<Vec<Lit>>, u32)> = None;
        for k in 0..kk {
            let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            //PZ if i1f && k == 1 { self.b.t(&pzero("I1 lane 515 before the k=1 carry row (expect 0)", &[515])); }
            //PZ if i1f && k == 1 { self.b.t(&pzero("I1 mask lane ZW (513) before fwd k=1 row (expect 0)", &[ZW_LANE])); }
            // P3_J1 plan: merge this row's opening toggle with the previous row's closing one (same mask lane, both rows with a toggle at i = 0)
            let mut j1_d: Option<Vec<Vec<Lit>>> = None;
            let mut j1_eb: Option<Vec<Vec<Lit>>> = None;
            let mut j1_skip = false;
            let mut j1_wm = 0u32;
            let mut j1_cur0: Option<Vec<Vec<Lit>>> = None;
            let kmask: u64 = u64::MAX;
            let kok = |kk_: i32| kk_ < 64 && (kmask >> kk_) & 1 == 1;
            if j1 && j1_lane(k) != 0 {
                j1_cur0 = self.row_tg0(&big, merge1, t, k, kk);
                if let Some(c0) = &j1_cur0 {
                    if let Some((pk, pc, pwm)) = &j1_prev {
                        if *pk == k - 1 && j1_lane(k - 1) == j1_lane(k) && kok(k) {
                            let mut d = j1_xor(pc, c0);
                            if p3brk("J1") == 1 { d.pop(); }
                            let mut eball = pc.clone();
                            eball.extend(d.iter().cloned());
                            j1_eb = Some(eball);
                            j1_d = Some(d);
                            j1_wm = *pwm;
                        }
                    }
                    if j1_lane(k + 1) == j1_lane(k) && kok(k + 1) && self.row_tg0(&big, merge1, t, k + 1, kk).is_some() {
                        j1_skip = true;
                    }
                }
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
            let actv: Vec<Vec<Lit>> = self.exact9_tree_at(&aset, &dom).into_iter().map(|li| cat(&li, &al)).collect();
            let flane: u32 = if k >= 3 || (i1f && k <= 2) { FL_LANE } else if d1_sw("D1_F012") && !(k == 1 && merge1) { if k == 0 { FL_LANE } else { ZW_LANE } } else { NONE };
            let use_f = d1_sw("D1_F") && flane != NONE;
            let fsrc: Vec<Vec<Lit>> = if use_f && d1_brk("D1_F_BREAK") == 2 && aset.len() >= 2 {
                let mut a2 = aset.clone();
                let top_e = *a2.iter().next_back().unwrap();
                a2.remove(&top_e);
                self.exact9_tree_at(&a2, &dom).into_iter().map(|li| cat(&li, &al)).collect()
            } else {
                actv.clone()
            };
            let (fcomp, funcomp): (GL, GL) = if i1f && k <= 2 {
                if k == 0 {
                    fcur = cub2.clone();
                    (self.f_trans(&i1_none, &cub2, &al), vec![])
                } else {
                    (vec![], vec![])
                }
            } else if use_f && finc && k >= 3 {
                let cub = if d1_brk("D1_F_BREAK") == 4 && aset.len() >= 2 {
                    let mut a2 = aset.clone();
                    let top_e = *a2.iter().next_back().unwrap();
                    a2.remove(&top_e);
                    self.f_idx(&a2, &dom9)
                } else {
                    self.f_idx(&aset, &dom9)
                };
                let g = self.f_trans(&fcur.clone(), &cub, &al);
                fcur = cub;
                (g, vec![])
            } else {
                (if use_f { fsrc.iter().flat_map(|li| self.m(li, flane)).collect() } else { vec![] },
                 if use_f && !(d1_brk("D1_F_BREAK") == 1 && k == 3) { fsrc.iter().flat_map(|li| self.m(li, flane)).collect() } else { vec![] })
            };
            let actv: Vec<Vec<Lit>> = if use_f { vec![vec![(flane, true)]] } else { actv };
            let mut allu: BTreeSet<u32> = act.iter().map(pu9).collect();
            if (k == 0 && merge0) || (k == 1 && merge1) {
                allu.insert(0);
            }
            let cv = if cv_v.is_empty() { None } else { Some(&cv_v) };
            D1_SKIPMID.store(use_f && d1_sw("D1_CVMID"), Ordering::Relaxed);
            if let Some(d) = &j1_d { *J1_FWD0.lock().unwrap() = Some(d.clone()); }
            J1_SKIP_END0.store(j1_skip, Ordering::Relaxed);
            let g = if k == 0 || k >= 3 {
                let cc = if k == 0 { y0 } else { y2 };
                assert!(k == 0 || alo + k >= 3);
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, us) in &starts {
                    let rest: BTreeSet<u32> = allu.difference(us).cloned().collect();
                    tg.insert((a - alo) as usize, self.tog9(us, &rest, 0));
                }
                let mut w_mask = act.iter().fold(0u32, |acc, pr| acc | (pr.1 as u32));
                if k == 1 && merge1 {
                    w_mask |= 1;
                }
                if lv(L3A) || lv(L3B) {
                    let lastk = (*starts.keys().next_back().unwrap() - alo) as usize;
                    self.l3_tg(&mut tg, starts.len(), lastk);
                }
                let cv_l3: GL = if lv(L3A) {
                    let (eb, wm) = self.l3_eb_mask(&j1_tgx(&tg, &j1_eb), w_mask | j1_wm, starts.len());
                    self.conv_u9_eb(lev, eb, wm)
                } else {
                    vec![]
                };
                let cv = if lv(L3A) { if cv_l3.is_empty() { None } else { Some(&cv_l3) } } else { cv };
                if k == 0 && merge0 {
                    // ZFOR-wait merge0: Y[1] is not a known 0 for the code-0 class at the slot start, so the merged row's
                    // mask is the clean AND lane; every multi-controlled gate in the row (conversions included) uses the
                    // borrowed-wire form meanwhile.
                    if ZW_SHARED {
                        Z_BUSY.store(true, Ordering::Relaxed);
                    }
                    let cvb = if lv(L3A) { cv_l3.clone() } else { self.conv_u9(lev) };
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
                let mut w_mask = act.iter().fold(0u32, |acc, pr| acc | (pr.1 as u32));
                if k == 1 && merge1 {
                    w_mask |= 1;
                }
                if (lv(L3A) || lv(L3B)) && FLAG_ON {
                    let lastk = (*starts.keys().next_back().unwrap() - alo) as usize;
                    self.l3_tg(&mut ftg, starts.len(), lastk);
                }
                let cv_l3: GL = if lv(L3A) {
                    let (eb, wm) = self.l3_eb_mask(&j1_tgx(&ftg, &j1_eb), w_mask | j1_wm, starts.len());
                    self.conv_u9_eb(lev, eb, wm)
                } else {
                    vec![]
                };
                let cv = if lv(L3A) { if cv_l3.is_empty() { None } else { Some(&cv_l3) } } else { cv };
                if k == 1 && merge1 {
                    // ZFOR-wait merge1: Y[1] is not a known 0 for the code-1 class; carry on the clean AND lane
                    if ZW_SHARED {
                        Z_BUSY.store(true, Ordering::Relaxed);
                    }
                    let cvb = if lv(L3A) { cv_l3.clone() } else { self.conv_u9(lev) };
                    let cvb_o = if cvb.is_empty() { None } else { Some(&cvb) };
                    let r = if FLAG_ON {
                        { if i1f { NO515.store(true, Ordering::Relaxed); } let rr = if i1f { self.row_v(&tv, &sv, t1, top, d, CC2_LANE + 1, ZW_LANE, &ftg, &actv, None, cvb_o) } else { self.row_v(&tv, &sv, t1, top, d, ZW_LANE, FL_LANE, &ftg, &actv, None, cvb_o) }; NO515.store(false, Ordering::Relaxed); rr }
                    } else {
                        self.row_v(&tv, &sv, t1, top, d, ZW_LANE, NONE, &no_tog, &actv, Some(&il), cvb_o)
                    };
                    Z_BUSY.store(false, Ordering::Relaxed);
                    r
                } else if FLAG_ON {
                    self.row_v(&tv, &sv, t1, top, d, y1, if i1f { ZW_LANE } else { FL_LANE }, &ftg, &actv, None, cv)
                } else {
                    self.row_v(&tv, &sv, t1, top, d, y1, NONE, &no_tog, &actv, Some(&il), cv)
                }
            };
            D1_SKIPMID.store(false, Ordering::Relaxed);
            let g: GL = if i1f && ((k == 1 && p3brk("I1") == 1) || (k == 2 && p3brk("I1") == 3)) { let ln = if k == 1 { CC2_LANE + 1 } else { ZW_LANE }; let mut w = vec![gx(ln)]; w.extend(g); w.push(gx(ln)); w } else { g };
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            self.b.t(&fcomp);
            self.b.t(&g);
            let mut g: GL = vec![];
            if k >= 1 {
                // L9_D_PAIR: the last forward k and the first reverse k (k = kk - 1) drop this loop pair. Break 1 = only the forward one dropped.
                if !(lv(L9) && k + 1 == kk) || brk(L9) == 3 {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                    }
                }
            } else {
                if p2("F1A") && !merge0 {
                    g.push(gc(d, y0)); // P2_F1A: d is 0 outside actv at k = 0 (no merge0 correction)
                } else {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(d, true)]), y0));
                }
                }
                if lv(L2) {
                    if brk(L2) != 2 {
                        g.push(gc(y0, d));
                    }
                } else {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(y0, true)]), d));
                    }
                }
            }
            self.b.t(&g);
            self.b.t(&funcomp);
            if d1_sw("D1_RZ") && (!(use_f && finc && k >= 3) || (d1_brk("D1_RZ_BREAK") == 1 && k == 4)) {
                self.b.t(&[grst(FL_LANE)]);
            }
            if d1_sw("D1_RZW") {
                self.b.t(&[grst(ZW_LANE)]);
            }
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            j1_prev = if j1_skip { let wk = big.iter().filter(|p| p.0 >= k).fold(0u32, |a, pr| a | (pr.1 as u32)); j1_cur0.map(|c| (k, c, j1_wm | wk)) } else { None };
        }
        let mut jb_prev: Option<(i32, Vec<Vec<Lit>>)> = None;
        for k in (0..kk).rev() {
            let act: Vec<(i32, i32, i32, i32)> = big.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            //PZ if i1b && k == 2 { self.b.t(&pzero("I1 mask lane ZW (513) before bwd k=2 row (expect 0)", &[ZW_LANE])); }
            // P3_J1 plan for the backward rows (time order k, k - 1, ...)
            let i1b_j = i1b;
            let jb_lane = |kq: i32| -> i32 { if kq >= 3 { 1 } else if kq == 2 && i1b_j { 3 } else { 2 } };
            let mut jb_d: Option<Vec<Vec<Lit>>> = None;
            let mut jb_eb: Option<Vec<Vec<Lit>>> = None;
            let mut jb_skip = false;
            let mut jb_wm = 0u32;
            let mut jb_cur0: Option<Vec<Vec<Lit>>> = None;
            if j1 {
                let kmask: u64 = u64::MAX;
                let kok = |kk_: i32| kk_ >= 0 && kk_ < 64 && (kmask >> kk_) & 1 == 1;
                jb_cur0 = self.row_tgb0(&big, merge0, merge1, t, k);
                if let Some(c0) = jb_cur0.clone() {
                    if let Some((pk, pc)) = &jb_prev {
                        if *pk == k + 1 && jb_lane(k + 1) == jb_lane(k) && kok(k) {
                            let mut d = j1_xor(pc, &c0);
                            if p3brk("J1") == 2 { d.pop(); }
                            let mut eball = pc.clone();
                            eball.extend(d.iter().cloned());
                            jb_eb = Some(eball);
                            jb_d = Some(d);
                        }
                    }
                    if k >= 1 && jb_lane(k - 1) == jb_lane(k) && kok(k - 1) && self.row_tgb0(&big, merge0, merge1, t, k - 1).is_some() {
                        jb_skip = true;
                    }
                    if jb_skip || jb_d.is_some() {
                        // chain mask: the lowest k of the pairable run (largest act set) converts every row of the chain
                        let mut j = k;
                        while j >= 1 && jb_lane(j - 1) == jb_lane(j) && kok(j - 1) && self.row_tgb0(&big, merge0, merge1, t, j - 1).is_some() { j -= 1; }
                        jb_wm = big.iter().filter(|p| p.0 >= j).fold(0u32, |a, pr| a | (pr.1 as u32));
                        if j == 1 && merge1 { jb_wm |= 1; }
                    }
                }
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
            let actv: Vec<Vec<Lit>> = self.exact9_tree_at(&aset, &dom).into_iter().map(|li| cat(&li, &al)).collect();
            let flane: u32 = if k >= 3 || (i1b && k == 2) { FL_LANE } else if d1_sw("D1_F012") && !(k == 1 && merge1) { ZW_LANE } else { NONE };
            let use_f = d1_sw("D1_F") && flane != NONE;
            let fsrc: Vec<Vec<Lit>> = if use_f && d1_brk("D1_F_BREAK") == 2 && aset.len() >= 2 {
                let mut a2 = aset.clone();
                let top_e = *a2.iter().next_back().unwrap();
                a2.remove(&top_e);
                self.exact9_tree_at(&a2, &dom).into_iter().map(|li| cat(&li, &al)).collect()
            } else {
                actv.clone()
            };
            let i1_recomp = i1_part & 4 != 0;
            let (fcomp, funcomp): (GL, GL) = if i1b && k == 2 {
                (if i1_recomp { self.f_trans(&i1_none, &cub2, &al) } else { vec![] }, if p3brk("I1") == 2 { vec![] } else { self.f_trans(&cub2, &i1_none, &al) })
            } else if use_f && finc && k >= 3 {
                let cub = if d1_brk("D1_F_BREAK") == 4 && aset.len() >= 2 {
                    let mut a2 = aset.clone();
                    let top_e = *a2.iter().next_back().unwrap();
                    a2.remove(&top_e);
                    self.f_idx(&a2, &dom9)
                } else {
                    self.f_idx(&aset, &dom9)
                };
                let g = self.f_trans(&fcur.clone(), &cub, &al);
                let u = if k == 3 { let z = if d1_brk("D1_F_BREAK") == 3 { vec![] } else if i1b && i1_part & 4 == 0 { fcur = cub2.clone(); self.f_trans(&cub, &cub2, &al) } else { self.f_trans(&cub, &[], &al) }; if !i1b || i1_part & 4 != 0 { fcur = vec![]; } z } else { fcur = cub; vec![] };
                (g, u)
            } else {
                (if use_f { fsrc.iter().flat_map(|li| self.m(li, flane)).collect() } else { vec![] },
                 if use_f && !(d1_brk("D1_F_BREAK") == 1 && k == 3) { fsrc.iter().flat_map(|li| self.m(li, flane)).collect() } else { vec![] })
            };
            let actv: Vec<Vec<Lit>> = if use_f { vec![vec![(flane, true)]] } else { actv };
            let allv: BTreeSet<u32> = spos.iter().map(|p| p.1).collect();
            let mut w_mask = act.iter().fold(0u32, |acc, pr| acc | (pr.1 as u32));
            if k == 1 && merge1 {
                w_mask |= 1;
            }
            w_mask |= jb_wm;
            D1_SKIPMID.store(use_f && d1_sw("D1_CVMID"), Ordering::Relaxed);
            if let Some(d) = &jb_d { *J1_END0.lock().unwrap() = Some(d.clone()); }
            J1_SKIP_START0.store(jb_skip, Ordering::Relaxed);
            let g = if k >= 3 {
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, vs) in &starts {
                    let rest: BTreeSet<u32> = allv.difference(vs).cloned().collect();
                    tg.insert((ahi - a) as usize, self.tog9(vs, &rest, 0));
                }
                if lv(L3A) || lv(L3B) {
                    let lastk = (ahi - *starts.keys().next().unwrap()) as usize;
                    self.l3_tg(&mut tg, starts.len(), lastk);
                }
                if lv(L3A) {
                    let (eb, wm) = self.l3_eb_mask(&j1_tgx(&tg, &jb_eb), w_mask, starts.len());
                    let cvk = self.conv_v9_eb(lev, eb, wm);
                    let cvo = if cvk.is_empty() { None } else { Some(&cvk) };
                    self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, y1, &tg, &actv, None, cvo)
                } else {
                    self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, y1, &tg, &actv, None, Some(&cv_c))
                }
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
                    let mut ftg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                    if FLAG_ON {
                        for (&a, vs) in &starts {
                            let rest: BTreeSet<u32> = allv.difference(vs).cloned().collect();
                            ftg.insert((ahi - a) as usize, self.tog9(vs, &rest, 0));
                        }
                    }
                    if (lv(L3A) || lv(L3B)) && FLAG_ON {
                        let lastk = (ahi - *starts.keys().next().unwrap()) as usize;
                        self.l3_tg(&mut ftg, starts.len(), lastk);
                    }
                    let cvb = if lv(L3A) {
                        let (eb, wm) = self.l3_eb_mask(&j1_tgx(&ftg, &jb_eb), w_mask, starts.len());
                        self.conv_v9_eb(lev, eb, wm)
                    } else {
                        self.conv_v9(lev)
                    };
                    // plain_vt's carry-out into top for the code-1 class (gated by zuiris's code-1 literal)
                    let mut xg: GL = vec![];
                    let xg0 = lv(L7) && (nn == 1 || (brk(L7) == 2 && nn == 2));
                    for li in &sp1 {
                        if !xg0 {
                            xg.extend(self.m(&cat(li, &[(d, true), (cc, true)]), top));
                            xg.extend(self.m(&cat(li, &[(d, true), (cc, false), (tv[nn - 1], true)]), top));
                        } else {
                            xg.extend(self.m(&cat(li, &[(d, true), (tv[nn - 1], true)]), top));
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
                        if lv(L3A) || lv(L3B) {
                            let lastk = (ahi - *starts.keys().next().unwrap()) as usize;
                            self.l3_tg(&mut ftg, starts.len(), lastk);
                        }
                        if lv(L3A) {
                            let (eb, wm) = self.l3_eb_mask(&j1_tgx(&ftg, &jb_eb), w_mask, starts.len());
                            let cvk = self.conv_v9_eb(lev, eb, wm);
                            let cvo = if cvk.is_empty() { None } else { Some(&cvk) };
                            self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, if i1b && k == 2 { ZW_LANE } else { FL_LANE }, &ftg, &actv, None, cvo)
                        } else {
                            self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, if i1b && k == 2 { ZW_LANE } else { FL_LANE }, &ftg, &actv, None, Some(&cv_c))
                        }
                    } else {
                        self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, NONE, &no_tog, &actv, Some(&il), Some(&cv_c))
                    }
                }
            };
            D1_SKIPMID.store(false, Ordering::Relaxed);
            let mut hh: GL = vec![];
            if k >= 1 {
                if !(lv(L9) && k + 1 == kk) || brk(L9) == 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                    }
                }
                hh.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    if lv(L2) {
                        hh.push(gc(xt, y0));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    if lv(L2) {
                        if brk(L2) != 1 {
                            hh.push(gc(xt, y0));
                        }
                    } else {
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                        }
                    }
                }
                if k == 1 && merge1 && !lv(L2) {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), top));
                    }
                } else if !(lv(L2) && brk(L2) == 3 && k == 1 && merge1) {
                    hh.push(gc(d, top));
                }
            } else {
                let host = x[W - 1];
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(host, true)]), d));
                }
                if lv(L2) {
                    if brk(L2) == 4 {
                        hh.push(gc(host, d));
                    } else {
                        hh.push(gc(d, host));
                    }
                } else {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
            }
            self.b.t(&fcomp);
            self.b.t(&hh);
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            jb_prev = if jb_skip { jb_cur0.clone().map(|c| (k, c)) } else { None };
            self.b.t(&rev(&g));
            if k == 0 && merge0 {
                self.b.t(&c10);
            }
            if k == 1 && merge1 {
                self.b.t(&c11);
            }
            self.b.t(&funcomp);
            if d1_sw("D1_RZ") && !(use_f && finc && k > 3) {
                self.b.t(&[grst(FL_LANE)]);
            }
            if d1_sw("D1_RZW") {
                self.b.t(&[grst(ZW_LANE)]);
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
        let acts: BTreeSet<i32> = if lv(L4) { es.clone() } else { (0..=em.min(ECAP)).collect() };
        let has_wait = !wait.is_empty();
        let acu: Vec<Vec<Lit>> = if has_wait { self.exact9_at(&acts, &dom) } else { vec![] };
        let wcu: Vec<Vec<Lit>> = if has_wait { self.exact9_at(&wait, &dom) } else { vec![] };
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
            let d2 = p2("D2");
            if d2 {
                // P2_D2 (valid walk states: y0 = 0 here, e in the acting-or-waiting domain): (yt & wcu) ^ ctl == yt, so z = yt
                g.push(gc(y[W - 1], z));
                if p2brk("D2") == 1 {
                    g.push(gc(ctl, z));
                }
            } else {
                for cu in &wcu {
                    g.extend(self.m(&cat(&[(y[W - 1], true)], cu), z));
                }
                g.push(gc(ctl, z));
            }
            self.b.t(&g);
            let g = rotate_up(z, &y, W - 1);
            self.b.t(&g);
            self.b.t(&[gc(ctl, z)]);
            let mut g: GL = vec![];
            // P2_D2: y[W-1] is 0 after the rotation (z = yt moved y[0] = 0 into the top), so this loop never fires
            if !d2 || p2brk("D2") == 2 || p2brk("D2") == 4 {
                for cu in &acu {
                    g.extend(self.m(&cat(&[(yt, true)], cu), ctl));
                }
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
        } else if p2("D2") && p2brk("D2") != 3 && p2brk("D2") != 4 {
            // P2_D2: after gc(ctl, y[W-1]) the top equals ctl, and ctl = 1 implies acu(e) = 1: the loop is ctl ^= ctl
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
            let wb = if lv(L4) { Self::wb_slot(t) } else { WB };
            let g = inc_ctl(&wl[..wb], &[(z, true)], &self.dirty);
            self.b.t(&g);
            if d1_sw("D1_RZW") && d1_brk("D1_RZ_BREAK") == 2 {
                self.b.t(&[grst(z)]);
            }
            let mut g: GL = vec![];
            for wc in self.wne0_wb(wb) {
                g.extend(self.m(&cat(&[(y[W - 1], false), (y[W - 2], true)], &wc), z));
            }
            if d1_sw("D1_RZW") {
                g.push(grst(z));
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
        let g7 = p3("G7");
        for i in (0..lev).rev() {
            if g7 {
                // P3_G7: act & wl[i] as one measured AND on lane 516 (idle here), CX into ctl around the rotation. Breaks: 1 = lane 516 dirty, 2 = second CX dropped.
                let b = p3brk("G7");
                //PZ self.b.t(&pzero("G7 lane 516 before act&wl[i] AND (expect 0)", &[FL_LANE]));
                if b == 1 { self.b.t(&[gx(FL_LANE)]); }
                self.b.t(&[gt(act, wl[i], FL_LANE | AND_FLAG), gc(FL_LANE, ctl)]);
                let g = rotate_up(ctl, &win, 1 << i);
                self.b.t(&g);
                if b != 2 { self.b.t(&[gc(FL_LANE, ctl)]); }
                self.b.t(&[gt(act, wl[i], FL_LANE | AND_FLAG)]);
                if b == 1 { self.b.t(&[gx(FL_LANE)]); }
                continue;
            }
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
        // P3_G5: prefix checkpoints Z4 = act & ~y1..~y4 on lane 513 (w >= 4) and Z9 = Z4 & ~y5..~y9 on lane 516 (w >= 9), unitary.
        // Breaks: 1 = lane 513 dirty around the block, 2 = lane 516 dirty, 3 = the Z9 users read Z4.
        let g5 = p3("G5") && lev >= 3;
        let g5_z4: Vec<Lit> = { let mut v: Vec<Lit> = vec![(act, true)]; v.extend((1..=4).map(|i| (y[i], false))); v };
        let g5_z9: Vec<Lit> = { let mut v: Vec<Lit> = vec![(ZW_LANE, true)]; v.extend((5..=9).map(|i| (y[i], false))); v };
        let g5_9 = g5 && lev >= 4;
        if g5 {
            //PZ g.extend(pzero("G5 lane 513 before Z4 compute (expect 0)", &[ZW_LANE]));
            if p3brk("G5") == 1 { g.push(gx(ZW_LANE)); }
            g.extend(self.m(&g5_z4, ZW_LANE));
        }
        if g5_9 {
            //PZ g.extend(pzero("G5 lane 516 before Z9 compute (expect 0)", &[FL_LANE]));
            if p3brk("G5") == 2 { g.push(gx(FL_LANE)); }
            g.extend(self.m(&g5_z9, FL_LANE));
        }
        for w in 1usize..(1 << lev) {
            let p = 1 + w;
            let mut li: Vec<Lit> = vec![];
            if g5_9 && w >= 9 {
                li.push((if p3brk("G5") == 3 { ZW_LANE } else { FL_LANE }, true));
                for i in 10..p {
                    li.push((y[i], false));
                }
            } else if g5 && w >= 4 {
                li.push((ZW_LANE, true));
                for i in 5..p {
                    li.push((y[i], false));
                }
            } else {
                li.push((act, true));
                for i in 1..p {
                    li.push((y[i], false));
                }
            }
            li.push((y[p], true));
            for i in 0..lev {
                if (w >> i) & 1 == 1 {
                    g.extend(self.m(&li, wl[i]));
                }
            }
        }
        if g5_9 {
            g.extend(self.m(&g5_z9, FL_LANE));
            if p3brk("G5") == 2 { g.push(gx(FL_LANE)); }
        }
        if g5 {
            g.extend(self.m(&g5_z4, ZW_LANE));
            if p3brk("G5") == 1 { g.push(gx(ZW_LANE)); }
        }
        self.b.t(&g);
        let mut g: GL = h.iter().map(|&q0| gc(act, q0)).collect();
        g.extend(inc_ctl(&h, &[(act, true)], &self.dirty));
        self.b.t(&g);
        if g7 {
            //PZ self.b.t(&pzero("G7 lane 516 before act&~xt AND (expect 0)", &[FL_LANE]));
            self.b.t(&[gx(xt), gt(act, xt, FL_LANE | AND_FLAG), gx(xt), gc(FL_LANE, ctl)]);
            let g = rot1(ctl, &win);
            self.b.t(&g);
            self.b.t(&[gc(FL_LANE, ctl), gx(xt), gt(act, xt, FL_LANE | AND_FLAG), gx(xt)]);
        } else {
        let g1 = self.m(&[(act, true), (xt, false)], ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        }
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
            if p3("G4") {
                // P3_G4: the shared prefix AND parked on 516 (and 513 for the second pair) as measured ANDs: xt & ~y1 on 516, ~y2 & y3 on 513 (gp = 1).
                // Breaks: 1 = lane 516 dirty, 2 = lane 513 dirty (gp = 1), 3 = hl value of the other pair.
                let b = p3brk("G4");
                let xp = |a: Lit| -> GL { if a.1 { vec![] } else { vec![gx(a.0)] } };
                let (a1, a2) = (gl[0], gl[1]);
                let pre1: GL = [xp(a1), xp(a2)].concat();
                //PZ g.extend(pzero("G4 lane 516 before park (expect 0)", &[FL_LANE]));
                if b == 1 { g.push(gx(FL_LANE)); }
                g.extend_from_slice(&pre1);
                g.push(gt(a1.0, a2.0, FL_LANE | AND_FLAG));
                g.extend(rev(&pre1));
                if gp == 0 {
                    let a3 = gl[2];
                    g.extend(self.m(&[(FL_LANE, true), a3], act));
                    g.extend(self.m(&cat(&[(FL_LANE, true), a3], &self.hl(if b == 3 { 1 } else { 0 })), act));
                } else {
                    let (a3, a4) = (gl[2], gl[3]);
                    let pre2: GL = [xp(a3), xp(a4)].concat();
                    //PZ g.extend(pzero("G4 lane 513 before park (expect 0)", &[ZW_LANE]));
                    if b == 2 { g.push(gx(ZW_LANE)); }
                    g.extend_from_slice(&pre2);
                    g.push(gt(a3.0, a4.0, ZW_LANE | AND_FLAG));
                    g.extend(rev(&pre2));
                    g.extend(self.m(&[(FL_LANE, true), (ZW_LANE, true)], act));
                    g.extend(self.m(&cat(&[(FL_LANE, true), (ZW_LANE, true)], &self.hl(1)), act));
                    g.extend_from_slice(&pre2);
                    g.push(gt(a3.0, a4.0, ZW_LANE | AND_FLAG));
                    g.extend(rev(&pre2));
                    if b == 2 { g.push(gx(ZW_LANE)); }
                }
                g.extend_from_slice(&pre1);
                g.push(gt(a1.0, a2.0, FL_LANE | AND_FLAG));
                g.extend(rev(&pre1));
                if b == 1 { g.push(gx(FL_LANE)); }
                continue;
            }
            g.extend(self.m(&gl, act));
            g.extend(self.m(&cat(&gl, &self.hl(gp as i32)), act));
        }
        // P3_G1: prefix checkpoints Z5 = ~y1..~y5 on lane ZW_LANE (513) and Z10 = Z5 & ~y6..~y10 on FL_LANE (516), both clean here
        // (513 reset after the waiter erase, 516 released after the last row); unitary compute / uncompute, no measurement.
        let g1 = p3("G1");
        let mut g1_maxgu = 0usize;
        if g1 {
            for gg in 0..2i32 {
                for w in 2i32..(1 << lev) {
                    if prs.iter().any(|p| p.1 == w) {
                        g1_maxgu = g1_maxgu.max((1 + gg + w) as usize);
                    }
                }
            }
        }
        let g1_z5: Vec<Lit> = (1..=5).map(|i| (y[i], false)).collect();
        let g1_z10: Vec<Lit> = { let mut v: Vec<Lit> = vec![(ZW_LANE, true)]; v.extend((6..=10).map(|i| (y[i], false))); v };
        // breaks: 1 = lane 513 dirty (|1>) around the block, 2 = lane 516 dirty, 3 = the Z10 users read Z5 instead
        if g1_maxgu >= 6 && p3brk("G1") == 1 { g.push(gx(ZW_LANE)); }
        if g1_maxgu >= 11 && p3brk("G1") == 2 { g.push(gx(FL_LANE)); }
        if g1_maxgu >= 6 {
            //PZ g.extend(pzero("G1 lane 513 before Z5 compute (expect 0)", &[ZW_LANE]));
            //PZ g.extend(pzero("G1 lane 516 before Z10 compute (expect 0)", &[FL_LANE]));
            g.extend(self.m(&g1_z5, ZW_LANE));
        }
        if g1_maxgu >= 11 {
            g.extend(self.m(&g1_z10, FL_LANE));
        }
        for gg in 0..2i32 {
            for w in 2i32..(1 << lev) {
                let vals: BTreeSet<i32> = prs.iter().filter(|p| p.1 == w).map(|p| (gg - p.2).rem_euclid(16)).collect();
                if vals.is_empty() {
                    continue;
                }
                let gu = (1 + gg + w) as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                if g1 && gu >= 11 {
                    li.push((if p3brk("G1") == 3 { ZW_LANE } else { FL_LANE }, true));
                    for i in 11..gu {
                        li.push((y[i], false));
                    }
                } else if g1 && gu >= 6 {
                    li.push((ZW_LANE, true));
                    for i in 6..gu {
                        li.push((y[i], false));
                    }
                } else {
                    for i in 1..gu {
                        li.push((y[i], false));
                    }
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
        if g1_maxgu >= 11 {
            g.extend(self.m(&g1_z10, FL_LANE));
        }
        if g1_maxgu >= 6 {
            g.extend(self.m(&g1_z5, ZW_LANE));
        }
        if g1_maxgu >= 6 && p3brk("G1") == 1 { g.push(gx(ZW_LANE)); }
        if g1_maxgu >= 11 && p3brk("G1") == 2 { g.push(gx(FL_LANE)); }
        self.b.t(&g);
        let e1 = p2("E1");
        // P2_E1: at t >= 2N-2 (l = 255) ripple 3 is empty, f3 stays 0 and the act gate (reads h[2] = 1) never fires
        let e1_skip = e1 && t >= 2 * N as i32 - 2 - if p2brk("E1") == 3 { 2 } else { 0 };
        if t + 1 <= 2 * N as i32 && !e1_skip {
            let tau = ctl;
            let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hl(0));
            let tg = self.m(&gl, tau);
            self.b.t(&tg);
            let dirty = if e1 { p2brk("E1") - 4 } else { 0 }; // breaks 5 / 6: the flag wire f1 = h[0] / f3 = h[2] is |1> (dirty) while ripples 1 / 3 run
            if dirty == 1 { self.b.t(&[gx(h[0])]); }
            if dirty == 2 { self.b.t(&[gx(h[2])]); }
            let pg = if e1 { self.pi_gates_open(t + 1, h[3], h[0], h[1], h[2]) } else { self.pi_gates(t + 1, h[3], h[0], h[1], h[2]) };
            self.b.t(&pg);
            let g = self.m(&[(tau, true), (h[0], false), (h[1], true), (h[2], true)], act);
            self.b.t(&g);
            if e1 && p2brk("E1") == 2 {
                // break 2: ripple 3 is not closed (its last gate dropped)
                let mut r = rev(&pg);
                r.pop();
                self.b.t(&r);
            } else {
                self.b.t(&rev(&pg));
            }
            if dirty == 1 { self.b.t(&[gx(h[0])]); }
            if dirty == 2 { self.b.t(&[gx(h[2])]); }
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
    if MAC_ON { let g = std::mem::take(&mut mc.b.gates); mc.b.gates = mac_finish(g); }
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
        if g.0 == RST {
            // an X-basis measurement into a fresh, never-read bit: on a wire that is |0> on the shot it changes neither
            // the state nor the phase (the judge's phase term is q & r); every post-pass already handles Hmr.
            let _ = self.hmr(g.1);
            return;
        }
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
/// P3_H1: add_gl with the top carries on clean lanes (AND_FLAG pairs, measured uncompute) and, when `c0` is set, the bottom carry as one
/// measured AND on the clean carry wire. Returns the gates and the wire that holds the final carry.
/// P3_H1 site counter: bumped at every allocation of the product-phase clean lanes (stream order); DEV_P3_H1_SITES = bitmask of sites where H1 applies (default all).
static H1_SITE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn site_bump() {
    let i = H1_SITE.fetch_add(1, Ordering::Relaxed);
    let _ = i;
}
fn h1_site_ok() -> bool {
    let m: u64 = 536;
    let i = H1_SITE.load(Ordering::Relaxed);
    i < 64 && (m >> i) & 1 == 1
}
/// P3_H2 site mask (same site numbering as H1; default = the three sites that passed the out-of-envelope test: 3, 4, 9).
fn h2_site_ok() -> bool {
    let m: u64 = 536;
    let i = H1_SITE.load(Ordering::Relaxed);
    i < 64 && (m >> i) & 1 == 1
}
fn h1_c0() -> bool {
    static C: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *C.get_or_init(|| true)
}
fn add_gl_l(t: &[u32], s: &[u32], c: u32, lanes: &[u32], c0: bool) -> (GL, u32) {
    let n = t.len();
    let nk = lanes.len().min(n.saturating_sub(1));
    let i0 = n - nk;
    let mut g = Vec::with_capacity(3 * n);
    for i in 0..n {
        if c0 && i == 0 && i0 > 0 {
            g.push(gt(s[0], t[0], c | AND_FLAG));
            continue;
        }
        if i >= i0 && nk > 0 {
            let (cin, ln) = (if i == i0 { c } else { lanes[i - i0 - 1] }, lanes[i - i0]);
            if EMIT_REROLL { g.push(gc(cin, t[i])); g.push(gc(cin, s[i])); } else { g.push(gc(cin, s[i])); g.push(gc(cin, t[i])); }
            g.push(gt(s[i], t[i], ln | AND_FLAG));
            if !(p3brk("H1") == 2 && i == i0) { g.push(gc(cin, ln)); }
            continue;
        }
        if EMIT_REROLL { g.push(gc(c, t[i])); g.push(gc(c, s[i])); } else { g.push(gc(c, s[i])); g.push(gc(c, t[i])); }
        g.push(gt(s[i], t[i], c));
    }
    (g, if nk > 0 { lanes[nk - 1] } else { c })
}
/// backward sweep matching add_gl_l: per bit [carry uncompute, gc(cin, t), x_j, gc(cin, s)]; `x(j)` is the gate the plain sweep has third.
fn add_bwd_l(t: &[u32], s: &[u32], c: u32, lanes: &[u32], c0: bool, x: &dyn Fn(usize) -> G) -> GL {
    let n = t.len();
    let nk = lanes.len().min(n.saturating_sub(1));
    let i0 = n - nk;
    let mut g = Vec::with_capacity(5 * n);
    for j in (0..n).rev() {
        if c0 && j == 0 && i0 > 0 {
            g.push(gt(s[0], t[0], c | AND_FLAG));
            g.push(x(0));
            continue;
        }
        if j >= i0 && nk > 0 {
            let (cin, ln) = (if j == i0 { c } else { lanes[j - i0 - 1] }, lanes[j - i0]);
            g.push(gc(cin, ln));
            g.push(gt(s[j], t[j], ln | AND_FLAG));
            g.push(gc(cin, t[j]));
            g.push(x(j));
            g.push(gc(cin, s[j]));
            continue;
        }
        g.push(gt(s[j], t[j], c));
        g.push(gc(c, t[j]));
        g.push(x(j));
        g.push(gc(c, s[j]));
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
    /// P2_B5: spare clean lanes of self.zl (beyond the 8 term lanes) for the split top part of a chain of length n
    fn split_extra(&self, n: usize) -> &[u32] {
        if p2("B5") && self.zl.len() > 8 && n >= 40 {
            &self.zl[8..]
        } else {
            &[]
        }
    }
    fn merged(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let ex = self.split_extra(r.len());
        let hk = if ex.is_empty() { 0 } else { ex.len() + 2 };
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..(r.len() - hk) {
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
        let sub1 = sub_pass(&r, &d, c, ex, 1);
        let sub2 = sub_pass(&r, &d, c, ex, 2);
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        g.extend_from_slice(&sub1);
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
        g.extend_from_slice(&sub2);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// L1_MERGED_C0M1: f * (2^32 + 976) on t as one merged chain over the full width of t (exact, no window).
    /// Breaks: 1 = the top term one lane low (2^31), 2 = chain cut to the fold window RW (the approximation we do NOT ship).
    fn c0m1(&self, t: &[u32], f: u32, z: &[u32], c: u32) -> GL {
        let b = brk(L1);
        let top = if b == 1 { 27 } else { 28 };
        let hi = if b == 2 { RW } else { t.len() };
        self.merged(&t[4..hi], f, &[(2, -1, z[0]), (6, 1, z[1]), (top, 1, z[2])], c)
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
        let sub = rev(&add_chain_h2(&r, &d, c));
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
        let ex = self.split_extra(r.len());
        let hk = if ex.is_empty() { 0 } else { ex.len() + 2 };
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..(r.len() - hk) {
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
        let sub1 = sub_pass(&r, &d, c, ex, 1);
        let sub2 = sub_pass(&r, &d, c, ex, 2);
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
        g.extend_from_slice(&sub1);
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
        g.extend_from_slice(&sub2);
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
    /// P3_H1: clean lanes for the carries of the adders (zl lanes, bitmask DEV_P3_H1_MASK over zl[0..8], default all) and whether c is a clean zero.
    fn h1_lanes(&self) -> Vec<u32> {
        if !p3("H1") || !h1_site_ok() { return vec![]; }
        let mask: u32 = 255;
        self.zl.iter().enumerate().filter(|(i, _)| *i < ZL_BASE && (mask >> i) & 1 == 1).map(|(_, &l)| l).collect()
    }
    /// ZFOR-wait: acc += a with no control, carry-out on ov (zuiris's add_ctl with the control removed: 2 T per wire).
    fn add_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let lanes = self.h1_lanes();
        if p3("H1") && h1_site_ok() {
            let b = p3brk("H1");
            let mut g: GL = vec![];
            if b == 1 { g.push(gx(lanes[0])); }
            if a.len() == 256 {
                let (f, cf) = add_gl_l(acc, a, c, &lanes, h1_c0());
                g.extend(f);
                g.push(gc(cf, ov));
                g.extend(add_bwd_l(acc, a, c, &lanes, h1_c0(), &|j| gc(a[j], acc[j])));
            } else {
                let (f, cf) = add_gl_l(&acc[..255], a, c, &lanes, h1_c0());
                g.extend(f);
                g.push(gt(cf, acc[255], ov));
                g.push(gc(cf, acc[255]));
                g.extend(add_bwd_l(&acc[..255], a, c, &lanes, h1_c0(), &|j| gc(a[j], acc[j])));
            }
            if b == 1 { g.push(gx(lanes[0])); }
            return g;
        }
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
        let lanes = self.h1_lanes();
        if a.len() == 256 {
            let (f, cf) = add_gl_l(&acc[k..], &a[k..], c, &lanes, false);
            h.extend(f);
            g = h.clone();
            g.push(gc(cf, ov));
        } else {
            let (f, cf) = add_gl_l(&acc[k..255], &a[k..], c, &lanes, false);
            h.extend(f);
            g = h.clone();
            g.push(gt(cf, acc[255], ov));
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
        if ZL_BASE >= 4 {
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
        let lanes = self.h1_lanes();
        if p3("H1") && h1_site_ok() {
            let mut g: GL = vec![];
            if a.len() == 256 {
                let (f, cf) = add_gl_l(acc, a, c, &lanes, h1_c0());
                g.extend(f);
                g.push(gt(ctl, cf, ov));
                g.extend(add_bwd_l(acc, a, c, &lanes, h1_c0(), &|j| gt(ctl, a[j], acc[j])));
            } else {
                let (f, cf) = add_gl_l(&acc[..255], a, c, &lanes, h1_c0());
                g.extend(f);
                g.extend(self.m(&[(ctl, true), (cf, true), (acc[255], true)], ov));
                g.push(gt(ctl, cf, acc[255]));
                g.extend(add_bwd_l(&acc[..255], a, c, &lanes, h1_c0(), &|j| gt(ctl, a[j], acc[j])));
            }
            return g;
        }
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
        let lanes = self.h1_lanes();
        if a.len() == 256 {
            let (f, cf) = add_gl_l(&acc[k..], &a[k..], c, &lanes, false);
            h.extend(f);
            g = h.clone();
            g.push(gt(ctl, cf, ov));
        } else {
            let (f, cf) = add_gl_l(&acc[k..255], &a[k..], c, &lanes, false);
            h.extend(f);
            g = h.clone();
            g.extend(self.m(&[(ctl, true), (cf, true), (acc[255], true)], ov));
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
        if lv(L6) {
            // L6_HORNER_LAST: i = 0 is a single subtraction of (1 - b0) a instead of double, add (2 b0 - 1) a, subtract a, halve.
            // Breaks: 1 = no conjugation of b0 (subtracts b0 a), 2 = the conjugation not undone (b0 left flipped), 3 = one doubling too many.
            let b6 = brk(L6);
            for i in (1..nb).rev() {
                let nxt = i > if b6 == 3 { 0 } else { 1 };
                g.extend(self.round3(&acc, a, bits[i], c, ov, nxt));
                if nxt {
                    let mut t2 = vec![acc[255]];
                    t2.extend_from_slice(&acc[..255]);
                    acc = t2;
                }
            }
            if b6 != 1 {
                g.push(gx(bits[0]));
            }
            g.extend(rev(&self.round(&acc, a, bits[0], c, ov)));
            if b6 != 1 && b6 != 2 {
                g.push(gx(bits[0]));
            }
        } else {
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
        }
        if w > 0 {
            p.rel(al);
        }
        (acc, low, g)
    }
    fn neg(&self, p: &mut P, t: &[u32], c2: u32) {
        let u = p.alloc();
        p.g(&[gx(u)]);
        let mut g: GL = t.iter().map(|&q0| gx(q0)).collect();
        static NEGN: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let site = 2u32 << NEGN.fetch_add(1, Ordering::Relaxed); // neg #1 = 2, neg #2 = 4 (cneg_list of division 1 = 1)
        let b4 = p2("B4") && lv(L1) && t.len() > 33 && p2_site("B4", site);
        let zs: Vec<u32> = if b4 { p.allocn(t.len() - 5) } else if lv(L1) { p.allocn(3) } else { vec![] };
        if b4 {
            // P2_B4: one ripple pass on t.len() - 5 clean wires (251 CCX) instead of the merged two-pass chain
            if p2brk("B4") == 1 { g.push(gx(zs[0])); }
            g.extend(c0m1_clean(t, u, &zs));
            if p2brk("B4") == 1 { g.push(gx(zs[0])); }
        } else if lv(L1) {
            g.extend(rev(&self.c0m1(t, u, &zs, c2)));
        } else {
            for &b in &C0M1 {
                g.extend(rev(&inc_long(&t[b..], u, &self.dirty, c2)));
            }
        }
        g.push(gx(u));
        p.g(&g);
        for &q0 in &zs {
            p.rel(q0);
        }
        p.rel(u);
    }
    fn cneg_list(&self, t: &[u32], ctl: u32, neg_when: bool, c2: u32, zs: &[u32]) -> GL {
        let pre: GL = if neg_when { vec![] } else { vec![gx(ctl)] };
        let mut g = pre.clone();
        for &q0 in t {
            g.push(gc(ctl, q0));
        }
        if p2("B4") && lv(L1) && t.len() > 33 && zs.len() + 5 >= t.len() {
            if p2brk("B4") == 1 { g.push(gx(zs[0])); }
            g.extend(c0m1_clean(t, ctl, &zs[..t.len() - 5]));
            if p2brk("B4") == 1 { g.push(gx(zs[0])); }
        } else if lv(L1) {
            g.extend(rev(&self.c0m1(t, ctl, zs, c2)));
        } else {
            for &b in &C0M1 {
                g.extend(rev(&inc_long(&t[b..], ctl, &self.dirty, c2)));
            }
        }
        g.extend_from_slice(&pre);
        g
    }
    /// t += classical s mod p (t -= s when sub), 128 lanes at a time.
    fn cl_add(&mut self, p: &mut P, t: &[u32], bits: u64, sub: bool) {
        const K: usize = 128;
        let l = p.allocn(K);
        let (k, c, o) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(zl_n()); site_bump();
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
        for i in 0..zl_n() {
            p.rel(self.zl[i]);
        }
        self.zl = vec![];
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
        self.zl = p.allocn(4); site_bump();
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
        self.zl = vec![];
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
        self.zl = p.allocn(zl_n()); site_bump();
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
        for i in 0..zl_n() {
            p.rel(self.zl[i]);
        }
        self.zl = vec![];
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
    if g.0 == RST {
        return G(RST, m[g.1 as usize], NONE);
    }
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

pub fn build_unfolded() -> Vec<Op> {
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
    a.zl = p.allocn(zl_n()); site_bump();
    let (lam, _low1, g) = a.product(&mut p, &a1[..255], &y, k1.xtop, a1[255], w);
    p.g(&g);
    drop(g);
    for i in 0..zl_n() {
        p.rel(a.zl[i]);
    }
    a.zl = vec![]; // P2_B5: the lanes are released; split_extra must not see them any more
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    // P2_B4: the one-pass clean chain needs no dirty wires, so y can be measured and released BEFORE the sign flip, and its lanes are the 251 clean ones
    let b4a = p2("B4") && lv(L1) && p2_site("B4", 1);
    let mut m1: Vec<u64> = vec![];
    if b4a {
        m1 = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
        for &q0 in &y[..256 - w] {
            p.rel(q0);
        }
    }
    let zc: Vec<u32> = if b4a { p.allocn(251) } else if lv(L1) { p.allocn(3) } else { vec![] };
    let cg = a.cneg_list(&lam, k1.par, false, k1.xtop, &zc);
    p.g(&cg);
    for &q0 in &zc {
        p.rel(q0);
    }
    if !b4a {
        m1 = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
        for &q0 in &y[..256 - w] {
            p.rel(q0);
        }
    }
    emit_finv(&mut p, &fc, &x, &lam, &k1);
    // dy recompute
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(zl_n()); site_bump();
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
    for i in 0..zl_n() {
        p.rel(a.zl[i]);
    }
    a.zl = vec![]; // P2_B5: the lanes are released; split_extra must not see them any more
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
    a.zl = p.allocn(zl_n()); site_bump();
    a.dirty = [&x[..], &lam[..256 - w]].concat();
    let (ndy, _low4, g) = a.product(&mut p, &x, &lam, c, ov, w);
    p.g(&g);
    drop(g);
    for i in 0..zl_n() {
        p.rel(a.zl[i]);
    }
    a.zl = vec![]; // P2_B5: the lanes are released; split_extra must not see them any more
    p.rel(ov);
    let b4c = p2("B4") && lv(L1) && p2_site("B4", 4);
    let mut m2: Vec<u64> = vec![];
    if b4c {
        // P2_B4: lam is measured and released before the negation (the clean chain does not read it)
        m2 = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
        for &q0 in &lam[..256 - w] {
            p.rel(q0);
        }
    }
    a.neg(&mut p, &ndy, c);
    p.rel(c);
    if !b4c {
        m2 = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
        for &q0 in &lam[..256 - w] {
            p.rel(q0);
        }
    }
    // division 2
    let (a2, k2) = emit_f(&mut p, &fc, &x, &ndy);
    a.dirty = [&a2[..255 - w], &ndy[..]].concat();
    a.zl = p.allocn(zl_n()); site_bump();
    let (l2, low5, g) = a.product(&mut p, &ndy, &a2[..255], k2.xtop, a2[255], w);
    p.g(&g);
    let cg = a.cneg_list(&l2, k2.par, true, k2.xtop, &a.zl[..3]);
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
    for i in 0..zl_n() {
        p.rel(a.zl[i]);
    }
    a.zl = vec![]; // P2_B5: the lanes are released; split_extra must not see them any more
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
mod peephole;
mod peephole_hook;
// shadow: three exact post-passes from the main-lane tree (files unchanged from main), run before the folds.
#[allow(dead_code)]
mod affine_simplify;
#[allow(dead_code)]
mod cond_pass;
#[allow(dead_code)]
mod quadratic_simplify;
#[allow(dead_code)]
mod truth_simplify;
fn build_w3_parent() -> Vec<Op> {
    let mut ops = peephole_hook::apply(build_unfolded());
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
    // shadow: the cap cleanup's own three rounds do not reach a fixed point on this stream; three calls do.
    for _ in 0..3 {
        ops = cond_pass::final_cap_cleanup(ops);
    }
    ops = gate_fold::apply(ops); ops = affine_simplify::simplify(ops); ops = truth_simplify::simplify_products(ops); for _ in 0..3 { ops = cond_pass::final_cap_cleanup(ops); }
    let rounds = std::env::var("FOLD2").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(3);
    ops = gate_fold2::apply(ops, rounds); ops = affine_simplify::simplify(ops); ops = truth_simplify::simplify_products(ops); for _ in 0..3 { ops = cond_pass::final_cap_cleanup(ops); }
    if holds && !holds_first {
        // Spare wires for the hold pass: 5 wires above the construction's 785 are zero and untouched, so the pass can
        // keep hold copies on them. An identity X;X pair on each makes them visible to it; the pairs are removed after.
        const BASE: u64 = 785;
        const SPARE: u64 = 5;
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

// ---------------------------------------------------------------------------------------------------------------------
// s18 unit tests: classical simulation of gate lists (incl. AND_FLAG measured-uncompute pairs) against arithmetic references.
// run: target/release/unit    (reads no environment except DEV_P2_*; builds with the same functions the circuit uses)
struct CSim {
    v: Vec<bool>,
    hold: std::collections::HashMap<u32, (u32, u32)>,
    errs: Vec<String>,
}
impl CSim {
    fn new(n: usize) -> Self {
        CSim { v: vec![false; n], hold: Default::default(), errs: vec![] }
    }
    fn run(&mut self, g: &[G]) {
        for &x in g {
            if x.2 != NONE {
                let flagged = x.2 & AND_FLAG != 0;
                let t = x.2 & !AND_FLAG;
                let a = self.v[x.0 as usize] & self.v[x.1 as usize];
                if flagged {
                    if let Some(&(a0, b0)) = self.hold.get(&t) {
                        if (a0, b0) != (x.0, x.1) {
                            self.errs.push(format!("uncompute controls differ on lane {}", t));
                        }
                        if self.v[t as usize] != a {
                            self.errs.push(format!("uncompute: lane {} holds {} but the AND of the controls is {} (phase would be wrong)", t, self.v[t as usize], a));
                        }
                        self.v[t as usize] = false;
                        self.hold.remove(&t);
                    } else {
                        if self.v[t as usize] {
                            self.errs.push(format!("compute onto lane {} that is not |0>", t));
                        }
                        self.v[t as usize] ^= a;
                        self.hold.insert(t, (x.0, x.1));
                    }
                } else {
                    self.v[t as usize] ^= a;
                }
            } else if x.1 != NONE {
                let a = self.v[x.0 as usize];
                self.v[x.1 as usize] ^= a;
            } else {
                self.v[x.0 as usize] ^= true;
            }
        }
        if !self.hold.is_empty() {
            self.errs.push("lane left holding an AND".into());
        }
    }
}
/// returns the number of failures
pub fn p2_unit_tests() -> usize {
    let mut fails = 0usize;
    let mut rng = 0x9E3779B97F4A7C15u64;
    let mut rnd = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    // 1. inc_ctl_clean: exhaustive, r = 3..=4, one literal (both polarities) and two literals (all polarities), lanes 512,514,515 -> sim wires 0..
    //    sim wire map: lanes 512/514/515 -> 20/21/22; reg wires 0..r; lits wires 10, 11
    for r in 3usize..=4 {
        for nl in 1usize..=2 {
            for pol in 0..(1 << nl) {
                for st in 0u32..(1 << (r + nl)) {
                    let reg: Vec<u32> = (0..r as u32).collect();
                    let lits: Vec<Lit> = (0..nl).map(|i| (10 + i as u32, (pol >> i) & 1 == 1)).collect();
                    let mut g = inc_ctl_clean(&reg, &lits);
                    for q0 in g.iter_mut() {
                        let mp = |w: u32| -> u32 {
                            let f = w & AND_FLAG;
                            let b = w & !AND_FLAG;
                            (if b == 512 { 20 } else if b == 514 { 21 } else if b == 515 { 22 } else { b }) | f
                        };
                        *q0 = G(if q0.0 == NONE { NONE } else { mp(q0.0) }, if q0.1 == NONE { NONE } else { mp(q0.1) }, if q0.2 == NONE { NONE } else { mp(q0.2) });
                    }
                    let mut s = CSim::new(24);
                    let mut rv = 0u32;
                    for i in 0..r {
                        s.v[i] = (st >> i) & 1 == 1;
                        rv |= (s.v[i] as u32) << i;
                    }
                    let mut act = true;
                    for i in 0..nl {
                        s.v[10 + i] = (st >> (r + i)) & 1 == 1;
                        act &= s.v[10 + i] == lits[i].1;
                    }
                    let l0: Vec<bool> = s.v.clone();
                    s.run(&g);
                    let mut want = rv + act as u32;
                    want &= (1 << r) - 1;
                    let mut got = 0u32;
                    for i in 0..r {
                        got |= (s.v[i] as u32) << i;
                    }
                    let mut ok = got == want && s.errs.is_empty();
                    for w in 10..24 {
                        if s.v[w] != l0[w] {
                            ok = false;
                        }
                    }
                    if !ok {
                        fails += 1;
                    }
                }
            }
        }
    }
    println!("unit inc_ctl_clean exhaustive r=3..4: fails so far {}", fails);
    // 2. c0m1_clean: reg -= par*(2^32+976) mod 2^n, structured random states (long runs of 0/1 so carries cross every bit), n = 34..=70, anc wires clean
    // 3. conv_clean: exhaustive, n = 2..=4, every addend pattern (0..2 wires at position 0, 0..1 above), every value, add and sub
    {
        let mut cases = 0usize;
        for n in 2usize..=4 {
            for sub in [false, true] {
                for pat in 0u32..(1 << (n + 1)) {
                    let mut adds: Vec<Vec<u32>> = vec![vec![]; n];
                    let mut nw = 0u32;
                    let mut pos_of: Vec<usize> = vec![];
                    for j in 0..2 {
                        if (pat >> j) & 1 == 1 {
                            adds[0].push(10 + nw);
                            pos_of.push(0);
                            nw += 1;
                        }
                    }
                    for k in 1..n {
                        if (pat >> (k + 1)) & 1 == 1 {
                            adds[k].push(10 + nw);
                            pos_of.push(k);
                            nw += 1;
                        }
                    }
                    if adds.iter().all(|a| a.is_empty()) {
                        continue;
                    }
                    let e: Vec<u32> = (0..n as u32).collect();
                    let g0 = conv_clean(&e, &adds, sub);
                    let g: GL = g0
                        .iter()
                        .map(|q0| {
                            let mp = |w: u32| -> u32 {
                                let f = w & AND_FLAG;
                                let b = w & !AND_FLAG;
                                (if b == 512 { 20 } else if b == 514 { 21 } else if b == 515 { 22 } else { b }) | f
                            };
                            G(if q0.0 == NONE { NONE } else { mp(q0.0) }, if q0.1 == NONE { NONE } else { mp(q0.1) }, if q0.2 == NONE { NONE } else { mp(q0.2) })
                        })
                        .collect();
                    for ev in 0u32..(1 << n) {
                        for wv in 0u32..(1 << nw) {
                            let mut s = CSim::new(24);
                            for i in 0..n {
                                s.v[i] = (ev >> i) & 1 == 1;
                            }
                            let mut add = 0u32;
                            for j in 0..nw as usize {
                                s.v[10 + j] = (wv >> j) & 1 == 1;
                                if s.v[10 + j] {
                                    add += 1 << pos_of[j];
                                }
                            }
                            s.run(&g);
                            let m = (1u32 << n) - 1;
                            let want = if sub { ev.wrapping_sub(add) & m } else { (ev + add) & m };
                            let mut got = 0u32;
                            for i in 0..n {
                                got |= (s.v[i] as u32) << i;
                            }
                            let mut ok = got == want && s.errs.is_empty();
                            for j in 0..nw as usize {
                                if s.v[10 + j] != ((wv >> j) & 1 == 1) {
                                    ok = false;
                                }
                            }
                            for w in 20..24 {
                                if s.v[w] {
                                    ok = false;
                                }
                            }
                            cases += 1;
                            if !ok {
                                fails += 1;
                            }
                        }
                    }
                }
            }
        }
        println!("unit conv_clean exhaustive ({} cases): fails total {}", cases, fails);
    }
    // 4. P2_B5: merged / merged_s with the split top (B5 on) against the dirty-chain originals (B5 off) on the same random states
    {
        let mut cases = 0usize;
        let dirty: Vec<u32> = (100..260).collect();
        let zl: Vec<u32> = (70..78).chain(80..86).collect();
        let a3 = S3 { dirty: dirty.clone(), zl: zl.clone() };
        let z = &zl;
        let reg: Vec<u32> = (1..=64).collect();
        let (f, c, wt, cc) = (0u32, 65u32, 66u32, 67u32);
        let terms: Vec<(usize, i32, u32)> = vec![(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])];
        let dterms: Vec<(usize, i32, u32)> = vec![(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])];
        let old_m = a3.merged(&reg, f, &terms, c);
        let old_s = a3.merged_s(&reg, f, &terms, wt, cc, &dterms, c);
        let new_m = a3.merged(&reg, f, &terms, c);
        let new_s = a3.merged_s(&reg, f, &terms, wt, cc, &dterms, c);
        let ccx = |g: &GL| g.iter().filter(|x| x.2 != NONE).count();
        println!("unit merged CCX-gates old {} new {}; merged_s old {} new {}", ccx(&old_m), ccx(&new_m), ccx(&old_s), ccx(&new_s));
        for (gold, gnew, name) in [(&old_m, &new_m, "merged"), (&old_s, &new_s, "merged_s")] {
            for trial in 0..6000 {
                let mut base = CSim::new(300);
                for w in 0..300usize {
                    base.v[w] = rnd() & 1 == 1;
                }
                // clean wires: c, the term and extra lanes
                base.v[c as usize] = false;
                for &q0 in &zl {
                    base.v[q0 as usize] = false;
                }
                // structured reg: carries must reach the top part
                let cut = 40 + (rnd() as usize % 24);
                match trial % 4 {
                    0 => {}
                    1 => for i in 0..64 { base.v[reg[i] as usize] = i >= cut },
                    2 => for i in 0..64 { base.v[reg[i] as usize] = i < cut },
                    _ => for i in 0..64 { base.v[reg[i] as usize] = i < cut || rnd() % 9 == 0 },
                }
                if trial % 3 == 0 {
                    for &w in &dirty[..70] {
                        base.v[w as usize] = trial % 2 == 0;
                    }
                }
                let mut s1 = CSim { v: base.v.clone(), hold: Default::default(), errs: vec![] };
                let mut s2 = CSim { v: base.v.clone(), hold: Default::default(), errs: vec![] };
                s1.run(gold);
                s2.run(gnew);
                cases += 1;
                if s1.v != s2.v || !s2.errs.is_empty() || !s1.errs.is_empty() {
                    fails += 1;
                    if fails < 4 {
                        println!("B5 mismatch {} trial {} errs {:?}", name, trial, s2.errs.first());
                    }
                }
            }
        }
        println!("unit merged/merged_s old vs split ({} states): fails total {}", cases, fails);
    }
    let mut nt = 0usize;
    for n in [34usize, 35, 40, 50, 63, 64, 65, 70, 100, 127, 128, 200, 255, 256] {
        let reg: Vec<u32> = (0..n as u32).collect();
        let par = n as u32;
        let anc: Vec<u32> = (0..(n - 5) as u32).map(|i| par + 1 + i).collect();
        let g = c0m1_clean(&reg, par, &anc);
        for trial in 0..3000 {
            let mut s = CSim::new(2 * n + 2);
            let mut val: Vec<bool> = vec![false; n];
            let cut = rnd() as usize % n;
            match trial % 6 {
                0 => for i in 0..n { val[i] = rnd() & 1 == 1 },
                1 => for i in 0..n { val[i] = i >= cut },
                2 => for i in 0..n { val[i] = i < cut || rnd() % 17 == 0 },
                3 => for i in 0..n { val[i] = (i >= 4 && i < cut) || (i == 32) },
                4 => for i in 0..n { val[i] = !(i >= cut && i < cut + 8) && rnd() % 5 != 0 },
                _ => for i in 0..n { val[i] = if i < 40 { rnd() & 1 == 1 } else { true } },
            }
            let pv = trial & 1 == 0 || trial % 7 == 0;
            for i in 0..n {
                s.v[i] = val[i];
            }
            s.v[par as usize] = pv;
            s.run(&g);
            // reference: val - pv*(2^32 + 976) mod 2^n, bitwise
            let mut want = val.clone();
            if pv {
                let mut borrow = 0i32;
                for i in 0..n {
                    let kb = if i == 32 || [4, 6, 7, 8, 9].contains(&i) { 1 } else { 0 };
                    let d = val[i] as i32 - kb - borrow;
                    want[i] = d & 1 == 1;
                    borrow = if d < 0 { 1 } else { 0 };
                }
            }
            let mut ok = s.errs.is_empty() && s.v[par as usize] == pv;
            for i in 0..n {
                if s.v[i] != want[i] {
                    ok = false;
                }
            }
            for a in &anc {
                if s.v[*a as usize] {
                    ok = false;
                }
            }
            nt += 1;
            if !ok {
                fails += 1;
            }
        }
    }
    println!("unit c0m1_clean ({} structured states over 9 widths): fails total {}", nt, fails);
    fails
}

mod ctx_hook;
#[allow(dead_code)]
mod schn_row;
/// b788: wave-three tree, the stock CTX hold pass, then the Schn cancel pass, then the CTX hold pass again on the donors Schn frees.
pub fn build() -> Vec<Op> {
    let p = ctx_hook::apply(build_w3_parent(), 790);
    let p = schn_row::schn_apply(p);
    ctx_hook::apply(p, 790)
}
