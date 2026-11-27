//! (internal) r4 S-Bp overlay: opt_scan.rs for a scan whose carry-in lane `zc` is never named by a record (scan B' at 632 lanes).
//! Differences from opt_scan.rs: (1) residue programs through borrow_rns (carry-lane-free, as scan B); (2) a top-level add / sub / carry / gt whose
//! c0 is `zc` uses the tree's carry-wire-free forms (`zero_*`), and the HYB form drops its c0 gates (c0 = 0 there by the scan's design);
//! (3) TICK counts the hit tests (census tools only).  With zc = -1 only (1) and (3) apply.
//! Scan expander: one trace per scan (the generator's calls: gates, adders, captures and replays, run-time constant loads,
//! measurements, a few macros, one event per residue program, calls of the classical layer) -> the scan's records.
use super::cl::{Big, Cl};
use super::borrow_rns::{Cst, Form, Prog, Rns, Rtk, Term};
use super::vm::{Block, Vm};
use super::Row;
use std::collections::{HashMap, VecDeque};
struct Rd<'a> { d: &'a [u8], p: usize, lists: Vec<Vec<u32>> }
impl<'a> Rd<'a> {
    #[inline] fn b(&mut self) -> u8 { let x = self.d[self.p]; self.p += 1; x }
    #[inline] fn v(&mut self) -> usize { let mut r = 0usize; let mut sh = 0; loop { let x = self.b(); r |= ((x & 127) as usize) << sh; if x < 128 { return r; } sh += 7; } }
    #[inline] fn lane(&mut self) -> i32 { self.v() as i32 - 1 }
    #[inline] fn q(&mut self) -> u16 { let l = self.lane(); debug_assert!(l >= 0); l as u16 }
    fn big(&mut self) -> Big { let n = self.v(); let b = Big::from_le_bytes(&self.d[self.p..self.p + n]); self.p += n; b }
    /// an interned list: index of its entry
    fn list(&mut self) -> usize { let id = self.v(); if id > 0 { return id - 1; }
        let n = self.v(); let mut prev: i64 = -1; let mut l = Vec::with_capacity(n); for _ in 0..n { let z = self.v() as i64; let d = if z & 1 == 0 { z / 2 } else { -(z + 1) / 2 }; prev = prev + 1 + d; l.push(prev as u32); }
        self.lists.push(l); self.lists.len() - 1 }
    fn lanes(&mut self) -> Vec<u16> { let i = self.list(); self.lists[i].iter().map(|&x| x as u16).collect() }
    fn cst(&mut self) -> Cst { match self.b() { 0 => Cst::None, 1 => Cst::Num(self.v() as u32), _ => Cst::Rt } }
}
const NFORMS: [usize; 11] = [3, 3, 3, 2, 2, 2, 1, 1, 1, 2, 2];
const NCONST: [usize; 11] = [1, 2, 3, 3, 0, 0, 1, 0, 0, 0, 1];
use super::scan::Classical;
/// expand one scan trace; `out` receives the records in order; returns the next free measurement bit
/// `zl`: local lane id that is 0 at every hit-test MCX of this scan (the adders' own clean carry-in lane), or -1: then the borrowed-lane V-chain is used
/// lane T (635) switches: LAD_MZ = the AND ladder that feeds a hit test is uncomputed by measurement (its mirror image after the test);
/// HYB = a plain adder / subtractor (no control, no carry-out) takes the lanes left clean by that uncompute as Gidney carry lanes;
/// CINC_MZ = the clean carry lanes of `cinc_clean` are uncomputed by measurement.  All three are exact given the lanes they use are 0
/// where the scan's own design has them 0 (the ladder accumulators: a Toffoli chain onto them computes the AND only if they are).
thread_local! { pub static TICK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) }; }
/// b += a (carry-in 0, no carry lane named): `Vm::add_h` without its c0 gates
fn add_h0(vm: &mut Vm, a: &[u16], b: &[u16], anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0); let m = anc.len().min(n - 1);
    if m == 0 { vm.zero_add(a, b, 0, -1, -1); return; }
    for i in 0..m { if i > 0 { let c = anc[i - 1]; vm.cx(c, a[i]); vm.cx(c, b[i]); } vm.ccx(a[i], b[i], anc[i]); if i > 0 { vm.cx(anc[i - 1], anc[i]); } }
    vm.add(&a[m..], &b[m..], anc[m - 1], -1, -1);
    for i in (0..m).rev() { if i > 0 { vm.cx(anc[i - 1], anc[i]); } vm.mz(a[i], b[i], anc[i]); if i > 0 { vm.cx(anc[i - 1], a[i]); } vm.cx(a[i], b[i]); } }
/// b -= a: the exact inverse of `add_h0`
fn sub_h0(vm: &mut Vm, a: &[u16], b: &[u16], anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0); let m = anc.len().min(n - 1);
    if m == 0 { vm.zero_sub(a, b, 0, -1, -1); return; }
    for i in 0..m { vm.cx(a[i], b[i]); if i > 0 { vm.cx(anc[i - 1], a[i]); } vm.ccx(a[i], b[i], anc[i]); if i > 0 { vm.cx(anc[i - 1], anc[i]); } }
    vm.sub(&a[m..], &b[m..], anc[m - 1], -1, -1);
    for i in (0..m).rev() { if i > 0 { vm.cx(anc[i - 1], anc[i]); } vm.mz(a[i], b[i], anc[i]); if i > 0 { let c = anc[i - 1]; vm.cx(c, b[i]); vm.cx(c, a[i]); } } }
pub const LAD_MZ: bool = true;
pub const HYB: bool = true;
pub const CINC_MZ: bool = true;
/// an AND ladder: CCX(x0, x1, t0), CCX(t0, x2, t1), ..., each target fresh and used as a control by the next step
fn is_ladder(up: &[(u16, u16, u16)], top: &[u16]) -> bool {
    if up.len() < 2 { return false; }
    for j in 0..up.len() { let (a, b, t) = up[j];
        if up[..j].iter().any(|&(x, y, z)| z == t || x == t || y == t) { return false; }
        if j > 0 { let p = up[j - 1].2; if a != p && b != p { return false; } } }
    top.contains(&up[up.len() - 1].2)
}
/// `allow`: the measurement-based levers may change the number of records (false: the scan's records are those of the original expansion)
pub fn run(trace: &[u8], bit0: u32, cls: &mut Classical, out: &mut dyn FnMut(Row), zl: i32, zc: i32, allow: bool) -> u32 {
    assert!(zl < 0 || zl != zc, "the lane that no record names cannot be the KG zero lane");
    let (lad_mz, hyb, cinc_mz) = (allow && LAD_MZ, allow && HYB, allow && CINC_MZ);
    let mut rd = Rd { d: trace, p: 0, lists: Vec::new() }; let mut vm = Vm::new(out, bit0);
    let mut blocks: Vec<Option<Block>> = Vec::new(); let mut rns: Option<Rns> = None;
    // lanes that the scan's design holds at 0 here (only lanes just uncomputed by `mz`), the CCX run before a hit test, its pending mirror image
    let mut clean: Vec<u16> = Vec::new(); let mut up: Vec<(u16, u16, u16)> = Vec::new(); let mut mirror: Vec<(u16, u16, u16)> = Vec::new();
    loop { let op = rd.b();
        if op != 3 { mirror.clear(); if op != 19 && op != 23 { up.clear(); } }
        match op {
            0 => break,
            1 => { let t = rd.q(); clean.retain(|&l| l != t); vm.x(t); }
            2 => { let c = rd.q(); let t = rd.q(); clean.retain(|&l| l != t); vm.cx(c, t); }
            3 => { let a = rd.q(); let b = rd.q(); let t = rd.q();
                if lad_mz && !vm.capturing() && mirror.last().map_or(false, |&(x, y, z)| z == t && ((x == a && y == b) || (x == b && y == a))) {
                    mirror.pop(); vm.mz(a, b, t); if !clean.contains(&t) { clean.push(t); } }
                else { if !mirror.is_empty() { mirror.clear(); up.clear(); } up.push((a, b, t)); clean.retain(|&l| l != t); vm.ccx(a, b, t); } }
            4 | 5 => { let a = rd.lanes(); let b = rd.lanes(); let c0 = rd.q(); let ctrl = rd.lane(); let cout = rd.lane();
                let anc: Vec<u16> = if hyb && !vm.capturing() && ctrl < 0 && cout < 0 { clean.iter().copied().filter(|l| !a.contains(l) && !b.contains(l) && *l != c0).collect() } else { Vec::new() };
                let z = zc >= 0 && c0 as i32 == zc; assert!(!z || (!a.contains(&c0) && !b.contains(&c0) && ctrl != zc && cout != zc), "zc lane used as data");
                if z { if !anc.is_empty() { if op == 4 { add_h0(&mut vm, &a, &b, &anc); } else { sub_h0(&mut vm, &a, &b, &anc); } }
                    else if op == 4 { vm.zero_add(&a, &b, c0, ctrl, cout); } else if cout < 0 { vm.zero_sub(&a, &b, c0, ctrl, -1); } else { vm.xs(&b); vm.zero_add(&a, &b, c0, ctrl, cout); vm.xs(&b); } }
                else if !anc.is_empty() { if op == 4 { vm.add_h(&a, &b, c0, &anc); } else { vm.sub_h(&a, &b, c0, &anc); } }
                else if op == 4 { vm.add(&a, &b, c0, ctrl, cout); } else { vm.sub(&a, &b, c0, ctrl, cout); }
                clean.retain(|l| !b.contains(l) && *l != c0 && (cout < 0 || *l != cout as u16)); }
            6 | 7 => { let a = rd.lanes(); let b = rd.lanes(); let c0 = rd.q(); let flag = rd.q(); let ctrl = rd.lane(); clean.retain(|&l| l != flag && l != c0 && !b.contains(&l) && !a.contains(&l)); let z = zc >= 0 && c0 as i32 == zc; assert!(!z || (!a.contains(&c0) && !b.contains(&c0) && flag != c0 && ctrl != zc), "zc lane used as data");
                if z { if op == 6 { vm.zero_carry(&a, &b, c0, flag, ctrl); } else { vm.zero_gt(&a, &b, c0, flag, ctrl); } } else if op == 6 { vm.carry(&a, &b, c0, flag, ctrl); } else { vm.gt(&a, &b, c0, flag, ctrl); } }
            8 => { clean.clear(); vm.cap_begin() }
            9 => { clean.clear(); let b = vm.cap_end(); blocks.push(Some(b)); }
            10 => { clean.clear(); let back = rd.v(); let rev = rd.b() != 0; let id = blocks.len() - 1 - back; let b = blocks[id].take().expect("replay of a finished block"); vm.play(&b, rev); if !rev { blocks[id] = Some(b); } }
            11 => { clean.clear(); let li = rd.list(); let ii = rd.list(); let ctl = rd.lane(); let lanes: Vec<u16> = rd.lists[li].iter().map(|&x| x as u16).collect(); vm.krt(&lanes, &rd.lists[ii], ctl); }
            12 => { let q = rd.q(); clean.retain(|&l| l != q); vm.hmr(q); }
            13 => { let m = rd.v(); let q = rd.q(); vm.zif(m, q); }
            14 => { let m = rd.v(); let a = rd.q(); let b = rd.q(); vm.czif(m, a, b); }
            15 => { clean.clear(); classical(&mut rd, cls, &mut vm) }
            16 => { let r = rd.lanes(); clean.retain(|l| !r.contains(l)); vm.xs(&r); }
            17 => { let ctl = rd.q(); let r = rd.lanes(); clean.retain(|l| !r.contains(l)); vm.fan(ctl, &r); }
            18 => { clean.clear(); let ctl = rd.q(); let c = rd.lanes(); let anc = rd.lanes(); if cinc_mz { vm.cinc_clean_mz(ctl, &c, &anc); } else { vm.cinc_clean(ctl, &c, &anc); } }
            19 | 23 => { TICK.with(|t| t.set(t.get() + 1)); let top = rd.lanes(); let acc = rd.q(); let d = rd.lanes(); let kg = zl >= 0 && top.len() >= 8;
                if lad_mz && !vm.capturing() && is_ladder(&up, &top) && !up.iter().any(|&(_, _, t)| t == acc || d.contains(&t) || (kg && t == zl as u16)) { mirror = std::mem::take(&mut up); } else { up.clear(); }
                clean.retain(|&l| l != acc && !top.contains(&l) && !d.contains(&l) && !(kg && l == zl as u16));
                if op == 19 { if kg { vm.mcx_neg_kg(&top, acc, zl as u16); } else { vm.mcx_neg(&top, acc, &d); } } else if kg { vm.mcx_kg(&top, acc, zl as u16); } else { vm.mcx(&top, acc, &d); } }
            20 => { clean.clear(); let k = rd.v(); let c0 = rd.q(); let f = rd.q(); let ext = rd.q(); let sigma = rd.lane(); let scr = rd.lanes(); let scrx = rd.lanes(); let lk = rd.lanes(); let m = rd.v();
                rns = Some(Rns { k, c0, f, ext, sigma, scr, scrx, lk, m, l: 0, free: Vec::new(), gar: HashMap::new(), rtq: VecDeque::new() }); }
            22 => { vm.next_bit = rd.v() as u32; }
            21 => { clean.clear(); let kind = rd.v(); let l = rd.v() as u32; let h = rd.lanes(); let free = rd.lanes();
                let mut forms = Vec::new(); for _ in 0..NFORMS[kind] { let nt = rd.v(); let mut terms = Vec::new(); for _ in 0..nt { let r = rd.lanes(); let coef = rd.v() as u32; let sig = rd.b() != 0; terms.push(Term { r, coef, sig }); }
                    let k0 = rd.cst(); let lazy = rd.b() != 0; forms.push(Form { terms, k0, lazy }); }
                let c: Vec<Cst> = (0..NCONST[kind]).map(|_| rd.cst()).collect(); let raw = rd.lanes(); let sig = rd.b() != 0;
                let nq = rd.v(); let mut rtq = VecDeque::new(); for _ in 0..nq { let n = rd.v(); let mut e = Vec::new(); for _ in 0..n { let li = rd.list(); let neg = rd.b() != 0; e.push(Rtk { ids: rd.lists[li].clone(), neg }); } rtq.push_back(e); }
                let r = rns.as_mut().expect("residue program before its setup"); r.l = l; r.free = free; r.gar.clear(); r.rtq = rtq;
                r.prog(&mut vm, &h, &Prog { kind, forms, c, raw, sig }); }
            _ => panic!("scan trace: event {}", op),
        } }
    assert!(rd.p == trace.len() && !vm.capturing(), "scan trace end");
    vm.next_bit
}
fn classical(rd: &mut Rd, cls: &mut Classical, vm: &mut Vm) {
    let which = rd.b() as usize; let method = rd.b(); let cl = &mut cls.cl[which];
    let bits = |rd: &mut Rd| -> Vec<u16> { let i = rd.list(); rd.lists[i].iter().map(|&x| x as u16).collect() };
    let mut e = |r: Row| vm.rec(r);
    let bit = |x: i32| if x < 0 { u16::MAX } else { x as u16 };
    match method {
        0 => { let m = rd.v(); let v = bits(rd); cl.keep(&mut e, m, &v); }
        1 => { let m = rd.v(); cl.release(&mut e, m); }
        2 => { let a = bits(rd); let b = bits(rd); cl.mulp(&mut e, &a, &b); }
        3 => { let a = bits(rd); let k = rd.big(); cl.mul_small(&mut e, &a, &k); }
        4 => { let a = bits(rd); cl.inverse(&mut e, &a); }
        5 => { let a = bits(rd); let k = rd.big(); cl.mul_constp(&mut e, &a, &k); }
        6 => { let a = bits(rd); cl.negp(&mut e, &a); }
        7 => { let a = bits(rd); let b = bits(rd); cl.addp(&mut e, &a, &b); }
        8 => { let a = bits(rd); let k = rd.big(); cl.add_constp(&mut e, &a, &k); }
        9 => { let a = bits(rd); let n = rd.v(); cl.expansion(&mut e, &a, n); }
        10 => { let n = rd.v(); cl.vec(n); }
        11 => { let t = rd.lane(); let a = rd.lane(); cl.xor_pub(&mut e, bit(t), bit(a)); }
        12 => { let b = bits(rd); let k = rd.big(); let cout = rd.lane(); cl.add_const(&mut e, &b, &k, bit(cout)); }
        13 => { let x = bits(rd); let l = rd.v() as u64; let k = rd.v(); cl.residue(&mut e, &x, l, k); }
        14 => { let v = bits(rd); let l = rd.v() as u64; let k = rd.v(); let bound = rd.big().to_u64(); cl.reduce_small(&mut e, &v, l, k, bound); }
        15 => { let r = bits(rd); let kc = rd.v() as u64; let l = rd.v() as u64; let k = rd.v(); cl.mul_const_small(&mut e, &r, kc, l, k); }
        16 => { let r = bits(rd); let l = rd.v() as u64; let k = rd.v(); let n = rd.v(); cl.expansion_small(&mut e, &r, l, k, n); }
        _ => panic!("scan trace: classical call {}", method),
    }
}
