//! Scan expander: one trace per scan (the generator's calls: gates, adders, captures and replays, run-time constant loads,
//! measurements, a few macros, one event per residue program, calls of the classical layer) -> the scan's records.
use super::cl::{Big, Cl};
use super::rns::{Cst, Form, Prog, Rns, Rtk, Term};
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
/// the three bit regions of the classical layer, kept across scans
pub struct Classical { cl: [Cl; 3] }
impl Classical { pub fn new() -> Self { Classical { cl: [Cl::new(13000, 27000), Cl::new(27000, 30000), Cl::new(30000, 65535)] } } }
/// expand one scan trace; `out` receives the records in order; returns the next free measurement bit
pub fn run(trace: &[u8], bit0: u32, cls: &mut Classical, out: &mut dyn FnMut(Row)) -> u32 {
    let mut rd = Rd { d: trace, p: 0, lists: Vec::new() }; let mut vm = Vm::new(out, bit0);
    let mut blocks: Vec<Option<Block>> = Vec::new(); let mut rns: Option<Rns> = None;
    loop { let op = rd.b();
        match op {
            0 => break,
            1 => { let t = rd.q(); vm.x(t); }
            2 => { let c = rd.q(); let t = rd.q(); vm.cx(c, t); }
            3 => { let a = rd.q(); let b = rd.q(); let t = rd.q(); vm.ccx(a, b, t); }
            4 | 5 => { let a = rd.lanes(); let b = rd.lanes(); let c0 = rd.q(); let ctrl = rd.lane(); let cout = rd.lane(); if op == 4 { vm.add(&a, &b, c0, ctrl, cout); } else { vm.sub(&a, &b, c0, ctrl, cout); } }
            6 | 7 => { let a = rd.lanes(); let b = rd.lanes(); let c0 = rd.q(); let flag = rd.q(); let ctrl = rd.lane(); if op == 6 { vm.carry(&a, &b, c0, flag, ctrl); } else { vm.gt(&a, &b, c0, flag, ctrl); } }
            8 => vm.cap_begin(),
            9 => { let b = vm.cap_end(); blocks.push(Some(b)); }
            10 => { let back = rd.v(); let rev = rd.b() != 0; let id = blocks.len() - 1 - back; let b = blocks[id].take().expect("replay of a finished block"); vm.play(&b, rev); if !rev { blocks[id] = Some(b); } }
            11 => { let li = rd.list(); let ii = rd.list(); let ctl = rd.lane(); let lanes: Vec<u16> = rd.lists[li].iter().map(|&x| x as u16).collect(); vm.krt(&lanes, &rd.lists[ii], ctl); }
            12 => { let q = rd.q(); vm.hmr(q); }
            13 => { let m = rd.v(); let q = rd.q(); vm.zif(m, q); }
            14 => { let m = rd.v(); let a = rd.q(); let b = rd.q(); vm.czif(m, a, b); }
            15 => classical(&mut rd, cls, &mut vm),
            16 => { let r = rd.lanes(); vm.xs(&r); }
            17 => { let ctl = rd.q(); let r = rd.lanes(); vm.fan(ctl, &r); }
            18 => { let ctl = rd.q(); let c = rd.lanes(); let anc = rd.lanes(); vm.cinc_clean(ctl, &c, &anc); }
            19 => { let top = rd.lanes(); let acc = rd.q(); let d = rd.lanes(); vm.mcx_neg(&top, acc, &d); }
            20 => { let k = rd.v(); let c0 = rd.q(); let f = rd.q(); let ext = rd.q(); let sigma = rd.lane(); let scr = rd.lanes(); let scrx = rd.lanes(); let lk = rd.lanes(); let m = rd.v();
                rns = Some(Rns { k, c0, f, ext, sigma, scr, scrx, lk, m, l: 0, free: Vec::new(), gar: HashMap::new(), rtq: VecDeque::new() }); }
            21 => { let kind = rd.v(); let l = rd.v() as u32; let h = rd.lanes(); let free = rd.lanes();
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
