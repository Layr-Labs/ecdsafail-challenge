//! Residue arithmetic for the scans' loads: one program per small prime l computes a site's relation modulo l in k-lane
//! registers (linear forms of the data registers by table lookups, modular multiplies and squarings), see the scan trace.
//! Lane bookkeeping (free list, garbage lanes of lazily reduced forms) follows the generator exactly.
use super::vm::Vm;
use std::collections::{HashMap, VecDeque};
pub struct Rtk { pub ids: Vec<u32>, pub neg: bool }
pub struct Term { pub r: Vec<u16>, pub coef: u32, pub sig: bool }
#[derive(Clone, Copy, PartialEq)]
pub enum Cst { None, Num(u32), Rt }
pub struct Form { pub terms: Vec<Term>, pub k0: Cst, pub lazy: bool }
pub struct Prog { pub kind: usize, pub forms: Vec<Form>, pub c: Vec<Cst>, pub raw: Vec<u16>, pub sig: bool }
pub struct Rns { pub k: usize, pub c0: u16, pub f: u16, pub ext: u16, pub sigma: i32, pub scr: Vec<u16>, pub scrx: Vec<u16>, pub lk: Vec<u16>, pub m: usize,
    pub l: u32, pub free: Vec<u16>, pub gar: HashMap<u16, Vec<u16>>, pub rtq: VecDeque<Vec<Rtk>> }
type R = Vec<u16>;
impl Rns {
    fn alloc(&mut self) -> R { assert!(self.free.len() >= self.k, "rns: out of lanes"); self.free.drain(0..self.k).collect() }
    fn release(&mut self, r: &[u16]) { if let Some(g) = self.gar.remove(&r[0]) { self.free.splice(0..0, g); } self.free.splice(0..0, r.iter().copied()); }
    fn md(&self, x: i64) -> u32 { x.rem_euclid(self.l as i64) as u32 }
    /// scr ^= [ctl] (sig ? c1 : c)
    fn load_c(&self, vm: &mut Vm, c: u32, ctl: i32, sig: i32, c1: u32) { for j in 0..=self.k { let b = (c >> j) & 1; let b1 = (c1 >> j) & 1;
            if b == 1 { if ctl >= 0 { vm.cx(ctl as u16, self.scr[j]); } else { vm.x(self.scr[j]); } }
            if sig >= 0 && b != b1 { if ctl >= 0 { vm.ccx(ctl as u16, sig as u16, self.scr[j]); } else { vm.cx(sig as u16, self.scr[j]); } } } }
    fn load1(&self, vm: &mut Vm, c: u32) { self.load_c(vm, c, -1, -1, c); }
    fn load_rt(&self, vm: &mut Vm, c: &Rtk, ctl: i32) { let ids: Vec<u32> = (0..=self.k).map(|i| if i < c.ids.len() { c.ids[i] } else { 1 }).collect(); vm.krt(&self.scr, &ids, ctl); }
    fn te(&self, t: &[u16]) -> R { let mut v = t.to_vec(); v.push(self.ext); v }
    /// [t, ext] < 2 l: subtract l if >= l; leaves f = [subtracted]
    fn reduce(&self, vm: &mut Vm, t: &[u16]) { let te = self.te(t); let neg = (2u32 << self.k) - self.l; self.load1(vm, neg); vm.carry(&self.scr, &te, self.c0, self.f, -1); self.load1(vm, neg);
        self.load_c(vm, self.l, self.f as i32, -1, self.l); vm.sub(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, self.l, self.f as i32, -1, self.l); }
    fn add_reg(&self, vm: &mut Vm, t: &[u16], y: &[u16], ctl: i32) { vm.add(y, t, self.c0, ctl, self.ext as i32); self.reduce(vm, t); vm.gt(y, t, self.c0, self.f, ctl); }
    /// t += [ctl] (sig ? c1 : c) mod l
    fn add_c(&self, vm: &mut Vm, t: &[u16], c: u32, ctl: i32, sig: i32, c1: u32) { let te = self.te(t); let sk = &self.scr[..self.k]; let top = 2u32 << self.k; let l = self.l;
        let (cm, c1m) = (c + top - l, c1 + top - l);
        self.load_c(vm, cm, ctl, sig, c1m); vm.add(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, cm, ctl, sig, c1m);
        vm.cx(self.ext, self.f); self.load_c(vm, l, self.f as i32, -1, l); vm.add(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, l, self.f as i32, -1, l);
        let (cc, cc1) = ((1u32 << self.k) - c, (1u32 << self.k) - c1);
        self.load_c(vm, cc, ctl, sig, cc1); vm.carry(sk, t, self.c0, self.f, -1); vm.cx(self.scr[self.k], self.f); self.load_c(vm, cc, ctl, sig, cc1); }
    fn add_c1(&self, vm: &mut Vm, t: &[u16], c: u32, ctl: i32) { self.add_c(vm, t, c, ctl, -1, c); }
    /// run-time constant (only its own bits are loaded); a negated one is the inverse circuit
    fn add_rt(&self, vm: &mut Vm, t: &[u16], c: &Rtk, ctl: i32) { if c.neg { vm.cap_begin(); self.add_rt_abs(vm, t, c, ctl); let g = vm.cap_end(); vm.play(&g, true); } else { self.add_rt_abs(vm, t, c, ctl); } }
    fn add_rt_abs(&self, vm: &mut Vm, t: &[u16], c: &Rtk, ctl: i32) { let sk = &self.scr[..self.k];
        self.load_rt(vm, c, ctl); vm.add(sk, t, self.c0, -1, self.ext as i32); self.load_rt(vm, c, ctl); self.reduce(vm, t); self.load_rt(vm, c, ctl); vm.gt(sk, t, self.c0, self.f, -1); self.load_rt(vm, c, ctl); }
    /// scr ^= table[address] (unary iteration with clean lanes from lk)
    fn lookup(&self, vm: &mut Vm, addr: &[u16], table: &[u32]) { let mut anc = self.lk.clone(); self.sel(vm, &mut anc, table, -1, addr, 0); }
    fn sel(&self, vm: &mut Vm, anc: &mut Vec<u16>, table: &[u32], ctl: i32, bits: &[u16], base: usize) {
        if bits.is_empty() { let v = table[base]; for j in 0..=self.k { if (v >> j) & 1 == 1 { if ctl >= 0 { vm.cx(ctl as u16, self.scr[j]); } else { vm.x(self.scr[j]); } } } return; }
        let b = bits[bits.len() - 1]; let rest = &bits[..bits.len() - 1]; let wt = 1usize << (bits.len() - 1);
        if ctl < 0 { vm.x(b); self.sel(vm, anc, table, b as i32, rest, base); vm.x(b); self.sel(vm, anc, table, b as i32, rest, base + wt); }
        else { let a = anc.pop().expect("lookup: no clean lane"); let c = ctl as u16; vm.ccx(c, b, a); vm.cx(c, a); self.sel(vm, anc, table, a as i32, rest, base); vm.cx(c, a); self.sel(vm, anc, table, a as i32, rest, base + wt); vm.ccx(c, b, a); anc.push(a); } }
    fn add_sel(&self, vm: &mut Vm, t: &[u16], addr: &[u16], table: &[u32]) { let te = self.te(t); let sk = &self.scr[..self.k]; let top = 2u32 << self.k; let l = self.l;
        let tm: Vec<u32> = table.iter().map(|&c| c + top - l).collect();
        self.lookup(vm, addr, &tm); vm.add(&self.scr, &te, self.c0, -1, -1); self.lookup(vm, addr, &tm);
        vm.cx(self.ext, self.f); self.load_c(vm, l, self.f as i32, -1, l); vm.add(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, l, self.f as i32, -1, l);
        let tc: Vec<u32> = table.iter().map(|&c| (1u32 << self.k) - c).collect();
        self.lookup(vm, addr, &tc); vm.carry(sk, t, self.c0, self.f, -1); vm.cx(self.scr[self.k], self.f); self.lookup(vm, addr, &tc); }
    /// t <- -t mod l if sigma
    fn cond_neg(&self, vm: &mut Vm, t: &[u16]) { let te = self.te(t); let sg = self.sigma; let k = self.k; let s = sg as u16;
        for &q in &te { vm.cx(s, q); } self.load_c(vm, self.l + 1, sg, -1, self.l + 1); vm.add(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, self.l + 1, sg, -1, self.l + 1);
        self.reduce(vm, t);
        for &q in t { vm.x(q); } vm.ccx(t[0], t[1], self.scr[0]); for i in 2..k { vm.ccx(self.scr[i - 2], t[i], self.scr[i - 1]); }
        vm.ccx(s, self.scr[k - 2], self.f);
        for i in (2..k).rev() { vm.ccx(self.scr[i - 2], t[i], self.scr[i - 1]); } vm.ccx(t[0], t[1], self.scr[0]); for &q in t { vm.x(q); } }
    fn dbl(&self, vm: &mut Vm, t: &[u16]) { vm.rot1_up(&self.te(t)); self.reduce(vm, t); vm.cx(t[0], self.f); }
    fn mul_to(&self, vm: &mut Vm, t: &[u16], x: &[u16], y: &[u16]) { for i in (0..self.k).rev() { if i < self.k - 1 { self.dbl(vm, t); } self.add_reg(vm, t, y, x[i] as i32); } }
    fn sq_to(&self, vm: &mut Vm, t: &[u16], x: &[u16]) { let g = self.lk[0]; for i in (0..self.k).rev() { if i < self.k - 1 { self.dbl(vm, t); } vm.cx(x[i], g); self.add_reg(vm, t, x, g as i32); vm.cx(x[i], g); } }
    /// t += m x mod l (m a classical constant: k controlled constant adds)
    fn acc_aff(&mut self, vm: &mut Vm, t: &[u16], x: &[u16], m: Cst) { match m {
            Cst::Rt => { let ks = self.rtq.pop_front().expect("run-time residues"); assert!(ks.len() == self.k); for j in 0..self.k { self.add_rt(vm, t, &ks[j], x[j] as i32); } }
            Cst::Num(v) => { let mut c = v % self.l; for j in 0..self.k { self.add_c1(vm, t, c, x[j] as i32); c = (2 * c) % self.l; } }
            Cst::None => panic!("affine constant") } }
    /// z += x y mod l (y doubled in place and restored)
    fn mul_acc(&self, vm: &mut Vm, z: &[u16], x: &[u16], y: &[u16]) { let mut gd = Vec::new();
        for i in 0..self.k { self.add_reg(vm, z, y, x[i] as i32); if i < self.k - 1 { vm.cap_begin(); self.dbl(vm, y); let g = vm.cap_end(); vm.play(&g, false); gd.push(g); } }
        for g in gd.iter().rev() { vm.play(g, true); } }
    fn pop1(&mut self) -> Rtk { let mut v = self.rtq.pop_front().expect("run-time residue"); assert!(v.len() == 1); v.pop().unwrap() }
    fn consts(&self, coef: u32, n: usize) -> Vec<u32> { let mut c = coef % self.l; (0..n).map(|_| { let v = c; c = (2 * c) % self.l; v }).collect() }
    fn table(&self, cs: &[u32]) -> Vec<u32> { (0..1usize << cs.len()).map(|a| { let mut v = 0u32; for j in 0..cs.len() { if (a >> j) & 1 == 1 { v = (v + cs[j]) % self.l; } } v }).collect() }
    fn k0(&mut self, vm: &mut Vm, t: &[u16], k0: Cst) { match k0 { Cst::Rt => { let c = self.pop1(); self.add_rt(vm, t, &c, -1); } Cst::Num(v) => self.add_c1(vm, t, v % self.l, -1), Cst::None => {} } }
    /// lazily reduced residue of a linear form: unreduced accumulation, then one restoring division
    fn lin_lazy(&mut self, vm: &mut Vm, form: &Form) -> R { let (k, m, l) = (self.k, self.m, self.l);
        let any_sig = form.terms.iter().any(|e| e.sig); assert!(form.terms.iter().all(|e| e.sig == any_sig), "lazy lin: mixed sign terms");
        let nn: usize = form.terms.iter().map(|e| (e.r.len() + m - 1) / m).sum(); let mut g_n = 1usize; while (1usize << g_n) < nn { g_n += 1; } assert!(g_n <= self.scrx.len(), "lazy lin: form too long");
        let t = self.alloc(); assert!(self.free.len() >= g_n, "lazy lin: out of lanes"); let g: R = self.free.drain(0..g_n).collect(); self.gar.insert(t[0], g.clone());
        let mut acc = t.clone(); acc.extend(&g); let mut wide: R = self.scr[..k].to_vec(); wide.extend(&self.scrx[..g_n]);
        for e in &form.terms { let cs = self.consts(e.coef, e.r.len()); let mut i = 0;
            while i < e.r.len() { let w = m.min(e.r.len() - i); let addr = &e.r[i..i + w]; let table = self.table(&cs[i..i + w]); self.lookup(vm, addr, &table); vm.add(&wide, &acc, self.c0, -1, -1); self.lookup(vm, addr, &table); i += m; } }
        let neg = (2u32 << k) - l;
        for j in (0..g_n).rev() { let te = &acc[j..j + k + 1]; let top = acc[j + k];
            self.load1(vm, neg); vm.carry(&self.scr, te, self.c0, self.f, -1); self.load1(vm, neg);
            self.load_c(vm, l, self.f as i32, -1, l); vm.sub(&self.scr, te, self.c0, -1, -1); self.load_c(vm, l, self.f as i32, -1, l);
            vm.cx(self.f, top); vm.cx(top, self.f); }
        if any_sig { self.cond_neg(vm, &t); }
        self.k0(vm, &t, form.k0); t }
    /// residue of a linear form into a fresh register, or accumulated into `into`
    fn lin(&mut self, vm: &mut Vm, form: &Form, into: Option<&[u16]>) -> R {
        if into.is_none() && form.lazy { return self.lin_lazy(vm, form); }
        let t: R = match into { Some(x) => x.to_vec(), None => self.alloc() }; let (m, l) = (self.m, self.l);
        let has_sig = form.terms.iter().any(|e| e.sig); let cn = has_sig && m > 1; if cn { assert!(into.is_none(), "sign terms into an accumulator"); }
        for pass in 0..2 { for e in form.terms.iter().filter(|e| e.sig == (pass == 0)) { let signed = e.sig && !cn; let cs = self.consts(e.coef, e.r.len()); let mut i = 0;
                while i < e.r.len() { let w = m.min(e.r.len() - i); let addr = &e.r[i..i + w];
                    if w == 1 || m == 1 { for j in 0..w { let c = cs[i + j]; if c != 0 { if signed { self.add_c(vm, &t, c, addr[j] as i32, self.sigma, (l - c) % l); } else { self.add_c1(vm, &t, c, addr[j] as i32); } } } }
                    else { let table = self.table(&cs[i..i + w]); self.add_sel(vm, &t, addr, &table); }
                    i += m; } }
            if pass == 0 && cn { self.cond_neg(vm, &t); } }
        self.k0(vm, &t, form.k0); t }
    // t (fresh) <- f(t); undo = the inverse circuit, then the register goes back
    fn mk(&mut self, vm: &mut Vm, f: &dyn Fn(&mut Rns, &mut Vm, &[u16])) -> R { let t = self.alloc(); f(self, vm, &t); t }
    fn un(&mut self, vm: &mut Vm, t: &[u16], f: &dyn Fn(&mut Rns, &mut Vm, &[u16])) { vm.cap_begin(); f(self, vm, t); let g = vm.cap_end(); vm.play(&g, true); self.release(t); }
    fn rev(&mut self, vm: &mut Vm, f: &dyn Fn(&mut Rns, &mut Vm)) { vm.cap_begin(); f(self, vm); let g = vm.cap_end(); vm.play(&g, true); }
    fn addc(&mut self, vm: &mut Vm, t: &[u16], v: Cst, negate: bool) { match v { Cst::Rt => { let c = self.pop1(); self.add_rt(vm, t, &c, -1); }
            Cst::Num(x) => { let m = if negate { self.md(-(x as i64)) } else { x % self.l }; self.add_c1(vm, t, m, -1); } Cst::None => panic!("program constant") } }
    fn cube(&mut self, vm: &mut Vm, h: &[u16], sr: &Form, nu: &[u16], a: Cst) { let z = self.lin(vm, sr, None); self.acc_aff(vm, &z, nu, a);            // z = s r + a v
        let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &z); let z2 = self.mk(vm, &sq); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.mul_acc(vm, h, &z, &z2)); self.un(vm, &z2, &sq); }
    /// the program of one prime: H (zero) <- the site's relation mod l; registers left allocated are cleaned by the caller's reverse pass
    pub fn prog(&mut self, vm: &mut Vm, h: &[u16], p: &Prog) { let f = &p.forms; let c = &p.c; let seven = Cst::Num(7);
        match p.kind {
            0 => { let nu = self.lin(vm, &f[0], None); let om = self.lin(vm, &f[1], None);                 // B: v^3 ((w + b)^2 - 7) - (s r + a v)^3
                let t1f = |r: &mut Rns, vm: &mut Vm, t: &[u16]| { r.sq_to(vm, t, &om); r.addc(vm, t, seven, true); };
                let t1 = self.mk(vm, &t1f); let x = self.alloc(); self.mul_to(vm, &x, &nu, &t1); self.un(vm, &t1, &t1f);
                let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &nu); let v2 = self.mk(vm, &sq); self.mul_acc(vm, h, &v2, &x); self.un(vm, &v2, &sq);
                let t1b = self.mk(vm, &t1f); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.mul_to(vm, &x, &nu, &t1b)); self.release(&x); self.un(vm, &t1b, &t1f);
                self.cube(vm, h, &f[2], &nu, c[0]); }
            1 => { let nu = self.lin(vm, &f[0], None); let y1 = self.lin(vm, &f[1], None); self.acc_aff(vm, &y1, &nu, c[1]);      // D: v ((Y + b v)^2 - 7 v^2) - (s r + a v)^3
                let tf = |r: &mut Rns, vm: &mut Vm, q: &[u16]| { r.sq_to(vm, q, &y1); let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &nu); let v2 = r.mk(vm, &sq);
                    r.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.acc_aff(vm, q, &v2, seven)); r.un(vm, &v2, &sq); };
                let t = self.mk(vm, &tf); self.mul_acc(vm, h, &nu, &t); self.un(vm, &t, &tf);
                self.cube(vm, h, &f[2], &nu, c[0]); }
            2 => { let lam = self.lin(vm, &f[0], None); let nu = self.lin(vm, &f[1], None);                 // F: v^2 (c2 L - c3) + s r (v (L^2 - c1) - s r)
                let (c1, c2, c3) = (c[0], c[1], c[2]);
                let t2f = |r: &mut Rns, vm: &mut Vm, t: &[u16]| { r.acc_aff(vm, t, &lam, c2); r.addc(vm, t, c3, true); }; let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &nu);
                let t2 = self.mk(vm, &t2f); let v2 = self.mk(vm, &sq); self.mul_acc(vm, h, &v2, &t2); self.un(vm, &v2, &sq); self.un(vm, &t2, &t2f);
                let t1f = |r: &mut Rns, vm: &mut Vm, t: &[u16]| { r.sq_to(vm, t, &lam); r.addc(vm, t, c1, true); };
                let t1 = self.mk(vm, &t1f); let p1 = self.alloc(); self.mul_to(vm, &p1, &nu, &t1); self.un(vm, &t1, &t1f);
                let rho = self.lin(vm, &f[2], None); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.add_reg(vm, &p1, &rho, -1)); self.mul_acc(vm, h, &rho, &p1); }
            3 => { let lam = self.lin(vm, &f[0], None); let mu = self.lin(vm, &f[1], None); let t = self.alloc();     // I: u (L^2 - c1 - u) + c2 L - c3
                self.sq_to(vm, &t, &lam); self.addc(vm, &t, c[0], true); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.add_reg(vm, &t, &mu, -1)); self.mul_acc(vm, h, &mu, &t);
                self.acc_aff(vm, h, &lam, c[1]); self.addc(vm, h, c[2], true); }
            4 => { let om = self.lin(vm, &f[0], None); let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &om);       // I': (w + b)^2 - (u + a)^3 - 7
                let t = self.mk(vm, &sq); self.add_reg(vm, h, &t, -1); self.un(vm, &t, &sq);
                let mu = self.lin(vm, &f[1], None); let m2 = self.alloc(); self.sq_to(vm, &m2, &mu); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.mul_acc(vm, h, &mu, &m2)); self.addc(vm, h, seven, true); }
            5 => { let c3 = self.alloc(); vm.cap_begin(); let nu = self.lin(vm, &f[0], None); let gv = vm.cap_end(); vm.play(&gv, false);      // BD: v^3 (2T w + k0)
                self.sq_to(vm, h, &nu); self.mul_to(vm, &c3, &nu, h); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.sq_to(vm, h, &nu)); vm.play(&gv, true); self.release(&nu);
                let om = self.lin(vm, &f[1], None); self.mul_acc(vm, h, &c3, &om); }
            6 => { let t = self.alloc(); vm.cap_begin(); self.lin(vm, &f[0], Some(h)); let gl = vm.cap_end(); vm.play(&gl, false);          // RAWSQ: (raw lanes) (x^2 + c)
                self.sq_to(vm, &t, h); if c[0] != Cst::None { self.addc(vm, &t, c[0], false); } vm.play(&gl, true);
                for m in 0..p.raw.len() { self.add_reg(vm, h, &t, p.raw[m] as i32); if m + 1 < p.raw.len() { self.dbl(vm, &t); } }
                if p.sig { self.cond_neg(vm, h); } }
            7 => { let x = self.lin(vm, &f[0], None); self.sq_to(vm, h, &x); }                           // SQ
            8 => { let x = self.lin(vm, &f[0], None); for m in 0..p.raw.len() { self.add_reg(vm, h, &x, p.raw[m] as i32); if m + 1 < p.raw.len() { self.dbl(vm, &x); } } }     // RAWLIN
            9 => { let x = self.lin(vm, &f[0], None); let y = self.lin(vm, &f[1], None); self.mul_to(vm, h, &x, &y); }                // MULLIN
            10 => { let x = self.lin(vm, &f[0], None); let t = self.alloc(); self.sq_to(vm, &t, &x); if c[0] != Cst::None { self.addc(vm, &t, c[0], false); }     // RHOSQ
                let rho = self.lin(vm, &f[1], None); self.mul_acc(vm, h, &rho, &t); }
            _ => panic!("residue program kind") }
        assert!(self.rtq.is_empty(), "unused run-time residues"); }
}
