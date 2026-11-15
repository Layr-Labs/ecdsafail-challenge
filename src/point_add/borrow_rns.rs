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
/// lane T (635) switch: the literal adders / comparators uncompute their clean work lanes by measurement (see `Vm::ccx_u`)
pub const LIT_MZ: bool = true;
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
    fn reduce(&self, vm: &mut Vm, t: &[u16]) { self.normalize(vm,&self.te(t),&self.scr,false,matches!(self.l,193|257|281|353|401|449|257|281|353|401|449|521|577|593|641|673|769|773)); }
    fn add_reg(&self, vm: &mut Vm, t: &[u16], y: &[u16], ctl: i32) { vm.zero_add(y, t, self.c0, ctl, self.ext as i32); self.reduce(vm, t); vm.zero_gt(y, t, self.c0, self.f, ctl); }
    /// t += [ctl] (sig ? c1 : c) mod l
    fn add_c(&self, vm: &mut Vm, t: &[u16], c: u32, ctl: i32, sig: i32, c1: u32) { let te = self.te(t); let sk = &self.scr[..self.k]; let top = 2u32 << self.k; let l = self.l;
        let (cm, c1m) = (c + top - l, c1 + top - l);
        if sig<0 || c==c1 { self.add_literal(vm, &te, cm, ctl); } else { self.load_c(vm, cm, ctl, sig, c1m); vm.zero_add(&self.scr, &te, self.c0, -1, -1); self.load_c(vm, cm, ctl, sig, c1m); }
        vm.cx(self.ext, self.f); self.add_literal(vm, &te, l, self.f as i32);
        let (cc, cc1) = ((1u32 << self.k) - c, (1u32 << self.k) - c1);
        if sig<0 || c==c1 { self.ge_literal(vm,t,c,ctl,self.f); } else { self.load_c(vm, cc, ctl, sig, cc1); vm.zero_carry(sk, t, self.c0, self.f, -1); vm.cx(self.scr[self.k], self.f); self.load_c(vm, cc, ctl, sig, cc1); } }
    fn add_c1(&self, vm: &mut Vm, t: &[u16], c: u32, ctl: i32) { self.add_c(vm, t, c, ctl, -1, c); }
    /// run-time constant (only its own bits are loaded); a negated one is the inverse circuit
    fn add_rt(&self, vm: &mut Vm, t: &[u16], c: &Rtk, ctl: i32) { if c.neg { vm.cap_begin(); self.add_rt_abs(vm, t, c, ctl); let g = vm.cap_end(); vm.play(&g, true); } else { self.add_rt_abs(vm, t, c, ctl); } }
    fn add_rt_abs(&self, vm: &mut Vm, t: &[u16], c: &Rtk, ctl: i32) {
        let protected=if ctl<0 {vec![]} else {vec![ctl as u16]};
        let top_unused=c.ids.get(self.k).copied().unwrap_or(1)==1;
        let spare=self.spare_for_literal(t,&protected,top_unused);
        if spare.len()>=self.k {
            self.load_rt(vm,c,ctl);
            self.add_loaded(vm,t,&spare);
            self.load_rt(vm,c,ctl);
            return;
        }
 let sk = &self.scr[..self.k];
        self.load_rt(vm, c, ctl); vm.zero_add(sk, t, self.c0, -1, self.ext as i32); self.load_rt(vm, c, ctl); self.reduce(vm, t); self.load_rt(vm, c, ctl); vm.zero_gt(sk, t, self.c0, self.f, -1); self.load_rt(vm, c, ctl); }
    /// scr ^= table[address] (unary iteration with clean lanes from lk)
    fn lookup(&self, vm: &mut Vm, addr: &[u16], table: &[u32]) { if table.len() <= 16 { emit_lookup_plan(vm, addr, &self.lk, &self.scr, table); } else { let mut anc = self.lk.clone(); self.sel(vm, &mut anc, table, -1, addr, 0); } }
    fn sel(&self, vm: &mut Vm, anc: &mut Vec<u16>, table: &[u32], ctl: i32, bits: &[u16], base: usize) {
        if bits.is_empty() { let v = table[base]; for j in 0..=self.k { if (v >> j) & 1 == 1 { if ctl >= 0 { vm.cx(ctl as u16, self.scr[j]); } else { vm.x(self.scr[j]); } } } return; }
        let b = bits[bits.len() - 1]; let rest = &bits[..bits.len() - 1]; let wt = 1usize << (bits.len() - 1);
        if ctl < 0 { vm.x(b); self.sel(vm, anc, table, b as i32, rest, base); vm.x(b); self.sel(vm, anc, table, b as i32, rest, base + wt); }
        else { let a = anc.pop().expect("lookup: no clean lane"); let c = ctl as u16; vm.ccx(c, b, a); vm.cx(c, a); self.sel(vm, anc, table, a as i32, rest, base); vm.cx(c, a); self.sel(vm, anc, table, a as i32, rest, base + wt); vm.ccx(c, b, a); anc.push(a); } }
    fn add_sel(&self, vm: &mut Vm, t: &[u16], addr: &[u16], table: &[u32]) {
        let spare=self.spare_for_literal(t,addr,true);
        if spare.len()>=self.k {
            assert!(table.iter().all(|&v|v<self.l));
            self.lookup(vm,addr,table);
            self.add_loaded(vm,t,&spare);
            self.lookup(vm,addr,table);
            return;
        }
 let te = self.te(t); let sk = &self.scr[..self.k]; let top = 2u32 << self.k; let l = self.l;
        let tm: Vec<u32> = table.iter().map(|&c| c + top - l).collect();
        self.lookup(vm, addr, &tm); vm.zero_add(&self.scr, &te, self.c0, -1, -1); self.lookup(vm, addr, &tm);
        vm.cx(self.ext, self.f); self.add_literal(vm, &te, l, self.f as i32);
        let tc: Vec<u32> = table.iter().map(|&c| (1u32 << self.k) - c).collect();
        self.lookup(vm, addr, &tc); vm.zero_carry(sk, t, self.c0, self.f, -1); vm.cx(self.scr[self.k], self.f); self.lookup(vm, addr, &tc); }
    /// t <- -t mod l if sigma
    fn cond_neg(&self, vm: &mut Vm, t: &[u16]) {self.cond_neg_on(vm,t,self.sigma);}
    fn cond_neg_on(&self,vm:&mut Vm,t:&[u16],sg:i32){let te=self.te(t); let k = self.k; let s = sg as u16;
        for &q in &te { vm.cx(s, q); } self.add_literal(vm, &te, self.l + 1, sg);
        self.reduce(vm, t);
        for &q in t { vm.x(q); } vm.ccx(t[0], t[1], self.scr[0]); for i in 2..k { vm.ccx(self.scr[i - 2], t[i], self.scr[i - 1]); }
        vm.ccx(s, self.scr[k - 2], self.f);
        for i in (2..k).rev() { vm.ccx(self.scr[i - 2], t[i], self.scr[i - 1]); } vm.ccx(t[0], t[1], self.scr[0]); for &q in t { vm.x(q); } }
    fn dbl(&self, vm: &mut Vm, t: &[u16]) { vm.rot1_up(&self.te(t)); self.reduce(vm, t); vm.cx(t[0], self.f); }
    fn mul_to(&self, vm: &mut Vm, t: &[u16], x: &[u16], y: &[u16]) { for (j,&dst) in t.iter().enumerate(){vm.ccx(x[self.k-1],y[j],dst);}
        for i in (0..self.k-1).rev(){self.dbl(vm,t);self.add_reg(vm,t,y,x[i] as i32);} }
    fn sq_to(&self, vm: &mut Vm, t: &[u16], x: &[u16]) {
        if self.k>=5 && self.l%2==1 {
            for w in self.scr.iter().chain(&self.lk).chain(&self.scrx) {
                assert!(!t.contains(w) && !x.contains(w));
            }
            self.square_rom(vm,t,x,true);
            return;
        }
 let g = self.lk[0]; for i in (0..self.k).rev() { if i < self.k - 1 { self.dbl(vm, t); } vm.cx(x[i], g); self.add_reg(vm, t, x, g as i32); vm.cx(x[i], g); } }
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
        // The original quotient allocation is preserved. Enlarging windows can
        // only reduce the number of canonical summands, so it cannot overflow.
        let mut first=true;
        let mut groups=Vec::<(Vec<u16>,Vec<u16>,Vec<u32>)>::new();
        let mut max_sum=0u64;
        for term in &form.terms {
            let cs=self.consts(term.coef,term.r.len());
            let mut available=self.lk.clone();
            for &wire in &[self.f,self.ext] {
                if !term.r.contains(&wire) && !acc.contains(&wire) && !wide.contains(&wire) && !available.contains(&wire) {
                    available.push(wire);
                }
            }
            let max_width=if true {4.min(available.len()+1)}else{m};
            assert!(m<=4 && max_width>=m);
            let n=cs.len();
            let mut best=vec![usize::MAX;n+1];
            let mut step=vec![0;n];
            best[n]=0;
            for i in (0..n).rev() {
                let maxw=max_width.min(n-i);
                let minw=m.min(n-i);
                for w in minw..=maxw {
                    if best[i+w]==usize::MAX {continue}
                    let table=self.table(&cs[i..i+w]);
                    let plan=cached_lookup(&table);
                    let (rows,ccx)=lutplan::cost(&plan);
                    let lp=rows+ccx;
                    // Baseline full-width Cuccaro add with no carry output is
                    // 6n records and 2n CCX. Count fresh initialization once.
                    let cost=if first && i==0 {lp} else {2*lp+8*acc.len()};
                    let price=cost+best[i+w];
                    if price<best[i] { best[i]=price;step[i]=w; }
                }
            }
            let mut i=0;
            while i<n {
                let w=step[i];assert!(w>0);
                let address=&term.r[i..i+w];
                let table=self.table(&cs[i..i+w]);
                max_sum+=u64::from(*table.iter().max().unwrap());
                groups.push((address.to_vec(),available.clone(),table));
                first=false;i+=w;
            }
        }
        // qlen decisions suffice precisely when max_sum < 2^qlen*l.
        // The same inequality also bounds the integer's k+qlen bits.
        let qmax=max_sum/u64::from(self.l);
        let needed=if qmax==0{0}else{qmax.ilog2() as usize+1};
        assert!(needed<=g_n);
        #[cfg(lyc_record)]
        if needed<g_n {crate::bound(self.k,self.l,g_n,needed,max_sum,&g[needed..]);}
        let g_n=needed;
        acc.truncate(k+g_n);
        wide.truncate(k+g_n);
        for (i,(address,available,table)) in groups.iter().enumerate(){
            if i==0 {
                emit_lookup_plan(vm,address,available,&acc[..k],table);
            } else {
                let mut active=wide.clone();
                active.extend(&acc);active.push(self.c0);
                let pair=lookup_lightcone(address,available,&wide[..k],table,&active);
                vm.cap_begin();play_lookup_prefix(vm,&pair);let forward=vm.cap_end();
                vm.play(&forward,false);vm.zero_add(&wide,&acc,self.c0,-1,-1);vm.play(&forward,true);
            }
        }
        let neg = (2u32 << k) - l;
        for j in (0..g_n).rev() { let te = &acc[j..j + k + 1]; let top = acc[j + k];
            self.normalize(vm,te,&self.scr,true,matches!(self.l,193|197|241|257|263|269|277|281|293|313|337|353|389|401|409|433|449|457|241|257|263|269|277|281|293|313|337|353|389|401|409|433|449|457|521|523|541|547|569|577|593|601|613|617|641|643|673|769|773|809|929)); }
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
        let power=|r:&mut Rns,vm:&mut Vm,t:&[u16]|r.cube_rom(vm,t,&z,true);
        let z3=self.mk(vm,&power);
        self.rev(vm,&|r:&mut Rns,vm:&mut Vm|r.add_reg(vm,h,&z3,-1));
        self.un(vm,&z3,&power); }
    /// the program of one prime: H (zero) <- the site's relation mod l; registers left allocated are cleaned by the caller's reverse pass
    pub fn prog(&mut self, vm: &mut Vm, h: &[u16], p: &Prog) { let f = &p.forms; let c = &p.c; let seven = Cst::Num(7);
        match p.kind {
            0 => {
                // H = v^3 (w^2 - 7) - z^3. H is a fresh relation
                // register. Accumulating into it costs more than initializing it.
                let nu=self.lin(vm,&f[0],None);
                let om=self.lin(vm,&f[1],None);
                let v3=|r:&mut Rns,vm:&mut Vm,t:&[u16]| r.cube_rom(vm,t,&nu,true);
                let w2=|r:&mut Rns,vm:&mut Vm,t:&[u16]| r.square_lut_bias(vm,t,&om,true,r.l-7);
                let a=self.mk(vm,&v3);
                let b=self.mk(vm,&w2);
                self.mul_to(vm,h,&a,&b);
                self.un(vm,&b,&w2);
                self.un(vm,&a,&v3);
                self.cube(vm,h,&f[2],&nu,c[0]);
            }
            1 => { let nu = self.lin(vm, &f[0], None); let y1 = self.lin(vm, &f[1], None); self.acc_aff(vm, &y1, &nu, c[1]);      // D: v ((Y + b v)^2 - 7 v^2) - (s r + a v)^3
                let tf = |r: &mut Rns, vm: &mut Vm, q: &[u16]| { r.sq_to(vm, q, &y1); let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &nu); let v2 = r.mk(vm, &sq);
                    r.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.acc_aff(vm, q, &v2, seven)); r.un(vm, &v2, &sq); };
                let t = self.mk(vm, &tf); self.mul_to(vm, h, &nu, &t); self.un(vm, &t, &tf);
                self.cube(vm, h, &f[2], &nu, c[0]); }
            2 => { let lam = self.lin(vm, &f[0], None); let nu = self.lin(vm, &f[1], None);                 // F: v^2 (c2 L - c3) + s r (v (L^2 - c1) - s r)
                let (c1, c2, c3) = (c[0], c[1], c[2]);
                let t2f = |r: &mut Rns, vm: &mut Vm, t: &[u16]| { r.acc_aff(vm, t, &lam, c2); r.addc(vm, t, c3, true); }; let sq = |r: &mut Rns, vm: &mut Vm, t: &[u16]| r.sq_to(vm, t, &nu);
                let t2 = self.mk(vm, &t2f); let v2 = self.mk(vm, &sq); self.mul_to(vm, h, &v2, &t2); self.un(vm, &v2, &sq); self.un(vm, &t2, &t2f);
                let t1f = |r: &mut Rns, vm: &mut Vm, t: &[u16]| { r.sq_to(vm, t, &lam); r.addc(vm, t, c1, true); };
                let t1 = self.mk(vm, &t1f); let p1 = self.alloc(); self.mul_to(vm, &p1, &nu, &t1); self.un(vm, &t1, &t1f);
                let rho = self.lin(vm, &f[2], None); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.add_reg(vm, &p1, &rho, -1)); self.mul_acc(vm, h, &rho, &p1); }
            3 => { let lam = self.lin(vm, &f[0], None); let mu = self.lin(vm, &f[1], None); let t = self.alloc();     // I: u (L^2 - c1 - u) + c2 L - c3
                self.sq_to(vm, &t, &lam); self.addc(vm, &t, c[0], true); self.rev(vm, &|r: &mut Rns, vm: &mut Vm| r.add_reg(vm, &t, &mu, -1)); self.mul_to(vm, h, &mu, &t);
                self.acc_aff(vm, h, &lam, c[1]); self.addc(vm, h, c[2], true); }
            4 => {
                // (w+b)^2 - (u+a)^3 - 7. The caller's reverse
                // program erases the retained cube and the form scratch.
                let om=self.lin(vm,&f[0],None);
                self.square_lut_bias(vm,h,&om,true,self.l-7);
                let mu=self.lin(vm,&f[1],None);
                let power=self.alloc();
                self.cube_rom(vm,&power,&mu,true);
                self.rev(vm,&|r,vm|r.add_reg(vm,h,&power,-1));
            }
            5 => { let c3 = self.alloc(); vm.cap_begin(); let nu = self.lin(vm, &f[0], None); let gv = vm.cap_end(); vm.play(&gv, false);      // BD: v^3 (2T w + k0)
                self.cube_rom(vm,&c3,&nu,true); vm.play(&gv,true); self.release(&nu);
                let om = self.lin(vm, &f[1], None); self.mul_to(vm, h, &c3, &om); }
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

#[path="lutplan.rs"] mod lutplan;
use std::rc::Rc;
use std::cell::RefCell;
thread_local! { static CACHE:RefCell<HashMap<Vec<u32>,Rc<lutplan::Plan>>>=RefCell::new(HashMap::new()); }
fn cached_lookup(table:&[u32])->Rc<lutplan::Plan>{
    CACHE.with(|cache| {
        let mut cache=cache.borrow_mut();
        if let Some(p)=cache.get(table){return Rc::clone(p);}
        let initial=lutplan::plan(table);
        let shapes=linear_outputs::shapes(table.len().ilog2() as u8);
        let chosen=linear_outputs::choose(table,&shapes,1,initial,12);
        linear_outputs::verify(&chosen,table);
        let p=Rc::new(chosen); cache.insert(table.to_vec(),Rc::clone(&p));p
    })
}
fn emit_lookup_plan(vm:&mut Vm,addr:&[u16],scratch:&[u16],targets:&[u16],table:&[u32]) {
    let p=cached_lookup(table);
    let wire=|i:u8| {if i<lutplan::AUX {addr[i as usize]}
                      else if i<lutplan::OUT {scratch[scratch.len()-1-(i-lutplan::AUX) as usize]}
                      else {targets[(i-lutplan::OUT) as usize]}};
    for &lutplan::Gate(a,b,t) in p.iter(){
        if a!=lutplan::NOT_USED {vm.ccx(wire(a),wire(b),wire(t));}
        else if b!=lutplan::NOT_USED {vm.cx(wire(b),wire(t));}
        else {vm.x(wire(t));}
    }
}

impl Rns {
    // For odd l and canonical x, s=x0 and h=x>>1.  Holding s fixed,
    // replace h by (l-1)/2 - h when s=1, then x^2 = 4 h^2 mod l.
    // This transformation is an involution on *all* k-bit strings.
    fn sq_fold(&self, vm: &mut Vm, x: &[u16]) {
        let parity = x[0];
        let upper = &x[1..];
        let add = (self.l + 1) / 2;
        for &q in upper { vm.cx(parity, q); }
        for j in 0..upper.len() {
            if (add >> j) & 1 != 0 { vm.cx(parity, self.scr[j]); }
        }
        vm.zero_add(&self.scr[..upper.len()], upper, self.c0, -1, -1);
        for j in 0..upper.len() {
            if (add >> j) & 1 != 0 { vm.cx(parity, self.scr[j]); }
        }
    }
    // Decode each upper address once. The seven nonzero two-variable
    // polynomials without constant term depend only on the two low bits.
    fn sq_rom_tree(vm:&mut Vm, hi:&[u16], work:&[u16], low:&[u16;8],
                   target:&[u16], modulus:u32, limit:usize, prefix:usize,
                   selector:Option<u16>, factor:u32, bias:u32) {
        if prefix >= limit { return; }
        if hi.is_empty() {
            let sel=selector.expect("nonempty upper address");
            let values=[0,1,2,3].map(|i|{
                let h=(prefix+i) as u32;
                (factor*h*h+bias)%modulus
            });
            for (j,&t) in target.iter().enumerate() {
                let b=values.map(|y| (y>>j)&1);
                let poly=(b[0]^b[1])|((b[0]^b[2])<<1)|((b[0]^b[1]^b[2]^b[3])<<2);
                if b[0]!=0 { vm.cx(sel,t); }
                if poly!=0 { vm.ccx(sel,low[poly as usize],t); }
            }
            return;
        }
        let (&bit,rest)=hi.split_last().unwrap();
        let one=prefix+(4usize<<rest.len());
        match selector {
            None => {
                vm.x(bit);
                Self::sq_rom_tree(vm,rest,work,low,target,modulus,limit,prefix,Some(bit),factor,bias);
                vm.x(bit);
                Self::sq_rom_tree(vm,rest,work,low,target,modulus,limit,one,Some(bit),factor,bias);
            }
            Some(s) => {
                let (&a,tail)=work.split_first().expect("clean address decode lane");
                vm.ccx(s,bit,a);vm.cx(s,a);
                Self::sq_rom_tree(vm,rest,tail,low,target,modulus,limit,prefix,Some(a),factor,bias);
                vm.cx(s,a);
                Self::sq_rom_tree(vm,rest,tail,low,target,modulus,limit,one,Some(a),factor,bias);
                vm.ccx(s,bit,a);
            }
        }
    }
    fn square_lut_bias(&self, vm:&mut Vm, t:&[u16], x:&[u16], folded:bool,bias:u32) {
        assert!(self.k>=5 && self.l%2==1);
        if folded { self.sq_fold(vm,x); }
        let addr=if folded { &x[1..] } else { x };
        let mut work=self.scr.clone();
        for &q in self.lk.iter().chain(self.scrx.iter()) {
            if !work.contains(&q){work.push(q);}
        }
        let (a,b)=(addr[0],addr[1]);
        let low=[0,a,b,work[0],work[1],work[2],work[3],work[4]];
        vm.cap_begin();
        vm.cx(a,low[3]); vm.cx(b,low[3]);
        vm.ccx(a,b,low[4]);
        for i in [5,6,7] { vm.cx(low[4],low[i]); }
        vm.cx(a,low[5]);vm.cx(b,low[6]);vm.cx(low[3],low[7]);
        let lut=vm.cap_end();
        vm.play(&lut,false);
        Self::sq_rom_tree(vm,&addr[2..],&work[5..],&low,t,self.l,
                          if folded { (self.l as usize+1)/2 } else { self.l as usize },
                          0,None,if folded {4} else {1},bias);
        vm.play(&lut,true);
        if folded { self.sq_fold(vm,x); }
    }

    fn square_rom(&self,vm:&mut Vm,t:&[u16],x:&[u16],folded:bool){
        self.square_lut_bias(vm,t,x,folded,0)
    }

}

impl Rns {
    // Conditional XOR of a compile-time 1, or unconditionally when f=-1.
    fn literal_guard(vm:&mut Vm,f:i32,t:u16) {
        if f<0 {vm.x(t);} else {vm.cx(f as u16,t);}
    }
    // A += f*K mod 2^n. If c_i is the ordinary incoming carry, encode it
    // as h_i=c_i XOR (K_i * f). The output sum at bit i is A_i XOR h_i.
    // h_(i+1)=(A_i XOR K_i)*h_i XOR ((K_i XOR K_(i+1))*f).
    // Work from high bits down on cleanup so each old A_i is still readable.
    fn add_literal(&self,vm:&mut Vm,reg:&[u16],v:u32,f:i32) {Self::add_literal_scratch(vm,reg,v,f,&self.scr); }
    fn add_literal_scratch(vm:&mut Vm,reg:&[u16],v:u32,f:i32,work:&[u16]) {
        let n=reg.len();assert!(n>0 && n<31);
        let k=v&((1u32<<n)-1);if k==0 {return;}
        let j=k.trailing_zeros() as usize;
        if n==j+1 {Self::literal_guard(vm,f,reg[j]);return;}
        let hs=&work[..n-1-j];
        // lane T (635): the work lanes start at 0, so each carry step computes an AND into a clean lane (ccx_c) and its cleanup twin,
        // with the linear terms removed first, uncomputes exactly that AND (ccx_u: measured when emitted)
        let step=|vm:&mut Vm,i:usize,unc:bool|{
            let t=hs[i-j]; let one=k>>i&1!=0; let flip=((k>>i)^(k>>(i+1)))&1!=0;
            if i==j {
                if unc && one!=flip {Self::literal_guard(vm,f,t);}
                if f<0 {vm.cx(reg[i],t);} else if !LIT_MZ {vm.ccx(reg[i],f as u16,t);} else if unc {vm.ccx_u(reg[i],f as u16,t);} else {vm.ccx_c(reg[i],f as u16,t);}
                if !unc && one!=flip {Self::literal_guard(vm,f,t);}
            } else {
                let h=hs[i-j-1];
                if unc { if one {vm.cx(h,t);} if flip {Self::literal_guard(vm,f,t);} }
                if !LIT_MZ {vm.ccx(reg[i],h,t);} else if unc {vm.ccx_u(reg[i],h,t);} else {vm.ccx_c(reg[i],h,t);}
                if !unc { if one {vm.cx(h,t);} if flip {Self::literal_guard(vm,f,t);} }
            }
        };
        for i in j..n-1 {step(vm,i,false);}
        for i in (j+1..n).rev() {
            vm.cx(hs[i-j-1],reg[i]);step(vm,i-1,true);
        }
        Self::literal_guard(vm,f,reg[j]);
    }
    // Toggle flag by [reg >= v] AND its optional guard. Lower zero digits of
    // the threshold cannot affect the comparison. For each other digit,
    // choosing a known carry polarity avoids materializing constant wires.
    fn ge_literal(&self,vm:&mut Vm,reg:&[u16],v:u32,f:i32,flag:u16) {Self::ge_literal_scratch(vm,reg,v,f,flag,&self.scr); }
    fn ge_literal_scratch(vm:&mut Vm,reg:&[u16],v:u32,f:i32,flag:u16,work:&[u16]) {
        let n=reg.len();assert!(n>0 && n<31);
        if v==0 {Self::literal_guard(vm,f,flag);return}
        if v >= 1<<n {return}
        let j=v.trailing_zeros() as usize;
        let last=n-1;
        let use_flag=f<0;
        let carries=&work[..n-j-1];
        let prev=|i:usize| if i==j+1 {reg[j]} else {carries[i-j-2]};
        // For threshold digit 1, true predicate is P & b. For digit 0,
        // it is P | b. Store its complement whenever it eliminates a toggle.
        let mut inv=vec![false;n];
        for i in j+1..n {
            inv[i]=((v>>i)&1)==0 && inv[i-1];
        }
        // Local polarity search. Costs for the chain are independent of
        // actual register values; bits are compiled, never lane inputs.
        let mut trace=vec![[false;2];n];
        let mut dp=[0usize,usize::MAX/4];
        for i in j+1..n {
            let mut next=[usize::MAX/4;2];
            for old in [false,true]{for new in [false,true] {
                let one=(v>>i)&1!=0;
                let lin_b=if one {old} else {!old};
                let offset=(if one {false} else {old})^new;
                let gates=1+usize::from(!one)+usize::from(lin_b)+usize::from(offset);
                let weight=if use_flag && i==last {1} else {2};
                let c=dp[old as usize]+gates*weight;
                if c<next[new as usize]{next[new as usize]=c;trace[i][new as usize]=old;}
            }}
            dp=next;
        }
        if j==last {
            if f<0 {vm.cx(reg[j],flag);}else{vm.ccx(f as u16,reg[j],flag);}return
        }
        inv[last]=!use_flag && dp[1]+1<dp[0];
        for i in (j+1..n).rev(){inv[i-1]=trace[i][inv[i] as usize];}
        assert!(!inv[j]);
        // lane T (635): mode 1 computes a carry into a clean work lane (ccx_c), mode 2 is its twin with the linear terms first (ccx_u), mode 0 targets the flag
        let step=|vm:&mut Vm,i:usize,t:u16,mode:u8|{
            let a=prev(i);let b=reg[i];let one=(v>>i)&1!=0;
            let lin=|vm:&mut Vm|{
                if !one {vm.cx(a,t);}
                if if one {inv[i-1]} else {!inv[i-1]} {vm.cx(b,t);}
                if ((if one {false} else {inv[i-1]})^inv[i]) {vm.x(t);}
            };
            match mode { 1 if LIT_MZ => {vm.ccx_c(a,b,t);lin(vm);} 2 if LIT_MZ => {lin(vm);vm.ccx_u(a,b,t);} _ => {vm.ccx(a,b,t);lin(vm);} }
        };
        let end=if use_flag {last} else {n};
        for i in j+1..end {step(vm,i,carries[i-j-1],1);}
        if use_flag {step(vm,last,flag,0);}
        else {
            vm.ccx(f as u16,carries[last-j-1],flag);
            if inv[last] {vm.cx(f as u16,flag);}
        }
        for i in (j+1..end).rev() {step(vm,i,carries[i-j-1],2);}
    }

pub fn test_literal(&self,vm:&mut Vm,reg:&[u16],v:u32,f:i32,flag:u16,add:bool){
    if add {self.add_literal(vm,reg,v,f);}else {self.ge_literal(vm,reg,v,f,flag);}
}
}

impl Rns {
    // The loaded residue lives in scr[0..k] across the reduction. All
    // temporary carries must be disjoint from it and from the other live data.
    fn spare_for_literal(&self,t:&[u16],address:&[u16],use_scr_top:bool)->Vec<u16>{
        let mut spare=vec![];
        let top=if use_scr_top{Some(self.scr[self.k])}else{None};
        for w in self.lk.iter().chain(&self.scrx).copied().chain(top).chain(self.free.iter().copied()) {
            if w!=self.ext && w!=self.f && (!self.scr.contains(&w) || top==Some(w)) &&
                !t.contains(&w) && !address.contains(&w) && !spare.contains(&w) {
                spare.push(w);
                if spare.len()==self.k {break}
            }
        }
        spare
    }
    fn add_loaded(&self,vm:&mut Vm,t:&[u16],spare:&[u16]){
        let te=self.te(t);
        let a=&self.scr[..self.k];
        vm.zero_add(a,t,self.c0,-1,self.ext as i32);
        self.normalize(vm,&te,spare,false,matches!(self.l,193|257|281|353|401|449|257|281|353|401|449|521|577|593|641|673|769|773));
        vm.zero_gt(a,t,self.c0,self.f,-1);
    }

pub fn test_loaded(&self,vm:&mut Vm,t:&[u16],y:&[u16],new:bool){
    if new {
        assert_eq!(y,&self.scr[..self.k]);let spare=self.spare_for_literal(t,&[],false);
        assert!(spare.len()>=self.k);self.add_loaded(vm,t,&spare);
    } else { self.add_reg(vm,t,y,-1); }
}
}

#[path="linear_outputs.rs"] mod linear_outputs;

impl Rns {
    fn cube_tree(vm:&mut Vm, hi:&[u16], work:&[u16], low:&[u16;8],
                   target:&[u16], modulus:u32, limit:usize, prefix:usize,
                   selector:Option<u16>, factor:u32) {
        if prefix >= limit { return; }
        if hi.is_empty() {
            let sel=selector.expect("nonempty upper address");
            let values=[0,1,2,3].map(|i|{
                let h=(prefix+i) as u32;
                (((u64::from(h)*u64::from(h))%u64::from(modulus))*u64::from(h)*u64::from(factor)%u64::from(modulus)) as u32
            });
            for (j,&t) in target.iter().enumerate() {
                let b=values.map(|y| (y>>j)&1);
                let poly=(b[0]^b[1])|((b[0]^b[2])<<1)|((b[0]^b[1]^b[2]^b[3])<<2);
                if b[0]!=0 { vm.cx(sel,t); }
                if poly!=0 { vm.ccx(sel,low[poly as usize],t); }
            }
            return;
        }
        let (&bit,rest)=hi.split_last().unwrap();
        let one=prefix+(4usize<<rest.len());
        match selector {
            None => {
                vm.x(bit);
                Self::cube_tree(vm,rest,work,low,target,modulus,limit,prefix,Some(bit),factor);
                vm.x(bit);
                Self::cube_tree(vm,rest,work,low,target,modulus,limit,one,Some(bit),factor);
            }
            Some(s) => {
                let (&a,tail)=work.split_first().expect("clean address decode lane");
                vm.ccx(s,bit,a);vm.cx(s,a);
                Self::cube_tree(vm,rest,tail,low,target,modulus,limit,prefix,Some(a),factor);
                vm.cx(s,a);
                Self::cube_tree(vm,rest,tail,low,target,modulus,limit,one,Some(a),factor);
                vm.ccx(s,bit,a);
            }
        }
    }
    fn cube_rom(&self, vm:&mut Vm, t:&[u16], x:&[u16], folded:bool) {
        assert!(self.k>=5 && self.l%2==1);
        if folded { self.sq_fold(vm,x); }
        let addr=if folded { &x[1..] } else { x };
        let mut work=self.scr.clone();
        for &q in self.lk.iter().chain(self.scrx.iter()) {
            if !work.contains(&q){work.push(q);}
        }
        let (a,b)=(addr[0],addr[1]);
        let low=[0,a,b,work[0],work[1],work[2],work[3],work[4]];
        vm.cap_begin();
        vm.cx(a,low[3]); vm.cx(b,low[3]);
        vm.ccx(a,b,low[4]);
        for i in [5,6,7] { vm.cx(low[4],low[i]); }
        vm.cx(a,low[5]);vm.cx(b,low[6]);vm.cx(low[3],low[7]);
        let lut=vm.cap_end();
        vm.play(&lut,false);
        Self::cube_tree(vm,&addr[2..],&work[5..],&low,t,self.l,
                          if folded { (self.l as usize+1)/2 } else { self.l as usize },
                          0,None,if folded {8} else {1});
        vm.play(&lut,true);
        if folded {
            self.sq_fold(vm,x);
            self.cond_neg_on(vm,t,x[0] as i32);
        }
    }
    pub fn check_cube(&self,vm:&mut Vm,t:&[u16],x:&[u16],mode:u8){
        if mode==0 {
            let mut tmp=self.scrx.clone();
            tmp.clear();
            tmp.extend((102..102+self.k as u16).into_iter());
            vm.cap_begin();self.sq_to(vm,&tmp,x);let sq=vm.cap_end();vm.play(&sq,false);
            self.mul_to(vm,t,x,&tmp);vm.play(&sq,true);
        } else { self.cube_rom(vm,t,x,mode==2); }
    }
}

impl Rns {
    // Input 0 <= x < 2*l in k+1 bits. Preserve the quotient either in
    // the high bit itself (long division) or in a separate clean flag.
    fn normalize(&self,vm:&mut Vm,word:&[u16],work:&[u16],store_top:bool,use_sub:bool){
        let k=self.k;
        let top=word[k];
        let low=&word[..k];
        let negative=(2u32<<k)-self.l;
        if use_sub {
            Self::add_literal_scratch(vm,word,negative,-1,work);
            // Underflow iff x<l. The correction may overflow the low
            // k bits; the high bit remains the Boolean underflow flag.
            Self::add_literal_scratch(vm,low,self.l,top as i32,work);
            vm.x(top);
            if !store_top {vm.cx(top,self.f);vm.cx(self.f,top);}
        } else {
            Self::ge_literal_scratch(vm,word,self.l,-1,self.f,work);
            Self::add_literal_scratch(vm,word,negative,self.f as i32,work);
            if store_top {vm.cx(self.f,top);vm.cx(top,self.f);}
        }
    }
    pub fn test_normalize(&self,vm:&mut Vm,word:&[u16],store_top:bool,use_sub:bool) {
        self.normalize(vm,word,&self.scr,store_top,use_sub);
    }

}

// P^-1 B P depends only on gates of P in the backwards cone of the physical
// operands of B. Removed gates commute through B and their adjoints cancel.
// For an NCT computation and a later reversible B, any gate targeting a wire
// outside that cone commutes with B as long as B does not change its controls.
// Therefore retain gates touching *any* live wire, not just target dependencies,
// unless B is known to be computational-basis diagonal on those controls.
fn lookup_lightcone(address:&[u16],scratch:&[u16],targets:&[u16],table:&[u32],active:&[u16])->Vec<[u16;3]> {
    let p=cached_lookup(table);
    let wire=|v:u8| if v==lutplan::NOT_USED {u16::MAX} else if v<lutplan::AUX {address[v as usize]}
        else if v<lutplan::OUT {scratch[scratch.len()-1-(v-lutplan::AUX) as usize]}
        else {targets[(v-lutplan::OUT) as usize]};
    let mut writes=active.to_vec();
    let mut reads=active.to_vec();
    let mut keep=Vec::new();
    for &lutplan::Gate(a,b,t) in p.iter().rev(){
        let (a,b,t)=(wire(a),wire(b),wire(t));
        // A later operation which merely reads the control can commute with
        // this gate. A later operation which writes that control cannot.
        if reads.contains(&t)||writes.contains(&t)||writes.contains(&a)||writes.contains(&b) {
            if !writes.contains(&t){writes.push(t);}
            for q in [a,b] {if q!=u16::MAX&&!reads.contains(&q){reads.push(q);}}
            keep.push([a,b,t]);
        }
    }
    keep.reverse();keep
}
fn play_lookup_prefix(vm:&mut Vm,rows:&[[u16;3]]){
    for &[a,b,t] in rows {
        if a!=u16::MAX {vm.ccx(a,b,t);}else if b!=u16::MAX {vm.cx(b,t);}else{vm.x(t);}
    }
}

impl Rns {pub fn test_square_bias(&self,vm:&mut Vm,t:&[u16],x:&[u16],fold:bool){self.square_lut_bias(vm,t,x,fold,self.l-7);}}
