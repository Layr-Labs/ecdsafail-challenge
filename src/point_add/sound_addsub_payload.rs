//! UNCOMPILED PROPOSAL derived from sound_table_payload.rs (M12 annotated divide).
//! Changes: (1) control rails track (f, W=2g+f) so every row is ONE uncontrolled
//! add-or-subtract; (2) payload tracks (u,w)=(V/2, R+V/2) in biased residues
//! x~ = x + A, A=(2^bits-1-p)/2, so every row is ONE add-or-subtract whose wrap is
//! the adder carry-out and whose halving needs no comparator.
//! Interface, transcript symbols, product bound and 2n round count are unchanged.
//! In-place normalized hddivsteps payload transfer with clean reversible flags.
//!
//! D(a,y)=(a,y/eff(a)), eff(a)=a mod p except zero is mapped to one.
//! Payload y must be canonical. Zero's identity extension is for reversibility,
//! NOT a claim that division by zero or exceptional curve addition is solved.
//! Pair: D(a) followed by D(c)^-1, with one shared clean workspace/frame.
use super::{Build, Gate, Spec,Site};

pub struct RateBoundary {pub gate:usize,pub step:usize,pub f_sign:u16,pub g_sign:u16,pub f_tail:Vec<u16>,pub g_tail:Vec<u16>}
pub struct PayloadProgram {pub sites:Vec<Site>,
    pub rate_checks:Vec<RateBoundary>,
    pub gates: Vec<Gate>,
    pub qubits: usize,
    pub a: Vec<u16>,
    pub c: Vec<u16>,
    pub y: Vec<u16>,
    pub phase_break: usize,
    pub constant_frame: Vec<u16>,
    pub toffolis: u64,
    pub phase_toffolis: u64,
}

/// M8 all-input positive-binary-GCD product bound; never the M5 CSV.
fn bound_widths(spec:&Spec)->Vec<usize>{
 use ruint::aliases::U512;let mut p=U512::ZERO;
 for(i,&v)in spec.prime.iter().enumerate(){if v{p|=U512::from(1)<<i;}}
 let initial=p*(p-U512::from(1));
 (0..=spec.rounds).map(|i|{let v=if i>=512{U512::ZERO}else{initial>>i};let cap=v.min(p).max(U512::from(1));(0..512).rfind(|&j|cap.bit(j)).unwrap()+2}).collect()
}
pub fn validate_rate_bounds(spec:&Spec){
 let actual=Spec::secp256k1();assert_eq!(spec.bits,256);assert_eq!(spec.rounds,512);assert_eq!(spec.prime,actual.prime);
 let widths=bound_widths(spec);let csv=include_str!("m19_widths.csv");
 let mut count=0;for(i,line)in csv.lines().skip(1).enumerate(){let f:Vec<_>=line.split(',').collect();assert_eq!(f[0].parse::<usize>().unwrap(),i);assert_eq!(f[3].parse::<usize>().unwrap(),widths[i]);count+=1;}
 assert_eq!(count,513);println!("PRODUCT_BOUND_GATE_PASS exact_rows={count} rounds=512 all_inputs=true");
}

#[derive(Clone)]
struct Work {
    f: Vec<u16>, g: Vec<u16>, v: Vec<u16>, r: Vec<u16>, delta: Vec<u16>,
    decoder:Vec<u16>, history: Vec<u16>, flag: u16, init_ge: u16, zero: u16,
}
impl Build {
    /// Exact multi-controlled X with clean borrowed *zero* mask ladder.
    /// No controls, carry or lower bits are omitted. The mask returns to zero.
    fn payload_mcx(&mut self, controls: &[u16], target: u16) {
        match controls.len() {
            0 => self.x(target),
            1 => self.cx(controls[0], target),
            2 => self.ccx(controls[0], controls[1], target),
            n => {
                assert!(n-2 <= self.mask.len());
                let anc = self.mask[..n-2].to_vec();
                assert!(controls.iter().all(|q| *q != target && !anc.contains(q)));
                self.ccx(controls[0], controls[1], anc[0]);
                for i in 2..n-1 { self.ccx(anc[i-2], controls[i], anc[i-1]); }
                self.ccx(anc[n-3], controls[n-1], target);
                for i in (2..n-1).rev() { self.ccx(anc[i-2], controls[i], anc[i-1]); }
                self.ccx(controls[0], controls[1], anc[0]);
            }
        }
    }
    fn payload_zero_toggle(&mut self, a: &[u16], target: u16, control: Option<u16>) {
        for &q in a { self.x(q); }
        let mut controls = a.to_vec();
        if let Some(c) = control { controls.push(c); }
        self.payload_mcx(&controls, target);
        for &q in a { self.x(q); }
    }
    /// Exact Schrottenloher Fig1 permutation. All64 inputs reversible; for
    /// each pair (e,c) with c=>e, output q[5] is PROVED zero (all27 states).
    fn pack_three(&mut self,q:&[u16]){
        assert_eq!(q.len(),6);for i in 0..6{assert!(!q[i+1..].contains(&q[i]));}
        self.cx(q[1],q[0]);self.cx(q[3],q[2]);self.cx(q[5],q[4]);
        self.cx(q[0],q[2]);self.cx(q[5],q[3]);self.x(q[4]);
        self.ccx(q[1],q[3],q[5]);self.cx(q[1],q[4]);self.x(q[2]);
        self.ccx(q[3],q[4],q[5]);self.ccx(q[4],q[5],q[1]);
        self.ccx(q[2],q[5],q[0]);self.ccx(q[0],q[1],q[5]);
    }
    /// Michelle's exact half-carry interpretation: 32-bit borrow chunks.
    /// Every inter-chunk borrow is retained in mask[i-1], never guessed/dropped.
    /// Full n-bit unsigned comparison, with ALL leading/guard bits included.
    /// Inputs must be nonnegative at the modular callers (as in M5).
    fn payload_ge_toggle(&mut self, a: &[u16], constant: &[bool], flag: u16) {
        let n=a.len(); assert!(constant.len()<=n && n<=self.mask.len());
        let m=self.mask[..n].to_vec();
        assert!(a.iter().all(|q|!m.contains(q)) && !m.contains(&flag));
        let outer=self.gates.len();let start=outer;
        for chunk in (0..n).step_by(32) {
            for i in chunk..(chunk+32).min(n) {
                let k=constant.get(i).copied().unwrap_or(false);
                if i==0 {
                    if k {self.x(m[i]);self.cx(a[i],m[i]);}
                } else if k {
                    // borrow' = NOT(a_i AND NOT borrow).
                    self.x(m[i-1]);self.ccx(a[i],m[i-1],m[i]);
                    self.x(m[i-1]);self.x(m[i]);
                } else {
                    // borrow' = NOT a_i AND borrow.
                    self.x(a[i]);self.ccx(a[i],m[i-1],m[i]);self.x(a[i]);
                }
            }
        }
        let end=self.gates.len();self.x(flag);self.cx(m[n-1],flag);
        for i in (start..end).rev(){self.gates.push(self.gates[i]);}
        self.sites.push(Site{start:outer,end:self.gates.len(),cleanup:false,flag,kind:0,width:n});
    }
    /// flag ^= control & [b<a], exact n-bit borrow propagation. Full input
    /// words and each boundary borrow remain available for reversible cleanup.
    fn payload_lt_toggle(&mut self, control:u16,a:&[u16],b:&[u16],flag:u16) {
        let n=a.len();assert_eq!(n,b.len());assert!(n<=self.mask.len());
        let m=self.mask[..n].to_vec();
        assert!(a.iter().chain(b).all(|q|!m.contains(q)));
        assert!(!m.contains(&control) && !m.contains(&flag));
        let outer=self.gates.len();let start=outer;
        for chunk in (0..n).step_by(32) {
            for i in chunk..(chunk+32).min(n) {
                if i==0 {
                    self.x(b[i]);self.ccx(a[i],b[i],m[i]);self.x(b[i]);
                }else{
                    // majority(a_i,NOT b_i,borrow)
                    // = a_i XOR ((a_i XOR NOT b_i) AND (a_i XOR borrow)).
                    self.x(b[i]);self.cx(a[i],b[i]);self.cx(a[i],m[i-1]);
                    self.ccx(b[i],m[i-1],m[i]);self.cx(a[i],m[i]);
                    self.cx(a[i],m[i-1]);self.cx(a[i],b[i]);self.x(b[i]);
                }
            }
        }
        let end=self.gates.len();self.ccx(control,m[n-1],flag);
        for i in (start..end).rev(){self.gates.push(self.gates[i]);}
        self.sites.push(Site{start:outer,end:self.gates.len(),cleanup:false,flag,kind:1,width:n});
    }
    /// Canonical a -> (-1)^c*a mod p. Retained sign erased from output exactly.
    fn payload_neg(&mut self, c: u16, a: &[u16], flag: u16) {
        self.cneg(c, a);
        self.cx(a[a.len()-1], flag);
        self.prime_add(a, Some(flag), false);
        // sign before correction = c & [canonical output != 0].
        self.cx(c, flag);
        self.payload_zero_toggle(a, flag, Some(c));
    }
    /// Canonical b -> b+c*a mod p; erase reduction iff output < c*a.
    fn payload_add(&mut self, c: u16, a: &[u16], b: &[u16], flag: u16) {
        self.gidney_cadd(c, a, b);
        let p = self.prime.clone();
        self.payload_ge_toggle(b, &p, flag);
        self.prime_add(b, Some(flag), true);
        // For canonical output b and unchanged a: wrap iff c AND b<a.
        // No masked source or two full destructive add/undo passes are needed.
        self.payload_lt_toggle(c,a,b,flag);self.sites.last_mut().unwrap().cleanup=true;
    }
    /// Canonical a -> a/2 mod p. Old odd bit = [new a >= (p+1)/2].
    fn payload_half(&mut self, a: &[u16], threshold: &[bool], flag: u16) {
        self.cx(a[0], flag);
        self.prime_add(a, Some(flag), false);
        self.rotate_right_zero(a);
        self.payload_ge_toggle(a, threshold, flag);self.sites.last_mut().unwrap().cleanup=true;
    }
    /// Fused signed add/halve kernel, for legal divstep symbols c implies e.
    /// Normalize the signed combined numerator once, not a separate canonical
    /// negate then canonical add. Half remains exact with its full comparison.
    fn payload_fused_step(&mut self,c:u16,e:u16,a:&[u16],b:&[u16],threshold:&[bool],flag:u16){
        self.signed_cadd(c,e,a,b);
        self.cx(b[b.len()-1],flag);self.prime_add(b,Some(flag),false);
        // For c=1,e=1: a-b<0 iff corrected result>a. For c=0 sign=0.
        self.payload_lt_toggle(c,b,a,flag);
        let prime=self.prime.clone();self.payload_ge_toggle(b,&prime,flag);
        self.prime_add(b,Some(flag),true);
        // Positive wrap is possible only in the e=1,c=0 branch.
        self.cx(c,e);self.payload_lt_toggle(e,a,b,flag);self.cx(c,e);
        self.payload_half(b,threshold,flag);
    }
    /// flag ^= [b >= a], exact n-bit borrow propagation (same cells as
    /// payload_lt_toggle; centre is X(flag),CX(last borrow,flag)). Site kind 2:
    /// its phase form is Neg, Z(last borrow), exactly like the constant GE site.
    fn payload_ge_word_toggle(&mut self,a:&[u16],b:&[u16],flag:u16) {
        let n=a.len();assert_eq!(n,b.len());assert!(n<=self.mask.len());
        let m=self.mask[..n].to_vec();
        assert!(a.iter().chain(b).all(|q|!m.contains(q)));assert!(!m.contains(&flag)&&!a.contains(&flag)&&!b.contains(&flag));
        let outer=self.gates.len();let start=outer;
        for i in 0..n {
            if i==0 {
                self.x(b[i]);self.ccx(a[i],b[i],m[i]);self.x(b[i]);
            }else{
                self.x(b[i]);self.cx(a[i],b[i]);self.cx(a[i],m[i-1]);
                self.ccx(b[i],m[i-1],m[i]);self.cx(a[i],m[i]);
                self.cx(a[i],m[i-1]);self.cx(a[i],b[i]);self.x(b[i]);
            }
        }
        let end=self.gates.len();self.x(flag);self.cx(m[n-1],flag);
        for i in (start..end).rev(){self.gates.push(self.gates[i]);}
        self.sites.push(Site{start:outer,end:self.gates.len(),cleanup:false,flag,kind:2,width:n});
    }
    /// Biased residues x~=x+A in [A,A+p). w <- w+u (e=0) or w-u (e=1) mod p.
    /// w~ + (u~ XOR e..e) + 1 = (w+u-p or w-u) + 2^bits, so the carry-out IS the
    /// exact reduction decision in both branches; h=NOT carry lives in the clean
    /// guard w[bits]. Re-bias: +A (h=0) or +A+p = -A-1 mod 2^bits (h=1).
    /// Erase: h=[w~ >= u~ XOR e..e] for every canonical input, then guard is zero.
    fn biased_addsub(&mut self,e:u16,u:&[u16],w:&[u16]) {
        let bits=self.prime.len();let ab=bias_bits(&self.prime);let h=w[bits];
        assert!(u.len()>bits&&w.len()>bits);
        for i in 0..bits{self.cx(e,u[i]);}
        self.x(self.carry);self.gidney_add(&u[..bits+1],&w[..bits+1]);self.x(self.carry);
        self.x(h);self.conj_add_const(h,&w[..bits],&ab);
        self.payload_ge_word_toggle(&u[..bits],&w[..bits],h);self.sites.last_mut().unwrap().cleanup=true;
        for i in 0..bits{self.cx(e,u[i]);}
    }
    /// w~ <- (w/2 mod p)~. Old parity k; (w~ + A + k p)/2. Since (p+1)/2+A=2^(bits-1),
    /// k is EXACTLY the new top bit: erased by one CNOT, no comparator.
    fn biased_half(&mut self,w:&[u16]) {
        let bits=self.prime.len();let ab=bias_bits(&self.prime);let k=w[bits];
        self.cx(w[0],k);if ab[0]{self.x(k);}
        self.conj_add_const(k,&w[..bits],&ab);
        self.cx(k,w[0]);self.cx(w[0],k);
        self.rotate_right_zero(&w[..bits]);
    }
    /// Biased w~ (value w) -> plain 2w mod p. [2w>=p] is the top bit of w~;
    /// after the rotation it is bit 0, and 2w mod p = rot - (1-bit0)*2A. No flag.
    fn biased_exit_double(&mut self,w:&[u16]) {
        let bits=self.prime.len();let ab=bias_bits(&self.prime);
        self.rotate_left(&w[..bits]);
        self.x(w[0]);self.constant(&w[1..bits],&ab[..bits-1],Some(w[0]),true);self.x(w[0]);
    }

}
/// A=(2^bits-1-p)/2: p is odd, so this is the bitwise complement of p shifted down.
fn bias_bits(prime:&[bool])->Vec<bool>{let n=prime.len();(0..n).map(|i|i+1<n&&!prime[i+1]).collect()}
/// W=2g+f<=3*cap needs one more bit than the certified f/g width (same theorem).
fn wide(widths:&[usize],i:usize,n:usize)->usize{(widths[i]+1).min(n)}
fn half_threshold(prime: &[bool]) -> Vec<bool> {
    let mut bits = prime.to_vec(); bits.push(false);
    let mut carry = true;
    for b in &mut bits { let old = *b; *b ^= carry; carry &= old; }
    assert!(!carry);
    bits.remove(0); bits
}
fn constants(b: &mut Build, w: &Work, undo: bool) {
    let start = b.gates.len();
    let p = b.prime.clone();
    for (i, set) in p.into_iter().enumerate() { if set { b.x(w.f[i]); } }
    if undo { b.reverse_from(start); }
}
/// Fixed-frame separated D core. u=p at entry/exit; g and all others zero.
fn divide_core(b:&mut Build,spec:&Spec,w:&Work,input:&[u16],_rate:bool)->Vec<RateBoundary>{
 let bits=spec.bits;let n=bits+2;let widths=bound_widths(spec);let mut checks=Vec::new();
 let ab=bias_bits(&spec.prime);let init_start=b.gates.len();
 assert_eq!(&w.g[..bits],input,"control g aliases the current divisor port");
 b.payload_ge_toggle(&w.g,&spec.prime,w.init_ge);b.prime_add(&w.g,Some(w.init_ge),true);
 b.payload_zero_toggle(&w.g,w.zero,None);b.cx(w.zero,w.g[0]);
 // W=2g+f. g<p<2^bits, so the top guard is zero and the rotation is 2g; W<3*2^bits<2^n.
 b.rotate_left(&w.g);b.gidney_add(&w.f,&w.g);let init_end=b.gates.len();
 let mut rails=Vec::new();let mut encodings=Vec::new();
 for i in 0..spec.rounds{
  let start=b.gates.len();let ww=wide(&widths,i,n);let old=if i==0{n}else{wide(&widths,i-1,n)};assert!(ww<=old&&ww>=3);
  if ww<old{checks.push(RateBoundary{gate:start,step:i,f_sign:w.f[ww-1],g_sign:w.g[ww-1],f_tail:w.f[ww..old].to_vec(),g_tail:w.g[ww..old].to_vec()});}
  // f,g<=cap_i (exact product theorem) => W=2g+f<2^ww and f<2^(ww-2): tails CERTIFIED ZERO.
  let(e,c)=(w.history[2*i],w.history[2*i+1]);let(f,g)=(&w.f[..ww],&w.g[..ww]);
  // f and W are odd; W-f=2g with no borrow out of bit0, so [g odd]=W_1 XOR f_1.
  b.cx(g[1],e);b.cx(f[1],e);
  // W <- W+f (e=0) or W-f=W+~f+1 (e=1): one uncontrolled adder, result 2*(g+f) or 2*g.
  for &q in f{b.cx(e,q);}b.cx(e,b.carry);b.gidney_add(f,g);b.cx(e,b.carry);for &q in f{b.cx(e,q);}
  b.rotate_right_zero(g);
  // Now W=g+f (e=0, never <f) or W=g (e=1): the M12 symbol c=e&[g<f] is e&[W<f].
  b.payload_lt_toggle(e,f,g,c);b.cswap(c,f,g);
  rails.push((start,b.gates.len()));
  if i%3==2{let a=b.gates.len();b.pack_three(&w.history[2*(i-2)..2*(i+1)]);encodings.push((i,a,b.gates.len()));}
 }
 // At step512, logical f=1, g=0, hence W=1, for ALL admissible inputs.
 b.x(w.f[0]); // full reserved u bank is now clean: (u,w)=(V/2,R+V/2)=(0,y).
 for i in 0..bits{if ab[i]{b.x(w.v[i]);}}
 b.constant(&w.r[..bits],&ab,None,false);
 for group in 0..spec.rounds/3{
  let base=6*group;for j in 0..5{b.cx(w.history[base+j],w.decoder[j]);}
  let a=b.gates.len();b.pack_three(&w.decoder);b.reverse_from(a);
  for j in 0..3{
   let(e,c)=(w.decoder[2*j],w.decoder[2*j+1]);
   b.biased_addsub(e,&w.v,&w.r);b.biased_half(&w.r);b.cswap(c,&w.v[..bits],&w.r[..bits]);
  }
  b.pack_three(&w.decoder);for j in 0..5{b.cx(w.history[base+j],w.decoder[j]);}
 }
 for i in (spec.rounds/3)*3..spec.rounds{
  let(e,c)=(w.history[2*i],w.history[2*i+1]);
  b.biased_addsub(e,&w.v,&w.r);b.biased_half(&w.r);b.cswap(c,&w.v[..bits],&w.r[..bits]);
 }
 // (V,R)=(y/a,0) means u~==w~ bit for bit: clear the u bank, then y port <- 2w mod p.
 for i in 0..bits{b.cx(w.r[i],w.v[i]);}
 b.biased_exit_double(&w.r);b.x(w.f[0]);
 for(i,(a,z))in rails.into_iter().enumerate().rev(){
  if i%3==2{let(step,x,y)=encodings.pop().unwrap();assert_eq!(step,i);b.append_reverse(x,y);}
  b.append_reverse(a,z);
 }
 b.append_reverse(init_start,init_end);checks
}

pub fn generate(spec:&Spec,pair:bool)->PayloadProgram {generate_inner(spec,pair,true)}
pub fn generate_rate(spec:&Spec,pair:bool)->PayloadProgram {validate_rate_bounds(spec);generate_inner(spec,pair,true)}
fn generate_inner(spec: &Spec, pair: bool, rate:bool) -> PayloadProgram {
    assert!(spec.bits>=2 && spec.prime.len()==spec.bits && spec.prime[0] && spec.prime[spec.bits-1]);
    assert_eq!(spec.rounds,2*spec.bits,"requires the proven 2n positive-binary-GCD bound");
    let n=spec.bits+2;
    let mut b=Build {sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:spec.prime.clone()};
    let a=b.alloc(spec.bits);
    let c=if pair {b.alloc(spec.bits)} else {vec![]};
    let y=b.alloc(spec.bits);
    let f=b.alloc(n); let mut g=a.clone();g.extend(b.alloc(2));let v=f.clone();
    let mut r=y.clone(); r.extend(b.alloc(1)); // one guard: reduction/parity flag
    let delta=vec![];
    b.mask=b.alloc(n.max(12)); b.carry=b.bit();
    let decoder=b.alloc(6);let flag=r[spec.bits];let init_ge=b.bit();let zero=b.bit();
    let widths=bound_widths(spec);let mut free=Vec::new();let mut history=Vec::new();let mut old=n;
    for i in 0..spec.rounds{
      let width=wide(&widths,i,n);for &q in &g[width..old]{free.push(q);}old=width;
      for _ in 0..2{history.push(if let Some(q)=free.pop(){q}else{b.bit()});}
      if i%3==2{free.push(*history.last().unwrap());}
    }
    println!("SEPARATED_LAYOUT rounds={} Q={} stored_tape={} remaining_free={}",spec.rounds,b.next,2*spec.rounds-spec.rounds/3,free.len());
    let w=Work{f,g,v,r,delta,history,decoder,flag,init_ge,zero};
    let frame:Vec<u16>=spec.prime.iter().enumerate().filter_map(|(i,&set)|if set{Some(w.f[i])}else{None}).collect();
    constants(&mut b,&w,false);
    let rate_checks=divide_core(&mut b,spec,&w,&a,rate);
    let phase_break=b.gates.len();
    let phase_toffolis=b.gates.iter().filter(|x|x.kind==13).count() as u64;
    if pair {
        let start=b.gates.len();
        // Rebind port-aliased g AND every tape wire leased from its tails.
        // No gate swap/erasure: this is a compile-time module-port mapping.
        let mut wc=w.clone();let map=|q:u16|w.g[..spec.bits].iter().position(|&z|z==q).map(|i|c[i]).unwrap_or(q);
        wc.g=w.g.iter().copied().map(map).collect();wc.history=w.history.iter().copied().map(map).collect();
        divide_core(&mut b,spec,&wc,&c,rate);
        // Multiplication is the exact gate inverse of a clean division core.
        // Scratch, flags and constant frame are shared, NOT two live inverse
        // outputs or an invalid cancellation of different divisors.
        b.reverse_from(start);
    }
    constants(&mut b,&w,true);
    let toffolis=b.gates.iter().filter(|x|x.kind==13).count() as u64;
    for &gate in &b.gates {gate.op().validate();}
    PayloadProgram {sites:b.sites,rate_checks,gates:b.gates,qubits:b.next,a,c,y,phase_break,constant_frame:frame,toffolis,phase_toffolis}
}

#[cfg(test)]
mod tests {
    use super::*;
    fn apply(gates:&[Gate],q:&mut[bool],reverse:bool) {
        let one=|x:Gate,q:&mut[bool]| {let(a,b,t)=(x.a as usize,x.b as usize,x.t as usize);
            match x.kind {6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],10=>q.swap(a,t),_=>panic!()}};
        if reverse {for &g in gates.iter().rev(){one(g,q);}}else{for &g in gates{one(g,q);}}
    }
    fn put(q:&mut[bool],r:&[u16],x:usize) {for(i,&j)in r.iter().enumerate(){q[j as usize]=x>>i&1!=0;}}
    fn get(q:&[bool],r:&[u16])->usize {r.iter().enumerate().map(|(i,&j)|(q[j as usize] as usize)<<i).sum()}
    fn spec(p:usize)->Spec {let bits=usize::BITS as usize-p.leading_zeros()as usize;Spec {bits,prime:(0..bits).map(|i|p>>i&1!=0).collect(),rounds:2*bits}}
    fn eff(a:usize,p:usize)->usize {if a%p==0{1}else{a%p}}
    fn inv(a:usize,p:usize)->usize {(1..p).find(|&x|a*x%p==1).unwrap()}
    #[test]
    fn clean_modular_primitives_all_small() {
        for p in [3usize,5,7,11,13,17,19,23,29,31] {
            let spec=spec(p);let n=spec.bits+2;
            for op in 0..3 {
                let mut b=Build {sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:spec.prime.clone()};
                let c=b.bit();let a=b.alloc(n);let dst=b.alloc(n);let flag=b.bit();
                b.mask=b.alloc(n.max(12));b.carry=b.bit();
                match op {0=>b.payload_neg(c,&dst,flag),1=>b.payload_add(c,&a,&dst,flag),2=>b.payload_half(&dst,&half_threshold(&spec.prime),flag),_=>panic!()}
                for control in 0..2 {for x in 0..p {for y in 0..p {
                    let mut q=vec![false;b.next];q[c as usize]=control!=0;put(&mut q,&a,x);put(&mut q,&dst,y);
                    apply(&b.gates,&mut q,false);
                    let want=match op {0=>if control==0{y}else{(p-y)%p},1=>(y+control*x)%p,2=>(y+(y%2)*p)/2,_=>panic!()};
                    assert_eq!(get(&q,&dst),want,"op={op} p={p} c={control} x={x} y={y}");
                    assert_eq!(get(&q,&a),x);assert_eq!(q[c as usize],control!=0);assert!(!q[flag as usize]);
                    assert!(b.mask.iter().all(|&v|!q[v as usize]));assert!(!q[b.carry as usize]);
                    apply(&b.gates,&mut q,true);assert_eq!(get(&q,&dst),y);assert!(!q[flag as usize]);
                }}}
            }
        }
    }
    #[test]
    fn in_place_division_all_small() {
        let mut checked=0usize;
        for p in [3usize,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,127,131,251] {
            let spec=spec(p);let program=generate(&spec,false);
            for a in 0..1<<spec.bits {for y in 0..p {
                let mut q=vec![false;program.qubits];put(&mut q,&program.a,a);put(&mut q,&program.y,y);
                apply(&program.gates,&mut q,false);
                assert_eq!(get(&q,&program.y),y*inv(eff(a,p),p)%p,"p={p} a={a} y={y}");
                assert_eq!(get(&q,&program.a),a);assert!(q[spec.bits*2..].iter().all(|x|!*x));
                apply(&program.gates,&mut q,true);assert_eq!(get(&q,&program.y),y);assert_eq!(get(&q,&program.a),a);assert!(q[spec.bits*2..].iter().all(|x|!*x));
                checked+=1;
            }}
        }
        assert_eq!(checked,157836);
        println!("M19_EXHAUSTIVE_PASS cases={checked} divisor_restored=true ancillas_zero=true reverse_identity=true");
    }
    #[test]
    fn two_divisors_shared_frame_all_small() {
        for p in [3usize,5,7] {
            let spec=spec(p);let program=generate(&spec,true);
            for a in 0..1<<spec.bits {for c in 0..1<<spec.bits {for y in 0..p {
                let mut q=vec![false;program.qubits];put(&mut q,&program.a,a);put(&mut q,&program.c,c);put(&mut q,&program.y,y);
                apply(&program.gates,&mut q,false);
                assert_eq!(get(&q,&program.y),y*eff(c,p)*inv(eff(a,p),p)%p,"p={p} a={a} c={c} y={y}");
                assert_eq!(get(&q,&program.a),a);assert_eq!(get(&q,&program.c),c);assert!(q[spec.bits*3..].iter().all(|x|!*x));
                apply(&program.gates,&mut q,true);assert_eq!(get(&q,&program.y),y);assert!(q[spec.bits*3..].iter().all(|x|!*x));
            }}}
        }
    }
    #[test]
    #[should_panic(expected="requires the proven 2n positive-binary-GCD bound")]
    fn payload_rejects_short_bound() {let mut s=Spec::secp256k1();s.rounds=511;let _=generate(&s,true);}
    #[test]
    fn full_width_corpus_and_long_chain_primitives() {
        use ruint::aliases::U256;
        let fixture=include_str!("m19_primitive_cases.tsv");
        let spec=Spec::secp256k1();let n=258;
        let parse=|x:&str|U256::from_str_radix(x,16).unwrap();
        let put256=|q:&mut[bool],reg:&[u16],x:U256| {
            for(i,&bit)in reg.iter().enumerate(){q[bit as usize]=i<256&&x.bit(i);}
        };
        let get256=|q:&[bool],reg:&[u16]| {
            let mut x=U256::ZERO;
            for(i,&bit)in reg.iter().take(256).enumerate(){if q[bit as usize]{x|=U256::from(1)<<i;}}
            assert!(reg.iter().skip(256).all(|&bit|!q[bit as usize]));x
        };
        for op in 0..4 {
            let mut b=Build {sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:spec.prime.clone()};
            let c=b.bit();let a=b.alloc(n);let dst=b.alloc(n);let flag=b.bit();
            b.mask=b.alloc(n);b.carry=b.bit();
            match op {
                0=>b.payload_add(c,&a,&dst,flag),
                1=>{b.payload_neg(c,&a,flag);b.payload_add(c,&a,&dst,flag);b.payload_neg(c,&a,flag);},
                2=>b.payload_neg(c,&dst,flag),
                3=>b.payload_half(&dst,&half_threshold(&spec.prime),flag),
                _=>panic!(),
            }
            for line in fixture.lines() {
                let f:Vec<_>=line.split('\t').collect();assert_eq!(f.len(),8);
                let x=parse(f[1]);let y=parse(f[2]);let control=parse(f[3])!=U256::ZERO;
                let mut q=vec![false;b.next];q[c as usize]=control;put256(&mut q,&a,x);put256(&mut q,&dst,y);
                apply(&b.gates,&mut q,false);
                assert_eq!(get256(&q,&dst),parse(f[4+op]),"{} op={op}",f[0]);
                assert_eq!(get256(&q,&a),x);assert_eq!(q[c as usize],control);assert!(!q[flag as usize]);
                assert!(b.mask.iter().all(|&bit|!q[bit as usize]));assert!(!q[b.carry as usize]);
                apply(&b.gates,&mut q,true);assert_eq!(get256(&q,&dst),y);assert_eq!(get256(&q,&a),x);
                assert!(!q[flag as usize]);assert!(b.mask.iter().all(|&bit|!q[bit as usize]));assert!(!q[b.carry as usize]);
            }
        }
    }

}

// Milestone 3: exact full point addition, reusing this verified core.


#[cfg(test)]
mod rate_tests {
    use super::*;
    #[test] fn certified_rate_layout_and_exact_raw_cost() {
        let p=generate_rate(&Spec::secp256k1(),false);
        // Values from the independent Python gate model (divmodel.py, variant "new").
        assert_eq!(p.qubits,1639);assert_eq!(p.toffolis,2179664);assert_eq!(p.gates.len(),14659417);
        assert_eq!(p.rate_checks.len(),255);
        assert_eq!(p.rate_checks.iter().map(|x|x.g_tail.len()).sum::<usize>(),255);

    }
}

#[cfg(test)]
mod exact_borrow_tests {
    use super::*;
    fn sim(gates:&[Gate],q:&mut[bool]){for g in gates{let(a,b,t)=(g.a as usize,g.b as usize,g.t as usize);match g.kind{6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],_=>panic!()}}}
    fn make(n:usize,constant:Option<&[bool]>)->(Build,Vec<u16>,Vec<u16>,u16,u16){let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let a=b.alloc(n);let d=b.alloc(n);let c=b.bit();let f=b.bit();b.mask=b.alloc(n);b.carry=b.bit();if let Some(k)=constant{b.payload_ge_toggle(&a,k,f);}else{b.payload_lt_toggle(c,&a,&d,f);}(b,a,d,c,f)}
    fn check(b:&Build,a:&[u16],d:&[u16],c:u16,f:u16,x:&[bool],y:&[bool],control:bool,initial:bool,want:bool){let mut q=vec![false;b.next];for(i,&v)in a.iter().enumerate(){q[v as usize]=x[i];}for(i,&v)in d.iter().enumerate(){q[v as usize]=y[i];}q[c as usize]=control;q[f as usize]=initial;let old=q.clone();sim(&b.gates,&mut q);let mut expected=old.clone();expected[f as usize]^=want;assert_eq!(q,expected);let rev:Vec<_>=b.gates.iter().copied().rev().collect();sim(&rev,&mut q);assert_eq!(q,old);}
    #[test]fn exhaustive_comparators_and_initial_flags(){for n in 2..=5{let(b,a,d,c,f)=make(n,None);for x in 0..1usize<<n{for y in 0..1usize<<n{let xb:Vec<_>=(0..n).map(|i|x>>i&1!=0).collect();let yb:Vec<_>=(0..n).map(|i|y>>i&1!=0).collect();for control in [false,true]{for initial in [false,true]{check(&b,&a,&d,c,f,&xb,&yb,control,initial,control&&y<x);}}}}
      for k in 0..1usize<<n{let kb:Vec<_>=(0..n).map(|i|k>>i&1!=0).collect();let(b,a,d,c,f)=make(n,Some(&kb));for x in 0..1usize<<n{let xb:Vec<_>=(0..n).map(|i|x>>i&1!=0).collect();for initial in [false,true]{check(&b,&a,&d,c,f,&xb,&vec![false;n],false,initial,x>=k);}}}
    }}
    #[test]fn every_full_width_chunk_boundary_and_guard(){let n=258;let(b,a,d,c,f)=make(n,None);let prime=Spec::secp256k1().prime;let(g,ga,gd,gc,gf)=make(n,Some(&prime));let mut p=prime;p.resize(n,false);let less=|x:&[bool],y:&[bool]|{(0..n).rev().find(|&i|x[i]!=y[i]).map(|i|!x[i]&&y[i]).unwrap_or(false)};let mut cases=0;
      for cut in 0..=n{let lo:Vec<_>=(0..n).map(|i|i<cut).collect();let one:Vec<_>=(0..n).map(|i|i==cut).collect();let hi:Vec<_>=lo.iter().map(|x|!*x).collect();for(x,y)in [(&lo,&one),(&one,&lo),(&hi,&lo),(&lo,&hi),(&lo,&lo)]{for control in [false,true]{for initial in [false,true]{check(&b,&a,&d,c,f,x,y,control,initial,control&&less(y,x));check(&g,&ga,&gd,gc,gf,x,y,control,initial,!less(x,&p));cases+=2;}}}}
      println!("EXACT_CHUNK_COMPARATOR_PASS checks={cases} bits=258 boundary_carries_all_retained=true");
    }
}

#[cfg(test)]mod fusion_tests{
 use super::*;use ruint::aliases::{U256,U512};
 fn sim(g:&[Gate],q:&mut[bool]){for x in g{let(a,b,t)=(x.a as usize,x.b as usize,x.t as usize);match x.kind{6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],10=>q.swap(a,t),_=>panic!()}}}
 #[test]fn incoming_carry_full_adder_exhaustive(){for n in 1..=7{let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let a=b.alloc(n);let d=b.alloc(n);b.carry=b.bit();b.add(&a,&d,false);for x in 0..1usize<<n{for y in 0..1usize<<n{for cin in [false,true]{let mut q=vec![false;b.next];for i in 0..n{q[a[i]as usize]=x>>i&1!=0;q[d[i]as usize]=y>>i&1!=0;}q[b.carry as usize]=cin;let old=q.clone();sim(&b.gates,&mut q);let got:usize=d.iter().enumerate().map(|(i,&v)|(q[v as usize]as usize)<<i).sum();assert_eq!(got,(x+y+cin as usize)&((1<<n)-1));assert_eq!(q[b.carry as usize],cin);let r:Vec<_>=b.gates.iter().copied().rev().collect();sim(&r,&mut q);assert_eq!(q,old);}}}}}
 #[test]fn fused_numerator_all_legal_symbols_full_width(){let spec=Spec::secp256k1();let p=U512::from(U256::from_limbs(super::super::P_LIMBS));let n=258;let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:spec.prime.clone()};let a=b.alloc(n);let d=b.alloc(n);let c=b.bit();let e=b.bit();let flag=b.bit();b.mask=b.alloc(n);b.carry=b.bit();b.payload_fused_step(c,e,&a,&d,&half_threshold(&spec.prime),flag);let rev:Vec<_>=b.gates.iter().copied().rev().collect();let mut checks=0;
 for line in include_str!("m19_primitive_cases.tsv").lines(){let f:Vec<_>=line.split('\t').collect();let x=U256::from_str_radix(f[1],16).unwrap();let y=U256::from_str_radix(f[2],16).unwrap();for(cc,ee)in[(false,false),(false,true),(true,true)]{let mut q=vec![false;b.next];for i in 0..256{q[a[i]as usize]=x.bit(i);q[d[i]as usize]=y.bit(i);}q[c as usize]=cc;q[e as usize]=ee;let old=q.clone();sim(&b.gates,&mut q);let z=if cc{(U512::from(x)+p-U512::from(y))%p}else{(U512::from(y)+if ee{U512::from(x)}else{U512::ZERO})%p};let want:U512=(z+if z.bit(0){p}else{U512::ZERO})>>1usize;let mut expected=old.clone();for i in 0..258{expected[d[i]as usize]=want.bit(i);}assert_eq!(q,expected,"{} c={cc} e={ee}",f[0]);sim(&rev,&mut q);assert_eq!(q,old);checks+=1;}}
 println!("FUSED_NUMERATOR_PASS checks={checks} all_three_legal_symbols=true guard_and_ancillas_clean=true");}
}

#[cfg(test)]mod packing_tests{
 use super::*;
 #[test]fn exact_codec_all64_inverse_and27_legal_zeros(){let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let q=b.alloc(6);b.pack_three(&q);assert_eq!(b.gates.iter().filter(|g|g.kind==13).count(),5);let mut seen=std::collections::HashSet::new();let mut legal=0;for x in 0..64{let mut v:Vec<bool>=(0..6).map(|i|x>>i&1!=0).collect();let apply=|g:Gate,v:&mut Vec<bool>|{let(a,c,t)=(g.a as usize,g.b as usize,g.t as usize);match g.kind{6=>v[t]^=true,8=>v[t]^=v[a],13=>v[t]^=v[a]&v[c],_=>panic!()}};for &g in &b.gates{apply(g,&mut v);}let y:usize=v.iter().enumerate().map(|(i,&b)|(b as usize)<<i).sum();assert!(seen.insert(y));if(0..3).all(|i|(x>>(2*i+1)&1)<=(x>>(2*i)&1)){assert!(!v[5]);legal+=1;}for &g in b.gates.iter().rev(){apply(g,&mut v);}assert_eq!(v,(0..6).map(|i|x>>i&1!=0).collect::<Vec<_>>());}assert_eq!(legal,27);println!("CODEC_FULL_DOMAIN_PASS inputs=64 legal=27 zero_bit_proved=true Toffoli=5");}
}

#[cfg(test)]mod biased_tests{
 use super::*;
 fn sim(g:&[Gate],q:&mut[bool]){for x in g{let(a,b,t)=(x.a as usize,x.b as usize,x.t as usize);match x.kind{6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],10=>q.swap(a,t),_=>panic!()}}}
 fn put(q:&mut[bool],r:&[u16],x:usize){for(i,&j)in r.iter().enumerate(){q[j as usize]=x>>i&1!=0;}}
 fn get(q:&[bool],r:&[u16])->usize{r.iter().enumerate().map(|(i,&j)|(q[j as usize]as usize)<<i).sum()}
 /// Every canonical pair, both directions, both bias parities (p=1 and 3 mod 4).
 #[test]fn biased_addsub_half_exit_all_small(){
  for p in [3usize,5,7,11,13,17,19,23,29,31,61,127,251]{
   let bits=usize::BITS as usize-p.leading_zeros()as usize;let prime:Vec<bool>=(0..bits).map(|i|p>>i&1!=0).collect();let a=((1usize<<bits)-1-p)/2;
   for op in 0..3{
    let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:prime.clone()};
    let e=b.bit();let u=b.alloc(bits+2);let w=b.alloc(bits+1);b.mask=b.alloc((bits+2).max(12));b.carry=b.bit();
    match op{0=>b.biased_addsub(e,&u,&w),1=>b.biased_half(&w),_=>b.biased_exit_double(&w)}
    let rev:Vec<_>=b.gates.iter().copied().rev().collect();
    for en in 0..2{for x in 0..p{for y in 0..p{
     let mut q=vec![false;b.next];q[e as usize]=en!=0;put(&mut q,&u,x+a);put(&mut q,&w,y+a);let old=q.clone();sim(&b.gates,&mut q);
     let want=match op{0=>(if en==0{(y+x)%p}else{(y+p-x)%p})+a,1=>(y+(y%2)*p)/2+a,_=>2*y%p};
     let mut expect=old.clone();for i in 0..bits+1{expect[w[i]as usize]=want>>i&1!=0;}
     assert_eq!(q,expect,"op={op} p={p} e={en} x={x} y={y}");assert_eq!(get(&q,&u),x+a);
     sim(&rev,&mut q);assert_eq!(q,old);
    }}}
   }
  }
 }
}

#[path="sound_addsub_point.rs"]
pub mod point;
