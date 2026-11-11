//! Correctness-first normalized hddivsteps inverse, no measurement or truncation.
//!
//! Oracle contract |a>|b>|0> -> |a>|b XOR inv(a mod p)>|0>, with inv(0)=0.
//! All arithmetic is coherent X/CX/CCX/SWAP. Full compute/copy/uncompute makes
//! flag histories clean without assuming an approximate or free phase eraser.
//! This module is intentionally NOT wired into the default point-add builder.
use quantum_ecc::circuit::{Op, OperationType, QubitId};

pub const P_LIMBS: [u64; 4] = [0xfffffffefffffc2f, u64::MAX, u64::MAX, u64::MAX];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Gate { pub kind: u16, pub a: u16, pub b: u16, pub t: u16 }
impl Gate {
    pub fn op(self) -> Op {
        let mut o=Op::empty();
        o.kind=match self.kind {6=>OperationType::X,8=>OperationType::CX,10=>OperationType::Swap,13=>OperationType::CCX,_=>panic!("nonunitary/unknown gate")};
        o.q_target=QubitId(self.t as u64);
        if self.kind!=6 {o.q_control1=QubitId(self.a as u64);}
        if self.kind==13 {o.q_control2=QubitId(self.b as u64);}
        o
    }
}
#[derive(Clone)]
pub struct Spec { pub bits: usize, pub prime: Vec<bool>, pub rounds: usize }
impl Spec {
    pub fn secp256k1() -> Self {Self {bits:256,prime:(0..256).map(|i| P_LIMBS[i/64]>>(i%64)&1!=0).collect(),rounds:512}}
}
pub struct Program {
    pub gates: Vec<Gate>, pub qubits:usize, pub input:Vec<u16>, pub output:Vec<u16>,
    pub f:Vec<u16>, pub g:Vec<u16>, pub v:Vec<u16>, pub r:Vec<u16>, pub delta:Vec<u16>,
    pub step_ends:Vec<usize>, pub compute_end:usize, pub toffolis:u64,
}
#[derive(Clone)]
pub struct Site{pub start:usize,pub end:usize,pub cleanup:bool,pub flag:u16,pub kind:u16,pub width:usize}
struct Build { sites:Vec<Site>,gates:Vec<Gate>, next:usize, mask:Vec<u16>, carry:u16, prime:Vec<bool> }
impl Build {
    fn alloc(&mut self,n:usize)->Vec<u16> {
        assert!(self.next+n<u16::MAX as usize);
        let v=(self.next..self.next+n).map(|i|i as u16).collect();self.next+=n;v
    }
    fn bit(&mut self)->u16 {self.alloc(1)[0]}
    fn x(&mut self,t:u16){self.gates.push(Gate{kind:6,a:0,b:0,t});}
    fn cx(&mut self,a:u16,t:u16){assert_ne!(a,t);self.gates.push(Gate{kind:8,a,b:0,t});}
    fn ccx(&mut self,a:u16,b:u16,t:u16){assert!(a!=b&&a!=t&&b!=t);self.gates.push(Gate{kind:13,a,b,t});}
    fn swap(&mut self,a:u16,t:u16){assert_ne!(a,t);self.gates.push(Gate{kind:10,a,b:0,t});}
    fn cswap(&mut self,c:u16,a:&[u16],b:&[u16]) {
        assert_eq!(a.len(),b.len());
        for (&x,&y) in a.iter().zip(b) {self.cx(x,y);self.ccx(c,y,x);self.cx(x,y);}
    }
    /// Cuccaro MAJ/UMA, modulo 2^n, preserving source and clean carry.
    /// All n bits participate; discarded overflow is intentional wrapped integer
    /// arithmetic only. Callers allocate TWO extra signed/overflow bits.
    fn add(&mut self,a:&[u16],b:&[u16],subtract:bool) {
        assert_eq!(a.len(),b.len());assert!(a.iter().all(|x| !b.contains(x)));
        let start=self.gates.len();
        // Exact top sum is retained. Only the unused carry beyond the FULL
        // word is absent: adjacent top MAJ/UMA gates cancel identically.
        for i in 0..a.len()-1 {
            let c=if i==0 {self.carry}else{a[i-1]};
            self.cx(a[i],b[i]);self.cx(a[i],c);self.ccx(c,b[i],a[i]);
        }
        let i=a.len()-1;let c=if i==0{self.carry}else{a[i-1]};
        self.cx(a[i],b[i]);self.cx(c,b[i]);
        for i in (0..a.len()-1).rev(){
            let c=if i==0 {self.carry}else{a[i-1]};
            self.ccx(c,b[i],a[i]);self.cx(a[i],c);self.cx(c,b[i]);
        }
        if subtract {self.gates[start..].reverse();}
    }
    fn constant(&mut self,acc:&[u16],bits:&[bool],ctrl:Option<u16>,subtract:bool) {
        assert!(bits.len()<=acc.len());let m=self.mask[..acc.len()].to_vec();
        for (i,&b) in bits.iter().enumerate() {if b {if let Some(c)=ctrl {self.cx(c,m[i]);} else {self.x(m[i]);}}}
        self.add(&m,acc,subtract);
        for (i,&b) in bits.iter().enumerate() {if b {if let Some(c)=ctrl {self.cx(c,m[i]);} else {self.x(m[i]);}}}
    }
    fn prime_add(&mut self,acc:&[u16],ctrl:Option<u16>,subtract:bool) {
        let p=self.prime.clone();self.constant(acc,&p,ctrl,subtract);
    }
    /// Exact controlled sum with a clean incoming carry (M8 callers have0).
    /// Carry bank is the existing mask; all n result bits, including top carry,
    /// participate. Subtraction is the actual inverse of this full permutation.
    /// Shared-control factoring makes each cleanup ONE AND, enabling exact MBU.
    fn gidney_cadd(&mut self,e:u16,a:&[u16],b:&[u16]){
      let n=a.len();assert_eq!(n,b.len());assert!(n>=1&&n<=self.mask.len());
      let cs=self.mask[..n-1].to_vec();assert!(a.iter().chain(b).all(|q|!cs.contains(q)));assert!(!a.contains(&e)&&!b.contains(&e)&&!cs.contains(&e));
      for i in 0..n-1{let c=if i==0{self.carry}else{cs[i-1]};
        self.cx(c,a[i]);self.cx(c,b[i]);self.ccx(a[i],b[i],cs[i]);self.cx(c,cs[i]);self.cx(c,b[i]);self.cx(c,a[i]);
      }
      for i in 0..n{let c=if i==0{self.carry}else{cs[i-1]};self.cx(c,a[i]);self.ccx(e,a[i],b[i]);self.cx(c,a[i]);}
      for i in(0..n-1).rev(){let c=if i==0{self.carry}else{cs[i-1]};
        self.cx(c,cs[i]);self.cx(c,a[i]);self.cx(c,b[i]);self.cx(e,b[i]);
        self.ccx(a[i],b[i],cs[i]);self.cx(e,b[i]);self.cx(c,b[i]);self.cx(c,a[i]);
      }
    }
    fn cadd(&mut self,c:u16,a:&[u16],b:&[u16]) {
        let m=self.mask[..a.len()].to_vec();
        for i in 0..a.len() {self.ccx(c,a[i],m[i]);}
        self.add(&m,b,false);
        for i in (0..a.len()).rev() {self.ccx(c,a[i],m[i]);}
    }
    fn cneg(&mut self,c:u16,a:&[u16]) {
        for &q in a {self.cx(c,q);}
        self.constant(a,&[true],Some(c),false);
    }
    /// Exact (-1)^neg * b + enable*a modulo the FULL allocated word.
    /// Incoming carry=neg fuses complement/+1 with addition; carry restored.
    fn signed_cadd(&mut self,neg:u16,enable:u16,a:&[u16],b:&[u16]) {
        for &q in b{self.cx(neg,q);}
        self.cx(neg,self.carry);
        self.cadd(enable,a,b);
        self.cx(neg,self.carry);
    }
    fn delta_update(&mut self,c:u16,d:&[u16]){
        for &q in d{self.cx(c,q);}
        self.cx(c,self.carry);self.constant(d,&[false,true],None,false);self.cx(c,self.carry);
    }
    /// Shared verified hddivsteps rail transition. Both the M1 oracle and M2
    /// payload integration use this exact gate order and full-width arithmetic.
    fn hd_rail_step(&mut self,e:u16,c:u16,f:&[u16],g:&[u16],delta:&[u16]) {
        self.cx(g[0],e);
        self.x(delta[11]);self.ccx(delta[11],e,c);self.x(delta[11]);
        self.delta_update(c,delta);
        self.cswap(c,f,g);self.signed_cadd(c,e,f,g);self.signed_half_even(g);
    }
    /// Retain an exact a>=p predicate. a is nonnegative and <2p; width is
    /// bits(p)+2, so the sign of a-p is exact, not a truncated compare.
    fn ge_prime(&mut self,a:&[u16])->u16 {
        let flag=self.bit();self.prime_add(a,None,true);
        self.x(flag);self.cx(a[a.len()-1],flag);
        self.prime_add(a,None,false);flag
    }
    /// Input -p<a<2p. Keep the two flags until the outer Bennett inverse.
    fn normalize(&mut self,a:&[u16]) {
        let neg=self.bit();self.cx(a[a.len()-1],neg);
        self.prime_add(a,Some(neg),false);
        let ge=self.ge_prime(a);self.prime_add(a,Some(ge),true);
    }
    fn rotate_right_zero(&mut self,a:&[u16]) {for i in 0..a.len()-1 {self.swap(a[i],a[i+1]);}}
    fn signed_half_even(&mut self,a:&[u16]) {
        self.rotate_right_zero(a);self.cx(a[a.len()-2],a[a.len()-1]);
    }
    fn modular_half(&mut self,a:&[u16]) {
        let odd=self.bit();self.cx(a[0],odd);self.prime_add(a,Some(odd),false);
        self.rotate_right_zero(a);
    }
}

pub fn generate(spec:&Spec)->Program { generate_inner(spec,None) }

/// Diagnostic only: inspect gcd rails for the published tight pair whose f0
/// differs from p. Its coefficient output is NOT a mod-p inverse oracle.
pub fn generate_gcd_probe(initial_f:&[bool])->Program {
    assert_eq!(initial_f.len(),256);assert!(initial_f[0]);
    generate_inner(&Spec::secp256k1(),Some(initial_f))
}
fn generate_inner(spec:&Spec,initial_override:Option<&[bool]>)->Program {
    assert!(spec.bits>=2&&spec.prime.len()==spec.bits&&spec.prime[0]&&spec.prime[spec.bits-1]);
    assert!(spec.rounds<=590);
    let proven_steps=(9437*spec.bits+1+4095)/4096;
    assert!(spec.rounds>=proven_steps,"requires the proven hddivsteps bound, not sampled convergence");
    let n=spec.bits+2;
    let mut b=Build{sites:vec![],gates:Vec::new(),next:0,mask:Vec::new(),carry:0,prime:spec.prime.clone()};
    let input=b.alloc(spec.bits);let output=b.alloc(spec.bits);
    let f=b.alloc(n);let g=b.alloc(n);let v=b.alloc(n);let r=b.alloc(n);let delta=b.alloc(12);
    b.mask=b.alloc(n.max(12));b.carry=b.bit();
    let initial=initial_override.unwrap_or(&spec.prime);
    for (i,&set) in initial.iter().enumerate() {if set {b.x(f[i]);}}
    for i in 0..spec.bits {b.cx(input[i],g[i]);}
    b.x(r[0]);b.x(delta[0]);
    // Accept all 256-bit inputs while invoking the theorem only on g<p.
    let init_ge=b.ge_prime(&g);b.prime_add(&g,Some(init_ge),true);
    let mut step_ends=Vec::new();
    for _ in 0..spec.rounds {
        let e=b.bit();let c=b.bit();
        b.hd_rail_step(e,c,&f,&g,&delta);
        b.cswap(c,&v,&r);b.cneg(c,&r);b.cadd(e,&v,&r);b.normalize(&r);b.modular_half(&r);
        step_ends.push(b.gates.len());
    }
    b.cneg(f[n-1],&v);b.normalize(&v);
    let compute_end=b.gates.len();
    for i in 0..spec.bits {b.cx(v[i],output[i]);}
    // No measurement inversion, hidden reset, garbage drop or phase erasure.
    for i in (0..compute_end).rev() {b.gates.push(b.gates[i]);}
    let toffolis=b.gates.iter().filter(|x|x.kind==13).count() as u64;
    for &gate in &b.gates {gate.op().validate();}
    Program{gates:b.gates,qubits:b.next,input,output,f,g,v,r,delta,step_ends,compute_end,toffolis}
}

#[cfg(test)]
mod tests {
 use super::*;
 fn apply(gates:&[Gate],q:&mut [bool]) {for x in gates {let(a,b,t)=(x.a as usize,x.b as usize,x.t as usize);match x.kind {6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],10=>q.swap(a,t),_=>panic!()}}}
 fn put(q:&mut[bool],r:&[u16],x:usize){for(i,&j)in r.iter().enumerate(){q[j as usize]=(x>>i)&1!=0;}}
 fn get(q:&[bool],r:&[u16])->usize{r.iter().enumerate().map(|(i,&j)|(q[j as usize] as usize)<<i).sum()}
 #[test] fn add_sub_all_small(){
  for n in 2..=7 {for sub in [false,true] {
   let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let a=b.alloc(n);let dst=b.alloc(n);b.carry=b.bit();b.add(&a,&dst,sub);
   for x in 0..1<<n {for y in 0..1<<n {let mut q=vec![false;b.next];put(&mut q,&a,x);put(&mut q,&dst,y);apply(&b.gates,&mut q);
    assert_eq!(get(&q,&a),x);assert_eq!(get(&q,&dst),if sub {(y+(1<<n)-x)&((1<<n)-1)}else{(y+x)&((1<<n)-1)});assert!(!q[b.carry as usize]);
   }}
  }}
 }
 #[test] fn inverse_small_primes_and_reverse(){
  for p in [3usize,5,7,11,13,17,19,23,29,31] {
   let bits=usize::BITS as usize-p.leading_zeros() as usize;let rounds=(9437*bits+1+4095)/4096;
   let program=generate(&Spec{bits,prime:(0..bits).map(|i|p>>i&1!=0).collect(),rounds});
   for a in 0..1<<bits {for seed in [0,(1<<bits)-1] {
    let mut q=vec![false;program.qubits];put(&mut q,&program.input,a);put(&mut q,&program.output,seed);apply(&program.gates,&mut q);
    let aa=a%p;let inv=if aa==0 {0}else{(1..p).find(|&v|v*aa%p==1).unwrap()};
    assert_eq!(get(&q,&program.output),seed^inv,"p={p} a={a}");assert_eq!(get(&q,&program.input),a);assert!(q[bits*2..].iter().all(|x|!*x));
    let rev:Vec<_>=program.gates.iter().copied().rev().collect();apply(&rev,&mut q);assert_eq!(get(&q,&program.output),seed);assert!(q[bits*2..].iter().all(|x|!*x));
   }}
  }
 }
 #[test]
 #[should_panic(expected="requires the proven hddivsteps bound")]
 fn rejects_589_for_secp256k1() {
    let mut spec=Spec::secp256k1();spec.rounds=589;let _=generate(&spec);
 }

}

// Milestone 2 reuses the exact arithmetic above; M1's oracle is unchanged.
#[path = "sound_addsub_payload.rs"]
pub mod payload;

#[cfg(test)]mod gidney_tests{
 use super::*;
 #[test]fn exact_controlled_carry_adder_all_small_and_reverse(){
 for n in 1..=7{let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let a=b.alloc(n);let out=b.alloc(n);let e=b.bit();b.mask=b.alloc(n);b.carry=b.bit();b.gidney_cadd(e,&a,&out);assert_eq!(b.gates.iter().filter(|g|g.kind==13).count(),3*n-2);
 let apply=|g:Gate,q:&mut Vec<bool>|{let(a,c,t)=(g.a as usize,g.b as usize,g.t as usize);match g.kind{6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[c],_=>panic!()}};
 for x in 0..1usize<<n{for y in 0..1usize<<n{for en in [false,true]{let mut q=vec![false;b.next];for i in 0..n{q[a[i]as usize]=x>>i&1!=0;q[out[i]as usize]=y>>i&1!=0;}q[e as usize]=en;let old=q.clone();for &g in &b.gates{apply(g,&mut q);}let mut expected=old.clone();let z=(y+if en{x}else{0})&((1<<n)-1);for i in 0..n{expected[out[i]as usize]=z>>i&1!=0;}assert_eq!(q,expected,"n={n} x={x} y={y} e={en}");for &g in b.gates.iter().rev(){apply(g,&mut q);}assert_eq!(q,old);}}}
 }}
}

impl Build{
 fn reverse_from(&mut self,a:usize){let z=self.gates.len();self.gates[a..].reverse();for s in &mut self.sites{if s.start>=a&&s.end<=z{let(x,y)=(s.start,s.end);s.start=a+z-y;s.end=a+z-x;s.cleanup=!s.cleanup;}}}
 fn append_reverse(&mut self,a:usize,z:usize){let at=self.gates.len();let old:Vec<_>=self.sites.iter().filter(|s|s.start>=a&&s.end<=z).cloned().collect();for j in(a..z).rev(){self.gates.push(self.gates[j]);}for mut s in old{let(x,y)=(s.start,s.end);s.start=at+z-y;s.end=at+z-x;s.cleanup=!s.cleanup;self.sites.push(s);}}
}

// ---- add-subtract variant: new shared primitives (UNCOMPILED PROPOSAL) ----
impl Build{
 /// b += a + carry (mod 2^n). gidney_cadd with the control removed: carries
 /// are clean ANDs in the mask bank, so each of the n-1 uncomputes is ONE AND
 /// on a wire that returns to zero. All n bits and every carry participate.
 fn gidney_add(&mut self,a:&[u16],b:&[u16]){
  let n=a.len();assert_eq!(n,b.len());assert!(n>=1&&n-1<=self.mask.len());
  let cs=self.mask[..n-1].to_vec();assert!(a.iter().chain(b).all(|q|!cs.contains(q)));
  for i in 0..n-1{let c=if i==0{self.carry}else{cs[i-1]};
   self.cx(c,a[i]);self.cx(c,b[i]);self.ccx(a[i],b[i],cs[i]);self.cx(c,cs[i]);self.cx(c,b[i]);self.cx(c,a[i]);
  }
  for i in 0..n{let c=if i==0{self.carry}else{cs[i-1]};self.cx(a[i],b[i]);self.cx(c,b[i]);}
  for i in(0..n-1).rev(){let c=if i==0{self.carry}else{cs[i-1]};
   self.cx(c,cs[i]);self.cx(c,a[i]);self.cx(c,b[i]);self.x(b[i]);
   self.ccx(a[i],b[i],cs[i]);self.x(b[i]);self.cx(c,b[i]);self.cx(c,a[i]);
  }
 }
 /// acc += K if ctrl=0; acc -= K+1 if ctrl=1 (mod 2^len). One UNCONTROLLED
 /// constant adder between CNOT fans: ~(~acc + K + 1) = acc - K - 1.
 fn conj_add_const(&mut self,ctrl:u16,acc:&[u16],bits:&[bool]){
  assert!(!acc.contains(&ctrl));
  for &q in acc{self.cx(ctrl,q);}
  self.cx(ctrl,self.carry);self.constant(acc,bits,None,false);self.cx(ctrl,self.carry);
  for &q in acc{self.cx(ctrl,q);}
 }
 /// Exact rotation towards the high end (inverse of rotate_right_zero).
 fn rotate_left(&mut self,a:&[u16]){for i in(0..a.len()-1).rev(){self.swap(a[i],a[i+1]);}}
}

#[cfg(test)]mod addsub_primitive_tests{
 use super::*;
 fn sim(g:&[Gate],q:&mut[bool]){for x in g{let(a,b,t)=(x.a as usize,x.b as usize,x.t as usize);match x.kind{6=>q[t]^=true,8=>q[t]^=q[a],13=>q[t]^=q[a]&q[b],10=>q.swap(a,t),_=>panic!()}}}
 #[test]fn uncontrolled_carry_adder_all_small_with_carry_in_and_reverse(){
  for n in 1..=7{let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let a=b.alloc(n);let d=b.alloc(n);b.mask=b.alloc(n);b.carry=b.bit();b.gidney_add(&a,&d);
   assert_eq!(b.gates.iter().filter(|g|g.kind==13).count(),2*(n-1));
   for x in 0..1usize<<n{for y in 0..1usize<<n{for cin in [false,true]{let mut q=vec![false;b.next];for i in 0..n{q[a[i]as usize]=x>>i&1!=0;q[d[i]as usize]=y>>i&1!=0;}q[b.carry as usize]=cin;let old=q.clone();sim(&b.gates,&mut q);
    let mut want=old.clone();let z=(x+y+cin as usize)&((1<<n)-1);for i in 0..n{want[d[i]as usize]=z>>i&1!=0;}assert_eq!(q,want);
    let r:Vec<_>=b.gates.iter().copied().rev().collect();sim(&r,&mut q);assert_eq!(q,old);}}}
  }
 }
 #[test]fn conjugated_constant_all_small(){
  for n in 1..=6{for k in 0..1usize<<n{let mut b=Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:vec![]};let acc=b.alloc(n);let c=b.bit();b.mask=b.alloc(n);b.carry=b.bit();
   let kb:Vec<_>=(0..n).map(|i|k>>i&1!=0).collect();b.conj_add_const(c,&acc,&kb);
   for x in 0..1usize<<n{for ctrl in [false,true]{let mut q=vec![false;b.next];for i in 0..n{q[acc[i]as usize]=x>>i&1!=0;}q[c as usize]=ctrl;let old=q.clone();sim(&b.gates,&mut q);
    let m=1usize<<n;let z=if ctrl{(x+2*m-k-1)%m}else{(x+k)%m};let mut want=old.clone();for i in 0..n{want[acc[i]as usize]=z>>i&1!=0;}assert_eq!(q,want);}}
  }}
 }
}
