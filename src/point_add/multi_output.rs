//! Vielchoerli: joint multioutput quadratic basis synthesis.
//! Exact dirty-output recoding, no added measurements, qubits or support assumptions.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};
use std::io::Write;
const SPAN: usize = 8192;
const OUTPUTS: usize = 8;
const WIDTH: usize = 16;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Aff { bits: u32, one: bool }
impl Aff { fn xor(self, b: Self) -> Self { Self { bits:self.bits^b.bits, one:self.one^b.one } } }
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Poly { a: [u32; WIDTH], lin: u32, one: bool }
impl Poly {
    fn product(&mut self, u: Aff, v: Aff) {
        self.one ^= u.one & v.one;
        if u.one { self.lin ^= v.bits; }
        if v.one { self.lin ^= u.bits; }
        for i in 0..WIDTH { if u.bits>>i&1 != 0 {
            for j in 0..WIDTH { if v.bits>>j&1 != 0 {
                if i==j { self.lin ^= 1<<i; }
                else { self.a[i] ^= 1<<j; self.a[j] ^= 1<<i; }
            }}
        }}
    }
    fn evaluate(&self, x:u32) -> bool {
        let mut r=self.one ^ ((self.lin&x).count_ones()%2!=0);
        for i in 0..WIDTH { if x>>i&1!=0 {
            r ^= (self.a[i]&x&(!0u32<<(i+1))).count_ones()%2!=0;
        }} r
    }
    fn factor(&self) -> (Vec<(u32,u32)>,u32,bool) {
        let mut rem=self.clone(); let mut pairs=vec![];
        while let Some(p)=(0..WIDTH).find(|&i|rem.a[i]!=0) {
            let q=rem.a[p].trailing_zeros() as usize;
            let u=rem.a[q]; let v=rem.a[p];
            assert_ne!(u,0); assert_ne!(v,0); assert_ne!(u,v);
            pairs.push((u,v));
            rem.product(Aff{bits:u,one:false},Aff{bits:v,one:false});
            assert_eq!(rem.a[p],0); assert_eq!(rem.a[q],0);
        }
        // Independent coefficient reconstruction of the proposed factor witness.
        let mut check=Poly{lin:rem.lin,one:rem.one,..Poly::default()};
        for &(u,v) in &pairs { check.product(Aff{bits:u,one:false},Aff{bits:v,one:false}); }
        assert_eq!(&check,self);
        (pairs,rem.lin,rem.one)
    }
}
fn gate(k:K,c:u64,d:u64,t:u64)->Op {
    let mut o=Op::empty();o.kind=k;o.q_control1=QubitId(c);o.q_control2=QubitId(d);o.q_target=QubitId(t);o.validate();o
}
const N:u64=u64::MAX;
fn cx(c:u64,t:u64)->Op {gate(K::CX,c,N,t)}
fn ccx(a:u64,b:u64,t:u64)->Op {gate(K::CCX,a,b,t)}
fn x(t:u64)->Op {gate(K::X,N,N,t)}
fn synth(w:&[u64], t:u64, pairs:&[(u32,u32)],lin:u32,one:bool)->Vec<Op> {
    let mut out=vec![];
    if one {out.push(x(t));}
    for j in 0..w.len(){if lin>>j&1!=0{out.push(cx(w[j],t));}}
    for &(u,v) in pairs {
        let p=u.trailing_zeros() as usize;
        let vp=if v>>p&1!=0 {v^u^(1<<p)} else {v};
        let q=(vp&!(1<<p)).trailing_zeros() as usize;assert!(q<w.len());
        let mut basis=vec![];
        for j in 0..w.len(){if j!=p&&u>>j&1!=0{basis.push(cx(w[j],w[p]));}}
        for j in 0..w.len(){if j!=q&&vp>>j&1!=0{basis.push(cx(w[j],w[q]));}}
        out.extend(basis.iter().copied());out.push(ccx(w[p],w[q],t));out.extend(basis.into_iter().rev());
    }
    out
}
/// Re-derive the emitted polynomial directly from gates, without using factors.
fn prove_synth(ops:&[Op],w:&[u64],t:u64,expected:&Poly) {
    let mut v:Vec<Aff>=(0..w.len()).map(|i|Aff{bits:1<<i,one:false}).collect();
    let mut f=Poly::default();
    for o in ops {
        assert_eq!(o.c_condition,NO_BIT);
        if o.q_target.0==t {
            match o.kind {
                K::X=>f.one^=true,
                K::CX=>{let a=v[index(w,o.q_control1.0).unwrap()];f.lin^=a.bits;f.one^=a.one;}
                K::CCX=>f.product(v[index(w,o.q_control1.0).unwrap()],v[index(w,o.q_control2.0).unwrap()]),
                _=>panic!("unsupported target operation"),
            }
        }else{
            assert_eq!(o.kind,K::CX);
            let a=index(w,o.q_control1.0).unwrap();let b=index(w,o.q_target.0).unwrap();v[b]=v[b].xor(v[a]);
        }
    }
    assert_eq!(&f,expected);
    for(i,a)in v.iter().enumerate(){assert_eq!(*a,Aff{bits:1<<i,one:false});}
}
fn index(w:&[u64],q:u64)->Option<usize>{w.iter().position(|&z|z==q)}
impl Poly {
 fn xor(&mut self,b:&Self){self.one^=b.one;self.lin^=b.lin;for i in 0..WIDTH{self.a[i]^=b.a[i];}}
 fn add_aff(&mut self,a:Aff){self.lin^=a.bits;self.one^=a.one;}
}
#[derive(Default)]
struct Block {
 end:usize, w:Vec<u64>, t:Vec<u64>, aff:Vec<Aff>, f:Vec<Poly>, a:Vec<u16>,
 input_ops:Vec<Op>, output_ops:Vec<Op>, selected:Vec<usize>, nonlinear_targets:Vec<u64>, stop:&'static str,
}
impl Block {
 fn input(&mut self,q:u64)->Option<usize>{
  if self.t.contains(&q){return None;}if let Some(i)=index(&self.w,q){return Some(i);}
  if self.w.len()==WIDTH{return None;}let i=self.w.len();self.w.push(q);self.aff.push(Aff{bits:1<<i,one:false});Some(i)
 }
 fn output(&mut self,q:u64)->Option<usize>{
  if self.w.contains(&q){return None;}if let Some(i)=index(&self.t,q){return Some(i);}
  if self.t.len()==OUTPUTS{return None;}let i=self.t.len();self.t.push(q);self.f.push(Poly::default());self.a.push(1<<i);Some(i)
 }
 fn consume(&mut self,o:Op,pos:usize)->Result<(),&'static str>{
  if o.c_condition!=NO_BIT{return Err("condition");}
  let (a,b,t)=(o.q_control1.0,o.q_control2.0,o.q_target.0);
  match o.kind {
   K::CCX=>{
    if self.t.contains(&a)||self.t.contains(&b)||self.w.contains(&t){return Err("nonlinear_feedback");}
    let ia=self.input(a).ok_or("input_width")?;let ib=self.input(b).ok_or("input_width")?;let it=self.output(t).ok_or("output_width")?;
    self.f[it].product(self.aff[ia],self.aff[ib]);self.selected.push(pos);
    if !self.nonlinear_targets.contains(&t){self.nonlinear_targets.push(t);}
   }
   K::CX=>{
    if let Some(ia)=index(&self.t,a){
     if self.w.contains(&t){return Err("linear_feedback");}
     let it=self.output(t).ok_or("output_width")?;let f=self.f[ia].clone();self.f[it].xor(&f);self.a[it]^=self.a[ia];self.output_ops.push(o);
    }else if let Some(it)=index(&self.w,t){
     let ia=self.input(a).ok_or("input_width")?;self.aff[it]=self.aff[it].xor(self.aff[ia]);self.input_ops.push(o);
    }else{
     let ia=self.input(a).ok_or("input_width")?;let it=self.output(t).ok_or("output_width")?;self.f[it].add_aff(self.aff[ia]);
    }
   }
   K::X=>{
    if let Some(it)=index(&self.w,t){self.aff[it].one^=true;self.input_ops.push(o);}
    else{let it=self.output(t).ok_or("output_width")?;self.f[it].one^=true;}
   }
   K::Swap=>{
    if self.t.contains(&a)||self.t.contains(&t){
     if self.w.contains(&a)||self.w.contains(&t){return Err("mixed_swap");}
     let ia=self.output(a).ok_or("output_width")?;let it=self.output(t).ok_or("output_width")?;
     self.f.swap(ia,it);self.a.swap(ia,it);self.output_ops.push(o);
    }else{
     let ia=self.input(a).ok_or("input_width")?;let it=self.input(t).ok_or("input_width")?;
     self.aff.swap(ia,it);self.input_ops.push(o);
    }
   }
   K::Neg|K::Z|K::CZ|K::CCZ=>{
    let qs=match o.kind{K::Neg=>vec![],K::Z=>vec![t],K::CZ=>vec![a,t],_=>vec![a,b,t]};
    if qs.iter().any(|q|self.t.contains(q)){return Err("output_phase");}
    for q in qs{self.input(q).ok_or("input_width")?;}self.input_ops.push(o);
   }
   _=>return Err("barrier"),
  }Ok(())
 }
}
fn collect(ops:&[Op],start:usize)->Block{
 let mut b=Block::default();b.end=start;b.stop="end";
 for j in start..ops.len().min(start+SPAN){
  match b.consume(ops[j],j){Ok(())=>b.end=j+1,Err(why)=>{b.stop=why;break;}}
 }
 if b.end-start==SPAN{b.stop="span";}assert!(b.end>start);b
}
fn combine(f:&[Poly],mask:u16)->Poly{let mut p=Poly::default();for (i,q)in f.iter().enumerate(){if mask>>i&1!=0{p.xor(q);}}p}
fn insert(basis:&mut [u16;OUTPUTS],mut v:u16)->bool{
 for k in (0..OUTPUTS).rev(){if v>>k&1!=0{if basis[k]==0{basis[k]=v;return true;}v^=basis[k];}}false
}
fn best_basis(f:&[Poly])->(Vec<u16>,usize,usize){
 let sep=f.iter().map(|p|p.factor().0.len()).sum();let mut choices=vec![];
 for m in 1..1u16<<f.len(){choices.push((combine(f,m).factor().0.len(),m));}
 choices.sort_unstable();let mut basis=[0u16;OUTPUTS];let mut picked=vec![];let mut cost=0;
 for (weight,m)in choices{if insert(&mut basis,m){picked.push(m);cost+=weight;if picked.len()==f.len(){break;}}}
 assert_eq!(picked.len(),f.len());(picked,sep,cost)
}
/// Return chronological row operations reducing M to identity. Reverse is M.
fn reduce_matrix(mut m:Vec<u16>,targets:&[u64])->Vec<Op>{
 let mut gates=vec![];let n=m.len();
 for col in 0..n{
  let p=(col..n).find(|&r|m[r]>>col&1!=0).expect("singular basis");
  if p!=col{m.swap(p,col);gates.push(gate(K::Swap,targets[p],N,targets[col]));}
  for r in 0..n{if r!=col&&m[r]>>col&1!=0{m[r]^=m[col];gates.push(cx(targets[col],targets[r]));}}
 }
 for i in 0..n{assert_eq!(m[i],1<<i);}gates
}
fn replacement(b:&Block,masks:&[u16])->Vec<Op>{
 let red=reduce_matrix(masks.to_vec(),&b.t);let mut out=b.output_ops.clone();
 out.extend(red.iter().rev().copied());
 for(i,&m)in masks.iter().enumerate(){let p=combine(&b.f,m);let(pair,l,c)=p.factor();let gates=synth(&b.w,b.t[i],&pair,l,c);prove_synth(&gates,&b.w,b.t[i],&p);out.extend(gates);}
 out.extend(red);out.extend(b.input_ops.iter().copied());out
}
pub fn run(ops:Vec<Op>)->Vec<Op>{
 let mut cert=std::env::var("MULTI_CERT").ok().map(|p|std::io::BufWriter::new(std::fs::File::create(p).unwrap()));
 if let Some(c)=&mut cert{writeln!(c,"start\tend\tinputs\toutputs\told_ccx\tseparate_ccx\tjoint_ccx\tbasis\taccepted\tnew_ops\tstop").unwrap();}
 let mut out=Vec::with_capacity(ops.len());let(mut i,mut depth)=(0,0usize);
 let(mut blocks,mut multi,mut accepted,mut old_t,mut sep_t,mut new_t,mut saved,mut marginal)=(0,0,0,0,0,0,0,0);
 let(mut eligible_old,mut ceiling,mut maxspan)=(0,0,0);let mut stops=std::collections::BTreeMap::new();
 while i<ops.len(){let o=ops[i];
  if depth==0&&o.kind==K::CCX&&o.c_condition==NO_BIT{
   let b=collect(&ops,i);blocks+=1;*stops.entry(b.stop).or_insert(0usize)+=1;
   if b.nonlinear_targets.len()>=2{
    multi+=1;let(masks,sep,joint)=best_basis(&b.f);let yes=joint<sep&&joint<b.selected.len();
    let rep=if yes{replacement(&b,&masks)}else{vec![]};
    eligible_old+=b.selected.len();if yes{ceiling+=b.selected.len()-joint;}
    if let Some(c)=&mut cert{
     let list=|v:&[u64]|v.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");
     writeln!(c,"{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",i,b.end,list(&b.w),list(&b.t),b.selected.len(),sep,joint,list(&masks.iter().map(|&x|x as u64).collect::<Vec<_>>()),u8::from(yes),rep.len(),b.stop).unwrap();
    }
    if yes{
     accepted+=1;old_t+=b.selected.len();sep_t+=sep;new_t+=joint;saved+=b.selected.len()-joint;marginal+=sep-joint;maxspan=maxspan.max(b.end-i);
     out.extend(rep);i=b.end;assert!(out.len()<40_000_000,"output cap");continue;
    }
   }
   out.extend_from_slice(&ops[i..b.end]);i=b.end;continue;
  }
  if o.kind==K::PushCondition{depth+=1;}else if o.kind==K::PopCondition{depth=depth.checked_sub(1).unwrap();}
  out.push(o);i+=1;
 }
 assert_eq!(depth,0);
 eprintln!("MULTI_OUTPUT blocks={blocks} multi={multi} accepted={accepted} old_T={old_t} separate_T={sep_t} new_T={new_t} saved_T={saved} basis_gain_T={marginal} eligible_old_T={eligible_old} class_ceiling_T={ceiling} max_span={maxspan} ops_in={} ops_out={}",ops.len(),out.len());
 eprintln!("MULTI_STOPS {stops:?}");out
}
#[cfg(test)] mod tests{
 use super::*;
 use crate::sim::Simulator;
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};
 fn native(ops:&[Op],n:usize,base:u64,phase:u64)->(Vec<u64>,u64){
  let mut h=Shake256::default();h.update(b"cxharvest-c11-native");let mut rng=h.finalize_xof();let mut s=Simulator::new(n,2,&mut rng);s.phase=phase;
  for q in 0..n{for j in 0..64{if (base+j)>>q&1!=0{s.qubits[q]|=1<<j;}}}s.bits[0]=0xAAAAAAAAAAAAAAAA;s.bits[1]=0xCCCCCCCCCCCCCCCC;
  s.apply_iter(ops.iter());(s.qubits,s.phase)
 }
 fn compare(a:&[Op],b:&[Op],n:usize)->usize{
  let mut count=0;for base in (0..1u64<<n).step_by(64){for phase in [0,u64::MAX]{assert_eq!(native(a,n,base,phase),native(b,n,base,phase),"base {base}");count+=64;}}count
 }
 fn choir()->Vec<Op>{vec![ccx(0,1,6),ccx(2,3,6),ccx(0,1,7),ccx(4,5,7),ccx(2,3,8),ccx(4,5,8)]}
 #[test]fn multi_output_distinct_products_dirty_outputs(){
  let a=choir();let b=collect(&a,0);let(m,s,j)=best_basis(&b.f);assert_eq!((s,j),(6,4));
  let mut b=run(a.clone());assert_eq!(b.iter().filter(|o|o.kind==K::CCX).count(),4);
  let mut a=a;a.push(gate(K::CZ,0,N,7));b.push(gate(K::CZ,0,N,7));
  eprintln!("MULTI_TEST dirty comparisons={}",compare(&a,&b,9));assert_eq!(m.len(),3);
 }
 #[test]fn multi_output_all_three_variable_pair_polynomials(){
  let mut count=0;let pairs=[(0,1),(0,2),(1,2)];
  for code in 0..512u32{
   let mut a=vec![];for t in 0..3{for(p,&(x,y))in pairs.iter().enumerate(){if code>>(3*t+p)&1!=0{a.push(ccx(x,y,3+t as u64));}}}
   a.extend([cx(3,4),gate(K::Swap,4,N,5),x(3),cx(0,4)]);
   let b=run(a.clone());count+=compare(&a,&b,6);
  }eprintln!("MULTI_TEST polynomial comparisons={count}");
 }
 #[test]fn multi_output_affine_phase_and_barriers(){
  let mut a=choir();a.insert(2,cx(0,2));a.insert(3,x(1));a.insert(5,gate(K::CZ,1,N,4));a.extend([cx(6,7),gate(K::Swap,7,N,8),x(8),cx(2,8),gate(K::CCZ,0,1,3)]);
  let b=collect(&a,0);let(m,_,_)=best_basis(&b.f);let out=replacement(&b,&m);let mut count=compare(&a,&out,9);
  for h in [ccx(6,0,1),cx(6,0),gate(K::Z,N,N,6),gate(K::Swap,6,N,0)]{
   let mut a=choir();a.insert(3,h);let b=run(a.clone());count+=compare(&a,&b,9);
  }
  let mut push=Op::empty();push.kind=K::PushCondition;push.c_condition=crate::circuit::BitId(0);let mut pop=Op::empty();pop.kind=K::PopCondition;
  let mut a=vec![push];a.extend(choir());a.push(pop);assert_eq!(run(a.clone()),a);
  let mut a=choir();a[2].c_condition=crate::circuit::BitId(1);let b=run(a.clone());count+=compare(&a,&b,9);
  eprintln!("MULTI_TEST affine_hazards comparisons={count}");
 }
 #[test]fn multi_output_wrong_basis_restoration_detected(){
  let mut a=choir();let b=collect(&a,0);let(m,_,_)=best_basis(&b.f);let red=reduce_matrix(m.clone(),&b.t);assert!(!red.is_empty());
  let mut good=replacement(&b,&m);let mut bad=good.clone();let pos=bad.len()-red.len();bad.remove(pos);
  for i in 0..3{a.push(gate(K::CZ,i,N,6+i));good.push(gate(K::CZ,i,N,6+i));bad.push(gate(K::CZ,i,N,6+i));}
  let mut val=0;let mut pha=0;for base in (0..512).step_by(64){let g=native(&a,9,base,0);let b=native(&bad,9,base,0);val+=g.0.iter().zip(&b.0).fold(0u64,|s,(a,b)|s|(a^b)).count_ones();pha+=(g.1^b.1).count_ones();}
  assert!(val>0);assert!(pha>0);eprintln!("MULTI_TEST mutation value={val} phase={pha}; good comparisons={}",compare(&a,&good,9));
 }
}
