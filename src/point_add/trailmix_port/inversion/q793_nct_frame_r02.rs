//! Exact X-frame and complementary-control simplification of NCT templates.
//! All rewrites are identities on arbitrary basis states, hence on superpositions;
//! no clean-wire, reachability, input-seed or measurement assumptions are used.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Gate {n:u8,c:[usize;2],neg:u8,t:usize}
impl Gate {
 fn reads(self,q:usize)->bool{self.c[..self.n as usize].contains(&q)}
 fn commutes(self,b:Self)->bool{!self.reads(b.t)&&!b.reads(self.t)}
 fn reduced(self,index:usize)->Self{let mut g=self;let last=self.n as usize-1;if index<last{g.c[index]=g.c[last];g.neg=(g.neg&!(1<<index))|(((g.neg>>last)&1)<<index);}g.n-=1;g.c[g.n as usize]=0;g.neg&=(1<<g.n)-1;g}
}
// XOR of two same-target cubes; None is no rule, Some(None) is cancellation.
fn combine(a:Gate,b:Gate)->Option<Option<Gate>> {
 if a.t!=b.t{return None;}
 if a.n==b.n&&a.c==b.c {
  let different=a.neg^b.neg;
  if different==0{return Some(None);}
  if different.count_ones()==1{return Some(Some(a.reduced(different.trailing_zeros()as usize)));}
 }
 let(s,l)=if a.n<b.n{(a,b)}else{(b,a)};
 if s.n+1==l.n {
  let mut missing=None;
  for i in 0..l.n as usize {
   if let Some(j)=s.c[..s.n as usize].iter().position(|&c|c==l.c[i]){
    if(l.neg>>i)&1!=(s.neg>>j)&1{return None;}
   }else{if missing.is_some(){return None;}missing=Some(i);}
  }
  if let Some(i)=missing{let mut g=l;g.neg^=1<<i;return Some(Some(g));}
 }
 None
}
fn lift(ops:&[Op],wires:usize)->(Vec<Gate>,Vec<bool>){
 let mut frame=vec![false;wires];let mut gates=Vec::with_capacity(ops.len());
 for o in ops{
  assert_eq!(o.c_condition,NO_BIT);o.validate();let t=o.q_target.0 as usize;
  match o.kind{
   K::X=>frame[t]^=true,
   K::CX|K::CCX=>{
    let n=if o.kind==K::CX{1}else{2};let mut c=[o.q_control1.0 as usize,if n==2{o.q_control2.0 as usize}else{0}];
    if n==2&&c[0]>c[1]{c.swap(0,1);}
    let mut neg=0;for i in 0..n{neg|=(frame[c[i]]as u8)<<i;}
    gates.push(Gate{n:n as u8,c,neg,t});
   },_=>panic!("only unconditional NCT templates")
  }
 }
 (gates,frame)
}
fn lower(gates:&[Gate],want:&[bool])->Vec<Op>{
 let mut frame=vec![false;want.len()];let mut out=Vec::with_capacity(gates.len());
 let x=|t:usize|{let mut o=Op::empty();o.kind=K::X;o.q_target=QubitId(t as u64);o};
 for &g in gates{
  if g.n==0{frame[g.t]^=true;continue;}
  if g.n==1{
   // A complemented CX control contributes only a target X. Track that X
   // in the output frame instead of physically toggling the control.
   let mut o=Op::empty();o.kind=K::CX;o.q_control1=QubitId(g.c[0]as u64);o.q_target=QubitId(g.t as u64);o.validate();out.push(o);
   frame[g.t]^=frame[g.c[0]]!=(g.neg&1!=0);continue;
  }
  for i in 0..g.n as usize{let neg=g.neg>>i&1!=0;if frame[g.c[i]]!=neg{out.push(x(g.c[i]));frame[g.c[i]]=neg;}}
  let mut o=Op::empty();o.kind=if g.n==1{K::CX}else{K::CCX};o.q_target=QubitId(g.t as u64);o.q_control1=QubitId(g.c[0]as u64);
  if g.n==2{o.q_control2=QubitId(g.c[1]as u64);}o.validate();out.push(o);
 }
 for i in 0..frame.len(){if frame[i]!=want[i]{out.push(x(i));}}
 out
}
fn simplify(gates:&mut Vec<Gate>,window:usize)->usize{
 let before=gates.len();let mut live:Vec<Gate>=Vec::with_capacity(before);
 for g in gates.drain(..){
  let mut found=None;
  for j in (live.len().saturating_sub(window)..live.len()).rev(){
   if let Some(rule)=combine(live[j],g){found=Some((j,rule));break;}
   if !g.commutes(live[j]){break;}
  }
  match found{Some((j,Some(h)))=>live[j]=h,Some((j,None))=>{live.remove(j);},None=>live.push(g)}
 }
 *gates=live;before-gates.len()
}
pub(super) fn apply(ops:&mut Vec<Op>)->(usize,usize){
 if ops.is_empty(){return(0,0);}
 let wires=ops.iter().flat_map(|o|[o.q_target,o.q_control1,o.q_control2]).filter(|q|q.0!=u64::MAX).map(|q|q.0 as usize+1).max().unwrap();
 let before=ops.len();let bt=ops.iter().filter(|o|o.kind==K::CCX).count();
 let (mut gates,frame)=lift(ops,wires);for _ in 0..4{if simplify(&mut gates,256)==0{break;}}
 let mut candidate=lower(&gates,&frame);super::shared_optimize::cancel_nct_live(&mut candidate,4096);
 let at=candidate.iter().filter(|o|o.kind==K::CCX).count();
 if candidate.len()<before&&at<=bt{let removed=before-candidate.len();*ops=candidate;(removed,bt-at)}else{(0,0)}
}
// Independent scalar evaluator and deterministic fixed-seed exhaustive controls.
fn scalar(ops:&[Op],mut x:u64)->u64{for o in ops{let on=match o.kind{K::X=>true,K::CX=>x>>o.q_control1.0&1!=0,K::CCX=>(x>>o.q_control1.0)&(x>>o.q_control2.0)&1!=0,_=>panic!()};if on{x^=1<<o.q_target.0;}}x}
fn op(n:usize,c:[usize;2],t:usize)->Op{let mut o=Op::empty();o.kind=[K::X,K::CX,K::CCX][n];o.q_target=QubitId(t as u64);if n>0{o.q_control1=QubitId(c[0]as u64);}if n>1{o.q_control2=QubitId(c[1]as u64);}o.validate();o}
pub fn check(){
 let mut cube_checks=0;let mut rules=0;
 let mut all=Vec::new();for t in 0..5{all.push(Gate{n:0,c:[0,0],neg:0,t});for a in 0..5{if a==t{continue;}for neg in 0..2{all.push(Gate{n:1,c:[a,0],neg,t});}for b in a+1..5{if b==t{continue;}for neg in 0..4{all.push(Gate{n:2,c:[a,b],neg,t});}}}}
 for &a in &all{for &b in &all{if let Some(rule)=combine(a,b){rules+=1;let before=lower(&[a,b],&[false;5]);let after=lower(&rule.into_iter().collect::<Vec<_>>(),&[false;5]);for x in 0..32{assert_eq!(scalar(&before,x),scalar(&after,x),"cube {a:?} {b:?}");cube_checks+=1;}}}}
 let mut seed=0x716793abcd489e63u64;fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut saved=0;let mut saved_t=0;
 for case in 0..4096{
  let mut old=Vec::new();for _ in 0..96{let mut q=[0,1,2,3,4,5];for i in(1..6).rev(){let j=rnd(&mut seed)as usize%(i+1);q.swap(i,j);}old.push(op(rnd(&mut seed)as usize%3,[q[0],q[1]],q[2]));}
  let(mut gates,frame)=lift(&old,6);let raw=lower(&gates,&frame);for x in 0..64{assert_eq!(scalar(&old,x),scalar(&raw,x),"frame case={case}");}
  for _ in 0..4{simplify(&mut gates,256);}let unfiltered=lower(&gates,&frame);
  let mut new=old.clone();let(a,b)=apply(&mut new);saved+=a;saved_t+=b;
  for x in 0..64{let y=scalar(&old,x);assert_eq!(y,scalar(&unfiltered,x),"rewrite case={case}");assert_eq!(y,scalar(&new,x),"accepted case={case}");assert_eq!(scalar(&new.iter().copied().rev().collect::<Vec<_>>(),y),x,"inverse case={case}");}
 }
 assert!(saved>0&&saved_t>0);eprintln!("Q793_NCT_FRAME_R02_PASS cube_rules={rules} cube_inputs={cube_checks} random_circuits=4096 exhaustive_inputs=262144 saved_ops={saved} saved_T={saved_t}");
}
