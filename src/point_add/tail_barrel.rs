//! Approximate only the final forward payload rotation: use rot4 instead of rot8.
//! Complete 508-Fredkin structural matching pins its original data/letter frame.
//! All e0..3 modes are exact; every RNG operation remains outside this unitary block.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
const N:usize=256;
fn cx(a:QubitId,t:QubitId)->Op{let mut o=Op::empty();o.kind=K::CX;o.q_control1=a;o.q_target=t;o}
fn ccx(a:QubitId,b:QubitId,t:QubitId)->Op{let mut o=Op::empty();o.kind=K::CCX;o.q_control1=a;o.q_control2=b;o.q_target=t;o}
fn fredkin(o:&[Op],i:usize)->Option<(QubitId,QubitId,QubitId)>{
 if i+2>=o.len(){return None;}
 let(a,b,c)=(&o[i],&o[i+1],&o[i+2]);
 if a.kind!=K::CX||b.kind!=K::CCX||c.kind!=K::CX||a.q_control1!=c.q_control1||a.q_target!=c.q_target||b.q_target!=a.q_control1||[a,b,c].iter().any(|o|o.c_condition!=NO_BIT){return None;}
 let host=if b.q_control1==a.q_target{b.q_control2}else if b.q_control2==a.q_target{b.q_control1}else{return None;};
 Some((host,a.q_target,a.q_control1))
}
fn pairs(axis:isize,par:usize)->Vec<(usize,usize)>{(0..N).filter(|i|par==2||i%2==par).filter_map(|i|{let j=(axis-i as isize).rem_euclid(N as isize)as usize;(i<j).then_some((i,j))}).collect()}
struct Block{start:usize,end:usize,k:[QubitId;3],t:Vec<QubitId>}
fn parse(ops:&[Op],start:usize)->Option<Block>{
 let units=[(0,0,4), (0,1,2), (-4,0,6), (-2,1,6), (-6,0,3), (-6,1,5), (-7,2,1)];
 let mut pos=start;let mut wires=vec![None;N];let mut k=[None;3];let mut trace=vec![];
 for &(axis,par,mask)in &units{
  let hostidx=if mask==4{2}else if mask==2||mask==6{1}else{0};
  for(a,b)in pairs(axis,par){
   let mut skips=0;
   while fredkin(ops,pos).is_none(){if pos>=ops.len()||ops[pos].kind!=K::CX||ops[pos].c_condition!=NO_BIT||skips>=4{return None;}trace.push((pos,0));pos+=1;skips+=1;}
   let(h,qa,qb)=fredkin(ops,pos)?;
   if let Some(q)=k[hostidx]{if q!=h{return None;}}else{k[hostidx]=Some(h);}
   for(index,q)in [(a,qa),(b,qb)]{if let Some(old)=wires[index]{if old!=q{return None;}}else{wires[index]=Some(q);}}
   trace.push((pos,mask));pos+=3;
  }
 }
 let t:Vec<_>=wires.into_iter().collect::<Option<_>>()?;let k:[QubitId;3]=[k[0]?,k[1]?,k[2]?];
 if t.iter().map(|q|q.0).collect::<std::collections::HashSet<_>>().len()!=N||k.iter().any(|x|t.contains(x))||k.iter().map(|q|q.0).collect::<std::collections::HashSet<_>>().len()!=3{return None;}
 let mut frame=[1,2,4];
 for(at,mask)in trace{
  if mask==0{let a=k.iter().position(|q|*q==ops[at].q_control1)?;let b=k.iter().position(|q|*q==ops[at].q_target)?;frame[b]^=frame[a];}
  else{let h=fredkin(ops,at)?.0;let hi=k.iter().position(|q|*q==h)?;if frame[hi]!=mask{return None;}}
 }
 if frame!=[1,2,4]{return None;}
 Some(Block{start,end:pos,k,t})
}
fn rot4(k:[QubitId;3],t:&[QubitId])->Vec<Op>{
 let mut out=vec![];
 for(axis,mask)in [(1,1),(0,3),(-2,2)]{
  let h=if mask==1{k[0]}else{k[1]};
  if mask==3{out.push(cx(k[0],k[1]));}
  for(a,b)in pairs(axis,2){out.extend([cx(t[b],t[a]),ccx(h,t[a],t[b]),cx(t[b],t[a])]);}
  if mask==3{out.push(cx(k[0],k[1]));}
 }
 out
}
fn check_low_modes(old:&[Op],new:&[Op],k:[QubitId;3],t:&[QubitId]) {
 let nq=t.iter().chain(k.iter()).map(|q|q.0 as usize+1).max().unwrap();
 let run=|ops:&[Op],q:&mut Vec<bool>|{for o in ops{assert_eq!(o.c_condition,NO_BIT);match o.kind{K::CX=>q[o.q_target.0 as usize]^=q[o.q_control1.0 as usize],K::CCX=>q[o.q_target.0 as usize]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize],_=>panic!("unexpected barrel operation")}}};
 for e in 0..4 {for basis in 0..=N {let mut q=vec![false;nq];for j in 0..3{q[k[j].0 as usize]=e>>j&1!=0;}if basis<N{q[t[basis].0 as usize]=true;}let mut p=q.clone();run(old,&mut q);run(new,&mut p);assert_eq!(p,q,"barrel low-mode mismatch e={e} basis={basis}");}}
}
pub(super) fn run(ops:Vec<Op>)->Vec<Op> {
 let mut blocks=Vec::new();let mut i=3_000_000;
 while i<3_400_000.min(ops.len()) {
  if let Some(b)=parse(&ops,i){i=b.end;blocks.push(b);}else{i+=1;}
 }
 assert_eq!(blocks.len(),14,"late forward rot8 catalog");
 let b=blocks.last().expect("final forward rot8");
 assert!(b.start>3_280_000&&b.end<3_320_000,"terminal full rot8 position");
 let replacement=rot4(b.k,&b.t);
 check_low_modes(&ops[b.start..b.end],&replacement,b.k,&b.t);
 assert_eq!(ops[b.start..b.end].iter().filter(|o|o.kind==K::CCX).count(),508);
 assert_eq!(replacement.iter().filter(|o|o.kind==K::CCX).count(),382);
 let mut out=Vec::with_capacity(ops.len());out.extend_from_slice(&ops[..b.start]);out.extend(replacement);out.extend_from_slice(&ops[b.end..]);
 eprintln!("TAIL_BARREL final forward rot8->rot4, saved126T, matched14 blocks");out
}
