use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
fn ccx(o:&Op)->Option<(QubitId,QubitId,QubitId)>{(o.kind==K::CCX&&o.c_condition==NO_BIT).then_some((o.q_control2,o.q_control1,o.q_target))}
fn cx(o:&Op,a:QubitId,b:QubitId)->bool{o.kind==K::CX&&o.c_condition==NO_BIT&&o.q_control1==a&&o.q_target==b}
fn phase(o:&Op,a:QubitId,b:QubitId,c:crate::circuit::BitId)->bool{o.kind==K::CZ&&o.c_condition==c&&((o.q_control1==a&&o.q_target==b)||(o.q_control1==b&&o.q_target==a))}
fn erase(o:&[Op],i:usize,t:QubitId,a:QubitId,b:QubitId)->bool{o[i].kind==K::Hmr&&o[i].q_target==t&&o[i].c_condition==NO_BIT&&phase(&o[i+1],a,b,o[i].c_target)}
fn chain(o:&Op,prev:QubitId)->Option<QubitId>{if o.c_condition!=NO_BIT{return None;}if o.kind==K::CX&&o.q_control1==prev{return Some(o.q_target);}if o.kind==K::CCX&&(o.q_control1==prev||o.q_control2==prev){return Some(o.q_target);}None}
fn erased(o:&[Op],i:usize,head:usize,prev:QubitId)->bool{let t=o[head].q_target;if o[i].kind!=K::Hmr||o[i].q_target!=t||o[i].c_condition!=NO_BIT{return false;}let c=&o[i+1];if c.kind!=K::CZ||c.c_condition!=o[i].c_target{return false;}let z=if c.q_control1==prev{c.q_target}else if c.q_target==prev{c.q_control1}else{return false;};cx(&o[head],prev,t)||ccx(&o[head]).is_some_and(|(a,b,_)|(a==prev&&b==z)||(a==z&&b==prev))}
pub(super) fn run(ops:Vec<Op>,divn:usize,muln:usize)->Vec<Op>{let mut somes=vec![];let mut nones=vec![];let mut counts=[0;2];let mut d=0;
 for i in 7..ops.len()-26{
  if ops[i-1].kind==K::PushCondition{d+=1;}if ops[i-1].kind==K::PopCondition{d-=1;}
  let Some((gw,z5,p5))=ccx(&ops[i])else{continue;};let Some(p6)=chain(&ops[i+1],p5)else{continue;};let Some(p7)=chain(&ops[i+2],p6)else{continue;};
  if let Some(p8)=chain(&ops[i+3],p7){
   let out=ops[i+4].q_target;let k3=ops[i+6].q_target;let k2=ops[i+8].q_target;let k1=ops[i+10].q_target;
   if ![(4,gw,out),(5,p8,out),(6,gw,k3),(7,p8,k3),(8,p6,k2),(9,p8,k2),(10,gw,k1),(11,p5,k1),(12,p6,k1),(13,p7,k1)].iter().all(|&(j,a,b)|cx(&ops[i+j],a,b)){continue;}
   if ![(14,3,p7),(16,2,p6),(18,1,p5),(20,0,gw)].iter().all(|&(j,h,p)|erased(&ops,i+j,i+h,p)){continue;}
   let plain=ops[i-6].kind==K::CCX&&ops[i-6].q_target==gw&&cx(&ops[i-3],gw,out)&&cx(&ops[i-1],gw,k2)&&ops[i+22].kind==K::Hmr&&ops[i+22].q_target==gw;
   eprintln!("some {i} end{} depth{d} plain{} gw{} z{:?} out{} k{:?}",i+22,plain as u8,gw.0,[z5.0,0,0,0],out.0,[k1.0,k2.0,k3.0]);counts[0]+=1;somes.push((i,gw));
  }else if ops[i+3].kind==K::CZ{
   let z8=if ops[i+3].q_control1==p7{ops[i+3].q_target}else if ops[i+3].q_target==p7{ops[i+3].q_control1}else{continue;};if ops[i+3].c_condition!=NO_BIT{continue;}
   if ![(4,2,p6),(6,1,p5),(8,0,gw)].iter().all(|&(j,h,p)|erased(&ops,i+j,i+h,p)){continue;}
   let plain=ops[i-1].kind==K::CCX&&ops[i-1].q_target==gw&&ops[i+10].kind==K::Hmr&&ops[i+10].q_target==gw;
   eprintln!("none {i} end{} depth{d} plain{} gw{} z{:?}",i+10,plain as u8,gw.0,[z5.0,0,0,0]);counts[1]+=1;nones.push((i,gw,plain));
  }
 }
 eprintln!("CAP3_CATALOG some{} none{}",counts[0],counts[1]);
 assert!(divn<=3&&muln<=3&&divn+muln>0);let n=divn+muln;assert_eq!(counts,[240,240]);
 let mut ss=vec![];let mut ns=vec![];for (w,n)in[(0,divn),(1,muln)]{ss.extend(somes[w*120..(w+1)*120].iter().rev().take(n).copied());ns.extend(nones[w*120..(w+1)*120].iter().take(n).copied());}
 let mut del=vec![false;ops.len()];let mut ins=std::collections::BTreeMap::new();
 for &(i,gw)in ss.iter(){let scratch:Vec<_>=(0..4).map(|j|ops[i+j].q_target).collect();assert_eq!(scratch.iter().map(|q|q.0).collect::<std::collections::HashSet<_>>().len(),4);assert!(!scratch.contains(&gw));
  for j in (0..14).chain([15,17,19,21]){del[i+j]=true;}eprintln!("CAP3 some at{i} gw{} removed4headcomputes/10fanouts/4repairs, retains4HMR",gw.0);
 }
 for &(i,gw,plain)in ns.iter(){for j in (0..4).chain([5,7,9]){del[i+j]=true;}if plain{let mut z=Op::empty();z.kind=K::Z;z.q_target=gw;ins.insert(i,z);}else{assert_eq!(ops[i-1].kind,K::Z);assert_eq!(ops[i-1].q_target,gw);assert_eq!(ops[i-1].c_condition,NO_BIT);assert_eq!(ops[i-2].kind,K::Z);assert_ne!(ops[i-2].q_target,gw);del[i-1]=true;}eprintln!("CAP3 none at{i} gw{} plain{plain}, applyphasep4, retains3HMR",gw.0);}
 let mut out=vec![];for(i,o)in ops.iter().enumerate(){if let Some(z)=ins.get(&i){out.push(*z);}if !del[i]{out.push(*o);}}
 assert_eq!(ops.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count(),out.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count());let before=ops.iter().filter(|o|o.kind==K::CCX).count();let after=out.iter().filter(|o|o.kind==K::CCX).count();eprintln!("CAP3 edited{n}ticks emittedCCXsaved{}",before-after);out
}
