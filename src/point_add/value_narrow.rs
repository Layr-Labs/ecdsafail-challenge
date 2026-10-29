use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
use std::collections::{BTreeMap,BTreeSet};
fn is(o:&Op,k:K,a:QubitId,b:QubitId,t:QubitId)->bool{o.kind==k&&o.q_control1==a&&o.q_control2==b&&o.q_target==t&&o.c_condition==NO_BIT}
fn cx(o:&Op,a:QubitId,t:QubitId)->bool{is(o,K::CX,a,NO_QUBIT,t)}
fn x(o:&Op,t:QubitId)->bool{is(o,K::X,NO_QUBIT,NO_QUBIT,t)}
fn cc(o:&Op,a:QubitId,b:QubitId)->Option<QubitId>{(o.kind==K::CCX&&o.c_condition==NO_BIT&&((o.q_control1==a&&o.q_control2==b)||(o.q_control1==b&&o.q_control2==a))).then_some(o.q_target)}
#[derive(Debug)]struct Site{at:usize,end:usize,u:Vec<QubitId>,v:Vec<QubitId>,c:Vec<QubitId>,seed:Option<QubitId>}
fn catalog(o:&[Op],at:usize)->Option<Site>{
 let mut j=at;let mut u=Vec::new();while j<o.len()&&o[j].kind==K::X&&o[j].c_condition==NO_BIT{u.push(o[j].q_target);j+=1;}
 let n=u.len();if !(5..=40).contains(&n)||j+16*n>=o.len(){return None;}
 if !(o[j].kind==K::CX&&o[j].q_control1==u[0]&&o[j].c_condition==NO_BIT){return None;}
 let mut v=vec![o[j].q_target];j+=1;let mut seed=None;
 if o[j].kind==K::CX&&o[j].q_control1==u[0]&&o[j].c_condition==NO_BIT{seed=Some(o[j].q_target);j+=1;}
 let mut c=vec![cc(&o[j],seed.unwrap_or(u[0]),v[0])?];j+=1;
 if !cx(&o[j],c[0],u[0]){return None;}j+=1;
 for z in 1..n-1{
  if !(o[j].kind==K::CX&&o[j].q_control1==u[z]&&o[j].c_condition==NO_BIT){return None;}v.push(o[j].q_target);
  if !cx(&o[j+1],u[z],u[z-1]){return None;}c.push(cc(&o[j+2],u[z-1],v[z])?);if !cx(&o[j+3],c[z],u[z]){return None;}j+=4;
 }
 if !cx(&o[j],u[n-2],u[n-1]){return None;}
 if !(o[j+1].kind==K::CX&&o[j+1].q_control1==u[n-2]&&o[j+1].c_condition==NO_BIT){return None;}v.push(o[j+1].q_target);
 let target=cc(&o[j+2],u[n-1],v[n-1])?;
 if !(cx(&o[j+3],u[n-2],target)&&cx(&o[j+4],u[n-2],v[n-1])&&cx(&o[j+5],u[n-2],u[n-1])){return None;}j+=6;
 let hmr=|o:&Op,q:QubitId|o.kind==K::Hmr&&o.q_target==q&&o.c_condition==NO_BIT;
 let czif=|o:&Op,a:QubitId,b:QubitId,m|o.kind==K::CZ&&o.q_control1==a&&o.q_target==b&&o.c_condition==m;
 for z in (1..n-1).rev(){
  if !(cx(&o[j],c[z],u[z])&&hmr(&o[j+1],c[z])&&czif(&o[j+2],u[z-1],v[z],o[j+1].c_target)&&cx(&o[j+3],u[z],u[z-1])&&cx(&o[j+4],u[z],v[z])){return None;}j+=5;
 }
 if !(cx(&o[j],c[0],u[0])&&hmr(&o[j+1],c[0])&&czif(&o[j+2],seed.unwrap_or(u[0]),v[0],o[j+1].c_target)){return None;}j+=3;
 if let Some(p)=seed{if !cx(&o[j],u[0],p){return None;}j+=1;}
 if !cx(&o[j],u[0],v[0]){return None;}j+=1;
 for &q in &c{if !is(&o[j],K::R,NO_QUBIT,NO_QUBIT,q){return None;}j+=1;}
 for &q in &u{if !x(&o[j],q){return None;}j+=1;}
 let qs:BTreeSet<_>=u.iter().chain(&v).chain(&c).copied().chain(seed).chain([target]).collect();
 if qs.len()!=3*n+usize::from(seed.is_some()){return None;}
 Some(Site{at,end:j,u,v,c,seed})
}
fn verify(s:&Site,ops:&[Op],cut:usize,target:QubitId,pred:usize){
 let maxbit=ops.iter().filter_map(|o|(o.c_target!=NO_BIT).then_some(o.c_target.0)).max().unwrap()as usize+1;
 let mut state=s.at as u64+1;let mut rnd=||{state=state.wrapping_add(0x9E3779B97F4A7C15);let mut z=state;z=(z^(z>>30)).wrapping_mul(0xBF58476D1CE4E5B9);z=(z^(z>>27)).wrapping_mul(0x94D049BB133111EB);z^(z>>31)};
 for _ in 0..16{
  let mut q=vec![0u64;1234];for p in s.u.iter().chain(&s.v).copied().chain(s.seed).chain([target]){q[p.0 as usize]=rnd();}let old=q.clone();let mut b=vec![0u64;maxbit];let mut phase=0;
  for o in ops{let cond=if o.c_condition==NO_BIT{u64::MAX}else{b[o.c_condition.0 as usize]};let t=o.q_target.0 as usize;match o.kind{
   K::X=>q[t]^=cond,K::CX=>q[t]^=q[o.q_control1.0 as usize]&cond,K::CCX=>q[t]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize]&cond,
   K::CZ=>phase^=q[t]&q[o.q_control1.0 as usize]&cond,
   K::R|K::Hmr=>{let r=rnd();phase^=q[t]&r&cond;q[t]&=!cond;if o.kind==K::Hmr{b[o.c_target.0 as usize]=r;}},_=>panic!("unexpected local op {:?}",o.kind)
  }}
  let mut borrow=match pred{0=>old[s.v[cut-1].0 as usize],1=>!old[s.u[cut-1].0 as usize],2=>0,3=>u64::MAX,4=>old[s.seed.unwrap().0 as usize],5=>old[s.u[0].0 as usize]^old[s.v[0].0 as usize]^old[s.seed.unwrap().0 as usize],_=>unreachable!()};for z in cut..s.u.len(){let(a,b)=(!old[s.u[z].0 as usize],old[s.v[z].0 as usize]);borrow=(a&b)|((a|b)&borrow);}
  assert_eq!(q[target.0 as usize],old[target.0 as usize]^borrow,"local value site{}",s.at);assert_eq!(phase,0,"local phase site{}",s.at);q[target.0 as usize]=old[target.0 as usize];assert_eq!(q,old,"local data/garbage site{}",s.at);
 }
}
pub fn describe(ops:&[Op]){
 let(mut depth,mut i)=(0,0);
 while i<ops.len(){if ops[i].kind==K::PushCondition{depth+=1;}else if ops[i].kind==K::PopCondition{depth-=1;}
  if i<5300000||depth!=0||ops[i].kind!=K::X{i+=1;continue;}let Some(s)=catalog(ops,i)else{i+=1;continue;};i=s.end;
  let target=ops[s.at..s.end].iter().filter(|o|o.kind==K::CCX).last().unwrap().q_target;
  eprintln!("VALUE_SITE {} {} {} {} {:?} {:?}",s.at,s.u.len(),s.seed.unwrap_or(NO_QUBIT).0,target.0,s.u.iter().map(|q|q.0).collect::<Vec<_>>(),s.v.iter().map(|q|q.0).collect::<Vec<_>>());
 }
}
/// Checked inverse-value comparators only; keep every reference random draw.
pub fn run(ops:Vec<Op>,from:usize,width:usize,cut:usize)->Vec<Op>{run_with(ops,from,width,cut,0,usize::MAX,0)}
pub fn run_with(ops:Vec<Op>,from:usize,width:usize,cut:usize,skip:usize,take:usize,pred:usize)->Vec<Op>{
 assert!(pred<=5);
 let mut edits=Vec::new();let mut hist=BTreeMap::<usize,usize>::new();let mut depth=0;let mut i=0;
 while i<ops.len(){
  if ops[i].kind==K::PushCondition{depth+=1;}else if ops[i].kind==K::PopCondition{depth-=1;}
  if i<from||depth!=0||ops[i].kind!=K::X{i+=1;continue;}
  let Some(s)=catalog(&ops,i)else{i+=1;continue;};let n=s.u.len();*hist.entry(n).or_default()+=1;i=s.end;
  let ordinal=hist[&n]-1;if width!=0&&n!=width||cut==0||ordinal<skip||ordinal>=skip.saturating_add(take){continue;}
  assert!(cut+3<n);let mut low:BTreeSet<_>=s.u[..cut].iter().chain(&s.v[..cut]).chain(&s.c[..cut]).copied().chain(s.seed).collect();low.remove(&NO_QUBIT);
  assert!(pred<4||cut==1&&s.seed.is_some());
  let pivot=s.u[cut-1];let repl=match pred{0=>s.v[cut-1],1=>pivot,4=>s.seed.unwrap(),_=>s.c[0]};let high=[s.u[cut],s.v[cut],s.c[cut]];let mut sub=Vec::new();
  let mut out=Vec::new();let mut ccx_cut=0;
  for mut o in ops[s.at..s.end].iter().copied(){
   let qs:Vec<_>=[o.q_control1,o.q_control2,o.q_target].into_iter().filter(|q|*q!=NO_QUBIT).collect();
   if !qs.iter().any(|q|low.contains(q)){out.push(o);continue;}
   if qs.iter().filter(|q|low.contains(q)).all(|q|*q==pivot)&&qs.iter().any(|q|high.contains(q))&&o.kind!=K::X{
    for q in [&mut o.q_control1,&mut o.q_control2,&mut o.q_target]{if *q==pivot{*q=repl;}}o.validate();sub.push(out.len());out.push(o);
   }else if o.kind==K::R{out.push(o);
   }else if o.kind==K::Hmr{o.kind=K::R;o.c_target=NO_BIT;out.push(o);
   }else if o.kind==K::CCX{ccx_cut+=1;}
  }
  assert_eq!(ccx_cut,cut);assert_eq!(sub.len(),4);if pred==1||pred==3{let mut o=Op::empty();o.kind=K::X;o.q_target=repl;o.validate();out.insert(sub[3]+1,o);out.insert(sub[0],o);}
  if pred==5{
   let pre:Vec<_>=[s.u[0],s.v[0],s.seed.unwrap()].into_iter().map(|q|{let mut o=Op::empty();o.kind=K::CX;o.q_control1=q;o.q_target=repl;o.validate();o}).collect();
   out.splice(sub[3]+1..sub[3]+1,pre.iter().rev().copied());out.splice(sub[0]..sub[0],pre);
  }
  let target=ops[s.at..s.end].iter().filter(|o|o.kind==K::CCX).last().unwrap().q_target;verify(&s,&out,cut,target,pred);eprintln!("VALUE_NARROW at={} width={n} ordinal={ordinal} cut={cut} pred={pred}",s.at);edits.push((s.at,s.end,out));
 }
 eprintln!("VALUE_WIDTHS {hist:?}; edited {}",edits.len());let mut out=Vec::new();let mut last=0;
 for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}


/// Six verified terminal multiply value bodies, disjoint from native24.
pub(super) fn verified_six(ops:Vec<Op>)->Vec<Op>{
 let count=|o:&[Op]|o.iter().filter(|x|x.kind==K::CCX).count();let before=count(&ops);let mut ops=ops;
 for(skip,cut)in[(3,1),(2,3),(1,5),(0,9)]{let before=count(&ops);ops=run_with(ops,5_300_000,17,cut,skip,1,0);assert_eq!(before-count(&ops),cut);}
 let prior=count(&ops);ops=run_with(ops,5_300_000,16,3,0,2,0);assert_eq!(prior-count(&ops),6);
 assert_eq!(before-count(&ops),24);ops
}
