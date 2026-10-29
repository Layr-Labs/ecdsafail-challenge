use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
use std::collections::{BTreeMap,BTreeSet};
fn is(o:&Op,k:K,a:QubitId,b:QubitId,t:QubitId)->bool{o.kind==k&&o.q_control1==a&&o.q_control2==b&&o.q_target==t&&o.c_condition==NO_BIT}
fn cx(o:&Op,a:QubitId,t:QubitId)->bool{is(o,K::CX,a,NO_QUBIT,t)}
fn cz(o:&Op,a:QubitId,t:QubitId)->bool{is(o,K::CZ,a,NO_QUBIT,t)}
fn x(o:&Op,t:QubitId)->bool{is(o,K::X,NO_QUBIT,NO_QUBIT,t)}
fn gate(k:K,a:QubitId,t:QubitId)->Op{let mut o=Op::empty();o.kind=k;o.q_control1=a;o.q_target=t;o.validate();o}
fn cc(o:&Op,a:QubitId,b:QubitId)->Option<QubitId>{(o.kind==K::CCX&&o.c_condition==NO_BIT&&((o.q_control1==a&&o.q_control2==b)||(o.q_control1==b&&o.q_control2==a))).then_some(o.q_target)}
#[derive(Debug)]struct Site{at:usize,end:usize,u:Vec<QubitId>,v:Vec<QubitId>,c:Vec<QubitId>,seed:Option<QubitId>}
fn catalog(o:&[Op],at:usize)->Option<Site>{
 if !(o[at].kind==K::Hmr&&o[at].c_condition==NO_BIT&&o[at+1].kind==K::PushCondition&&o[at+1].c_condition==o[at].c_target){return None;}
 let mut j=at+2;let mut u=Vec::new();while j<o.len()&&o[j].kind==K::X&&o[j].c_condition==NO_BIT{u.push(o[j].q_target);j+=1;}
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
 if !(o[j].kind==K::CZ&&o[j].q_control1==u[n-1]&&o[j].c_condition==NO_BIT){return None;}v.push(o[j].q_target);
 if !(cz(&o[j+1],u[n-1],u[n-2])&&cz(&o[j+2],v[n-1],u[n-2])){return None;}j+=3;
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
 if o[j].kind!=K::PopCondition{return None;}j+=1;
 let qs:BTreeSet<_>=u.iter().chain(&v).chain(&c).copied().chain(seed).collect();
 if qs.len()!=3*n-1+usize::from(seed.is_some()){return None;}
 Some(Site{at,end:j,u,v,c,seed})
}
fn cut(mode:usize)->usize{match mode{1..=3=>mode,9..=11=>1,12|14|15=>2,13|16|17=>3,18..=24=>mode-14,_=>0}}
fn rewrite(ops:&[Op],s:&Site,mode:usize)->Vec<Op>{
 let n=cut(mode);assert!((1..=24).contains(&mode)&&n+3<s.u.len());
 let mut out=Vec::new();
 if n>0{
  let low:BTreeSet<_>=s.u[..n].iter().chain(&s.v[..n]).chain(&s.c[..n]).copied().chain(s.seed).collect();
  let pivot=s.u[n-1];let high=[s.u[n],s.v[n],s.c[n]];
  let repl=match mode{1..=3|18..=24=>s.v[n-1],9|12|13=>pivot,_=>s.c[0]};
  let inv=matches!(mode,9|11|12|13|15|17);let mut sub=Vec::new();let mut saved=0;
  for mut o in ops[s.at..s.end].iter().copied(){
   let qs:Vec<_>=[o.q_control1,o.q_control2,o.q_target].into_iter().filter(|q|*q!=NO_QUBIT).collect();
   if !qs.iter().any(|q|low.contains(q)){out.push(o);continue;}
   if qs.iter().filter(|q|low.contains(q)).all(|q|*q==pivot)&&qs.iter().any(|q|high.contains(q))&&o.kind!=K::X{
    for q in [&mut o.q_control1,&mut o.q_control2,&mut o.q_target]{if *q==pivot{*q=repl;}}o.validate();sub.push(out.len());out.push(o);
   }else if o.kind==K::R{out.push(o);
   }else if o.kind==K::Hmr{out.push(o);
   }else if o.kind==K::CCX{saved+=1;}
  }
  assert_eq!(saved,n);assert_eq!(sub.len(),4);
  if inv{out.insert(*sub.last().unwrap()+1,gate(K::X,NO_QUBIT,repl));out.insert(sub[0],gate(K::X,NO_QUBIT,repl));}
 }else if mode==4||mode==5{
  for mut o in ops[s.at..s.end].iter().copied(){
   if let Some(seed)=s.seed{
    if cx(&o,s.u[0],seed){continue;}
    for q in [&mut o.q_control1,&mut o.q_control2,&mut o.q_target]{if *q==seed{*q=s.u[0];}}o.validate();
   }
   let invert=mode==5&&((o.kind==K::CCX&&o.q_target==s.c[0])||(o.kind==K::CZ&&o.q_control1==s.u[0]&&o.q_target==s.v[0]));
   if invert{out.push(gate(K::X,NO_QUBIT,s.u[0]));}out.push(o);if invert{out.push(gate(K::X,NO_QUBIT,s.u[0]));}
  }
 }else{
  let Some(seed)=s.seed else{return ops[s.at..s.end].to_vec()};
  let mut pre=Vec::new();if mode==6||mode==8{pre.push(gate(K::X,NO_QUBIT,seed));}if mode==7||mode==8{pre.push(gate(K::CX,s.u[0],seed));}
  out.extend_from_slice(&ops[s.at..s.at+2]);out.extend(pre.iter().copied());out.extend_from_slice(&ops[s.at+2..s.end-1]);out.extend(pre.into_iter().rev());out.push(ops[s.end-1]);
 }
 out
}
fn verify(s:&Site,ops:&[Op],mode:usize){
 let maxbit=ops.iter().filter_map(|o|(o.c_target!=NO_BIT).then_some(o.c_target.0)).max().unwrap()as usize+1;
 let mut state=s.at as u64+1;let mut rnd=||{state=state.wrapping_add(0x9E3779B97F4A7C15);let mut z=state;z=(z^(z>>30)).wrapping_mul(0xBF58476D1CE4E5B9);z=(z^(z>>27)).wrapping_mul(0x94D049BB133111EB);z^(z>>31)};
 for _ in 0..8{
  let mut q=vec![0u64;1234];for p in s.u.iter().chain(&s.v).copied().chain(s.seed){q[p.0 as usize]=rnd();}let old=q.clone();let mut b=vec![0u64;maxbit];let mut phase=0;
  // Verify body at an active outer condition; HMR(target) is left to the caller.
  for o in &ops[2..ops.len()-1]{let cond=if o.c_condition==NO_BIT{u64::MAX}else{b[o.c_condition.0 as usize]};let t=o.q_target.0 as usize;match o.kind{
   K::X=>q[t]^=cond,K::CX=>q[t]^=q[o.q_control1.0 as usize]&cond,K::CCX=>q[t]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize]&cond,
   K::CZ=>phase^=q[t]&q[o.q_control1.0 as usize]&cond,
   K::R|K::Hmr=>{let r=rnd();phase^=q[t]&r&cond;q[t]&=!cond;if o.kind==K::Hmr{b[o.c_target.0 as usize]=r;}},_=>panic!("unexpected local op {:?}",o.kind)
  }}
  let n=cut(mode);let orig=s.seed.map_or(0,|p|old[p.0 as usize]);let mut borrow=match mode{
   1..=3|18..=24=>old[s.v[n-1].0 as usize],4|10|14|16=>0,5|11|15|17=>u64::MAX,6=>!orig,7=>orig^old[s.u[0].0 as usize],8=>orig^!old[s.u[0].0 as usize],9|12|13=>!old[s.u[n-1].0 as usize],_=>unreachable!()
  };
  for z in n..s.u.len(){let(a,b)=(!old[s.u[z].0 as usize],old[s.v[z].0 as usize]);borrow=(a&b)|((a|b)&borrow);}
  assert_eq!(phase,borrow,"phase mode{mode} site{}",s.at);assert_eq!(q,old,"data/garbage mode{mode} site{}",s.at);
 }
}
/// Apply a fixed cohort policy (band 99, width 0, seed 2 are wildcards).
pub fn run(ops:Vec<Op>,policy:&[(usize,usize,usize,usize)])->Vec<Op>{
 let mut edits=Vec::new();let mut hist=BTreeMap::<(usize,usize,usize),usize>::new();let mut i=5300000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;let n=s.u.len();let seeded=usize::from(s.seed.is_some());*hist.entry((s.at/500000,n,seeded)).or_default()+=1;
  let modes:Vec<_>=policy.iter().filter(|&&(b,w,p,_)|(b==99||b==s.at/500000)&&(w==0||w==n)&&(p==2||p==seeded)).map(|&(_,_,_,m)|m).collect();assert!(modes.len()<=1,"overlapping policy");let Some(&mode)=modes.first()else{continue;};
  if mode==0{for m in 1..=17{if cut(m)+3>=n||(6..=8).contains(&m)&&s.seed.is_none(){continue;}let rep=rewrite(&ops,&s,m);verify(&s,&rep,m);}continue;}
  if (6..=8).contains(&mode)&&s.seed.is_none(){continue;}
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);eprintln!("PHASE_PATCH at={} width={n} seed={seeded} mode={mode}",s.at);edits.push((s.at,s.end,rep));
 }
 eprintln!("PHASE_WIDTHS {hist:?}; edited {}",edits.len());let mut out=Vec::new();let mut last=0;
 for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}

/// Fixed source-index intervals over the frozen verified prefix.
/// Selection uses the original complete stream before collecting any edits.
pub fn run_ranges(ops:Vec<Op>,policy:&[(usize,usize,usize,usize,usize)])->Vec<Op>{
 let mut edits=Vec::new();let mut i=5300000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;let n=s.u.len();let seeded=usize::from(s.seed.is_some());
  let modes:Vec<_>=policy.iter().filter(|&&(lo,hi,w,p,_)|s.at>=lo&&s.at<hi&&n==w&&seeded==p).map(|&(_,_,_,_,m)|m).collect();assert!(modes.len()<=1,"overlapping phase intervals");let Some(&mode)=modes.first()else{continue;};
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);eprintln!("PHASE_RANGE_PATCH at={} width={n} seed={seeded} mode={mode}",s.at);edits.push((s.at,s.end,rep));
 }
 assert_eq!(edits.len(),91,"fixed terminal native18 phase cohort count");let mut out=Vec::new();let mut last=0;
 for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}

/// Strict content-bound substitution of the verified61-body terminal policy.
/// The original full-body hash includes every operand, target, scratch and RNG slot.
pub fn run_bound(ops:Vec<Op>,table:&str)->Vec<Op>{
 use sha3::{Digest,Sha3_256};
 let wanted:BTreeMap<String,usize>=table.lines().filter(|l|!l.trim().is_empty()).map(|l|{let a:Vec<_>=l.split_whitespace().collect();(a[0].to_owned(),a[1].parse().unwrap())}).collect();
 assert_eq!(wanted.len(),61);let mut hits=BTreeSet::new();let mut edits=Vec::new();let mut i=0;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;
  if ![16,17].contains(&s.u.len()){continue;}
  let mut h=Sha3_256::new();for o in &ops[s.at..s.end]{for v in [o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
  let key=format!("{:x}",h.finalize());let Some(&mode)=wanted.get(&key)else{continue;};assert!(hits.insert(key),"duplicate bound phase body");
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);edits.push((s.at,s.end,rep));
 }
 assert_eq!(hits.len(),61,"all original terminal bodies survive lambda exclusion");
 eprintln!("PHASE_BOUND matched {} exact full bodies",hits.len());
 let mut out=Vec::new();let mut last=0;for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}
