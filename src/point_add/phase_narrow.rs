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
fn cut(mode:usize)->usize{match mode{1100..=2715=>(mode-1000)/100,1..=3=>mode,9..=11=>1,12|14|15=>2,13|16|17=>3,18..=24=>mode-14,25|26=>1,_=>0}}
fn rewrite(ops:&[Op],s:&Site,mode:usize)->Vec<Op>{
 let n=cut(mode);assert!(((1..=26).contains(&mode)||(1100..=2715).contains(&mode))&&(1..=17).contains(&n)&&n<s.u.len());
 let mut out=Vec::new();
 if n>0{
  let low:BTreeSet<_>=s.u[..n].iter().chain(&s.v[..n]).chain(&s.c[..n]).copied().chain(s.seed).collect();
  let pivot=s.u[n-1];let mut high=vec![s.u[n],s.v[n]];if n<s.c.len(){high.push(s.c[n]);}
  let repl=match mode{1..=3|18..=24=>s.v[n-1],9|12|13=>pivot,25=>s.seed.unwrap(),_=>s.c[0]};
  let inv=matches!(mode,9|11|12|13|15|17);let mut sub=Vec::new();let mut saved=0;
  for mut o in ops[s.at..s.end].iter().copied(){
   let qs:Vec<_>=[o.q_control1,o.q_control2,o.q_target].into_iter().filter(|q|*q!=NO_QUBIT).collect();
   if !qs.iter().any(|q|low.contains(q)){out.push(o);continue;}
   if qs.iter().filter(|q|low.contains(q)).all(|q|*q==pivot)&&qs.iter().any(|q|high.contains(q))&&o.kind!=K::X{
    for q in [&mut o.q_control1,&mut o.q_control2,&mut o.q_target]{if *q==pivot{*q=repl;}}o.validate();sub.push(out.len());out.push(o);
   }else if o.kind==K::R{out.push(o);
   }else if o.kind==K::Hmr{o.kind=K::R;o.c_target=NO_BIT;out.push(o);
   }else if o.kind==K::CCX{saved+=1;}
  }
  assert_eq!(saved,n);assert_eq!(sub.len(),if n+1==s.u.len(){2}else{4});
  if inv{out.insert(*sub.last().unwrap()+1,gate(K::X,NO_QUBIT,repl));out.insert(sub[0],gate(K::X,NO_QUBIT,repl));}
  if mode>=1100{
   let code=(mode-1000)%100;assert!(code<16);let(mask,inv)=(code/2,code%2!=0);let mut pre=Vec::new();for(j,q)in [Some(s.u[n-1]),Some(s.v[n-1]),s.seed].into_iter().enumerate(){if mask>>j&1!=0{pre.push(gate(K::CX,q.expect("missing affine seed"),repl));}}if inv{pre.push(gate(K::X,NO_QUBIT,repl));}
   out.splice(*sub.last().unwrap()+1..*sub.last().unwrap()+1,pre.iter().rev().copied());out.splice(sub[0]..sub[0],pre);
  }
  if mode==26{
   let pre:Vec<_>=[s.u[0],s.v[0],s.seed.unwrap()].into_iter().map(|q|gate(K::CX,q,repl)).collect();
   out.splice(*sub.last().unwrap()+1..*sub.last().unwrap()+1,pre.iter().rev().copied());out.splice(sub[0]..sub[0],pre);
  }
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
 for _ in 0..16{
  let mut q=vec![0u64;1234];for p in s.u.iter().chain(&s.v).copied().chain(s.seed){q[p.0 as usize]=rnd();}let old=q.clone();let mut b=vec![0u64;maxbit];let mut phase=0;
  // Verify body at an active outer condition; HMR(target) is left to the caller.
  for o in &ops[2..ops.len()-1]{let cond=if o.c_condition==NO_BIT{u64::MAX}else{b[o.c_condition.0 as usize]};let t=o.q_target.0 as usize;match o.kind{
   K::X=>q[t]^=cond,K::CX=>q[t]^=q[o.q_control1.0 as usize]&cond,K::CCX=>q[t]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize]&cond,
   K::CZ=>phase^=q[t]&q[o.q_control1.0 as usize]&cond,
   K::R|K::Hmr=>{let r=rnd();phase^=q[t]&r&cond;q[t]&=!cond;if o.kind==K::Hmr{b[o.c_target.0 as usize]=r;}},_=>panic!("unexpected local op {:?}",o.kind)
  }}
  let n=cut(mode);let orig=s.seed.map_or(0,|p|old[p.0 as usize]);let mut borrow=match mode{
   1100..=2715=>{let code=(mode-1000)%100;let(mask,inv)=(code/2,code%2!=0);let mut p=if inv{u64::MAX}else{0};for(j,q)in [Some(s.u[n-1]),Some(s.v[n-1]),s.seed].into_iter().enumerate(){if mask>>j&1!=0{p^=old[q.unwrap().0 as usize];}}p},
   1..=3|18..=24=>old[s.v[n-1].0 as usize],4|10|14|16=>0,5|11|15|17=>u64::MAX,6=>!orig,7=>orig^old[s.u[0].0 as usize],8=>orig^!old[s.u[0].0 as usize],9|12|13=>!old[s.u[n-1].0 as usize],25=>orig,26=>old[s.u[0].0 as usize]^old[s.v[0].0 as usize]^orig,_=>unreachable!()
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
  if ((6..=8).contains(&mode)||mode>=25)&&s.seed.is_none(){continue;}
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);eprintln!("PHASE_PATCH at={} width={n} seed={seeded} mode={mode}",s.at);edits.push((s.at,s.end,rep));
 }
 eprintln!("PHASE_WIDTHS {hist:?}; edited {}",edits.len());let mut out=Vec::new();let mut last=0;
 for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}
/// Research-only cohort policy indexed by the following strict M2 boundary.
pub fn run_cohorts(ops:Vec<Op>,bounds:&[usize],policy:&[(usize,usize,usize,usize)])->Vec<Op>{
 let mut edits=Vec::new();let mut hist=BTreeMap::<(usize,usize,usize),usize>::new();let mut i=5300000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;let n=s.u.len();let seeded=usize::from(s.seed.is_some());let cohort=1120-bounds.partition_point(|&v|v<s.at);*hist.entry((cohort,n,seeded)).or_default()+=1;
  let modes:Vec<_>=policy.iter().filter(|&&(b,w,p,_)|(b==99||b==cohort)&&(w==0||w==n)&&(p==2||p==seeded)).map(|&(_,_,_,m)|m).collect();assert!(modes.len()<=1,"overlapping cohort policy");let Some(&mode)=modes.first()else{continue;};
  if ((6..=8).contains(&mode)||mode>=25)&&s.seed.is_none(){continue;}
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);eprintln!("PHASE_COHORT_PATCH at={} cohort={cohort} width={n} seed={seeded} mode={mode}",s.at);edits.push((s.at,s.end,rep));
 }
 eprintln!("PHASE_COHORT_WIDTHS {hist:?}; edited {}",edits.len());let mut out=Vec::new();let mut last=0;
 for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}
/// Bind every terminal native18 body to its complete operand/carry wiring.
/// Source indices are descriptive; comparison uses all remaining fields.
pub fn dump_bindings(ops:&[Op])->String{
 let mut rows=Vec::new();let mut i=5_300_000;
 while i+1<ops.len(){let Some(s)=catalog(ops,i)else{i+=1;continue;};i=s.end;if s.u.len()!=18||s.seed.is_none(){continue;}
  let fields:Vec<_>=[s.at as u64,ops[s.at].q_target.0,s.seed.unwrap().0].into_iter().chain(s.u.iter().chain(&s.v).chain(&s.c).map(|q|q.0)).collect();assert_eq!(fields.len(),56);rows.push(fields.iter().map(|q|q.to_string()).collect::<Vec<_>>().join(" "));
 }assert_eq!(rows.len(),144,"terminal body count");rows.join("\n")+"\n"
}
pub fn run_bound(ops:Vec<Op>,text:&str)->Vec<Op>{run_deep_bound(ops,text,4)}
pub fn run_deep_bound(ops:Vec<Op>,text:&str,deep:usize)->Vec<Op>{
 assert!((4..=17).contains(&deep));
 let expected:Vec<Vec<u64>>=text.lines().map(|l|l.split_whitespace().map(|s|s.parse().unwrap()).collect()).collect();assert_eq!(expected.len(),144);let mut index=0;let mut edits=Vec::new();let mut i=5_300_000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;if s.u.len()!=18||s.seed.is_none(){continue;}
  let actual:Vec<_>=[ops[s.at].q_target.0,s.seed.unwrap().0].into_iter().chain(s.u.iter().chain(&s.v).chain(&s.c).map(|q|q.0)).collect();assert!(index<expected.len());assert_eq!(actual,expected[index][1..],"terminal body binding {index}");let mode=match index{0=>1000+100*deep+4,1..=36=>18,37..=54=>3,55..=72=>2,73..=90=>1,_=>0};index+=1;if mode==0{continue;}let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);edits.push((s.at,s.end,rep));
 }
 assert_eq!(index,144);assert_eq!(edits.len(),91);let mut out=Vec::new();let mut last=0;for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}
/// Match canonical body identities even when other policies introduce additional
/// native18 bodies. Every canonical identity must still occur exactly once.
pub fn run_keyed(ops:Vec<Op>,text:&str)->Vec<Op>{
 let expected:Vec<Vec<u64>>=text.lines().map(|l|l.split_whitespace().map(|s|s.parse().unwrap()).collect()).collect();assert_eq!(expected.len(),144);let map:BTreeMap<Vec<u64>,usize>=expected.iter().enumerate().map(|(i,r)|(r[1..].to_vec(),i)).collect();assert_eq!(map.len(),144);let mut found=vec![false;144];let mut extras=0;let mut edits=Vec::new();let mut i=5_300_000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;if s.u.len()!=18||s.seed.is_none(){continue;}let actual:Vec<_>=[ops[s.at].q_target.0,s.seed.unwrap().0].into_iter().chain(s.u.iter().chain(&s.v).chain(&s.c).map(|q|q.0)).collect();let Some(&index)=map.get(&actual)else{extras+=1;continue;};assert!(!found[index],"duplicate canonical body identity {index}");found[index]=true;let mode=match index{0..=36=>18,37..=54=>3,55..=72=>2,73..=90=>1,_=>0};if mode==0{continue;}let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);edits.push((s.at,s.end,rep));
 }
 let missing:Vec<_>=found.iter().enumerate().filter(|(_,v)|!**v).map(|(i,_)|i).collect();eprintln!("KEYED_TERMINAL matched={} extras={extras} selected={} missing={missing:?}",144-missing.len(),edits.len());assert!(missing.is_empty(),"canonical body identities changed");assert_eq!(edits.len(),91);let mut out=Vec::new();let mut last=0;for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}
/// Predetermined small phase cohorts from the complete native-width catalog.
fn extra_mode(s:&Site)->Option<usize>{let b=s.at/500_000;match(s.u.len(),s.seed.is_some(),b){(17,false,12|13)=>Some(2),(11,false,12)=>Some(3),(20,true,_)=>Some(2),(19,false,15)=>Some(18),_=>None}}
pub fn dump_extra(ops:&[Op])->String{let mut rows=Vec::new();let mut i=5_300_000;while i+1<ops.len(){let Some(s)=catalog(ops,i)else{i+=1;continue;};i=s.end;let Some(mode)=extra_mode(&s)else{continue;};let vals:Vec<u64>=[mode as u64,s.at as u64,s.u.len()as u64,ops[s.at].q_target.0,s.seed.unwrap_or(NO_QUBIT).0].into_iter().chain(s.u.iter().chain(&s.v).chain(&s.c).map(|q|q.0)).collect();rows.push(vals.iter().map(|n|n.to_string()).collect::<Vec<_>>().join(" "));}assert_eq!(rows.len(),9);rows.join("\n")+"\n"}
pub fn run_extra(ops:Vec<Op>,text:&str)->Vec<Op>{let rows:Vec<Vec<u64>>=text.lines().map(|l|l.split_whitespace().map(|s|s.parse().unwrap()).collect()).collect();assert_eq!(rows.len(),9);let map:BTreeMap<Vec<u64>,usize>=rows.iter().enumerate().map(|(i,r)|(r[2..].to_vec(),i)).collect();assert_eq!(map.len(),9);let mut found=vec![false;9];let mut edits=Vec::new();let mut i=5_300_000;while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;let actual:Vec<_>=[s.u.len()as u64,ops[s.at].q_target.0,s.seed.unwrap_or(NO_QUBIT).0].into_iter().chain(s.u.iter().chain(&s.v).chain(&s.c).map(|q|q.0)).collect();let Some(&index)=map.get(&actual)else{continue;};assert!(!found[index]);found[index]=true;let mode=rows[index][0]as usize;let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);eprintln!("SMALL_PHASE_BOUND index={index} at={} width={} mode={mode}",s.at,s.u.len());edits.push((s.at,s.end,rep));}assert!(found.into_iter().all(|v|v));assert_eq!(edits.len(),9);let mut out=Vec::new();let mut last=0;for(at,end,rep)in edits{out.extend_from_slice(&ops[last..at]);out.extend(rep);last=end;}out.extend_from_slice(&ops[last..]);out
}

/// Apply the verified cut10 constructor to exactly one complete original body.
/// Other phase-table choices and every original occurrence remain unchanged.
pub fn run_single_bound(ops:Vec<Op>,text:&str)->Vec<Op>{
 use sha3::{Digest,Sha3_256};
 let fields:Vec<_>=text.split_whitespace().collect();assert_eq!(fields.len(),2);
 let expected=fields[0];let mode:usize=fields[1].parse().unwrap();assert_eq!(mode,2004);
 let mut selected=None;let mut i=5_300_000;
 while i+1<ops.len(){let Some(s)=catalog(&ops,i)else{i+=1;continue;};i=s.end;
  if s.u.len()!=18||s.seed.is_none(){continue;}
  let mut h=Sha3_256::new();for o in &ops[s.at..s.end]{for v in [o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
  if format!("{:x}",h.finalize())!=expected{continue;}
  assert!(selected.is_none(),"unique full special body");
  let rep=rewrite(&ops,&s,mode);verify(&s,&rep,mode);
  assert_eq!(ops[s.at..s.end].iter().filter(|o|o.kind==K::CCX).count()-rep.iter().filter(|o|o.kind==K::CCX).count(),10);
  assert_eq!(ops[s.at..s.end].iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count(),rep.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count());
  eprintln!("SINGLE_PHASE cut10 at{} exactbody{} original{} replacement{}",s.at,expected,s.end-s.at,rep.len());
  selected=Some((s.at,s.end,rep));
 }
 let(at,end,rep)=selected.expect("original special phase body must survive every prior policy");
 let mut out=Vec::new();out.extend_from_slice(&ops[..at]);out.extend(rep);out.extend_from_slice(&ops[end..]);out
}
