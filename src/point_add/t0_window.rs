use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
fn cx(o:&Op,a:QubitId,t:QubitId)->bool{o.kind==K::CX&&o.c_condition==NO_BIT&&o.q_control1==a&&o.q_target==t}
fn cz(o:&Op,a:QubitId,t:QubitId,m:crate::circuit::BitId)->bool{o.kind==K::CZ&&o.c_condition==m&&((o.q_control1==a&&o.q_target==t)||(o.q_control1==t&&o.q_target==a))}
fn ccx(o:&Op,a:QubitId,b:QubitId)->bool{o.kind==K::CCX&&o.c_condition==NO_BIT&&((o.q_control1==a&&o.q_control2==b)||(o.q_control1==b&&o.q_control2==a))}
#[derive(Debug)]struct Site{at:usize,begin:usize,end:usize,v:Vec<QubitId>,b:Vec<QubitId>,c:Vec<QubitId>,head:Vec<(usize,usize)>,erase:Vec<(usize,usize)>,full:bool,out:Option<QubitId>}
fn parse(o:&[Op],at:usize)->Option<Site>{
 if at+200>=o.len(){return None;}
 let sg=o[at].q_control1;let mut v=vec![];
 for j in 0..12{if !cx(&o[at+j],sg,o[at+j].q_target){return None;}v.push(o[at+j].q_target);}
 let mut begin=at+12;
 let phase=o[begin].kind==K::Hmr&&o[begin].c_condition==NO_BIT&&o[begin+1].kind==K::PushCondition&&o[begin+1].c_condition==o[begin].c_target;
 if phase{begin+=2;}
 let mut p=begin;let cin=o[p].q_control1;let mut c=vec![cin];let mut b=vec![];let mut head=vec![];
 // A phase compare omits its final AND. A full compare has an output CX.
 let mut full=false;let mut out=None;
 for j in 0..12{
  let start=p;
  if !cx(&o[p],c[j],v[j])||o[p+1].kind!=K::CX||o[p+1].c_condition!=NO_BIT||o[p+1].q_control1!=c[j]{return None;}
  b.push(o[p+1].q_target);p+=2;
  if ccx(&o[p],v[j],b[j]){c.push(o[p].q_target);p+=1;}
  else if j==0&&o[p].kind==K::CX&&o[p].q_control1==cin&&o[p].c_condition==NO_BIT{c.push(o[p].q_target);}
  else if j==0&&phase&&o[p].kind==K::PushCondition&&o[p].c_condition==o[at+12].c_target&&o[p+1].kind==K::CX&&o[p+1].q_control1==b[0]&&o[p+1].c_condition==NO_BIT&&o[p+2].kind==K::PopCondition{c.push(o[p+1].q_target);p+=3;}
  else if j==11&&cz(&o[p],v[j],b[j],NO_BIT){
   p+=1;if !cx(&o[p],c[j],v[j])||!cx(&o[p+1],c[j],b[j]){return None;}p+=2;
   if !(o[p].kind==K::X&&o[p].q_target==c[j]&&o[p].c_condition==NO_BIT&&o[p+1].kind==K::Z&&o[p+1].q_target==c[j]&&o[p+1].c_condition==NO_BIT&&o[p+2].kind==K::X&&o[p+2].q_target==c[j]&&o[p+2].c_condition==NO_BIT){return None;}p+=3;break;
  }else{return None;}
  if !cx(&o[p],c[j],c[j+1]){return None;}p+=1;head.push((start,p));
 }
 if c.len()==13 {full=true;if o[p].kind!=K::CX||o[p].c_condition!=NO_BIT||o[p].q_control1!=c[12]{return None;}out=Some(o[p].q_target);p+=1;}
 let n=if full{12}else{11};let mut erase=vec![(0,0);n];
 for j in(0..n).rev(){let start=p;if !cx(&o[p],c[j],c[j+1]){return None;}p+=1;
  if !(o[p].kind==K::Hmr&&o[p].q_target==c[j+1]&&o[p].c_condition==NO_BIT&&cz(&o[p+1],v[j],b[j],o[p].c_target)){return None;}p+=2;
  if !cx(&o[p],c[j],v[j])||!cx(&o[p+1],c[j],b[j]){return None;}p+=2;erase[j]=(start,p);
 }
 if phase{
  if full{return None;}
  if !(o[p].kind==K::X&&o[p].q_target==cin&&o[p].c_condition==NO_BIT&&o[p+1].kind==K::Z&&o[p+1].q_target==cin&&o[p+1].c_condition==NO_BIT&&o[p+2].kind==K::X&&o[p+2].q_target==cin&&o[p+2].c_condition==NO_BIT&&o[p+3].kind==K::PopCondition){return None;}p+=4;
 }else if !full{return None;}
 for j in 0..12{if !cx(&o[p+j],sg,v[j]){return None;}}
 Some(Site{at,begin,end:p,v,b,c,head,erase,full,out})
}
pub fn catalog(ops:&[Op]){let mut n=0;for i in 0..ops.len().saturating_sub(250){if let Some(s)=parse(ops,i){n+=1;eprintln!("T0_CAND at{} begin{} end{} full{} v{:?} b{:?} c{:?}",s.at,s.begin,s.end,s.full as u8,s.v.iter().map(|q|q.0).collect::<Vec<_>>(),s.b.iter().map(|q|q.0).collect::<Vec<_>>(),s.c.iter().map(|q|q.0).collect::<Vec<_>>());}}eprintln!("T0_CAND_TOTAL {n}");}
fn selector(o:&[Op],s:&Site)->QubitId{
 let mut p=s.at-12;let end=s.at;let mut sel=None;
 for j in 0..12 {
  if(0xcccusize>>j)&1!=0{assert_eq!(o[p].kind,K::X);assert_eq!(o[p].q_target,s.b[j]);assert_eq!(o[p].c_condition,NO_BIT);p+=1;}
  if(0x666usize>>j)&1!=0{assert_eq!(o[p].kind,K::CX);assert_eq!(o[p].q_target,s.b[j]);assert_eq!(o[p].c_condition,NO_BIT);if let Some(q)=sel{assert_eq!(q,o[p].q_control1);}else{sel=Some(o[p].q_control1);}p+=1;}
 }
 assert_eq!(p,end);sel.unwrap()
}
fn local(s:&Site,body:&[Op],kh:usize){
 // The only dependence on scratch measurement outcomes is linear in phase;
 // packed lanes contain zero, ALL1, and every single-outcome basis vector.
 // All 8192 source-window/selector states therefore check ALL outcomes.
 use std::collections::BTreeSet;
 let all:BTreeSet<_>=s.v.iter().chain(&s.b).chain(&s.c).copied().chain(s.out).collect();
 assert_eq!(all.len(),24+s.c.len()+usize::from(s.out.is_some()));
 let maxq=all.iter().map(|q|q.0 as usize).max().unwrap()+1;
 let maxb=body.iter().filter(|o|o.c_target!=NO_BIT).map(|o|o.c_target.0 as usize+1).max().unwrap_or(0);
 for sel in 0..2 {let threshold=4096/if sel==1{3}else{5};
  for value in 0..4096 {
   let mut q=vec![0u64;maxq];let mut b=vec![0u64;maxb];
   for j in 0..12{if value>>j&1!=0{q[s.v[j].0 as usize]=u64::MAX;}if(!threshold)>>j&1!=0{q[s.b[j].0 as usize]=u64::MAX;}}
   if let Some(t)=s.out{q[t.0 as usize]=0xaaaaaaaaaaaaaaaa;}
   let old=q.clone();let mut phase=0u64;let mut ordinal=0;
   for o in body {
    if matches!(o.kind,K::PushCondition|K::PopCondition){continue;}
    let t=o.q_target.0 as usize;let cond=if o.c_condition==NO_BIT{u64::MAX}else{b[o.c_condition.0 as usize]};
    match o.kind {
     K::X=>q[t]^=cond,K::Z=>phase^=q[t]&cond,
     K::CX=>q[t]^=q[o.q_control1.0 as usize]&cond,
     K::CCX=>q[t]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize]&cond,
     K::CZ=>phase^=q[t]&q[o.q_control1.0 as usize]&cond,
     K::Hmr=>{assert_eq!(cond,u64::MAX);let coin=2u64|(1u64<<(ordinal+2));ordinal+=1;phase^=q[t]&coin;q[t]=0;b[o.c_target.0 as usize]=coin;},
     _=>panic!("unexpected t0 local op {:?}",o.kind)
    }
   }
   assert_eq!(ordinal,if s.full{12}else{11});
   let carry=(value>>(12-kh))>(threshold>>(12-kh));
   let want=if s.full{0}else if carry{u64::MAX}else{0};assert_eq!(phase,want,"t0 phase at{} KH{kh} x{value} sel{sel}",s.at);
   let mut expected=old;if let Some(t)=s.out{if carry{expected[t.0 as usize]^=u64::MAX;}}
   assert_eq!(q,expected,"t0 data/scratch at{} KH{kh} x{value} sel{sel}",s.at);
  }
 }
}
pub fn run(ops:Vec<Op>,kh:usize,walks:usize)->Vec<Op>{run_inner(ops,kh,walks,false)}
pub fn run_minimal(ops:Vec<Op>,kh:usize,walks:usize)->Vec<Op>{assert!([4,8].contains(&kh));run_inner(ops,kh,walks,true)}
fn run_inner(ops:Vec<Op>,kh:usize,walks:usize,drop_common:bool)->Vec<Op>{
 assert!([4,6,8,12].contains(&kh));assert!((1..=3).contains(&walks));
 let mut sites=vec![];let mut i=0;
 while i<ops.len().saturating_sub(250){if let Some(s)=parse(&ops,i){i=s.end+12;sites.push(s);}else{i+=1;}}
 assert_eq!(sites.len(),6,"complete t0 full/phase comparison census");
 assert_eq!(sites.iter().map(|s|s.full).collect::<Vec<_>>(),[true,true,false,true,true,false]);
 let mut edits=vec![];
 for(si,s)in sites.iter().enumerate(){
  let control=selector(&ops,s);assert!(!s.v.contains(&control)&&!s.b.contains(&control)&&!s.c.contains(&control));
  local(s,&ops[s.begin..s.end],12);
  if walks&(1<<(si/3))==0{continue;}
  // Both selected constants have bit(12-kh)=1 when KH=4 or8.
  // Dropping this common1 bit leaves the strict predicate exactly unchanged.
  // Local exhaustive proof below checks the original KH predicate directly.
  if drop_common{for den in[3,5]{assert_eq!(((4096/den)>>(12-kh))&1,1);}}
  let cut=12-kh+usize::from(drop_common);let mut del=vec![false;s.end-s.begin];
  for j in 0..cut{
   let(a,b)=s.head[j];for p in a..b{if !matches!(ops[p].kind,K::PushCondition|K::PopCondition){del[p-s.begin]=true;}}
   let(a,b)=s.erase[j];for p in a..b{if ops[p].kind!=K::Hmr{del[p-s.begin]=true;}}
  }
  let body:Vec<_>=ops[s.begin..s.end].iter().enumerate().filter(|(j,_)|!del[*j]).map(|(_,o)|*o).collect();
  local(s,&body,kh);
  let signature=|o:&[Op]|o.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).map(|o|(o.kind,o.q_target,o.c_target,o.c_condition)).collect::<Vec<_>>();
  assert_eq!(signature(&ops[s.begin..s.end]),signature(&body));
  let oldt=ops[s.begin..s.end].iter().filter(|o|o.kind==K::CCX).count();let newt=body.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(oldt-newt,if cut>0{cut-1}else{0});
  eprintln!("T0_WINDOW site{si} at{} full{} KH{kh} selector{} removed{}CCX all8192data/ALLmeasurementassignmentsPASS",s.at,s.full as u8,control.0,oldt-newt);
  edits.push((s.begin,s.end,body));
 }
 let mut out=vec![];let mut last=0;
 for(a,b,body)in edits{out.extend_from_slice(&ops[last..a]);out.extend(body);last=b;}out.extend_from_slice(&ops[last..]);out
}
