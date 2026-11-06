use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
fn x(o:&Op,q:QubitId)->bool{o.kind==K::X&&o.q_target==q&&o.c_condition==NO_BIT}
fn cx(o:&Op,a:QubitId,b:QubitId)->bool{o.kind==K::CX&&o.q_control1==a&&o.q_target==b&&o.c_condition==NO_BIT}
fn cz(o:&Op,a:QubitId,b:QubitId)->bool{o.kind==K::CZ&&((o.q_control1==a&&o.q_target==b)||(o.q_control1==b&&o.q_target==a))}
pub(super) fn run(ops:Vec<Op>,walkmask:usize)->Vec<Op>{
assert!((1..=3).contains(&walkmask));let mut nf=0;let mut nr=0;let mut fs=vec![];let mut rs=vec![];
for i in 14..ops.len()-12{let h=ops[i];if h.kind!=K::CCX||h.c_condition!=NO_BIT{continue;}let(t,a,b)=(h.q_target,h.q_control2,h.q_control1);
 for(w,g)in [(a,b),(b,a)]{
  if !x(&ops[i-1],w)||!x(&ops[i+1],w){continue;}
  if ops[i+2].kind==K::CX&&ops[i+2].q_control1==t&&x(&ops[i+3],w)&&ops[i+4].kind==K::Hmr&&ops[i+4].q_target==t&&cz(&ops[i+5],g,w)&&ops[i+5].c_condition==ops[i+4].c_target&&x(&ops[i+6],w){
   if ops[i-5].kind==K::CCX&&ops[i-5].q_target==g&&ops[i-4].kind==K::CX&&ops[i-3].kind==K::X&&ops[i-2].kind==K::CX{
    nf+=1;fs.push((i,g,w));eprintln!("FORWARD {i} g{} w{} tmp{} out{}",g.0,w.0,t.0,ops[i+2].q_target.0);
   }
  }
 }
 // Reverse is q=and(z2,eq), X(w), CZ(q,w), X(w), HMR(q), CZ(z2,eq)|m, inside measurement condition.
 if ops[i+1].kind==K::X&&cz(&ops[i+2],t,ops[i+1].q_target)&&x(&ops[i+3],ops[i+1].q_target)&&ops[i+4].kind==K::Hmr&&ops[i+4].q_target==t&&cz(&ops[i+5],a,b)&&ops[i+5].c_condition==ops[i+4].c_target&&ops[i+6].kind==K::PopCondition{
  let z2=ops[i-4].q_target;let z3=ops[i-3].q_target;let z4=ops[i-2].q_target;
  if ![4,3,2,13,12,11].iter().all(|&d|ops[i-d].kind==K::X)||!x(&ops[i-13],z2)||!x(&ops[i-12],z3)||!x(&ops[i-11],z4){continue;}
  if ![1,10].iter().all(|&d|ops[i-d].kind==K::PushCondition)||ops[i-1].c_condition!=ops[i-10].c_condition||ops[i-9].kind!=K::CCX||!((ops[i-9].q_control1==z2&&ops[i-9].q_control2==z3)||(ops[i-9].q_control1==z3&&ops[i-9].q_control2==z2))||!cz(&ops[i-8],ops[i-9].q_target,z4)||ops[i-7].kind!=K::Hmr||ops[i-7].q_target!=ops[i-9].q_target||!cz(&ops[i-6],z2,z3)||ops[i-6].c_condition!=ops[i-7].c_target||ops[i-5].kind!=K::PopCondition||!(a==z2||b==z2){continue;}
  nr+=1;rs.push((i,a,b,ops[i+1].q_target));eprintln!("REVERSE {i} z2{} eq{} tmp{} w{}",a.0,b.0,t.0,ops[i+1].q_target.0);
 }
}
assert_eq!((nf,nr),(2,2),"complete terminal veto template census");
let mut del=vec![false;ops.len()];let mut replacements=std::collections::BTreeMap::new();
for walk in 0..2{if walkmask>>walk&1==0{continue;}
 let(i,g,w)=fs[walk];let(ri,ra,rb,rw)=rs[walk];
 assert!(if walk==0{i>3_180_000&&i<3_200_000&&ri>3_290_000&&ri<3_310_000}else{i>6_450_000&&i<6_470_000&&ri>6_570_000&&ri<6_590_000});
 let mut op=ops[i+2];op.q_control1=g;replacements.insert(i+2,op);del[i]=true;del[i+5]=true;
 let mut op=ops[ri+2];op.kind=K::CZ;op.q_control1=ra;op.q_target=rb;replacements.insert(ri+2,op);del[ri]=true;del[ri+5]=true;
 let(zstart,zend,ts,bs)=forward_zlin(&ops,i);
 let(prefix,suffix,inputs,ones)=comparison_ranges(&ops,zstart,zend,ts,bs);
 let mut comp:Vec<_>=ops[prefix.0..prefix.1].iter().chain(&ops[suffix.0..suffix.1]).copied().collect();
 let mut all=inputs.clone();all.extend(ones);super::last_veto_local::comparator(&comp,&all);drop(comp);
 for(p,q)in[prefix,suffix]{for j in p..q{if !matches!(ops[j].kind,K::Hmr|K::PushCondition|K::PopCondition){del[j]=true;}}}
 let new:Vec<_>=(i-1..i+7).filter(|&j|!del[j]).map(|j|replacements.get(&j).copied().unwrap_or(ops[j])).collect();
 super::last_veto_local::forward(&ops[i-1..i+7],&new,g.0,w.0,ops[i+2].q_target.0,false);
 
 assert_eq!(ops[ri+7].kind,K::CX);assert_eq!(ops[ri+8].kind,K::CX);
 // The first operand can be either z2 or eq. Derive sign hosts from the zlin_off pair on eq.
 let eq=if ra==ops[ri-4].q_target{rb}else{ra};
 assert_eq!(ops[ri+7].q_target,eq);assert_eq!(ops[ri+8].q_target,eq);
 let dq=ops[ri+7].q_control1;let btop=ops[ri+8].q_control1;
 let mut z=ri+7;for j in [7,8,9,10,11,12,13,14,15]{assert_eq!(ops[ri+j].kind,K::CX);z=ri+j+1;}
 let ttop=eq; // At this boundary the physical eq wire is the original target sign.
 let rzo=ri-25;assert_eq!(ops[rzo].kind,K::CX);assert_eq!(ops[rzo+8].kind,K::CX);assert_eq!(ops[rzo+8].q_target,eq);assert_eq!(ops[rzo+8].q_control1,dq);
 let(rprefix,rsuffix,rinputs,rones)=comparison_ranges(&ops,rzo,z,ttop,btop);
 comp=ops[rprefix.0..rprefix.1].iter().chain(&ops[rsuffix.0..rsuffix.1]).copied().collect();
 // The comparator prefixes/suffixes retain enclosing condition delimiters; balance any outer boundary locally.
 let mut all=rinputs.clone();all.extend(rones);super::last_veto_local::comparator(&comp,&all);
 for(p,q)in[rprefix,rsuffix]{for j in p..q{if !matches!(ops[j].kind,K::Hmr|K::PushCondition|K::PopCondition){del[j]=true;}}}
 let new:Vec<_>=(ri..ri+6).filter(|&j|!del[j]).map(|j|replacements.get(&j).copied().unwrap_or(ops[j])).collect();
 super::last_veto_local::reverse(&ops[ri..ri+6],&new,ra.0,rb.0,rw.0,false);
 eprintln!("LAST_VETO walk{walk} constantYfalse forward{i} reverse{ri} compare{prefix:?}/{suffix:?}/{rprefix:?}/{rsuffix:?}");
}
let before=ops.iter().filter(|o|o.kind==K::CCX).count();let draws=ops.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count();
let out:Vec<_>=ops.iter().enumerate().filter(|(j,_)|!del[*j]).map(|(j,o)|replacements.get(&j).copied().unwrap_or(*o)).collect();
assert_eq!(draws,out.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count());eprintln!("LAST_VETO emittedCCXsaved{}",before-out.iter().filter(|o|o.kind==K::CCX).count());out}

fn forward_zlin(ops:&[Op],i:usize)->(usize,usize,QubitId,QubitId){
 let start=i-22;let end=i+35;
 let t1=ops[start].q_target;let top=ops[start+7].q_target;let bs=ops[start+7].q_control1;
 for j in 0..9{assert_eq!(ops[start+j].kind,K::CX);assert_eq!(ops[end-9+j].kind,K::CX);}
 assert!(cx(&ops[start+8],t1,top));assert!(cx(&ops[end-9],t1,top));assert!(cx(&ops[end-8],bs,top));
 assert_eq!(ops[end-1].q_control1,ops[start].q_control1);assert_eq!(ops[end-1].q_target,t1);
 (start,end,top,bs)
}
fn comparison_ranges(ops:&[Op],zstart:usize,zend:usize,ts:QubitId,bs:QubitId)->((usize,usize),(usize,usize),std::collections::BTreeSet<u64>,[u64;2]){
 // Terminal windows have five non-sign positions on each six-bit rail; pin this complete interface.
 let mut e=zstart;while matches!(ops[e-1].kind,K::PopCondition|K::PushCondition){e-=1;}
 assert!(e>=10);let last=&ops[e-10..e];
 assert!((0..5).all(|j|ops[e-10+j].kind==K::CX&&ops[e-10+j].q_control1==bs));
 assert!((0..5).all(|j|ops[e-5+j].kind==K::CX&&ops[e-5+j].q_control1==ts));
 let mut first=last[5..10].to_vec();first.extend_from_slice(&last[..5]);
 let mut starts=vec![];for j in zstart.saturating_sub(160)..e-10{if same(&ops[j..j+10],&first){starts.push(j);}}
 assert_eq!(starts.len(),1,"complete comparison prefix conjugation");let mut start=starts[0];if ops[start-1].kind==K::PushCondition{start-=1;}
 let mut starts=vec![];let mut ends=vec![];for j in zend..(zend+180).min(ops.len()-10){if same(&ops[j..j+10],&first){starts.push(j);}if same(&ops[j..j+10],last){ends.push(j+10);}}
 assert!(!starts.is_empty()&&!ends.is_empty());let mut ss=starts[0];if ops[ss-1].kind==K::PushCondition{ss-=1;}let mut se=*ends.iter().find(|&&j|j>ss).unwrap();if ops[se].kind==K::PopCondition{se+=1;}
 let mut inputs=std::collections::BTreeSet::new();for o in &first{inputs.insert(o.q_control1.0);inputs.insert(o.q_target.0);}
 assert_eq!(inputs.len(),12);assert_eq!(ops[start..zstart].iter().filter(|o|o.kind==K::Hmr).count(),0);
 let ones=[first[0].q_target.0,first[5].q_target.0];assert_ne!(ones[0],ones[1]);for q in ones{assert!(inputs.remove(&q));}
 ((start,zstart),(ss,se),inputs,ones)
}
fn same(a:&[Op],b:&[Op])->bool{a.len()==b.len()&&a.iter().zip(b).all(|(a,b)|a.kind==b.kind&&a.q_control1==b.q_control1&&a.q_target==b.q_target&&a.c_condition==b.c_condition)}

