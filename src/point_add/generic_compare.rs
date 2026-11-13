use crate::circuit::{Op,OperationType as K,QubitId,BitId,NO_BIT};
use super::cmp_narrow;
#[derive(Clone,Debug)]
pub struct Compare {pub at:usize,pub end:usize,pub u:Vec<QubitId>,pub v:Vec<QubitId>,pub carries:Vec<QubitId>,pub pb:Option<QubitId>,pub direct:bool}
pub fn parse(ops:&[Op],i:usize)->Option<Compare>{
 if i>=ops.len() || ops[i].kind!=K::X || ops[i].c_condition!=NO_BIT || (i>0&&ops[i-1].kind==K::X&&ops[i-1].c_condition==NO_BIT){return None;}
 let mut j=i;let mut u=vec![];while j<ops.len()&&ops[j].kind==K::X&&ops[j].c_condition==NO_BIT{u.push(ops[j].q_target);j+=1;}
 let k=u.len();if !(5..=128).contains(&k){return None;}
 let cx=|o:&Op,c:QubitId,t:QubitId|o.kind==K::CX&&o.c_condition==NO_BIT&&o.q_control1==c&&o.q_target==t;
 let mut v=vec![];let mut carries=vec![];
 if j+4*k>=ops.len() || ops[j].kind!=K::CX||ops[j].c_condition!=NO_BIT||ops[j].q_control1!=u[0]{return None;}
 v.push(ops[j].q_target);j+=1;
 let pb=if ops[j].kind==K::CX&&ops[j].c_condition==NO_BIT&&ops[j].q_control1==u[0]{j+=1;Some(ops[j-1].q_target)}else{None};
 let cc=|o:&Op,a:QubitId,b:QubitId|o.kind==K::CCX&&o.c_condition==NO_BIT&&((o.q_control1==a&&o.q_control2==b)||(o.q_control1==b&&o.q_control2==a));
 if !cc(&ops[j],pb.unwrap_or(u[0]),v[0]){return None;}carries.push(ops[j].q_target);j+=1;
 if !cx(&ops[j],carries[0],u[0]){return None;}j+=1;
 for m in 1..k-1{
  if ops[j].kind!=K::CX||ops[j].c_condition!=NO_BIT||ops[j].q_control1!=u[m]{return None;}v.push(ops[j].q_target);
  if !cx(&ops[j+1],u[m],u[m-1])||!cc(&ops[j+2],u[m-1],v[m])||!cx(&ops[j+3],ops[j+2].q_target,u[m]){return None;}
  carries.push(ops[j+2].q_target);j+=4;
 }
 if ops[j].kind!=K::CZ||ops[j].c_condition!=NO_BIT||ops[j].q_control1!=u[k-1]{return None;}v.push(ops[j].q_target);
 if ops[j+1].kind!=K::CZ||ops[j+1].c_condition!=NO_BIT||ops[j+1].q_control1!=u[k-1]||ops[j+1].q_target!=u[k-2]||ops[j+2].kind!=K::CZ||ops[j+2].c_condition!=NO_BIT||ops[j+2].q_control1!=v[k-1]||ops[j+2].q_target!=u[k-2]{return None;}
 let end=(j+3..(i+20*k+100).min(ops.len()-k+1)).find(|&at|(0..k).all(|m|ops[at+m].kind==K::X&&ops[at+m].c_condition==NO_BIT&&ops[at+m].q_target==u[m]))?+k;
 // A compare body does not push a new condition. Refuse larger lookalikes.
 // Every scratch measurement/reset in it must belong to this carry ladder;
 // this also rejects unrelated work accidentally matching the X suffix.
 if ops[i..end].iter().any(|o|matches!(o.kind,K::Hmr|K::R)&&!carries.contains(&o.q_target)){return None;}
 if ops[i..end].iter().any(|o|matches!(o.kind,K::PushCondition|K::PopCondition)){return None;}
 let direct=i>=2&&ops[i-2].kind==K::Hmr&&ops[i-2].c_condition==NO_BIT&&ops[i-1].kind==K::PushCondition&&ops[i-1].c_condition==ops[i-2].c_target;
 Some(Compare{at:i,end,u,v,carries,pb,direct})
}
pub fn transform(ops:Vec<Op>,lo:usize,hi:usize,widths:&[usize],removed:usize,pred:usize,nested_only:bool)->Vec<Op>{
 let mut out=Vec::with_capacity(ops.len());let mut i=0;let mut done=0;let mut cut=0;
 while i<ops.len(){
  if let Some(s)=parse(&ops,i){let k=s.u.len();if s.at>=lo&&s.at<hi&&widths.contains(&k)&&(!nested_only||!s.direct){
   let mut fragment=Vec::with_capacity(s.end-s.at+3);let mut h=Op::empty();h.kind=K::Hmr;h.q_target=QubitId(0);h.c_target=BitId(0);fragment.push(h);
   let mut p=Op::empty();p.kind=K::PushCondition;p.c_condition=BitId(0);fragment.push(p);fragment.extend_from_slice(&ops[s.at..s.end]);let mut e=Op::empty();e.kind=K::PopCondition;fragment.push(e);
   let before=fragment.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
   let f=cmp_narrow::run_predictor(fragment,removed,k,0,usize::MAX,&[k],pred);
   let after=f.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();assert_eq!(before-after,removed,"unmatched generic comparator at {}",s.at);cut+=removed;done+=1;
   out.extend_from_slice(&f[2..f.len()-1]);i=s.end;continue;
  }}
  out.push(ops[i].clone());i+=1;
 }
 assert_eq!(done, 39, "nested divide comparison count");
 eprintln!("GENERIC_COMPARE transformed={done} ccx_cut={cut}");out
}
