use super::builder::B;
use super::row_add::Row;
use crate::circuit::{QubitId,BitId};
fn signed_block(b:&mut B,t:&[QubitId],s:&[QubitId],incoming:QubitId,flag:Option<QubitId>,work:&[QubitId]){
    let n=t.len();assert!(n>=1&&s.len()==n&&work.len()>=n-1);
    for i in 0..n{
        let prev=if i==0{incoming}else{work[i-1]};
        b.cx(prev,t[i]);b.cx(prev,s[i]);
        let next=if i+1<n{Some(work[i])}else{flag};
        if let Some(next)=next{b.and_c(t[i],s[i],next);b.cx(prev,next);}
    }
    for i in (0..n).rev(){
        let prev=if i==0{incoming}else{work[i-1]};
        if i+1<n{b.cx(prev,work[i]);b.and_u(t[i],s[i],work[i]);}
        b.cx(prev,t[i]);b.cx(s[i],t[i]);b.cx(prev,s[i]);
    }
}
fn cmp_phase(b:&mut B,u:&[QubitId],v:&[QubitId],incoming:QubitId,work:&[QubitId]) {
    let n=u.len();assert!(n==v.len()&&work.len()>=n-1);
    if n==1 {
        b.cz(u[0],v[0]);b.cz(u[0],incoming);b.cz(v[0],incoming);
    }else{
        b.cx(u[0],v[0]);b.cx(u[0],incoming);
        b.and_c(incoming,v[0],work[0]);b.cx(work[0],u[0]);
        for i in 1..n-1 {
            b.cx(u[i],v[i]);b.cx(u[i],u[i-1]);b.and_c(u[i-1],v[i],work[i]);b.cx(work[i],u[i]);
        }
        b.cz(u[n-1],v[n-1]);b.cz(u[n-1],u[n-2]);b.cz(v[n-1],u[n-2]);
        for i in (1..n-1).rev() {
            b.cx(work[i],u[i]);b.and_u(u[i-1],v[i],work[i]);b.cx(u[i],u[i-1]);b.cx(u[i],v[i]);
        }
        b.cx(work[0],u[0]);b.and_u(incoming,v[0],work[0]);b.cx(u[0],incoming);b.cx(u[0],v[0]);
    }
}

fn need(n:usize)->usize{super::frogdrop::conditional_inc_need(n)}
fn inc_choice(n:usize,nb:usize,force:usize)->(usize,usize,bool){
 assert!(n>0&&force<=nb.min(n-1));let k=nb.min(n-1);let mut best=(k+if n-k==1{0}else{4*(n-k)},k,false);
 for k in force..=nb.min(n-1){let su=n-k;if need(su)<=nb-k{let cost=k+super::frogdrop::conditional_inc_cost(su);if cost<best.0{best=(cost,k,true)}}}best
}
fn tail(b:&mut B,ctrl:QubitId,t:&[QubitId],anc:&[QubitId],dirty:&[QubitId],capture:Option<QubitId>,phase:Option<BitId>,force:usize){
 if let Some(nu)=capture{
  assert!(anc.len()>=t.len());let mut prev=ctrl;
  for(i,&q)in t.iter().enumerate(){b.and_c(prev,q,anc[i]);prev=anc[i];}
  b.cx(prev,nu);
  for i in(0..t.len()).rev(){let prev=if i==0{ctrl}else{anc[i-1]};b.and_u(prev,t[i],anc[i]);b.cx(prev,t[i]);}
 }else{
  let(_,k,unitary)=inc_choice(t.len(),anc.len(),force);let mut prev=ctrl;
  for i in 0..k{b.and_c(prev,t[i],anc[i]);prev=anc[i];}
  b.z_if(anc[force-1],phase.unwrap());
  if unitary{super::frogdrop::conditional_inc(b,prev,&t[k..],&anc[k..]);}
  else if t.len()-k==1{b.cx(prev,t[k]);}
  else{let mut high=vec![prev];high.extend_from_slice(&t[k..]);super::modp_frogdrop::inc_dirty_free(b,&high,dirty);b.x(prev);}
  for i in(0..k).rev(){let prev=if i==0{ctrl}else{anc[i-1]};b.and_u(prev,t[i],anc[i]);b.cx(prev,t[i]);}
 }
}
// key is the canonical F low-prefix geometry. Outer BatchMasks independently
// pins the FULL physical target span/ordered rows and exact K. Only source
// block flags are paired by this canonical prefix; I tail is explicit/paid.
fn row(b:&mut B,key:&Row,physical_tail:&[QubitId],inverse:bool,capture:Option<QubitId>,phase:Option<BitId>,force:usize){
 let n=key.t.len();let blocks=n.div_ceil(key.chunk);let nf=blocks;
 assert!(!key.tail.is_empty()&&!physical_tail.is_empty());
 let deferred=b.deferred_row_enter(key,inverse,nf).unwrap();let flags=&key.bank[..nf];let work=&key.bank[nf..];
 if inverse{for&q in key.t.iter().chain(physical_tail){b.x(q);}}
 for&q in &key.s{b.cx(key.c0,q);}let mut prev=key.c0;
 for j in 0..blocks{let lo=j*key.chunk;let hi=n.min(lo+key.chunk);signed_block(b,&key.t[lo..hi],&key.s[lo..hi],prev,Some(flags[j]),work);prev=flags[j];}
 if !deferred.0{for(&f,&m)in flags.iter().zip(&deferred.1){b.z_if(f,m)}}
 let early=deferred.0&&nf>=2;if early{for j in 0..nf-1{b.hmr_to(flags[j],deferred.1[j]);}}
 let mut tw=Vec::new();if early{tw.extend_from_slice(&flags[..nf-1]);}tw.extend_from_slice(work);
 let cout=flags[nf-1];b.cx(key.c0,cout);for&q in physical_tail{b.cx(key.c0,q);}
 tail(b,cout,physical_tail,&tw,&key.dirty,capture,phase,force);
 for&q in physical_tail{b.cx(key.c0,q);}b.cx(key.c0,cout);
 for j in(0..nf).rev(){
  if deferred.0{if !early||j+1==nf{b.hmr_to(flags[j],deferred.1[j]);}continue;}
  let lo=j*key.chunk;let hi=n.min(lo+key.chunk);let incoming=if j==0{key.c0}else{flags[j-1]};
  b.row_measure(flags[j]);b.row_condition(true);for&q in &key.t[lo..hi]{b.x(q);}cmp_phase(b,&key.t[lo..hi],&key.s[lo..hi],incoming,work);for&q in &key.t[lo..hi]{b.x(q);}b.row_condition(false);
 }
 for&q in &key.s{b.cx(key.c0,q);}if inverse{for&q in key.t.iter().chain(physical_tail){b.x(q);}}
}
#[derive(Clone,Debug,PartialEq,Eq)]pub struct Shape{pub v:Vec<QubitId>,pub source:Vec<QubitId>,pub enables:Vec<QubitId>,pub bank:Vec<QubitId>,pub high_bank:Vec<QubitId>,pub dirty:Vec<QubitId>,pub c0:QubitId,pub h:QubitId,pub nu:QubitId,pub sig:QubitId,pub lo:usize,pub hi:usize,pub k:usize,pub inverse:bool,pub chunks:Vec<usize>}
#[derive(Clone)]pub struct Masks{key:Shape,parity:BitId,sign:Option<BitId>}
fn query_sign(b:&mut B,s:&Shape){b.and_c(s.enables[s.hi-s.lo],s.v[s.hi],s.sig);b.x(s.sig);}
fn unquery_sign(b:&mut B,s:&Shape){b.x(s.sig);b.and_u(s.enables[s.hi-s.lo],s.v[s.hi],s.sig);}
fn digit(b:&mut B,s:&Shape,i:usize,inverse:bool,capture:Option<QubitId>,phase:Option<BitId>){
 let e=s.enables[i-s.lo];let m=s.source.len();let st=s.k-i-m;
 let key=Row{g:s.h,t:s.v[i..i+m].to_vec(),s:s.source.clone(),tail:s.v[i+m..s.k].to_vec(),mux:None,signed_binary:true,c0:s.c0,h:s.h,bank:s.bank.clone(),dirty:s.dirty.clone(),chunk:s.chunks[i-s.lo]};
 b.and_c(e,s.v[i],s.c0);if inverse{b.ccx(e,s.source[0],s.c0);}b.x(s.c0);
 let full=if capture.is_some(){&s.v[i+m..s.k]}else{&s.v[i+m..]};row(b,&key,full,inverse,capture,phase,st);
 b.x(s.c0);if !inverse{b.ccx(e,s.source[0],s.c0);}b.and_u(e,s.v[i],s.c0);
}
pub(super) fn forward_walk(b:&mut B,s:&Shape,mut before:impl FnMut(&mut B,usize))->Masks{
 assert_eq!(s.k,s.hi+s.source.len()+1);assert!(s.k<s.v.len()&&s.lo<=s.hi);assert_eq!(s.enables.len(),s.hi-s.lo+1);
 let bits=b.fresh_bits(4);let sign=if s.inverse{None}else{Some(bits[1])};
 if !s.inverse{query_sign(b,s);}
 let indices:Vec<_>=if s.inverse{(s.lo..=s.hi).collect()}else{(s.lo..=s.hi).rev().collect()};
 for i in indices{before(b,i);digit(b,s,i,s.inverse,Some(s.nu),None);}
 if s.inverse{query_sign(b,s);b.x(s.sig);}
 for&q in &s.v[s.k..]{b.cx(s.sig,q);}super::frogdrop::inc_mixed(b,s.nu,&s.v[s.k..],&s.high_bank,&s.dirty);for&q in &s.v[s.k..]{b.cx(s.sig,q);}
 if s.inverse{b.x(s.sig);unquery_sign(b,s);}else{b.hmr_to(s.sig,sign.unwrap());}
 b.hmr_to(s.nu,bits[0]);Masks{key:s.clone(),parity:bits[0],sign}
}
pub(super) fn inverse_walk(b:&mut B,s:&Shape,masks:Masks,mut before:impl FnMut(&mut B,usize)){
 assert_eq!(*s,masks.key);let indices:Vec<_>=if s.inverse{(s.lo..=s.hi).rev().collect()}else{(s.lo..=s.hi).collect()};
 for i in indices{before(b,i);digit(b,s,i,!s.inverse,None,Some(masks.parity));}
 if let Some(sign)=masks.sign{query_sign(b,s);b.z_if(s.sig,sign);unquery_sign(b,s);}
}
