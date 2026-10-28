use super::{builder::B,signed_batch::{Shape,Masks as CoreMasks,forward_walk,inverse_walk}};
use crate::circuit::QubitId;
#[derive(Clone,Debug,PartialEq,Eq)]pub(super)struct Recipe{pub shape:Shape,pub cut:Vec<QubitId>,pub pre:Vec<QubitId>,pub e:QubitId,pub tmp:QubitId,pub offset:isize,pub lhi:usize}
pub(super)struct Masks{pub key:Recipe,pub masks:CoreMasks}
struct Walk<'a>{r:&'a Recipe,last:usize}
impl<'a> Walk<'a>{
 fn predicate(b:&mut B,r:&Recipe,i:usize){if i>=r.lhi{b.x(r.e);}else{super::mask::ge_const(b,&r.cut,r.offset+i as isize+1,r.e,&r.pre);b.x(r.e);}}
 fn new(b:&mut B,r:&'a Recipe,i:usize)->Self{Self::predicate(b,r,i);Self{r,last:i}}
 fn before(&mut self,b:&mut B,i:usize){if i==self.last{return;}assert!(i.abs_diff(self.last)==1);if i.min(self.last)<self.r.lhi{let j=self.r.offset+i.max(self.last)as isize;if j>=0&&(j as usize)<1usize<<self.r.cut.len(){let mut d=super::mask::Dec::new(&self.r.cut,&self.r.pre);let c=d.ctrls(b,j as usize);super::mask::mc_xor(b,&c,self.r.e,&[self.r.tmp],&self.r.shape.dirty);d.clear(b);}}self.last=i;}
 fn clear(self,b:&mut B){Self::predicate(b,self.r,self.last);}
}
fn validate(r:&Recipe){
 let s=&r.shape;assert!(s.enables.iter().all(|&e|e==r.e));assert!(r.cut.len()==8&&r.pre.len()==7);assert_eq!(s.k,s.hi+s.source.len()+1);
 let bank:std::collections::BTreeSet<_>=s.bank.iter().copied().collect();assert_eq!(bank.len(),s.bank.len());assert!(r.pre.iter().all(|q|bank.contains(q)));assert!(s.high_bank.iter().all(|q|bank.contains(q)));
 for q in [s.c0,s.nu,s.sig,r.e]{assert!(!bank.contains(&q));assert!(!s.v.contains(&q)&&!s.source.contains(&q)&&!s.dirty.contains(&q)&&!r.cut.contains(&q));}
 assert!(s.nu!=s.sig&&s.nu!=r.e&&s.sig!=r.e&&s.c0!=r.e);assert!(r.cut.iter().all(|q|!bank.contains(q)&&!s.v.contains(q)&&!s.source.contains(q)&&!s.dirty.contains(q)));
 assert!(bank.iter().all(|q|!s.v.contains(q)&&!s.source.contains(q)&&!s.dirty.contains(q)));
 // h/g are idle metadata in the signed row and can belong to the bank,
 // exactly as in the original signed_binary_* helpers.
}
pub(super)fn forward(b:&mut B,r:&Recipe,direction:bool)->Masks{validate(r);let mut s=r.shape.clone();s.inverse=direction;let first=if direction{s.lo}else{s.hi};let mut w=Walk::new(b,r,first);let masks=forward_walk(b,&s,|b,i|w.before(b,i));w.clear(b);Masks{key:r.clone(),masks}}
pub(super)fn inverse(b:&mut B,r:&Recipe,direction:bool,m:Masks){validate(r);assert_eq!(m.key,*r);let mut s=r.shape.clone();s.inverse=!direction;let first=if s.inverse{s.hi}else{s.lo};let mut w=Walk::new(b,r,first);inverse_walk(b,&s,m.masks,|b,i|w.before(b,i));w.clear(b);}

pub(super)struct Plan{pub old:usize,pub new:usize,pub batches:Vec<(usize,usize,usize,Vec<usize>)>}
pub(super)fn plan(top:usize,llo:usize,lhi:usize,m:usize,na:usize,np:usize,nc:usize)->Option<Plan>{
 type K=(usize,usize,usize,usize,usize,usize,usize);type V=(usize,usize,Vec<(usize,usize,usize,Vec<usize>)>);
 static T:std::sync::OnceLock<std::collections::HashMap<K,V>>=std::sync::OnceLock::new();
 let t=T.get_or_init(||{let mut h=std::collections::HashMap::new();
  {let p="sb_plans.txt";let s=include_str!("sb_plans.txt");
   // line: top llo lhi m na np nc old new ; lo hi k c,c,c ; lo hi k c,c ...
   for line in s.lines(){let line=line.trim();if line.is_empty()||line.starts_with('#'){continue;}
    let mut parts=line.split(';');let head:Vec<usize>=parts.next().unwrap().split_whitespace().map(|x|x.parse().unwrap()).collect();assert_eq!(head.len(),9);
    let mut bs=Vec::new();for p in parts{let w:Vec<&str>=p.split_whitespace().collect();assert_eq!(w.len(),4);
     bs.push((w[0].parse().unwrap(),w[1].parse().unwrap(),w[2].parse().unwrap(),w[3].split(',').map(|x|x.parse().unwrap()).collect()));}
    assert!(h.insert((head[0],head[1],head[2],head[3],head[4],head[5],head[6]),(head[7],head[8],bs)).is_none(),"duplicate plan key");}
   let _=p;}
  h});
 t.get(&(top,llo,lhi,m,na,np,nc)).map(|(o,n,b)|Plan{old:*o,new:*n,batches:b.clone()})
}
