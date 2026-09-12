//! Local validation storage only. Every packed NCT expands to the same public
//! 56-byte Op before the unchanged Simulator consumes it. Official emission
//! keeps the ordinary Op ABI and must independently fit the 128GB RAM budget.
use crate::circuit::{Op,OperationType as K,QubitId,NO_QUBIT,NO_BIT,NO_REG};
use std::sync::Arc;
pub(crate) enum Block { Raw(Vec<Op>), Nct(Vec<u32>) }
fn unpack(z:u32)->Op{
 let mut o=Op::empty();o.kind=match z>>30{0=>K::X,1=>K::CX,2=>K::CCX,_=>panic!("invalid local NCT code")};
 for (i,q) in [&mut o.q_target,&mut o.q_control1,&mut o.q_control2].into_iter().enumerate(){let v=(z>>(10*i))&1023;*q=if v==1023{NO_QUBIT}else{QubitId(v as u64)};}o
}
impl Block{
 pub(crate) fn raw(mut ops:Vec<Op>)->Self{let mut depth=0;for o in &ops{o.validate();match o.kind{K::PushCondition=>depth+=1,K::PopCondition=>{assert!(depth>0,"condition scope crosses local block boundary");depth-=1;},_=>{}}}assert_eq!(depth,0,"condition scope crosses local block boundary");ops.shrink_to_fit();Self::Raw(ops)}
 pub(crate) fn nct(ops:&[Op])->Self{let mut packed=Vec::with_capacity(ops.len());for &o in ops{o.validate();assert_eq!(o.c_target,NO_BIT);assert_eq!(o.c_condition,NO_BIT);assert_eq!(o.r_target,NO_REG);let k=match o.kind{K::X=>0,K::CX=>1,K::CCX=>2,_=>panic!("non-NCT in packed schedule")};let mut z=k<<30;for(i,q)in[o.q_target,o.q_control1,o.q_control2].into_iter().enumerate(){let v=if q==NO_QUBIT{1023}else{assert!(q.0<1023);q.0 as u32};z|=v<<(10*i);}assert_eq!(unpack(z),o,"local codec must preserve every field");packed.push(z);}Self::Nct(packed)}
 pub(crate) fn len(&self)->usize{match self{Self::Raw(v)=>v.len(),Self::Nct(v)=>v.len()}}
 pub(crate) fn bytes(&self)->usize{match self{Self::Raw(v)=>v.capacity()*std::mem::size_of::<Op>(),Self::Nct(v)=>v.capacity()*4}}
}
pub(crate) struct Program{pub(crate) blocks:Vec<Arc<Block>>,pub(crate) len:usize}
impl Program{
 pub(crate) fn len(&self)->usize{self.len}
 /// Four decoded blocks cover one schedule clock cycle. This bounds memory
 /// independently of expanded operation count; all operations stay ordered.
 pub(crate) fn visit(&self,mut f:impl FnMut(&[Op])){let mut cache:Vec<(usize,Vec<Op>)>=Vec::new();let mut next=0;for block in &self.blocks{match block.as_ref(){Block::Raw(ops)=>f(ops),Block::Nct(words)=>{let id=Arc::as_ptr(block)as usize;let at=if let Some(i)=cache.iter().position(|(key,_)|*key==id){i}else{let ops=words.iter().map(|&z|unpack(z)).collect();if cache.len()<4{cache.push((id,ops));cache.len()-1}else{let i=next;cache[i]=(id,ops);next=(next+1)%4;i}};f(&cache[at].1);}}}}
}
pub(crate) fn check(){let mut ops=Vec::new();for t in 0..1023{for k in [K::X,K::CX,K::CCX]{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t);if k!=K::X{o.q_control1=QubitId((t+1)%1023);}if k==K::CCX{o.q_control2=QubitId((t+293)%1023);}ops.push(o);}}let packed=Arc::new(Block::nct(&ops));let program=Program{blocks:vec![packed.clone();7],len:ops.len()*7};let mut actual=Vec::new();program.visit(|slice|actual.extend_from_slice(slice));assert_eq!(actual,ops.repeat(7));assert_eq!(actual.len(),program.len());eprintln!("Q792_LOCAL_PACK_PASS operations={} copies=7 all_fields=true expanded_bytes={} packed_bytes={} official_ABI_unchanged=true",ops.len(),ops.len()*56,packed.bytes());}
