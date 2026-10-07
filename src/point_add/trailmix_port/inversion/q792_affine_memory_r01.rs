//! Exact nonlinear transvections in a common affine coordinate system.
//! CNOT frames may hide repeated products. No initial zero assumptions.
use crate::circuit::{Op,OperationType as K,QubitId,NO_QUBIT,NO_BIT};
type Bits=Vec<u64>;
fn bit(a:&Bits,i:usize)->bool{a[i/64]>>(i%64)&1!=0}
fn flip(a:&mut Bits,i:usize){a[i/64]^=1u64<<(i%64);}
fn xor(a:&mut Bits,b:&Bits){for(x,y)in a.iter_mut().zip(b){*x^=*y;}}
fn dot(a:&Bits,b:&Bits)->bool{a.iter().zip(b).fold(0u32,|p,(x,y)|p^((x&y).count_ones()&1))!=0}
fn zero(a:&Bits)->bool{a.iter().all(|&x|x==0)}
#[derive(Clone)]struct Product{a:Bits,b:Bits,u:Bits}
fn commute(a:&Product,b:&Product)->bool{!dot(&a.a,&b.u)&&!dot(&a.b,&b.u)&&!dot(&b.a,&a.u)&&!dot(&b.b,&a.u)}
fn combine(a:&Product,b:&Product)->Option<Product>{
 if a.a==b.a&&a.b==b.b || a.a==b.b&&a.b==b.a{let mut z=a.clone();xor(&mut z.u,&b.u);return Some(z);}
 if a.u==b.u{for(x,y)in[(&a.a,&a.b),(&a.b,&a.a)]{for(v,w)in[(&b.a,&b.b),(&b.b,&b.a)]{if x==v{let mut z=y.clone();xor(&mut z,w);return Some(Product{a:x.clone(),b:z,u:a.u.clone()});}}}}
 None
}
fn op(k:K,t:u64,a:Option<u64>,b:Option<u64>)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t);if let Some(a)=a{o.q_control1=QubitId(a);}if let Some(b)=b{o.q_control2=QubitId(b);}o.validate();o}
fn emit(product:&Product,ids:&[u64],out:&mut Vec<Op>){
 if zero(&product.u){return;}let n=ids.len();let mut a=product.a.clone();let mut b=product.b.clone();
 assert!(!dot(&a,&product.u)&&!dot(&b,&product.u));
 let r=(0..n).find(|&i|bit(&product.u,i)).unwrap();let mut frame=Vec::new();
 // Align the nonlinear output direction with one physical target.
 for i in 0..n{if i!=r&&bit(&product.u,i){frame.push(op(K::CX,ids[i],Some(ids[r]),None));if bit(&a,i){flip(&mut a,r);}if bit(&b,i){flip(&mut b,r);}}}
 assert!(!bit(&a,r)&&!bit(&b,r));
 let av=(0..n).any(|i|bit(&a,i));let bv=(0..n).any(|i|bit(&b,i));
 let ca=bit(&a,n);let cb=bit(&b,n);let mut one=None;
 if !av{if !ca{return;}one=Some(b.clone());}else if !bv{if !cb{return;}one=Some(a.clone());}
 else{let mut diff=a.clone();xor(&mut diff,&b);if(0..n).all(|i|!bit(&diff,i)){if ca!=cb{return;}one=Some(a.clone());}}
 let mut middle=Vec::new();
 if let Some(v)=one{
  if let Some(p)=(0..n).find(|&i|bit(&v,i)){
   for i in 0..n{if i!=p&&bit(&v,i){frame.push(op(K::CX,ids[p],Some(ids[i]),None));}}
   middle.push(op(K::CX,ids[r],Some(ids[p]),None));if bit(&v,n){middle.push(op(K::X,ids[r],None,None));}
  }else if bit(&v,n){middle.push(op(K::X,ids[r],None,None));}
 }else{
  let p=(0..n).find(|&i|bit(&a,i)).unwrap();
  for i in 0..n{if i!=p&&bit(&a,i){frame.push(op(K::CX,ids[p],Some(ids[i]),None));if bit(&b,p){flip(&mut b,i);}}}
  let q=(0..n).find(|&i|i!=p&&bit(&b,i)).expect("independent product controls");
  for i in 0..n{if i!=q&&bit(&b,i){frame.push(op(K::CX,ids[q],Some(ids[i]),None));}}
  if ca{middle.push(op(K::X,ids[p],None,None));}if cb{middle.push(op(K::X,ids[q],None,None));}
  middle.push(op(K::CCX,ids[r],Some(ids[p]),Some(ids[q])));
  if cb{middle.push(op(K::X,ids[q],None,None));}if ca{middle.push(op(K::X,ids[p],None,None));}
 }
 out.extend(frame.iter().copied());out.extend(middle);out.extend(frame.into_iter().rev());
}
fn window(input:&[Op])->Option<Vec<Op>>{
 let old_t=input.iter().filter(|o|o.kind==K::CCX).count();if old_t<2{return None;}
 let mut ids:Vec<_>=input.iter().flat_map(|o|[o.q_target,o.q_control1,o.q_control2]).filter(|q|*q!=NO_QUBIT).map(|q|q.0).collect();ids.sort_unstable();ids.dedup();let n=ids.len();let words=(n+1).div_ceil(64);
 let mut rows:Vec<Bits>=(0..n).map(|i|{let mut v=vec![0;words];flip(&mut v,i);v}).collect();let mut columns=rows.clone();let mut linear=Vec::new();let mut products:Vec<Option<Product>>=Vec::new();let mut merges=0;
 for &o in input{let t=ids.binary_search(&o.q_target.0).unwrap();match o.kind{
  K::X=>{flip(&mut rows[t],n);linear.push(o);},
  K::CX=>{let a=ids.binary_search(&o.q_control1.0).unwrap();let v=rows[a].clone();xor(&mut rows[t],&v);let v=columns[t].clone();xor(&mut columns[a],&v);linear.push(o);},
  K::CCX=>{let a=ids.binary_search(&o.q_control1.0).unwrap();let b=ids.binary_search(&o.q_control2.0).unwrap();let mut p=Product{a:rows[a].clone(),b:rows[b].clone(),u:columns[t].clone()};
   loop{let mut found=None;for i in (0..products.len()).rev(){if let Some(old)=&products[i]{if let Some(next)=combine(old,&p){if products[i+1..].iter().flatten().all(|q|commute(old,q)){found=Some((i,next));break;}}}}
    if let Some((i,next))=found{products[i]=None;p=next;merges+=1;}else{break;}}
   if !zero(&p.u){products.push(Some(p));}
  },_=>unreachable!()}}
 if merges==0{return None;}let mut result=Vec::new();for p in products.iter().flatten(){emit(p,&ids,&mut result);}result.extend(linear);
 super::q792_trace_cancel_r01::reduce(&mut result);
 let new_t=result.iter().filter(|o|o.kind==K::CCX).count();
 if new_t<old_t&&result.len()<=input.len()+input.len()/3+16{Some(result)}else{None}
}
pub(super) fn apply(ops:&mut Vec<Op>)->usize{
 assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)&&o.c_condition==NO_BIT));let old_t=ops.iter().filter(|o|o.kind==K::CCX).count();
 for width in [64usize,128]{let mut out=Vec::with_capacity(ops.len());for part in ops.chunks(width){if let Some(next)=window(part){out.extend(next);}else{out.extend_from_slice(part);}}*ops=out;}
 old_t-ops.iter().filter(|o|o.kind==K::CCX).count()
}
pub fn check(){
 use crate::sim::Simulator;use sha3::digest::XofReader;struct F;impl XofReader for F{fn read(&mut self,b:&mut[u8]){b.fill(0x36)}}let mut seed=0xaff179220260913u64;let mut saved=0;
 for case in 0..2048{let mut original=Vec::new();for _ in 0..32+case%160{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;let a=seed%8;let b=(a+1+(seed>>8)%7)%8;let mut t=(b+1+(seed>>16)%7)%8;while t==a||t==b{t=(t+1)%8;}let k=[K::X,K::CX,K::CCX][(seed>>24)as usize%3];original.push(op(k,t,if k!=K::X{Some(a)}else{None},if k==K::CCX{Some(b)}else{None}));}
  let mut candidate=original.clone();saved+=apply(&mut candidate);for base in [0,64,128,192]{let before:Vec<_>=(0..8).map(|i|(0..64).fold(0u64,|v,l|v|((((base+l)>>i)&1)as u64)<<l)).collect();let mut ra=F;let mut rb=F;let mut a=Simulator::new(8,0,&mut ra);let mut b=Simulator::new(8,0,&mut rb);a.qubits.copy_from_slice(&before);b.qubits.copy_from_slice(&before);a.apply_iter(original.iter());b.apply_iter(candidate.iter());assert_eq!(a.qubits,b.qubits,"affine memory case={case}");assert_eq!(a.phase,b.phase);b.apply_iter(candidate.iter().rev());assert_eq!(b.qubits,before);}
 }assert!(saved>0);eprintln!("AFFINE_MEMORY_NATIVE_PASS programs=2048 exhaustive_cases=524288 phase=0 inverse=true saved_T={saved}");
}
