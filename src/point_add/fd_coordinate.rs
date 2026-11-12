//! Coordinate subtraction / native FD seed fusion. Public ecdsa.fail research.
use super::{Builder,U256,N};
use crate::circuit::{QubitId,BitId};
use super::{modular as md,const_arith as ca,compare,width_composition as wc};
use super::pingpong::heo_hooks as h7;
static BORROW:std::sync::Mutex<Option<(QubitId,Vec<BitId>)>>=std::sync::Mutex::new(None);
pub(crate) fn enabled()->bool{std::env::var_os("FD_COORD_FUSE").is_some()}
fn room(c:&Builder)->usize{h7::cap().saturating_sub(c.active_qubits()as usize)}
pub(crate) fn mapped(c:&mut Builder,b:&[QubitId],map:&[Vec<QubitId>]){
 let zero=c.alloc_qubit();let plan=wc::direct_plan(b.len(),room(c)).expect("FD selector carry plan");wc::direct_add(c,map,b,zero,&plan);c.release_clean(zero);
}
pub(crate) fn measured_and_clear(c:&mut Builder,u:QubitId,a:QubitId,b:QubitId){let m=c.alloc_bit();c.hmr(u,m);c.cz_if(a,b,m);c.free_bit(m);c.release_clean(u);}
pub(crate) fn raw_sub(c:&mut Builder,x:&[QubitId],value:&[QubitId])->QubitId{
 c.x_all(x);let out=md::heo_fitted_vented_add(c,value,x).unwrap_or_else(||{let q=c.alloc_qubit();md::peak_fitted_add(c,value,x,q);q});c.x_all(x);out
}
fn ordinary_seed(c:&mut Builder,x:&[QubitId],f:U256,fw:usize)->(Vec<QubitId>,Vec<QubitId>){
 let n=x.len();let b=c.alloc_qubit();c.cx(x[0],b);let y=c.alloc_qubits(n+1);c.cx_pairs(x,&y[..n]);
 c.x(b);ca::cadd_const_trunc(c,&y[..fw],f,b,false);c.cx(b,y[n]);c.x(b);
 c.cx(b,x[0]);ca::cadd_const_trunc(c,&x[1..fw],(f+U256::from(1))>>1,b,false);
 let mut a=x[1..].to_vec();a.push(x[0]);c.cx(b,a[n-1]);let sign=c.alloc_qubit();c.cx(b,sign);a.push(sign);c.cx(a[n-1],b);c.release_clean(b);
 super::heo::gidney_add(c,&a,&y,None);(a,y)
}
fn erase_exact(c:&mut Builder,borrow:QubitId,d:&[QubitId],value:&[QubitId],f:U256){
 let m=c.alloc_bit();c.hmr(borrow,m);c.release_clean(borrow);c.push_condition(m);
 // threshold=p-1-value=~value-f; borrow iff threshold < canonical d.
 c.x_all(value);ca::sub_const(c,value,f);compare::cmp_lt_phase(c,value,d,None);ca::add_const(c,value,f);c.x_all(value);
 c.pop_condition();c.free_bit(m);
}
fn fused_seed(c:&mut Builder,x:&[QubitId],borrow:QubitId,f:U256,fw:usize,erase:impl FnOnce(&mut Builder,&[QubitId],&[QubitId],QubitId)) ->(Vec<QubitId>,Vec<QubitId>){
 let n=x.len();let r=x[0];let u=c.alloc_qubit();c.ccx(r,borrow,u);let one=c.alloc_qubit();c.x(one);
 let y=c.alloc_qubits(n+1);c.cx_pairs(x,&y[..n]);
 let negf=U256::ZERO.wrapping_sub(f);let ym:Vec<Vec<QubitId>>=(0..fw).map(|i|{let p=f.bit(i);let m=negf.bit(i);let mut v=vec![];if p{v.extend([one,r]);}if p!=m{v.extend([borrow,u]);}v}).collect();
 if std::env::var_os("FD_COORD_LOW_ONE").is_some(){
  // Raw Y0=r and the selected +/-F low bit is !r: sum0=1, carry0=0.
  // Materialize only that affine sum and start the ripple at bit1.
  c.cx(one,y[0]);c.cx(r,y[0]);mapped(c,&y[1..fw],&ym[1..]);
 }else{mapped(c,&y[..fw],&ym);}
 let plus:U256=(f+U256::from(1))>>1;let minus=U256::ZERO.wrapping_sub(f>>1);
 let xm:Vec<Vec<QubitId>>=(0..fw-1).map(|i|{let p=plus.bit(i);let m=minus.bit(i);let mut v=vec![];if p{v.push(r);}if p!=m{v.push(u);}v}).collect();mapped(c,&x[1..fw],&xm);
 measured_and_clear(c,u,r,borrow);c.x(one);c.release_clean(one);
 let b=c.alloc_qubit();c.cx(r,b);c.cx(borrow,b);c.cx(b,r);c.cx(borrow,r); // r now zero
 let mut a=x[1..].to_vec();a.push(r);c.cx(b,r);let sign=c.alloc_qubit();c.cx(b,sign);a.push(sign);
 c.x(b);c.cx(b,y[n]);c.x(b);c.cx(r,b);c.release_clean(b);
 erase(c,x,&a,borrow);
 super::heo::gidney_add(c,&a,&y,None);(a,y)
}
/// Exact small control and fused construction, quantum source preserved.
pub(crate) fn generic(c:&mut Builder,x:&[QubitId],value:&[QubitId],f:U256,fused:bool)->(Vec<QubitId>,Vec<QubitId>){
 let n=x.len();let borrow=raw_sub(c,x,value);
 if !fused{ca::cadd_const_trunc(c,x,U256::ZERO.wrapping_sub(f),borrow,false);erase_exact(c,borrow,x,value,f);return ordinary_seed(c,x,f,n);}
 fused_seed(c,x,borrow,f,n,|c,x,a,borrow|{
  let m=c.alloc_bit();c.hmr(borrow,m);c.release_clean(borrow);c.push_condition(m);
  let b=a[n];c.cx(b,x[0]);ca::cadd_const_trunc(c,&x[1..],U256::ZERO.wrapping_sub((f+U256::from(1))>>1),b,false);c.cx(b,x[0]);
  c.x_all(value);ca::sub_const(c,value,f);compare::cmp_lt_phase(c,value,x,None);ca::add_const(c,value,f);c.x_all(value);
  c.cx(b,x[0]);ca::cadd_const_trunc(c,&x[1..],(f+U256::from(1))>>1,b,false);c.cx(b,x[0]);
  c.pop_condition();c.free_bit(m);
 })
}
/// Small exact circuit for the production finite-window map, including its
/// deliberately exposed finite comparison exceptions.
pub(crate) fn generic_window(c:&mut Builder,x:&[QubitId],value:&[QubitId],f:U256,fw:usize,k:usize,fused:bool)->(Vec<QubitId>,Vec<QubitId>){
 let n=x.len();assert!(fw<=n-k);let borrow=raw_sub(c,x,value);
 let erase=|c:&mut Builder,x:&[QubitId],_:&[QubitId],q:QubitId|{c.x_all(&x[n-k..]);compare::erase_with_compare(c,q,&x[n-k..],&value[n-k..],None);c.x_all(&x[n-k..]);c.release_clean(q);};
 if !fused{ca::cadd_const_trunc(c,&x[..fw],U256::ZERO.wrapping_sub(f),borrow,false);erase(c,x,&[],borrow);ordinary_seed(c,x,f,fw)}
 else{fused_seed(c,x,borrow,f,fw,erase)}
}
/// Native selected-window seed, consuming the actual coord_sub_keep borrow.
pub(crate) fn native_seed(c:&mut Builder,x:&[QubitId],wout:usize)->Option<(Vec<QubitId>,Vec<QubitId>)>{
 let(borrow,coord)=BORROW.lock().unwrap().take()?;assert_eq!(x.len(),N);let fw=md::f_slice();let k=super::j_fuse::x_erase_width();assert!(fw<=N-k);
 let(a,mut y)=fused_seed(c,x,borrow,md::f(),fw,|c,x,_,q|super::j_fuse::erase_x_carry(c,q,&x[N-k..],&coord));
 let mut a=a;while a.len()<wout{let q=c.alloc_qubit();c.cx(a[N],q);a.push(q);}while y.len()<wout{let q=c.alloc_qubit();c.cx(y[N],q);y.push(q);}Some((a,y))
}
pub(crate) fn retained_coord_sub(c:&mut Builder,x:&[QubitId],coord:&[BitId]){
 if md::r5_cbits(1){c.x_all(x);let borrow=c.alloc_qubit();md::r5_ripple_add_cbits(c,coord,x,borrow);c.x_all(x);assert!(BORROW.lock().unwrap().replace((borrow,coord.to_vec())).is_none());return;}
 let value=c.alloc_qubits(coord.len());for(&q,&b)in value.iter().zip(coord){c.x_if_bit(q,b);}let borrow=raw_sub(c,x,&value);for(&q,&b)in value.iter().zip(coord){c.x_if_bit(q,b);}c.free_vec(&value);assert!(BORROW.lock().unwrap().replace((borrow,coord.to_vec())).is_none());
}
