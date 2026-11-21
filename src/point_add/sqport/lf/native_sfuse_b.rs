//! Staged native B-square / FD seed. Public ecdsa.fail research, no key target.
use super::{Builder,U256,N,QubitId};
use super::{fd_coordinate as fd,const_arith as ca,modular as md,width_composition as wc};
static PENDING:std::sync::Mutex<Option<(Vec<QubitId>,Vec<QubitId>)>>=std::sync::Mutex::new(None);
pub(crate) fn mode()->usize{std::env::var("NATIVE_SFUSE_B").ok().map(|s|s.parse().unwrap()).unwrap_or(0)}
fn defer_sign(c:&mut Builder,a:&mut Vec<QubitId>){let s=a.pop().unwrap();c.cx(*a.last().unwrap(),s);c.release_clean(s);}
fn restore_sign(c:&mut Builder,a:&mut Vec<QubitId>){let s=c.alloc_qubit();c.cx(*a.last().unwrap(),s);a.push(s);}
fn start(c:&mut Builder,x:&[QubitId],borrow:QubitId,f:U256,fw:usize,erase:impl FnOnce(&mut Builder,&[QubitId],&[QubitId],QubitId))->Vec<QubitId>{
 let n=x.len();let r=x[0];let u=c.alloc_qubit();c.ccx(r,borrow,u);
 let plus:U256=(f+U256::from(1))>>1;let minus=U256::ZERO.wrapping_sub(f>>1);
 let map:Vec<Vec<QubitId>>=(0..fw-1).map(|i|{let mut v=vec![];if plus.bit(i){v.push(r);}if plus.bit(i)!=minus.bit(i){v.push(u);}v}).collect();
 fd::mapped(c,&x[1..fw],&map);fd::measured_and_clear(c,u,r,borrow);
 c.cx(borrow,r);let mut a=x[1..].to_vec();a.push(r);let sign=c.alloc_qubit();c.cx(r,sign);a.push(sign);
 erase(c,x,&a,borrow);assert_eq!(a.len(),n+1);a
}
fn finish(c:&mut Builder,a:&[QubitId],f:U256,fw:usize,low:bool)->Vec<QubitId>{
 let n=a.len()-1;let b=a[n];let y=c.alloc_qubits(n+1);
 for i in 0..n{c.cx(a[i],y[i+1]);}c.x(y[n]);
 c.cx_all(b,&y[..fw]);
 if low {
  // Low target was0 before complement; carry0 after +F is exactly b.
  c.x(y[0]);let one=c.alloc_qubit();c.x(one);
  let map:Vec<Vec<QubitId>>=(1..fw).map(|i|if f.bit(i){vec![one]}else{vec![]}).collect();
  let room=super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits()as usize);
  let plan=wc::direct_plan(fw-1,room).expect("staged Y carry plan");wc::direct_add(c,&map,&y[1..fw],b,&plan);
  c.x(one);c.release_clean(one);
 }else{ca::add_const(c,&y[..fw],f);}
 c.cx_all(b,&y[..fw]);super::heo::gidney_add(c,a,&y,None);y
}
pub(crate) fn prepare_native(c:&mut Builder,x:&[QubitId],value:&[QubitId]){
 let q=fd::raw_sub(c,x,value);let fw=md::f_slice();let k=super::j_fuse::x_erase_width();assert!(fw<=N-k);
 let loans=super::square::SQ_LOANS.with(|l|l.borrow().clone());c.set_avoid(&loans);
 let mut a=start(c,x,q,md::f(),fw,|c,x,_,q|super::j_fuse::erase_q_carry(c,q,&x[N-k..],&value[N-k..]));
 assert!(!loans.contains(a.last().unwrap()));if mode()>=4{defer_sign(c,&mut a);}
 c.set_avoid(&[]);assert!(PENDING.lock().unwrap().replace((x.to_vec(),a)).is_none());
}
pub(crate) fn take_native(c:&mut Builder,x:&[QubitId],wout:usize)->Option<(Vec<QubitId>,Vec<QubitId>)>{
 let (saved,mut a)=PENDING.lock().unwrap().take()?;assert_eq!(saved,x);if a.len()==N{restore_sign(c,&mut a);}let mut y=finish(c,&a,md::f(),md::f_slice(),mode()==3||mode()==5);
 while a.len()<wout{let q=c.alloc_qubit();c.cx(a[N],q);a.push(q);}while y.len()<wout{let q=c.alloc_qubit();c.cx(y[N],q);y.push(q);}Some((a,y))
}
