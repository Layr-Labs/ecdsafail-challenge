//! Read-only short-fragment census, public ecdsa.fail resource research.
use super::Builder;
use crate::circuit::{QubitId,BitId,Op,OperationType as K,NO_BIT};
thread_local!{static TAPE:std::cell::Cell<Option<QubitId>>=const{std::cell::Cell::new(None)};}
pub(crate) fn with_tape(c:&mut Builder,q:Option<QubitId>,body:impl FnOnce(&mut Builder)){
 let old=TAPE.with(|x|x.replace(q));body(c);TAPE.with(|x|x.set(old));
}
pub(crate) fn try_tail(c:&mut Builder,u:&[QubitId],v:&[QubitId],seed:Option<QubitId>)->bool{
 let mode=std::env::var("DIRTY_BOUNDARY_MODE").unwrap_or_default();if mode.is_empty(){return false;}
 let Some(d)=TAPE.with(|x|x.get())else{return false;};let n=u.len();
 let room=super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits()as usize);let r=(n-1).saturating_sub(room);
 if r==0||r>=n-1||seed==Some(v[0]){return false;}
 let before=c.report_totals().map_or(0.,|x|x.1);let op=c.op_count();hybrid(c,u,v,seed,d,r,mode=="dirty");
 eprintln!("DIRTY_DEPLOY\t{}\t{}\t{}\t{}\t{}\t{}\t{}",mode,n,r,room,d.0,op,c.report_totals().map_or(0.,|x|x.1)-before);true
}
pub(crate) fn hybrid(c:&mut Builder,u:&[QubitId],v:&[QubitId],seed:Option<QubitId>,dirty:QubitId,r:usize,use_dirty:bool){
 let n=u.len();assert_eq!(n,v.len());assert!(r>0&&r<n-1);if use_dirty{assert!(!u.contains(&dirty)&&!v.contains(&dirty)&&seed!=Some(dirty));}
 let cut=n-1-r;let alias=seed.is_some_and(|p|v[1..].contains(&p));let cs=c.alloc_qubits(cut);c.x_all(u);
 for i in 0..cut{c.cx(u[i],v[i]);let prev=if i==0{seed.map(|p|{c.cx(u[i],p);p}).unwrap_or(u[i])}else{c.cx(u[i],u[i-1]);u[i-1]};c.ccx(prev,v[i],cs[i]);if i==0&&alias{c.cx(u[i],seed.unwrap());}c.cx(cs[i],u[i]);}
 let stop=if use_dirty{n-2}else{n-1};
 for i in cut..stop{c.cx(u[i],v[i]);c.cx(u[i],u[i-1]);c.ccx(u[i-1],v[i],u[i]);}
 if use_dirty{let i=n-2;c.cz(u[n-1],v[n-1]);c.cx(u[n-1],v[n-1]);c.cx(u[i],v[i]);c.cx(u[i],u[i-1]);c.cz(u[i],v[n-1]);c.cz(dirty,v[n-1]);c.ccx(u[i-1],v[i],dirty);c.cz(dirty,v[n-1]);c.ccx(u[i-1],v[i],dirty);c.cx(u[i],u[i-1]);c.cx(u[i],v[i]);c.cx(u[n-1],v[n-1]);}
 else{c.cz(u[n-1],v[n-1]);c.cz(u[n-1],u[n-2]);c.cz(v[n-1],u[n-2]);}
 for i in(cut..stop).rev(){c.ccx(u[i-1],v[i],u[i]);c.cx(u[i],u[i-1]);c.cx(u[i],v[i]);}
 for i in(0..cut).rev(){c.cx(cs[i],u[i]);let m=c.alloc_bit();c.hmr(cs[i],m);if i==0{if alias{c.cx(u[i],seed.unwrap());}c.cz_if(seed.unwrap_or(u[i]),v[i],m);if let Some(p)=seed{c.cx(u[i],p);}}else{c.cz_if(u[i-1],v[i],m);c.cx(u[i],u[i-1]);}c.cx(u[i],v[i]);c.free_bit(m);}
 c.free_vec(&cs);c.x_all(u);
}

#[derive(Clone,Copy)]enum C{Zero,One,Var(usize)}
fn formal(ops:&[Op],q:&mut[u64],nb:usize,external:BitId,on:bool)->(u64,usize){
 let mut bs=vec![C::Zero;nb];bs[external.0 as usize]=if on{C::One}else{C::Zero};let mut stack=Vec::new();let mut active=true;let mut phase=vec![0u64];let mut dirty=0;
 for op in ops{let cond=if op.c_condition==NO_BIT{C::One}else{bs[op.c_condition.0 as usize]};let enabled=active&&!matches!(cond,C::Zero);let a=op.q_control1.0 as usize;let b=op.q_control2.0 as usize;let t=op.q_target.0 as usize;let cb=op.c_target.0 as usize;
  match op.kind{
   K::PushCondition=>{stack.push(active);assert!(!matches!(cond,C::Var(_)));active=enabled;},K::PopCondition=>active=stack.pop().unwrap(),
   K::X|K::CX|K::CCX|K::Swap=>{if enabled{assert!(!matches!(cond,C::Var(_)));match op.kind{K::X=>q[t]^=u64::MAX,K::CX=>q[t]^=q[a],K::CCX=>q[t]^=q[a]&q[b],K::Swap=>q.swap(t,a),_=>unreachable!()}}},
   K::Z|K::CZ|K::CCZ|K::Neg=>{if enabled{let p=match cond{C::Var(x)=>x,_=>0};let v=match op.kind{K::Z=>q[t],K::CZ=>q[t]&q[a],K::CCZ=>q[t]&q[a]&q[b],K::Neg=>u64::MAX,_=>unreachable!()};phase[p]^=v;}},
   K::Hmr=>{if enabled{assert!(!matches!(cond,C::Var(_)));let id=phase.len();phase.push(q[t]);bs[cb]=C::Var(id);q[t]=0;}},K::R=>{if enabled{dirty|=q[t];q[t]=0;}},
   K::BitStore0=>if enabled{bs[cb]=C::Zero},K::BitStore1=>if enabled{bs[cb]=C::One},K::BitInvert=>if enabled{bs[cb]=match bs[cb]{C::Zero=>C::One,C::One=>C::Zero,_=>panic!("unexpected variable invert")}},K::Register|K::AppendToRegister|K::DebugPrint=>{}
  }
 }
 assert!(stack.is_empty());assert_eq!(dirty,0,"dirty release");assert!(phase[1..].iter().all(|&x|x==0),"HMR phase coefficient");(phase[0],phase.len()-1)
}
fn put(q:&mut[u64],r:&[QubitId],x:u64,l:usize){for(i,w)in r.iter().enumerate(){if x>>i&1!=0{q[w.0 as usize]|=1<<l;}}}
fn get(q:&[u64],r:&[QubitId],l:usize)->u64{r.iter().enumerate().fold(0,|x,(i,w)|x|((q[w.0 as usize]>>l&1)<<i))}
pub fn run(){
 let dir=std::env::var("DIRTY_PROBE_DIR").unwrap();std::fs::create_dir_all(&dir).unwrap();
 for(n,r)in[(3,1),(4,1),(6,1),(6,4),(14,1),(14,5),(20,1),(20,5)]{for sk in 0..3{for mode in 0..3{
  let mut c=Builder::new();let u=c.alloc_qubits(n);let v=c.alloc_qubits(n);let seed=c.alloc_qubit();let d=c.alloc_qubit();let ext=c.alloc_bit();let start=c.op_count();c.push_condition(ext);let si=match sk{0=>None,1=>Some(seed),_=>Some(v[1])};if mode==0{super::compare::cmp_lt_phase(&mut c,&u,&v,si);}else{hybrid(&mut c,&u,&v,si,d,r,mode==1);}c.pop_condition();let t=c.report_totals().unwrap().1;let peak=c.peak_total();let(nq,nb)=c.i13_dims();let ops=c.take_ops();
  assert_eq!(t,((n-1+if mode==0{0}else{r})as f64)/2.);assert_eq!(peak as usize,2*n+2+n-1-if mode==0{0}else{r});
  let mut vals=Vec::new();if n<=6{for a in 0..1u64<<n{for b in 0..1u64<<n{for s in 0..2{for dd in 0..2{vals.push((a,b,s,dd));}}}}}else{let mut z=987654321u64;for _ in 0..4096{z^=z<<13;z^=z>>7;z^=z<<17;let a=z&((1<<n)-1);z^=z<<13;z^=z>>7;z^=z<<17;vals.push((a,z&((1<<n)-1),(z>>31)&1,(z>>37)&1));}}
  let mut phases=0;for rows in vals.chunks(64){for on in[false,true]{let mut q=vec![0;nq];for(l,&(a,b,s,dd))in rows.iter().enumerate(){put(&mut q,&u,a,l);put(&mut q,&v,b,l);put(&mut q,&[seed],s,l);put(&mut q,&[d],dd,l);}let(phi,pcount)=formal(&ops[start..],&mut q,nb,ext,on);phases=phases.max(pcount);for(l,&(a,b,s,dd))in rows.iter().enumerate(){let cin=match sk{0=>0,1=>s,_=>b>>1&1};assert_eq!((get(&q,&u,l),get(&q,&v,l),get(&q,&[seed],l),get(&q,&[d],l)),(a,b,s,dd));assert_eq!(phi>>l&1,u64::from(on&&a<b+cin));}for reg in[&u,&v,&vec![seed,d]]{for x in reg{q[x.0 as usize]=0;}}assert_eq!(q.iter().fold(0,|a,b|a|b),0);}}
  let tag=format!("n{n}-r{r}-seed{sk}-mode{mode}");let dump=ops[start..].iter().map(|x|format!("{} {} {} {} {} {}",x.kind as u8,x.q_target.0,x.q_control1.0,x.q_control2.0,x.c_target.0,x.c_condition.0)).collect::<Vec<_>>().join("\n");std::fs::write(format!("{dir}/{tag}.gates.tsv"),dump).unwrap();println!("{{\"tag\":\"{tag}\",\"n\":{n},\"tail\":{r},\"seed_kind\":{sk},\"mode\":{mode},\"T\":{t},\"Q\":{peak},\"cases\":{},\"external_phase_branches\":2,\"HMR_coefficients\":{phases},\"all_phase_value_dirty_pass\":true}}",vals.len());
 }}}
}
pub(crate) struct Trace{c:*mut Builder,name:&'static str,n:usize,op:usize,live:u32,t:f64}
impl Trace{pub(crate) fn new(c:&mut Builder,name:&'static str,n:usize)->Self{Self{c:c as *mut Builder,name,n,op:c.op_count(),live:c.active_qubits(),t:c.report_totals().map_or(0.,|x|x.1)}}}
impl Drop for Trace{fn drop(&mut self){unsafe{let c=&*self.c;eprintln!("DIRTY_FRAGMENT\t{}\t{}\t{}\t{}\t{}\t{}\t{}",self.name,self.n,self.op,c.op_count(),self.live,c.active_qubits(),c.report_totals().map_or(0.,|x|x.1)-self.t);}}}
