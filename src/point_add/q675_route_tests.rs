//! Test-only local routing overlay. No production allocator or emitter changes.
use super::builder::B;
use crate::circuit::{QubitId,OperationType};
use super::tests_frogdrop::run;
use super::q675_support::{route,ROUTES};
fn model(fam:i8,sy:u8,mut x:u16,active:bool)->u16{
 if active {for &(f,s,o,t,m,v) in ROUTES {if f==fam&&s==sy&&(x as u8&m)==v&&((x>>(5+o))^(x>>t))&1!=0{x^=(1u16<<(5+o))|(1u16<<t);}}}x
}
#[test]
fn q675_four_owner_routes_all_channels(){
 let cases:Vec<(i8,u8,u16)>=include_str!("q675_route_cases.tsv").lines().map(|l|{let x:Vec<i32>=l.split_whitespace().map(|v|v.parse().unwrap()).collect();(x[0]as i8,x[1]as u8,x[2]as u16)}).collect();
 let mut total=0usize;let mut negative=0usize;
 for parity in 0..2 { for fam in -1..5i8 {
  let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258); if parity==1 {std::mem::swap(&mut fd.sy,&mut fd.sx);} let sc=super::frogdrop_col::ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false); let sy=fd.sy[..7].to_vec();let gap=sc.sz[..5].to_vec();let own=vec![sc.bq,fd.q[127],fd.q[126],fd.q[125]];let guards=vec![fd.ph,sc.sw];
  b.begin();route(&mut b,fam,&sy,&gap,&own,&guards,&dirty,false);let rec=b.end();b.play(&rec,false);let forward=b.ops.len();let t=b.tof;b.play(&rec,true);
  assert!(b.ops.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
  let mut bad=B::new();bad.alloc_n(b.width()as usize);route(&mut bad,fam,&sy,&gap,&own,&guards,&dirty,true);
  let selected:Vec<_>=cases.iter().filter(|x|x.0==fam).collect();
  for chunk in selected.chunks(64){for tape in 0..3 {for mode in 0..4 {
   let mut input=vec![0u64;b.width()as usize];
   for (lane,&&(_,size,state)) in chunk.iter().enumerate(){
    for i in 0..7 {if size>>i&1!=0{input[sy[i].0 as usize]|=1<<lane;}}
    for i in 0..5 {if state>>i&1!=0{input[gap[i].0 as usize]|=1<<lane;}}
    for i in 0..4 {if state>>(5+i)&1!=0{input[own[i].0 as usize]|=1<<lane;}}
   }
   for (i,&q) in dirty.iter().enumerate(){input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*7)as u32)};}
   input[guards[0].0 as usize]=match mode{0=>0,1=>u64::MAX,2=>0x5555555555555555,_=>0x3333333333333333};
   input[guards[1].0 as usize]=if mode==3{0xaaaaaaaaaaaaaaaa}else{0};
   let mut want=input.clone();
   for(lane,&&(_,size,state))in chunk.iter().enumerate(){let active=((input[guards[0].0 as usize]|input[guards[1].0 as usize])>>lane)&1==0;let z=model(fam,size,state,active);if active{assert_eq!(z>>5,0);}
    for(i,&q)in gap.iter().chain(own.iter()).enumerate(){want[q.0 as usize]=(want[q.0 as usize]&!(1<<lane))|((((z>>i)&1)as u64)<<lane);}}
   // Unused packed lanes also obey the complete permutation; the padded zero state is fixed.
   let f=run(&b.ops[..forward],b.width()as usize,&|q|*q=input.clone());assert_eq!(f.q,want);assert_eq!(f.phase,0);
   let rt=run(&b.ops,b.width()as usize,&|q|*q=input.clone());assert_eq!(rt.q,input);assert_eq!(rt.phase,0);
   if mode==0&&tape==2{let n=run(&bad.ops,b.width()as usize,&|q|*q=input.clone());for lane in 0..chunk.len(){if own.iter().any(|q|n.q[q.0 as usize]>>lane&1!=0){negative+=1;}}}
   total+=chunk.len();
  }}}
  eprintln!("Q675_ROUTE family={fam} cases={} forward_ops={forward} forward_T={t} local_Q={}",selected.len(),b.width());
 }
 } assert_eq!(cases.len(),19487);assert!(negative>0);eprintln!("Q675_ROUTE_PASS lane_cases={total} omitted_fourth_detected={negative} phase=0 dirty=restored guards=preserved Op_bytes={} G_bytes={}",std::mem::size_of::<crate::circuit::Op>(),std::mem::size_of::<super::builder::G>());
}
