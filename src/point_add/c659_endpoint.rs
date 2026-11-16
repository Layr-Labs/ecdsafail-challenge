//! Qualified endpoint substitutions in their exact sequential lifetimes.
//! B0 uses q114, returns it, then raw payload endpoint uses q99. q108 is
//! never the raw helper; it remains the parent's independent narrow temp.
use super::builder::{B,G};
use super::c659_column::Column;
use super::fixed_epoch::EndpointLayout;
use super::frogdrop_col::{ColPar,ColScr,Fd};
use crate::circuit::QubitId;
use std::collections::BTreeSet;
fn b0_flag(b:&mut B,col:&Column<'_>,flag:QubitId,dirty:&[QubitId]){
 let cnt=&col.q[121..128];b.x(flag);b.cx(cnt[0],flag);
 for value in 1..128{if super::frogdrop_col::map_ctrl_skipped(value)%2==1{
  let ctl:Vec<_>=cnt.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)).collect();
  super::mask::mc_xor(b,&ctl,flag,&[],dirty);
 }}
}
/// The old logical prefix appears exactly once after cut/toggle in the
/// parent's ordered scratch/donor list. Build its replacement in that same
/// position, after the parent's exclusion/dedup step; it is not refiltered.
fn b0_ports(col:&Column<'_>)->(Vec<QubitId>,Vec<QubitId>){
 let r=col.roles;
 let mut scratch:Vec<_>=std::iter::once(r.tag).chain(col.meta.sum.iter().copied()).chain([r.cut,r.toggle]).collect();
 let mut excluded:BTreeSet<_>=[r.tag,col.phase].into_iter().collect();excluded.extend(col.q[114..].iter().copied());
 if let Some(p)=col.compact{excluded.extend(p.iter().copied());}
 let mut seen=BTreeSet::new();
 let mut dirty:Vec<_>=col.ring.iter().chain(&col.q[..114]).chain(&col.meta.y).chain(&scratch[1..]).copied()
  .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect();
 // q114 was excluded above. This insertion is the exact old prefix slot.
 dirty.push(col.q[114]);
 dirty.extend(col.dirty.iter().copied().filter(|q|!excluded.contains(q)&&seen.insert(*q)));
 scratch.push(col.q[114]);assert_eq!(scratch.len(),9);(scratch,dirty)
}
fn raw_entry(b:&mut B,col:&Column<'_>)->(EndpointLayout,Vec<G>){
 let r=col.roles;let q=col.q;let meta=col.meta;
 let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).chain(q).copied()
  .chain([r.tag,r.cut,r.toggle,col.phase]).collect();
 assert_eq!(used.len(),144);
 let d:Vec<_>=col.ring.iter().copied().filter(|p|used.insert(*p)).collect();assert_eq!(d.len(),257);
 let high=[q[114],q[115],q[116]];
 let layout=EndpointLayout{
 raw_y:[meta.y[0],meta.y[1],meta.y[2],meta.y[3],meta.y[4],high[0],high[1],high[2]],
 sx:[r.cut,r.toggle,q[99],r.tag,meta.sum[4],meta.y[5],meta.y[6]],
 pool:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3]],
 raw_z:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3],q[112],q[109],q[110],q[111]],
 qmap_end:114,replay_helper:q[117],b0_flag:q[118],tz:q[119],payload_extra:q[113],sum_ninth:q[117]};
 b.begin();super::frogdrop::add_const_dirty_exact(b,&meta.y,1,&d);
 for i in 0..2{b.cx(meta.y[5+i],high[i]);b.cx(high[i],meta.y[5+i]);}
 (layout,b.end())
}
pub(crate) fn finish(b:&mut B,col:&Column<'_>,b0:Option<&ColPar>,last:&ColPar){
 assert!(!super::frogdrop_col::c660_joint_size());assert!(last.nomap&&last.ht&&last.sy==(1,1));
 assert_eq!((col.ring.len(),col.q.len()),(257,128));
 let(scratch,dirty)=b0_ports(col);
 if let Some(cp)=b0{
  assert!(cp.sz==(0,0)&&cp.dn&&cp.m==28&&cp.emax<=31);
  let par=super::frogdrop::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:128,tail:cp.tail,emax:cp.emax};
  let old_booth=b.allow_booth;b.allow_booth=false;
  let capture=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
   super::frogdrop::direct_map::stage_record(b,col.ring,&col.q[..114],&col.meta.y,&scratch,col.phase,&par,28,&dirty)));
  b.allow_booth=old_booth;
  let tape=match capture{Ok(t)=>t,Err(e)=>std::panic::resume_unwind(e)};
  b0_flag(b,col,col.roles.tag,&dirty);b.x(col.phase);b.play_ctrl(&tape,col.roles.tag,col.phase);b.x(col.phase);b0_flag(b,col,col.roles.tag,&dirty);
 }
 // q114's B0 lifetime is closed before it hosts raw Y's upper transport.
 if let Some(p)=col.compact{
  let(layout,entry)=raw_entry(b,col);assert_eq!(layout.sx[2],col.q[99]);assert_ne!(layout.sx[2],col.q[108]);
  let raw=Fd{ring:col.ring.to_vec(),q:col.q.to_vec(),sy:layout.raw_y.to_vec(),sx:layout.sx.to_vec(),ph:col.phase,cnt:col.q[121..128].to_vec()};
  let mut sc=ColScr::carve_col(&layout.pool,&layout.sx,col.dirty,last.kp,last.qb,last.tail,false);sc.sz=layout.raw_z.to_vec();
  let payload=super::pointadd_frogdrop::pl_col(p,&raw,&layout.pool);assert!(!payload.dirty.contains(&col.q[99]));
  b.play(&entry,false);super::payload::pl_end(b,&raw,last,&sc,&payload);b.play(&entry,true);
 }
}
