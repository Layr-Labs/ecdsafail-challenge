//! Exact original-care HT pair, asymmetric F with complete original I.
//! Fresh typed HY/q/HC masks; no HMR is recorded or declared self-inverse.
use super::builder::{B,G};
use super::frogdrop_col::{Fd,ColScr,ColPar};
use super::frogdrop::{Cut,MapPar,rot_by_source_support};
use crate::circuit::{QubitId,BitId};
#[derive(Clone,Debug)]pub(crate)struct FusionMasks{
 pair:usize,ring:Vec<QubitId>,q:Vec<QubitId>,hy:Vec<QubitId>,hc:Vec<QubitId>,cache:Vec<QubitId>,
 ph:QubitId,cnt:Vec<QubitId>,pool:Vec<QubitId>,dirty:Vec<QubitId>,shape:String,m1:usize,m2:usize,mhy:Vec<BitId>,mq:Vec<BitId>,mhc:Vec<BitId>,
}
fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn column_rec(b:&mut B,fd:&mut Fd,cp:&ColPar,sc:&ColScr)->(Vec<G>,Vec<(usize,usize)>){
 b.component_stage_marks.clear();b.begin();super::frogdrop_col::column(b,fd,cp,sc);let r=b.end();
 let marks=std::mem::take(&mut b.component_stage_marks);assert_eq!(marks.len(),10);assert_eq!(marks.last().unwrap().1,r.len());
 for(i,&(stage,end))in marks.iter().enumerate(){assert_eq!(stage,i+1);assert!(end<=r.len());}
 (r,marks)
}
fn range(m:&[(usize,usize)],stage:usize)->std::ops::Range<usize>{let end=m[stage-1].1;let start=if stage==1{0}else{m[stage-2].1};start..end}
fn prefix_swap(b:&mut B,ring:&[QubitId],q:&[QubitId],hc:&[QubitId],active:QubitId,m:usize,work:&[QubitId]){
 use super::mask::{Dec,mc_xor};let(f,tmp,u)=(work[0],work[1],work[2]);let pre=&work[3..10];let hb=(usize::BITS-m.leading_zeros())as usize;let mut header=hc[..hb].to_vec();header.push(active);let mut dec=Dec::new(&header,pre);
 for i in(0..m).rev(){let lits=dec.ctrls(b,(1usize<<hb)|(i+1));mc_xor(b,&lits,f,&[tmp],&[]);b.cswap(f,ring[ring.len()-1-i],q[i]);}dec.clear(b);
 super::mask::ge_const(b,hc,1,u,pre);b.ccx(active,u,f);super::mask::ge_const(b,hc,1,u,pre);super::mask::ge_const(b,hc,m as isize+1,u,pre);b.ccx(active,u,f);super::mask::ge_const(b,hc,m as isize+1,u,pre);
}
fn echo(b:&mut B,fd:&Fd,hy:&[QubitId],hc:&[QubitId],pool:&[QubitId],dirty:&[QubitId],m:usize,inverse:bool){
 let mut cache=fd.q[121..138].to_vec();cache.extend_from_slice(&pool[55..64]);let qr=&pool[..26];let work=&pool[26..54];let act=pool[54];
 for(&a,&t)in cache.iter().zip(qr){b.swap(a,t);}
 let target:Vec<_>=fd.ring.iter().rev().take(m).copied().collect();let source=&fd.q[..m];
 super::ht_window_parking::swap_hy(b,source,&target,hy,act,work);
 super::ht_window_parking::park(b,source,&cache,hc,hy,act,work);
 super::ht_radix4_clean_echo::echo(b,&target,source,qr,act,work,dirty,inverse);
 super::ht_window_parking::swap_hy(b,source,&target,hy,act,work);
 let unpark=rec(b,|b|super::ht_window_parking::park(b,&target,&cache,hc,hy,act,work));b.play(&unpark,true);
 for(&a,&t)in cache.iter().zip(qr){b.swap(a,t);}
}
fn kernel(b:&mut B,fd:&Fd,q:&[QubitId],hc:&[QubitId],cp:&ColPar,source_m:usize,sc:&ColScr,pool:&[QubitId],inverse:bool){
 let held=&pool[55..64];let active=pool[54];let mut ms=sc.ms.clone();ms.andc.extend([sc.bq,sc.sw]);
 ms.anc.retain(|w|!held.contains(w)&&*w!=active);ms.andc.retain(|w|!held.contains(w)&&*w!=active);
 let mut bank=super::priority_probe::map_bank(&ms);bank.retain(|w|!ms.ez.contains(w));assert!(!bank.contains(&active)&&!bank.iter().any(|w|held.contains(w)));
 let cut=Cut{v:hc.to_vec(),a:fd.ring.len()as isize,neg:true};let par=MapPar{clo:fd.ring.len()-cp.smax.1,chi:fd.ring.len()-cp.smax.0,m:source_m,tail:cp.tail,emax:cp.emax};
 super::priority_probe::trailing(b,q,28,&ms.ez,&bank);
 rot_by_source_support(b,q,&ms.ez,source_m,true);
 super::frogdrop::fusion_kernel_invoice(b,&fd.ring,q,&cut,&par,&ms,inverse);
 rot_by_source_support(b,q,&ms.ez,source_m,false);
 super::priority_probe::trailing(b,q,28,&ms.ez,&bank);
}
fn validate_pair(cp1:&ColPar,cp2:&ColPar){for cp in[cp1,cp2]{assert!(cp.ht&&!cp.hr&&!cp.sw&&cp.dn&&cp.fin&&!cp.nomap);assert_eq!(cp.n,288);assert_eq!(cp.nq,138);assert_eq!(cp.emax,28);assert!(cp.m<=121&&cp.m>=28);}}
pub(crate)fn forward(b:&mut B,fd:&mut Fd,cp1:&ColPar,cp2:&ColPar,pool:&[QubitId],dirty:&[QubitId],pair:usize){
 validate_pair(cp1,cp2);assert!(b.allow_booth);assert_eq!(pool.len(),64);b.header_erasure_enabled=false;
 let hy=fd.sy.clone();let hc=fd.sx.clone();let sc1=ColScr::carve(pool,&hc,dirty,30,24,40);
 let(r1,marks1)=column_rec(b,fd,cp1,&sc1);assert_eq!(fd.sy,hc);assert_eq!(fd.sx,hy);
 // Every real first nonmap mask is kept unchanged. Its complete source and
 // header domain precedes any new arithmetic. Original first map is omitted.
 b.fusion_mode(1);for stage in 1..=8{b.play(&r1[range(&marks1,stage)],false);}
 super::priority_probe::emit(b,&fd.q,0,cp1.m,&hc,&pool[..54]);
 b.play(&r1[range(&marks1,10)],false); // genuine first FIN/CNT with HC already live
 b.fusion_discard_unused(&r1[range(&marks1,9)]);drop(r1);
 b.fusion_mode(0);
 super::ht_fusion_qphase::first_active(b,fd,pool); // CNT epoch after first finish
 let mut cache=fd.q[121..138].to_vec();cache.extend_from_slice(&pool[55..64]);
 let y:Vec<_>=fd.ring.iter().rev().take(cp1.m).copied().collect();
 super::ht_packed_divmod::divmod(b,&y,&fd.q[..cp1.m],&hy,&hc,&cache,pool[54],&pool[..20]);
 prefix_swap(b,&fd.ring,&fd.q[..121],&hc,pool[54],cp1.m,&pool[..10]);
 kernel(b,fd,&fd.q[..121],&hc,cp2,cp2.m,&sc1,pool,false);
 super::qp_naf_cut::correction(b,&fd.ring,&cache,&hc,cp2.m,pool[54],&pool[..18]);
 echo(b,fd,&hy,&hc,pool,dirty,cp1.m,false);
 kernel(b,fd,&fd.q[..121],&hc,cp2,cp1.m,&sc1,pool,true);
 echo(b,fd,&hy,&hc,pool,dirty,cp1.m,true);
 prefix_swap(b,&fd.ring,&fd.q[..121],&hc,pool[54],cp1.m,&pool[..10]);
 // HY lives until both echoes. Fresh masks are immutable through all products
 // and popped only at the same pair's regenerated original inverse.
 let mhy=b.fresh_bits(hy.len());
 let mq=b.fresh_bits(cache.len());for(&q,&m)in cache.iter().zip(&mq){b.hmr_to(q,m);}
 // The public ring prefix includes foreign low-cofactor data when its top
 // is short. Preserve original HY as the exact source mask until HD is made.
 // q HMR made these eight physical cache lanes GLOBAL0, with no new qubit.
 let hd=&cache[..hy.len()];let zrev:Vec<_>=fd.ring.iter().rev().copied().collect();
 let old_y_cut=Cut::reg(&hy);
 super::masked_priority_probe::emit(b,&zrev,&old_y_cut,0,cp2.m,0,cp2.m,hd,&pool[..54],dirty);
 for(&q,&m)in hy.iter().zip(&mhy){b.hmr_to(q,m);}
 let mhc=b.fresh_bits(hc.len());for(&q,&m)in hc.iter().zip(&mhc){b.hmr_to(q,m);}
 for(&a,&t)in hd.iter().zip(&hy){b.swap(a,t);} // cache returns zero, HY is exact HD
 super::ht_fusion_qphase::first_active(b,fd,pool); // clear before second finish changes CNT
 let sc2=ColScr::carve(pool,&hy,dirty,30,24,40);
 let(r2,marks2)=column_rec(b,fd,cp2,&sc2);assert_eq!(fd.sy,hy);assert_eq!(fd.sx,hc);
 b.fusion_mode(1);b.play(&r2[range(&marks2,10)],false); // exact second CNT/DONE
 for stage in 1..=9{b.fusion_discard_unused(&r2[range(&marks2,stage)]);}drop(r2);
 b.fusion_tape.push(FusionMasks{pair,ring:fd.ring.clone(),q:fd.q.clone(),hy,hc,cache,ph:fd.ph,cnt:fd.cnt.clone(),pool:pool.to_vec(),dirty:dirty.to_vec(),shape:format!("{:?}|{:?}",cp1,cp2),m1:cp1.m,m2:cp2.m,mhy,mq,mhc});
}
pub(crate)fn inverse(b:&mut B,fd:&mut Fd,cp1:&ColPar,cp2:&ColPar,pool:&[QubitId],dirty:&[QubitId],pair:usize){
 validate_pair(cp1,cp2);assert!(b.allow_booth);b.header_erasure_enabled=false;
 let masks=b.fusion_tape.pop().expect("missing fused forward masks");assert_eq!(masks.pair,pair);assert_eq!(masks.ring,fd.ring);assert_eq!(masks.q,fd.q);assert_eq!(masks.hy,fd.sy);assert_eq!(masks.hc,fd.sx);assert_eq!(masks.m1,cp1.m);assert_eq!(masks.m2,cp2.m);assert_eq!(masks.ph,fd.ph);assert_eq!(masks.cnt,fd.cnt);assert_eq!(masks.pool,pool);assert_eq!(masks.dirty,dirty);assert_eq!(masks.shape,format!("{:?}|{:?}",cp1,cp2));
 let mut cache=fd.q[121..138].to_vec();cache.extend_from_slice(&pool[55..64]);assert_eq!(cache,masks.cache);
 assert!(masks.mhy.iter().chain(&masks.mq).chain(&masks.mhc).all(|m|m.0>=10000&&m.0<b.fusion_mask_upper()));
 for(which,cp)in[(2,cp2),(1,cp1)]{
  std::mem::swap(&mut fd.sy,&mut fd.sx);let names=(fd.sy.clone(),fd.sx.clone());
  let sc=ColScr::carve(pool,&fd.sx,dirty,30,24,40);let(rec,marks)=column_rec(b,fd,cp,&sc);
  b.fusion_mode(2);b.play(&rec[range(&marks,10)],true); // inverse FIN restores exact entry CNT
  b.fusion_mode(0);b.play(&rec[range(&marks,9)],true);
  let(header,phase)=if which==2{(&masks.hc,&masks.mhc)}else{(&masks.hy,&masks.mhy)};
  for(&q,&m)in header.iter().zip(phase){b.z_if(q,m);} // same fully restored original header
  for stage in(1..=8).rev(){
   if which==1{b.fusion_mode(2);b.play(&rec[range(&marks,stage)],true);}
   else if stage==6{
    let s=&rec[range(&marks,stage)];let id=match *s.last().expect("empty HT correction"){G::DeferredErase(id,false)=>id,_=>panic!("HT tag501 not final correction gate")};assert_eq!(b.fusion_erasure_tag(id),501);
    b.play(&s[s.len()-1..],true); // exact original E^-1 recreates correction bq
    super::ht_fusion_qphase::restore_phase(b,fd,&sc,&masks.mq);
    b.play(&s[..s.len()-1],true); // only now inverse correction/sign
   }else{b.play(&rec[range(&marks,stage)],true);}
  }
  b.fusion_mode(2);fd.sy=names.0;fd.sx=names.1;
  if which==2{for stage in 1..=9{b.fusion_discard_unused(&rec[range(&marks,stage)]);}} // completed local-I replay recipes, after their final physical use
  drop(rec);
 }
 assert_eq!(fd.sy,masks.hy);assert_eq!(fd.sx,masks.hc);
}
