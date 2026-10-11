use super::builder::B;use super::frogdrop_col::{Fd,ColScr};use crate::circuit::{QubitId,BitId};
// Exact diagonal q-cache phase at inverse corrected HT seam: qtrue=active*(q0-bq).
// ps.q0 may be arbitrary on inactive; bq is original recreated tag501 value.
// ph/cnt/q0/bq read-only after cleanup. Four PScr misc globals are0 here.
pub fn restore_phase(b:&mut B,fd:&Fd,sc:&ColScr,masks:&[BitId]){
 let q=&sc.ps.q0;assert_eq!(q.len(),26);assert_eq!(masks.len(),q.len());let active=sc.act;let tmp=sc.cmpc;let work=[sc.cmpc,sc.g,sc.c0];
 let mut seen=std::collections::BTreeSet::new();for w in q.iter().chain(&fd.cnt).chain([fd.ph,sc.bq,active,sc.cmpc,sc.g,sc.c0].iter()){assert!(seen.insert(w.0));}
 let mut lits=vec![(fd.ph,false)];lits.extend(fd.cnt.iter().map(|&w|(w,true)));
 super::mask::mc_xor(b,&lits,active,&work,&sc.dirty);
 b.begin();super::frogdrop::inc_mixed(b,sc.bq,q,&work,&sc.dirty);let increment=b.end();
 b.play(&increment,true);
 for (&qi,&mi)in q.iter().zip(masks){b.and_c(active,qi,tmp);b.z_if(tmp,mi);b.and_u(active,qi,tmp);}
 b.play(&increment,false);
 super::mask::mc_xor(b,&lits,active,&work,&sc.dirty);
}
pub fn first_active(b:&mut B,fd:&Fd,pool:&[QubitId]){let mut lits=vec![(fd.ph,false)];lits.extend(fd.cnt.iter().map(|&w|(w,true)));super::mask::mc_xor(b,&lits,pool[54],&pool[..7],&[]);}


