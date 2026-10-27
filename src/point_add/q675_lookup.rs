//! Source-bound lookup transfer from independently reviewed bd1442/cee5.
use super::{builder::B, frogdrop_col::{Fd,ColScr}};
use crate::circuit::QubitId;
// Same binary routing construction as original midg::swap_tree.
fn tree(reg:&[QubitId], leaves:&[(usize,QubitId)], level:usize,
        swaps:&mut Vec<(QubitId,QubitId,QubitId)>)->QubitId {
    assert!(!leaves.is_empty());
    if level==0 {assert_eq!(leaves.len(),1);return leaves[0].1;}
    let bit=level-1;
    let split=leaves.partition_point(|&(v,_)|v>>bit&1==0);
    if split==0||split==leaves.len(){return tree(reg,leaves,bit,swaps);}
    let l=tree(reg,&leaves[..split],bit,swaps);
    let r=tree(reg,&leaves[split..],bit,swaps);
    swaps.push((reg[bit],l,r));l
}

// Disjoint dyadic cover: every eligible code occurs in exactly one term.
fn cover(valid:&[bool;256],lo:usize,span:usize,out:&mut Vec<(usize,usize)>){
    if valid[lo..lo+span].iter().all(|x|!*x){return;}
    if valid[lo..lo+span].iter().all(|x|*x){out.push((lo,span));return;}
    assert!(span>1);cover(valid,lo,span/2,out);cover(valid,lo+span/2,span/2,out);
}

pub(crate) fn park(b:&mut B,fd:&Fd,sc:&ColScr,fam:usize,omit_membership:bool){
    use super::q675_support::CUTS;
    assert!(fam<5);
    for i in 0..5 {
        let leaves:Vec<_>=(1..=128).filter(|&sy|CUTS[sy-1][fam+1]-CUTS[sy-1][fam]>i)
            .map(|sy|(sy,if sy+i<128{fd.q[sy+i]}else{sc.bq})).collect();
        if leaves.is_empty(){continue;}
        let mut valid=[false;256];for &(v,_)in &leaves{valid[v]=true;}
        let mut terms=Vec::new();cover(&valid,0,256,&mut terms);
        for v in 0..256 {assert_eq!(terms.iter().filter(|&&(lo,n)|v>=lo&&v<lo+n).count(),usize::from(valid[v]));}
        let mut swaps=Vec::new();let root=tree(&fd.sy,&leaves,8,&mut swaps);
        assert!(leaves.iter().all(|(_,q)|!fd.sy.contains(q)&&*q!=sc.g&&*q!=fd.sx[1+i]&&!sc.dirty.contains(q)));
        for &(c,a,z)in &swaps{b.cswap(c,a,z);}
        if omit_membership {b.cswap(sc.g,fd.sx[1+i],root);} else {
            for (lo,span)in terms {
                let low=span.trailing_zeros() as usize;
                let mut ctl:Vec<_>=(low..8).map(|k|(fd.sy[k],lo>>k&1==0)).collect();ctl.push((sc.g,false));
                super::mid2::mc_swap(b,&ctl,fd.sx[1+i],root,&[],&sc.dirty);
            }
        }
        for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
    }
}

pub(crate) fn flight(b:&mut B,fd:&Fd,sc:&ColScr,fam:usize,j:usize,lo:usize,hi:usize,literal:bool){
    use super::q675_support::CUTS;
    assert!(fam<5&&j<23&&lo>=1&&hi<=128&&lo<=hi);
    let act=fd.sx[6];let from=fd.sx[7];
    if literal {
        for sy in lo..=hi {let a=CUTS[sy-1][fam];let end=CUTS[sy-1][fam+1];if j<a||j>=end{continue;}
            let pos=sy+j-a;assert!(pos<=128);let target=if pos==128{sc.bq}else{fd.q[pos]};
            let mut ct=vec![(act,false)];ct.extend((0..8).map(|i|(fd.sy[i],sy>>i&1==0)));
            super::mid2::mc_swap(b,&ct,from,target,&[],&sc.dirty);
        }return;
    }
    // Partition by offset i so each group's selected physical target is injective.
    // Different groups have disjoint size support; their full transforms commute.
    for i in 0..5 {
        let leaves:Vec<_>=(lo..=hi).filter(|&sy|{let a=CUTS[sy-1][fam];j==a+i&&j<CUTS[sy-1][fam+1]})
            .map(|sy|(sy,if sy+i<128{fd.q[sy+i]}else{sc.bq})).collect();
        if leaves.is_empty(){continue;}
        let mut valid=[false;256];for &(v,_)in &leaves{valid[v]=true;}
        let mut terms=Vec::new();cover(&valid,0,256,&mut terms);
        let mut swaps=Vec::new();let root=tree(&fd.sy,&leaves,8,&mut swaps);
        assert!(leaves.iter().all(|(_,q)|!fd.sy.contains(q)&&*q!=act&&*q!=from&&!sc.dirty.contains(q)));
        for &(c,a,z)in &swaps{b.cswap(c,a,z);}
        for (v,span)in terms {let low=span.trailing_zeros()as usize;
            let mut ct:Vec<_>=(low..8).map(|k|(fd.sy[k],v>>k&1==0)).collect();ct.push((act,false));
            super::mid2::mc_swap(b,&ct,from,root,&[],&sc.dirty);
        }
        for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
    }
}

pub(crate) fn flight_selected(b:&mut B,fd:&Fd,sc:&ColScr,fam:usize,j:usize,lo:usize,hi:usize)->bool{
    use super::builder::G;
    let cost=|r:&[G]|{assert!(r.iter().all(|g|matches!(g,G::X(..)|G::Cx(..)|G::Ccx(..))));
        (r.iter().filter(|g|matches!(g,G::Ccx(..))).count(),r.len())};
    b.begin();flight(b,fd,sc,fam,j,lo,hi,true);let old=b.end();
    b.begin();flight(b,fd,sc,fam,j,lo,hi,false);let new=b.end();
    let lookup=cost(&new)<cost(&old);b.play(if lookup{&new}else{&old},false);lookup
}

#[cfg(test)]
fn set(q:&mut[u64],id:QubitId,lane:usize,v:bool){q[id.0 as usize]&=!(1<<lane);if v{q[id.0 as usize]|=1<<lane;}}

#[test]
fn q675_lookup_transport_exact_all_size_codes(){
    super::bake_knobs();let mut lanes=0;let mut negatives=0;
    for parity in 0..2 {for fam in 0..5 {
        let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
        if parity==1{std::mem::swap(&mut fd.sy,&mut fd.sx);}
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        b.begin();super::q675_support::park_literal(&mut b,&fd,&sc,fam);let old=b.end();
        b.play(&old,false);let oldops=b.ops.clone();let oldt=b.tof;b.ops.clear();b.tof=0;
        b.begin();park(&mut b,&fd,&sc,fam,false);let new=b.end();
        b.play(&new,false);let newops=b.ops.clone();let newt=b.tof;assert!(newt<oldt);b.ops.clear();b.tof=0;
        b.play(&new,true);let inv=b.ops.clone();b.ops.clear();b.tof=0;
        park(&mut b,&fd,&sc,fam,true);let bad=b.ops.clone();
        assert_eq!(b.width(),675);
        let mut rng=0x8badf00ddecafbad_u64;
        for batch in 0..4 {for noise in 0..4 {for active in [0,u64::MAX,0x5555555555555555] {
            let mut q=vec![0u64;675];
            for x in &mut q {rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;*x=match noise{0=>0,1=>u64::MAX,_=>rng};}
            q[sc.g.0 as usize]=active;
            for lane in 0..64 {let sy=64*batch+lane;for i in 0..8{set(&mut q,fd.sy[i],lane,sy>>i&1!=0);}}
            let mut expected=q.clone();
            for lane in 0..64 {let sy=64*batch+lane;if !(1..=128).contains(&sy)||active>>lane&1==0{continue;}
                let len=super::q675_band_handoff_tests::CUTS[sy-1][fam+1]-super::q675_band_handoff_tests::CUTS[sy-1][fam];
                for i in 0..len {let a=fd.sx[1+i].0 as usize;let z=if sy+i<128{fd.q[sy+i]}else{sc.bq}.0 as usize;
                    let d=(expected[a]^expected[z])&(1<<lane);expected[a]^=d;expected[z]^=d;}
            }
            let run=|ops:&[_],q:&[u64]|super::q675_vform_tests::run_tape(ops,675,q,2);
            let a=run(&oldops,&q);let c=run(&newops,&q);
            assert_eq!(a.q,expected);assert_eq!(c.q,expected);assert_eq!(c.phase,0);
            assert_eq!(run(&inv,&expected).q,q);
            let wrong=run(&bad,&q);let mut changed=0;for(x,y)in wrong.q.iter().zip(&expected){changed|=x^y;}
            negatives+=changed.count_ones() as usize;lanes+=64;
        }}}
        eprintln!("Q675_LOOKUP family={fam} parity={parity} old_ops={} new_ops={} old_T={oldt} new_T={newt} Q=675 no_new_ancilla=true",oldops.len(),newops.len());
    }}
    assert!(negatives>0);
    eprintln!("Q675_LOOKUP_PASS lanes={lanes} missing_membership_negative_lanes={negatives} all_size_codes=256 arbitrary_data_and_dirty=true complete_quantum_phase_receipts_statistics_rng=true production=false");
}

#[test]
fn q675_flight_transport_all_sizes_and_column_ranges(){
    super::bake_knobs();let mut lanes=0;let mut aggregate=[0u64;4];let mut regressions=0;
    let(cps,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let mut ranges:std::collections::BTreeSet<_>=cps.iter().map(|c|(c.sy.0.max(1),c.sy.1.min(128))).collect();ranges.insert((1,128));
    let nr=ranges.len();let mut lookup_calls=0;
    for parity in 0..2 {for &(lo,hi)in &ranges {for fam in 0..5 {for j in 0..23 {
        let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
        if parity==1{std::mem::swap(&mut fd.sy,&mut fd.sx);}
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        b.begin();flight(&mut b,&fd,&sc,fam,j,lo,hi,true);let oldr=b.end();b.play(&oldr,false);let old=b.ops.clone();let oldt=b.tof;b.ops.clear();b.tof=0;
        b.begin();if flight_selected(&mut b,&fd,&sc,fam,j,lo,hi){lookup_calls+=1;}let r=b.end();b.play(&r,false);
        let new=b.ops.clone();let newt=b.tof;b.ops.clear();b.tof=0;b.play(&r,true);let inv=b.ops.clone();
        assert_eq!(b.width(),675);assert!(new.len()<10000&&old.len()<10000);
        if newt>oldt{regressions+=1;}
        aggregate[0]+=old.len()as u64;aggregate[1]+=new.len()as u64;aggregate[2]+=oldt;aggregate[3]+=newt;
        if old.is_empty(){assert!(new.is_empty());continue;}
        let mut rng=0x9e3779b97f4a7c15_u64;
        for batch in 0..4 {for active in [0,u64::MAX,0x5555555555555555] {
            let mut q=vec![0u64;675];for x in &mut q{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;*x=rng;}
            q[fd.sx[6].0 as usize]=active;
            for lane in 0..64 {let sy=64*batch+lane;for k in 0..8{set(&mut q,fd.sy[k],lane,sy>>k&1!=0);}}
            let mut want=q.clone();
            for lane in 0..64{let sy=batch*64+lane;if sy<lo||sy>hi||active>>lane&1==0{continue;}
                let a=super::q675_band_handoff_tests::CUTS[sy-1][fam];let end=super::q675_band_handoff_tests::CUTS[sy-1][fam+1];if j<a||j>=end{continue;}
                let pos=sy+j-a;let z=if pos==128{sc.bq}else{fd.q[pos]}.0 as usize;let c=fd.sx[7].0 as usize;
                let d=(want[c]^want[z])&(1<<lane);want[c]^=d;want[z]^=d;
            }
            let run=|ops:&[_],q:&[u64]|super::q675_vform_tests::run_tape(ops,675,q,2);
            assert_eq!(run(&old,&q).q,want);assert_eq!(run(&new,&q).q,want);assert_eq!(run(&inv,&want).q,q);lanes+=64;
        }}
    }}}}
    assert_eq!(regressions,0);
    eprintln!("Q675_FLIGHT_LOOKUP_PASS ranges={nr} lanes={lanes} old_ops={} new_ops={} old_T={} new_T={} T_regressions={regressions} lookup_selected_calls={lookup_calls} Q=675 complete_quantum_phase_receipts_stats_rng=true all_encoded_sizes=256 production=false",aggregate[0],aggregate[1],aggregate[2],aggregate[3]);
}
