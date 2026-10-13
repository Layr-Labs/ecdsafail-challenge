//! Actual carved698-wire map, including parking and controlled B0. Finite only.
use super::builder::{B, G};
use super::frogdrop_col::{Fd, ColScr, map_stage};
use super::frogdrop_sched::N;
use super::tests_frogdrop::{map_cases, Rng};
use crate::circuit::{Op, analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, value: N) {
    for (i,&q) in qs.iter().enumerate() {
        w[q.0 as usize]=(w[q.0 as usize]&!(1u64<<shot))
            |(u64::from(value.bit(i))<<shot);
    }
}
fn run(ops: &[Op], initial: &[u64], salt:u64) -> (Vec<u64>,u64) {
    let (_, bits, _, _)=analyze_ops(ops.iter());
    let mut h=sha3::Shake256::default(); h.update(b"q698-owned-map-measurements");
    h.update(&salt.to_le_bytes()); let mut xof=h.finalize_xof();
    let mut sim=Simulator::new(initial.len(),(bits as usize).max(1),&mut xof);
    sim.qubits.copy_from_slice(initial); sim.apply_iter(ops.iter());
    (sim.qubits,sim.phase)
}
fn inverse(recipe:&[G])->Vec<G> {
    recipe.iter().rev().map(|g|match *g {
        G::AndC(a,c,t)=>G::AndU(a,c,t), G::AndU(a,c,t)=>G::AndC(a,c,t),
        G::RowAdd(i,inv)=>G::RowAdd(i,!inv),
        G::DeferredErase(i,inv)=>G::DeferredErase(i,!inv), x=>x,
    }).collect()
}

#[test]
fn q698_actual_carve_map_all_sy_ordinary_switch_park_and_b0() {
    let schedule=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols,b0,_)=super::pointadd_frogdrop::col_pars(&schedule);
    assert!(b0.as_ref().unwrap().m<=128-super::pointadd_frogdrop::CNTB);
    let mut admitted=Vec::new();
    for seed in 491..523 {
        for case in map_cases(seed,64) {
            if !case.1.is_zero() && !case.2.is_zero()
                && case.1.bit_len().max(case.2.bit_len())<=128 {
                admitted.push(case);
                if admitted.len()==64 {break;}
            }
        }
        if admitted.len()==64 {break;}
    }
    assert_eq!(admitted.len(),64,"fixed component admission, not a contest screen");
    let p=(N::from(1u64)<<256)-(N::from(1u64)<<32)-N::from(977u64);
    let mut rng=Rng::new(0x698);
    let done:Vec<_>=(0..64).map(|_|{
        let x=rng.below(23)|(N::from(1u64)<<23)|N::from(1u64);
        let z=p/x; (z,x,N::from(1u64),p-z*x)
    }).collect();
    for kind in 0..4 {
        let mut b=B::new(); b.allow_booth=kind!=3;
        let ring=b.alloc_n(281); let q=b.alloc_n(128); let sy=b.alloc_n(8);
        let sx=b.alloc_n(8); let ph=b.alloc(); let pool=b.alloc_n(13);
        let dirty=b.alloc_n(259);
        assert_eq!(b.width(),698);
        let cnt=q[121..].to_vec();
        let fd=Fd{ring:ring.clone(),q:q.clone(),sy:sy.clone(),sx:sx.clone(),ph,cnt:cnt.clone()};
        let sc=ColScr::carve(&pool,&sx,&dirty,24,24,40);
        let mut cp=cols[10].clone();
        cp.sz=(1,255); cp.sy=(1,128); cp.smax=(1,128); cp.m=128;
        cp.sw=kind==1; cp.dn=kind>=2; cp.cntw=if kind>=2 {7}else{0};
        if kind==3 {
            cp=b0.as_ref().unwrap().clone();
            assert_eq!(cp.smax,(1,28),"actual frozen B0 envelope");
            assert_eq!(cp.m,28);
        }
        let cases=if kind>=2 {&done}else{&admitted};
        let recipe=map_stage(&mut b,&fd,&cp,&sc);
        if kind==3 { b.play_ctrl(&recipe,sc.sw,sc.bq); }
        else { b.play(&recipe,false); }
        let fwd=b.ops.len();
        if kind==3 { b.play_ctrl(&inverse(&recipe),sc.sw,sc.bq); }
        else { b.play(&recipe,true); }
        let mut initial=vec![0u64;698];
        let ctrl=0xa5a5_5a5a_9696_6969u64;
        if kind==3 {initial[sc.sw.0 as usize]=ctrl;}
        if kind>=2 {initial[ph.0 as usize]=u64::MAX;}
        for (i,&wire) in dirty.iter().enumerate() {
            initial[wire.0 as usize]=0x9e37_79b9_7f4a_7c15u64.rotate_left(i as u32)
                ^0xa5a5_5a5a_9696_6969u64.wrapping_mul(i as u64+1);
        }
        let mut expected=initial.clone();
        for (shot,&(z,x,y,next)) in cases.iter().enumerate() {
            let cut=281-x.bit_len().max(y.bit_len());
            let top:Vec<_>=ring[cut..].iter().rev().copied().collect();
            put(&mut initial,&ring[..cut],shot,z); put(&mut initial,&top,shot,y);
            put(&mut initial,if kind>=2 {&q[..121]}else{&q},shot,x);
            put(&mut initial,&sy,shot,N::from(y.bit_len() as u64));
            if kind>=2 {put(&mut initial,&cnt,shot,N::from((shot%127+1) as u64));}
        }
        expected.copy_from_slice(&initial);
        for (shot,&(_,x,y,next)) in cases.iter().enumerate() {
            if kind==3 && ctrl>>shot&1==0 {continue;}
            let cut=281-x.bit_len().max(y.bit_len());
            let top:Vec<_>=ring[cut..].iter().rev().copied().collect();
            put(&mut expected,&ring[..cut],shot,next); put(&mut expected,&top,shot,x);
            put(&mut expected,if kind>=2 {&q[..121]}else{&q},shot,y);
            put(&mut expected,&sy,shot,N::ZERO);
            put(&mut expected,&sx,shot,N::from(x.bit_len() as u64));
        }
        for salt in [0u64,1,0x4ab7] {
            let (fw,pf)=run(&b.ops[..fwd],&initial,salt);
            assert_eq!(pf,0,"forward phase kind{kind} salt{salt}");
            assert_eq!(fw,expected,"full698 forward state kind{kind} salt{salt}");
            let (both,pb)=run(&b.ops,&initial,salt);
            assert_eq!(pb,0,"roundtrip phase kind{kind} salt{salt}");
            assert_eq!(both,initial,"full698 roundtrip kind{kind} salt{salt}");
        }
        eprintln!("OWNED_Q698_MAP_PASS kind={kind} width698 cases64 salts3 forward_ops={fwd} actual_carve=true complete_states_dirty_counter_control=true");
    }
}
