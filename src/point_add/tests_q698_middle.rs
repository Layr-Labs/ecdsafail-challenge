//! Actual Scheme-G middle with a distinct external q23 owner. Finite only.
use super::builder::B;
use super::frogdrop_col::{ColScr, Fd};
use super::frogdrop_sched::N;
use super::pointadd_frogdrop::{col_pars, pl_col, SCHED_FROGDROP};
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, value: N) {
    for (i,&q) in qs.iter().enumerate() {
        w[q.0 as usize]=(w[q.0 as usize]&!(1u64<<shot))
            |(u64::from(value.bit(i))<<shot);
    }
}
fn apply(ops: &[Op], initial: &[u64], salt: u64) -> (Vec<u64>,u64) {
    for op in ops { op.validate(); }
    let (_, bits, _, _)=analyze_ops(ops.iter());
    let mut h=sha3::Shake256::default(); h.update(b"q698-external-q23-middle");
    h.update(&salt.to_le_bytes()); let mut xof=h.finalize_xof();
    let mut sim=Simulator::new(initial.len(),(bits as usize).max(1),&mut xof);
    sim.qubits.copy_from_slice(initial); sim.apply_iter(ops.iter());
    (sim.qubits,sim.phase)
}
fn frame(b: &mut B) -> (Fd, Vec<QubitId>, Vec<QubitId>) {
    let ring=b.alloc_n(281); let q=b.alloc_n(128);
    let sy=b.alloc_n(8); let sx=b.alloc_n(8); let ph=b.alloc();
    let pool=b.alloc_n(13); let dirty=b.alloc_n(259);
    assert_eq!(b.width(),698);
    let cnt=q[121..].to_vec();
    (Fd{ring,q,sy,sx,ph,cnt},pool,dirty)
}

#[test]
fn q698_actual_middle_q23_hr_ht_complete_states() {
    let sched=super::frogdrop_sched::from_text(SCHED_FROGDROP);
    let (cols,_,_)=col_pars(&sched);
    let mut cp=cols[3].clone();
    cp.sz=(209,255); cp.sy=(1,45); cp.xw=48; cp.smax=(1,48);
    cp.m=48; cp.hr=true; cp.ht=true; cp.sw=true; cp.dn=false;
    cp.tt=false; cp.dl=false; cp.dq=false; cp.psw=false; cp.pht=false;
    cp.fin=false; cp.cntw=0;
    let mut visits=0usize; let mut high_quotients=0usize;
    for returned_head in [false,true] {
    cp.sw=!returned_head;
    let head=if returned_head {32usize}else{24usize};
    for stop in [3usize,5,7] {
        let mut b=B::new(); let (fd,pool,dirty)=frame(&mut b);
        let sc=ColScr::carve(&pool,&fd.sx,&dirty,24,24,40);
        let mut stage=2usize;
        super::midg::middle(&mut b,&fd,&cp,&sc,None,&[],&mut |_b| {
            stage+=1; stage<stop
        });
        for op in &b.ops { op.validate(); }
        assert_eq!(b.peak,698);
        for mode in 0..3 {
            let mut initial=vec![0u64;698];
            for (i,&q) in dirty.iter().enumerate() {
                initial[q.0 as usize]=0x9e37_79b9_7f4a_7c15u64.rotate_left(i as u32)
                    ^0xa5a5_5a5a_9696_6969u64.wrapping_mul(i as u64+1);
            }
            let mut cases: Vec<(usize,N,N,N,bool)>=vec![];
            for shot in 0..64 {
                let sz=[209usize,230,231,232,233][shot%5];
                let zh: N=match shot%3 {
                    0=>N::from(1u64)<<23,
                    1=>(N::from(1u64)<<24)-N::from(1u64),
                    _=>(N::from(1u64)<<23)+N::from(0x234567u64),
                };
                let mut z: N=zh<<(sz-24);
                if returned_head {
                    // Exercise the paid lower-eight divisor-head bits, including
                    // even/odd heads; the oracle applies the same virtual OR1.
                    let low8=[0u64,1,0x55,0xfe,0xff,0x96][shot%6];
                    z|=N::from(low8)<<(sz-32);
                }
                let t: N=N::from(1u64)<<(257-sz);
                // Integer oracle uses the actual paid head, not physical K.
                let divisor: N=(z>>(sz-head))|N::from(1u64);
                let f: N=((N::from(1u64)<<(256+head-sz))-N::from(1u64))/divisor;
                let u=(257-sz).saturating_sub(super::midg::TC);
                let g: N=(((f>>u)+N::from(1u64))<<u)-N::from(1u64);
                let y: N=(t>>24)+N::from(if shot&1==0 {1u64}else{3u64});
                let ht=mode==1 || (mode==2 && shot&1!=0);
                let x: N=if ht {g-y/N::from(2u64)}else{y/N::from(2u64)};
                let quotient: N=if ht {x/y}else{(g-x)/y};
                assert!(quotient.bit_len()<=24);
                if quotient.bit(23) {high_quotients+=1;}
                put(&mut initial,&fd.ring[..sz],shot,z);
                let top:Vec<_>=fd.ring.iter().rev().take(257-sz).copied().collect();
                put(&mut initial,&top,shot,x);
                put(&mut initial,&fd.q,shot,y);
                put(&mut initial,&fd.sy,shot,N::from(y.bit_len() as u64));
                put(&mut initial,&sc.sz,shot,N::from(sz as u64));
                if ht {initial[fd.ph.0 as usize]|=1u64<<shot;}
                cases.push((sz,x,y,quotient,ht));
            }
            let mut expected=initial.clone();
            for (shot,&(sz,x,y,quotient,ht)) in cases.iter().enumerate() {
                let (out,q)=if ht {
                    if stop>=5 {(x%y,if stop==5 {quotient}else{N::ZERO})}
                    else {(x,N::ZERO)}
                } else {
                    if stop>=5 {(x+quotient*y,N::ZERO)}else{(x,quotient)}
                };
                let top:Vec<_>=fd.ring.iter().rev().take(257-sz).copied().collect();
                put(&mut expected,&top,shot,out);
                for kb in 0..23 {
                    let wire=fd.ring[sz+kb];
                    expected[wire.0 as usize]=(expected[wire.0 as usize]&!(1u64<<shot))
                        |(u64::from(q.bit(kb))<<shot);
                }
                let wire=fd.sx[3];
                expected[wire.0 as usize]=(expected[wire.0 as usize]&!(1u64<<shot))
                    |(u64::from(q.bit(23))<<shot);
            }
            for salt in [0u64,1,0x4ab7] {
                let (actual,phase)=apply(&b.ops,&initial,salt);
                assert_eq!(phase,0,"actual middle phase stop{stop} mode{mode} salt{salt}");
                assert_eq!(actual,expected,"full698 middle state stop{stop} mode{mode} salt{salt}");
                visits+=64;
            }
        }
        eprintln!("EXTERNAL_Q23_MIDDLE_STAGE_PASS head={head} crossing_recipe={} stop={stop} width698 emitted_ops={} all_ops_valid=true high_quotient_bit_exercised=true",!returned_head,b.ops.len());
    }
    }
    assert!(high_quotients>0);
    assert_eq!(visits,3456);
    eprintln!("EXTERNAL_Q23_MIDDLE_NATIVE_PASS visits3456 q23_cases={high_quotients} HR_HT_mixed3 stops3_5_7 salts3 heads24_32 full_state_dirty259=true TC32_caps24=true paid_head_low8_exercised=true source_returned_head32_exercised=true");
}

#[test]
fn q698_actual_all_columns_middle_structure() {
    let sched=super::frogdrop_sched::from_text(SCHED_FROGDROP);
    let (cols,_,_)=col_pars(&sched);
    let mut count=0usize; let mut operations=0usize; let mut largest=0usize;
    for (index,cp) in cols.iter().enumerate() {
        let mut b=B::new(); let (mut fd,pool,dirty)=frame(&mut b);
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,24,40,cp.sz.1>255);
        let pl=pl_col(&dirty,&fd,&pool);
        super::frogdrop_col::column_upto(&mut b,&mut fd,cp,&sc,6,Some(&pl));
        for op in &b.ops { op.validate(); }
        assert_eq!(b.peak,698,"extra owner column{index}");
        assert_eq!(b.width(),698);
        operations+=b.ops.len(); largest=largest.max(b.ops.len()); count+=1;
    }
    assert_eq!(count,203);
    eprintln!("EXTERNAL_Q23_ALL_COLUMN_STRUCTURE_PASS columns203 actual_carve_and_payload=true through_middle6=true all_ops_valid=true width698=true operations={operations} largest_column_ops={largest}");
}
