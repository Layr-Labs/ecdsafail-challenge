//! R14 T2/T3 complete K1 map equivalence on actual packed parent stage-10 states.
use super::{builder::B, frogdrop::direct_map::k1_map3::{self as k1,Boundary,Context,Roles3},
    frogdrop_col::{self,ColPar}, pointadd_frogdrop, k1_complete_io as io, k1_complete_caller};
use crate::circuit::QubitId;
const COLS:[usize;7]=[36,50,96,97,113,114,119];
fn context<'a>(ring:&'a[QubitId],q:&'a[QubitId],y:&'a[QubitId],sum:&'a[QubitId],
    ph:QubitId,pool:&[QubitId],terminal:&'a[QubitId],payload:bool)->Context<'a>{
    Context{ring,q,y,sum,roles:Roles3{tag:pool[0],cut:pool[1],
        toggle:if payload||!super::c659::t23_enabled(){pool[2]}else{terminal[0]}},ph,
        payload:payload.then_some(terminal),terminal_loans:if payload{&[]}else if super::c659::t23_enabled(){&terminal[1..2]}else{&terminal[..2]},
        boundary:Boundary::Stage10Returned}
}
fn map(b:&mut B,ctx:&Context<'_>,cp:&ColPar,inverse:bool){
    b.begin();k1::apply(b,ctx,cp,|b,target,donors|
        super::direct_map_tail_counter::done3(b,ctx,target,&[],donors));
    let tape=b.end();b.play(&tape,inverse);
}
#[test]
fn r14_t23_k1_complete_pair_all_wire(){
    assert!(super::c659::t23_enabled(),"run with C658_T23=1");
    k1_complete_caller::frozen_environment();
    let schedule=super::frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for payload in [true,false]{
        let mut source=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut source);
        let initial=k1_complete_caller::initial(&layout,payload,0);
        let seed=if payload{b"r14-parent-payload".as_slice()}else{b"r14-parent-no-payload".as_slice()};
        let scope=io::begin(initial,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let mut captures=vec![];
        for cp in cps.iter().take(120){
            let mut b=k1_complete_caller::builder();let mut l=k1_complete_caller::Layout::allocate(&mut b);
            frogdrop_col::set_counter_epoch(&mut l.fd,cp.col);
            {let col=l.column(payload);let mut middle=super::direct_middle::DirectMiddle;
                super::direct_column::through_stage10(&mut b,&col,cp,&mut middle);
                b.flush_global();
                if COLS.contains(&cp.col){let(image,_)=io::snapshot();captures.push((cp.col,image));}
                super::direct_map_tail_counter::finish_k1_observed(&mut b,&col,cp,|_|{});
            }
            assert!(b.ops.is_empty()&&b.pending_count()==0);
        }
        let(_,source_receipt)=io::finish(scope);
        assert_eq!(captures.len(),COLS.len());
        eprintln!("R14_SOURCE payload={payload} ops={} captures={}",source_receipt.ops,captures.len());
        for (column,mut image) in captures{
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
            let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            image.q[p[0].0 as usize]=0;image.q[p[1].0 as usize]=0;
            if column==36||column==50 {image.q[pool[0].0 as usize]|=0x0000_0000_0000_ffff;}
            let cp=&cps[column];let forward=context(&ring,&q,&y,&sum,ph,&pool,&p,payload);
            let inverse=context(&ring,&q,&y,&sum,ph,&pool,&p,!payload);
            let before=image.clone();let seed=(column as u64 ^ ((payload as u64)<<32)).to_le_bytes();
            let scope=io::begin(image,&seed,io::RECORD_OP_CAP);
            map(&mut b,&forward,cp,false);map(&mut b,&inverse,cp,true);b.flush_global();
            let(after,receipt)=io::finish(scope);
            before.signed_eq(&after,&format!("column={column} T{} forward T{} inverse",if payload{1}else{3},if payload{2}else{4}));
            eprintln!("R14_K1_PAIR_PASS column={column} pair=T{}T{} ops={} shots=64 phase=0 C_mask={:016x} PH_mask={:016x}",if payload{1}else{3},if payload{2}else{4},receipt.ops,before.q[pool[0].0 as usize],before.q[ph.0 as usize]);
        }
    }
}
