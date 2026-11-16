//! SOURCE-ONLY child of midg. Explicit direct-size -> inherited fixed ABI.
//! This scope supplies the existing fixed-source owner remaps WITHOUT
//! enabling the global joint-prefix flag. No partial-stage entry is exposed.
use super::super::builder::B;
use super::super::direct_column::Column;
use super::super::fixed_epoch::{self,FixedColumn,FixedRawLayout};
use super::super::frogdrop_col::{Fd,ColPar,ColScr};

thread_local!{
    static MUTANT:std::cell::Cell<u8>=const{std::cell::Cell::new(0)};
    static LOAN:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};
    static CURRENT:std::cell::RefCell<Option<FixedRawLayout>>=const{std::cell::RefCell::new(None)};
}
pub(crate) fn current()->Option<FixedRawLayout>{CURRENT.with(|c|c.borrow().clone())}
pub(crate) fn enabled()->bool{CURRENT.with(|c|c.borrow().is_some())}

pub(crate) fn run(b:&mut B,column:&Column<'_>,cp:&ColPar){
    assert!(!super::joint_size::enabled());
    assert!(!enabled()&&!cp.nomap&&!(cp.sw||cp.psw||cp.dl||cp.dq));
    assert!(cp.sy.1<=96&&cp.n==257&&cp.qb==30);
    let descriptor=FixedColumn{column:cp.col,y_hi:cp.sy.1,z_lo:cp.sz.0,
        hr:cp.hr,ht:cp.ht,done_possible:cp.dn,counter_max:cp.cntmax,
        sw:cp.sw,psw:cp.psw,dl:cp.dl,dq:cp.dq};
    let(entry,transport)=fixed_epoch::entry_record(b,column.meta,column.roles,
        column.q,column.phase,descriptor,column.ring);
    let raw=Fd{ring:column.ring.to_vec(),q:column.q.to_vec(),
        sy:entry.raw_y.to_vec(),sx:entry.sx.to_vec(),ph:column.phase,
        cnt:column.q[121..128].to_vec()};
    let sc=ColScr::carve_col(&entry.pool,&entry.sx,column.dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
    assert_eq!(&sc.sz[..5],entry.sum.as_slice());
    // entry_record already supplies the five-bit sum frame and returns
    // its three raw-SZ high owners. Match column_upto's middle-only role
    // binding; carve_col intentionally aliases those roles outside it.
    // Fixed columns have no switch/tag, so no physical SW transfer is due.
    let mut sc = sc.mid_alias(&entry.sx);
    sc.sw = entry.sx[5];
    let payload=column.compact.map(|p|super::super::pointadd_frogdrop::pl_col(p,&raw,&entry.pool));
    b.play(&transport,false);
    CURRENT.with(|c|*c.borrow_mut()=Some(entry.clone()));
    super::super::payload::with_direct_column_index(cp.col,||{
        super::super::frogdrop_col::with_fixed_done_override(b,entry.held_done,|b|{
            let mut whole=|_:&mut B|true;
            super::middle(b,&raw,cp,&sc,payload.as_ref(),&[],&mut whole);
        });
    });
    CURRENT.with(|c|*c.borrow_mut()=None);
    b.play(&transport,true);
}

// Isolated c162 experiment: original run above remains byte-for-byte intact.
pub(crate) fn c162_loan()->bool{LOAN.with(|x|x.get())}
pub(crate) fn run_c162(b:&mut B,column:&Column<'_>,cp:&ColPar,on:bool){
    if !on {run(b,column,cp);return;}
    assert_eq!(cp.col,162); assert_eq!(cp.sy.1,62);
    assert!(!c162_loan());
    struct Reset;
    impl Drop for Reset{fn drop(&mut self){LOAN.with(|x|x.set(false));CURRENT.with(|x|*x.borrow_mut()=None);}}
    LOAN.with(|x|x.set(true));let _reset=Reset;
    run_loan(b,column,cp);
}

fn run_loan(b:&mut B,column:&Column<'_>,cp:&ColPar){
    assert!(!super::joint_size::enabled());
    assert!(!enabled()&&!cp.nomap&&!(cp.sw||cp.psw||cp.dl||cp.dq));
    assert!(cp.sy.1<=96&&cp.n==257&&cp.qb==30);
    let descriptor=FixedColumn{column:cp.col,y_hi:cp.sy.1,z_lo:cp.sz.0,
        hr:cp.hr,ht:cp.ht,done_possible:cp.dn,counter_max:cp.cntmax,
        sw:cp.sw,psw:cp.psw,dl:cp.dl,dq:cp.dq};
    let(mut entry,transport)=fixed_epoch::entry_record(b,column.meta,column.roles,
        column.q,column.phase,descriptor,column.ring);
    // Entry and inverse transport still use the distinct physical prefix.
    assert_eq!(entry.sx[2],column.roles.prefix);
    entry.sx[2]=column.q[if c162_mutant()==1{74}else{62}];
    assert!(!entry.reserved_q().contains(&column.q[62]));
    let raw=Fd{ring:column.ring.to_vec(),q:column.q.to_vec(),
        sy:entry.raw_y.to_vec(),sx:entry.sx.to_vec(),ph:column.phase,
        cnt:column.q[121..128].to_vec()};
    let sc=ColScr::carve_col(&entry.pool,&entry.sx,column.dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
    assert_eq!(&sc.sz[..5],entry.sum.as_slice());
    // entry_record already supplies the five-bit sum frame and returns
    // its three raw-SZ high owners. Match column_upto's middle-only role
    // binding; carve_col intentionally aliases those roles outside it.
    // Fixed columns have no switch/tag, so no physical SW transfer is due.
    let mut sc = sc.mid_alias(&entry.sx);
    sc.sw = entry.sx[5];
    let payload=column.compact.map(|p|super::super::pointadd_frogdrop::pl_col(p,&raw,&entry.pool));
    b.play(&transport,false);
    CURRENT.with(|c|*c.borrow_mut()=Some(entry.clone()));
    super::super::payload::with_direct_column_index(cp.col,||{
        super::super::frogdrop_col::with_fixed_done_override(b,entry.held_done,|b|{
            let mut whole=|_:&mut B|true;
            super::middle(b,&raw,cp,&sc,payload.as_ref(),&[],&mut whole);
        });
    });
    CURRENT.with(|c|*c.borrow_mut()=None);
    b.play(&transport,true);
}

pub(crate) fn c162_mutant()->u8{MUTANT.with(|v|v.get())}
pub(crate) fn with_c162_mutant<T>(id:u8,f:impl FnOnce()->T)->T{
 struct Reset;impl Drop for Reset{fn drop(&mut self){MUTANT.with(|v|v.set(0));}}
 assert_eq!(c162_mutant(),0);MUTANT.with(|v|v.set(id));let _r=Reset;f()
}

// Typed test-only guard receipt; production guard remains immediately after it.
#[cfg(test)]
#[derive(Debug)]
pub(crate) struct C162EarlyAAlias {
    pub observed:crate::circuit::QubitId,
    pub required:crate::circuit::QubitId,
    pub recorded_gates:usize,
    pub emitted_ops:usize,
}

// This diagnostic never changes production alias guards or emitted operations.
#[cfg(test)]
pub(crate) mod c162_unpark_guard {
    use super::ColPar;
    use crate::circuit::QubitId;
    use std::any::Any;

    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    pub(crate) enum Site { UnparkBankDisjoint, PayloadAlias }

    // Every disjunct of the unchanged unpark assertion has its own evidence.
    // SX indices also reject a duplicate/extra SX alias of the same owner.
    #[derive(Clone,Debug,PartialEq,Eq)]
    pub(crate) struct Reasons {
        pub dirty:bool, pub reciprocal_r:bool, pub ring:bool,
        pub sx_indices:Vec<usize>, pub raw_size:bool,
        pub act:bool, pub c0:bool, pub x128:bool,
        pub pzero:bool, pub ph:bool, pub sw:bool,
    }
    impl Reasons {
        fn any(&self)->bool {
            self.dirty || self.reciprocal_r || self.ring || !self.sx_indices.is_empty()
                || self.raw_size || self.act || self.c0 || self.x128
                || self.pzero || self.ph || self.sw
        }
    }
    #[derive(Clone,Debug,PartialEq,Eq)]
    pub(crate) struct Offender { pub owner:QubitId, pub reasons:Reasons }

    #[derive(Clone,Debug)]
    pub(crate) struct C162EarlyAUnparkAlias {
        pub site:Site, pub profile:ColPar, pub audit_enabled:bool,
        pub loan:bool, pub mutant:u8,
        pub observed:QubitId, pub required:QubitId, pub a_owner:QubitId,
        pub sx2:QubitId, pub x128:QubitId,
        pub offenders:Vec<Offender>,
        pub unpark_bank:Vec<QubitId>, pub comparator_bank:Vec<QubitId>,
        pub recorded_gates:usize, pub emitted_ops:usize,
    }

    pub(crate) fn offending_owners(bank:&[QubitId],dirty:&[QubitId],r:&[QubitId],
        ring:&[QubitId],sx:&[QubitId],sz:&[QubitId],scalars:[QubitId;6])->Vec<Offender>
    {
        let [act,c0,x128,pzero,ph,sw]=scalars;
        bank.iter().copied().filter_map(|owner| {
            let reasons=Reasons {
                dirty:dirty.contains(&owner), reciprocal_r:r.contains(&owner),
                ring:ring.contains(&owner),
                sx_indices:sx.iter().enumerate().filter_map(|(i,q)|(*q==owner).then_some(i)).collect(),
                raw_size:sz.contains(&owner), act:act==owner, c0:c0==owner,
                x128:x128==owner, pzero:pzero==owner, ph:ph==owner, sw:sw==owner,
            };
            reasons.any().then_some(Offender{owner,reasons})
        }).collect()
    }

    fn exact_profile(cp:&ColPar)->bool {
        // Exhaustive pattern: adding a ColPar field requires a fresh binding.
        matches!(cp,ColPar {
            n:257,nq:128,h:0,k:0,kp:24,qb:30,tot:83,
            sz:(192,255),sy:(1,62),smax:(1,62),m:62,tail:40,emax:31,
            hr:false,ht:true,sw:false,l0:128,swl:(0,0),dn:true,fin:true,
            nomap:false,tt:false,pht:true,psy:(1,64),xw:64,psw:false,
            cntw:7,cntmax:127,col:162,dl:false,dq:false,dlr:999,
        })
    }

    // Used at the actual guard, by the real harness, and by all controls.
    pub(crate) fn recognize(id:u8,payload:&(dyn Any+Send))->Option<&C162EarlyAUnparkAlias> {
        let e=payload.downcast_ref::<C162EarlyAUnparkAlias>()?;
        let a=QubitId(257+74);let h=QubitId(257+62);
        let expected=Offender {owner:a,reasons:Reasons {
            dirty:false,reciprocal_r:true,ring:false,sx_indices:vec![2],raw_size:false,
            act:false,c0:false,x128:true,pzero:false,ph:false,sw:false,
        }};
        if id==1 && e.site==Site::UnparkBankDisjoint && exact_profile(&e.profile)
            && e.audit_enabled && e.loan && e.mutant==1
            && e.observed==a && e.required==h && e.a_owner==a && e.sx2==a && e.x128==a
            && e.offenders.as_slice()==[expected]
            && e.unpark_bank.len()==47 && e.comparator_bank.len()==24
            && e.unpark_bank.contains(&a) && !e.unpark_bank.contains(&h)
            && e.recorded_gates>0
        {Some(e)} else {None}
    }

    pub(crate) fn dispatch(id:u8,payload:Box<dyn Any+Send>)->C162EarlyAUnparkAlias {
        if let Some(e)=recognize(id,payload.as_ref()) {return e.clone();}
        std::panic::resume_unwind(payload)
    }
}

// Complete product adapter; separate from the historical c162 diagnostic.
thread_local!{static THREE_LOAN:std::cell::Cell<Option<crate::circuit::QubitId>>=const{std::cell::Cell::new(None)};}
pub(crate) fn three_loan()->Option<crate::circuit::QubitId>{THREE_LOAN.with(|c|c.get())}
pub(crate) fn run_three(b:&mut B,column:&super::super::c659_column::Column<'_>,cp:&ColPar,
 entry:FixedRawLayout,transport:&[super::super::builder::G]){
 assert!(!enabled()&&!super::joint_size::enabled()&&three_loan().is_none());
 assert_eq!(entry.sx[2],column.q[cp.sy.1]);
 let raw=Fd{ring:column.ring.to_vec(),q:column.q.to_vec(),sy:entry.raw_y.to_vec(),sx:entry.sx.to_vec(),
 ph:column.phase,cnt:column.q[121..128].to_vec()};
 let sc=ColScr::carve_col(&entry.pool,&entry.sx,column.dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
 assert_eq!(&sc.sz[..5],entry.sum.as_slice());let mut sc=sc.mid_alias(&entry.sx);sc.sw=entry.sx[5];
 let payload=column.compact.map(|p|super::super::pointadd_frogdrop::pl_col(p,&raw,&entry.pool));
 b.play(transport,false);
 struct Reset;impl Drop for Reset{fn drop(&mut self){CURRENT.with(|c|*c.borrow_mut()=None);THREE_LOAN.with(|c|c.set(None));}}
 CURRENT.with(|c|*c.borrow_mut()=Some(entry.clone()));THREE_LOAN.with(|c|c.set(Some(entry.sx[2])));let reset=Reset;
 super::super::payload::with_direct_column_index(cp.col,||{
  super::super::frogdrop_col::with_fixed_done_override(b,entry.held_done,|b|{
   let mut whole=|_:&mut B|true;super::middle(b,&raw,cp,&sc,payload.as_ref(),&[],&mut whole);
  });
 });
 drop(reset);b.play(transport,true);
}
