//! SOURCE-ONLY child of midg. Explicit direct-size -> inherited fixed ABI.
//! This scope supplies the existing fixed-source owner remaps WITHOUT
//! enabling the global joint-prefix flag. No partial-stage entry is exposed.
use super::super::builder::B;
use super::super::direct_column::Column;
use super::super::fixed_epoch::{self,FixedColumn,FixedRawLayout};
use super::super::frogdrop_col::{Fd,ColPar,ColScr};

thread_local!{
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
