//! Three-role terminal adapter. The only fourth fixed-endpoint scalar is
//! an explicit Q99 loan AFTER the B0 map. Every endpoint shot has R<2^26;
//! Q99 is outside the existing Q26..30 digit loans, Q100..120 endpoint
//! scratch and Q121..127 counter. No fourth traversal owner is allocated.
use super::builder::B;
use super::direct_three::Column;
use super::frogdrop_col::{Fd,ColPar,ColScr};
use super::map_three::{bank,eq,nand_replay,record,xor};
use crate::circuit::QubitId;

fn b0_flag(b:&mut B,col:&Column<'_>,flag:QubitId,d:&[QubitId]){
    let cnt=&col.q[121..128];b.x(flag);b.cx(cnt[0],flag);
    for value in 1..128{if super::frogdrop_col::map_ctrl_skipped(value)%2==1{
        xor(b,&eq(cnt,value),flag,d);
    }}
}
pub(crate) fn finish(b:&mut B,col:&Column<'_>,b0:Option<&ColPar>,last:&ColPar){
    assert!(last.nomap&&last.ht&&last.sy==(1,1));
    assert_eq!((col.ring.len(),col.q.len()),(257,128));
    let r=col.roles;let scratch:Vec<_>=std::iter::once(r.tag)
        .chain(col.meta.sum.iter().copied()).chain([r.cut,r.work]).collect();
    let all:Vec<_>=col.ring.iter().chain(&col.q[..114]).chain(&col.meta.y)
        .chain(&scratch[1..]).chain(col.dirty).copied().collect();
    let mut held=vec![r.tag,col.phase];held.extend(&col.q[114..]);
    if let Some(p)=col.compact{held.extend(p);}
    let d=bank(&all,&held);
    if let Some(cp)=b0{
        assert!(cp.sz==(0,0)&&cp.dn&&cp.m<=114&&cp.emax<=31);
        let par=super::frogdrop::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:128,tail:cp.tail,emax:cp.emax};
        let tape=super::map_three::stage_record(b,col.ring,&col.q[..114],&col.meta.y,
            &scratch,col.phase,&par,cp.m,&d);
        b0_flag(b,col,r.tag,&d);b.x(r.tag);nand_replay(b,&tape,col.phase,r.tag,&d);b.x(r.tag);b0_flag(b,col,r.tag,&d);
    }
    if let Some(p)=col.compact{
        let loan=col.q[99];let q=col.q;let meta=col.meta;
        let raw_y=vec![meta.y[0],meta.y[1],meta.y[2],meta.y[3],meta.y[4],q[114],q[115],q[116]];
        let sx=vec![r.cut,r.work,loan,r.tag,meta.sum[4],meta.y[5],meta.y[6]];
        let pool=meta.sum[..4].to_vec();
        let raw_z=vec![meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3],q[112],q[109],q[110],q[111]];
        let entry=record(b,|b|{
            super::frogdrop::add_const_dirty_exact(b,&meta.y,1,col.ring);
            for i in 0..2{b.cx(meta.y[5+i],q[114+i]);b.cx(q[114+i],meta.y[5+i]);}
        });
        let raw=Fd{ring:col.ring.to_vec(),q:q.to_vec(),sy:raw_y,sx:sx.clone(),ph:col.phase,cnt:q[121..128].to_vec()};
        let dirty=bank(col.dirty,&[loan]);
        let mut sc=ColScr::carve_col(&pool,&sx,&dirty,last.kp,last.qb,last.tail,false);sc.sz=raw_z;
        let payload=super::pointadd_frogdrop::pl_col(p,&raw,&pool);
        b.play(&entry,false);super::payload::pl_end(b,&raw,last,&sc,&payload);b.play(&entry,true);
    }
}
