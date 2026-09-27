//! A sparse or repeated-bit source is materialized one clean block at a time.
//! The source mapping is read-only. A copied source block and a native carry
//! ladder are both charged; boundaries remain live until exact phase repair.
use super::{Builder,modular,compare};
use crate::circuit::QubitId;
pub(crate) type SourceBit=(Option<QubitId>,bool);
fn copy(c:&mut Builder,map:&[SourceBit],buffer:&[QubitId]){for(i,&q)in buffer.iter().enumerate(){if let Some(&(src,one))=map.get(i){if let Some(s)=src{c.cx(s,q);}if one{c.x(q);}}}}
fn erase(c:&mut Builder,flag:QubitId,source:&[QubitId],sum:&[QubitId],incoming:Option<QubitId>){
    if sum.len()>1{compare::erase_with_compare(c,flag,sum,source,incoming);return;}
    let m=c.alloc_bit();c.hmr(flag,m);c.push_condition(m);c.x(sum[0]);c.cz(source[0],sum[0]);if let Some(q)=incoming{c.cz(source[0],q);c.cz(sum[0],q);}c.x(sum[0]);c.pop_condition();c.free_bit(m);
}
pub(crate) fn add(c:&mut Builder,map:&[SourceBit],b:&[QubitId],negative:bool,chunk:usize){
    assert!(!map.is_empty()&&map.len()<=b.len()&&chunk>=1);if negative{c.x_all(b);}let buffer=c.alloc_qubits(chunk.min(b.len()));let mut stages=Vec::new();let mut at=0;let mut previous=None;
    while at<b.len(){let end=(at+chunk).min(b.len());let src=if at<map.len(){&map[at..end.min(map.len())]}else{&[]};let tmp=&buffer[..end-at];copy(c,src,tmp);let flag=if end<b.len(){Some(c.alloc_qubit())}else{None};modular::ripple_add(c,tmp,&b[at..end],previous,flag);copy(c,src,tmp);
        if let Some(q)=flag{stages.push((at,end,previous,q));}previous=flag;at=end;
    }
    for(at,end,prev,q)in stages.into_iter().rev(){let src=if at<map.len(){&map[at..end.min(map.len())]}else{&[]};let tmp=&buffer[..end-at];copy(c,src,tmp);erase(c,q,tmp,&b[at..end],prev);copy(c,src,tmp);c.release_clean(q);}
    for q in buffer{c.release_clean(q);}if negative{c.x_all(b);}
}
