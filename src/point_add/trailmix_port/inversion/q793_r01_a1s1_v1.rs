//! Constant A1/S1 R01 arithmetic. SM3 is an untouched parked passenger.
//! Every operation is paired off g; caller funds mask=hs=HA=0 under g.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_phase115_programs.rs"] mod programs;
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut seen:Vec<(&QReg,bool)>=Vec::new();for &(q,v) in cs {assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=seen.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{seen.push((q,v));}}
    mixed_mcx(circ,&seen,out,dirty);
}
/// C-addressed route uses no low-A addition and never names an absent leaf.
fn gather<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],w1:&'a[QReg],offset:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    assert!((1..=3).contains(&offset));let start=circ.b.ops.len();
    let mut nodes:Vec<_>=(0..256).map(|cv|if cv<=252{Some(&w1[cv+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{mux::predicate_swap(circ,rank,1,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
pub(super) fn quotient(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,decision:&QReg,w1:&[QReg],dirty:&[QReg]){
    let(root,route)=gather(circ,rank,c,w1,3,dirty);circ.cswap(g,root,decision);circ.b.ops.extend(route.into_iter().rev());
}
fn prefix(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,out:&QReg,w1:&[QReg],dirty:&[QReg],offset:usize,needed:usize){
    let(root,route)=gather(circ,rank,c,w1,offset,dirty);let base=[(g,true),(root,true)];gate(circ,&base,out,dirty);
    // Under A1/S1 only ranks0,4,8,11 occur. Ch=0 iff rank2=rank3=0.
    for value in 0..needed{let mut cs=base.to_vec();cs.extend([(&rank[2],false),(&rank[3],false)]);
        cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));gate(circ,&cs,out,dirty);}
    circ.b.ops.extend(route.into_iter().rev());
}
fn seed_terms()->&'static[usize]{
    static TERMS:std::sync::OnceLock<Vec<usize>>=std::sync::OnceLock::new();
    TERMS.get_or_init(||{let mut truth:Vec<_>=(0..512).map(|code|{
        let odd=code&1!=0;let b=code>>1&7;let v=code>>4&7;let q=(code>>7&1)*2+(code>>8&1)*4;
        let r=if odd{7usize.wrapping_sub(b*v).wrapping_mul(3).wrapping_sub(q*v)&7}else{b};r<v
    }).collect();for bit in 0..9{for m in 0..512{if m>>bit&1!=0{truth[m]^=truth[m^(1<<bit)];}}}
        truth.into_iter().enumerate().filter_map(|(m,on)|on.then_some(m)).collect()})
}
fn seed(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,ha:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    prefix(circ,rank,c,g,&sm[0],w1,dirty,2,1);prefix(circ,rank,c,g,&sm[1],w1,dirty,1,2);
    let word=[&w1[0],&w2[0],&w2[1],&w2[2],&w2[258],&w2[257],&w2[256],&sm[0],&sm[1]];
    for &term in seed_terms(){let mut cs=vec![(g,true)];cs.extend((0..9).filter(|&i|term>>i&1!=0).map(|i|(word[i],true)));gate(circ,&cs,ha,dirty);}
    prefix(circ,rank,c,g,&sm[1],w1,dirty,1,2);prefix(circ,rank,c,g,&sm[0],w1,dirty,2,1);
}
fn high_transition(circ:&mut Circuit,rank:&[QReg],g:&QReg,hs:&QReg,dirty:&[QReg],old:isize,new:isize){
    if old==new{return;}for high in [old,new]{if high<0{continue;}for &(m,v)in programs::C_EQUAL[high as usize]{
        let mut cs=vec![(g,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));gate(circ,&cs,hs,dirty);}}
}
fn carry(circ:&mut Circuit,g:&QReg,mask:&QReg,ha:&QReg,s:&QReg,t:&QReg,inverse:bool){
    if !inverse{circ.cx(s,t);circ.cx(ha,s);}circ.x(g);
    super::paired_clean_mcx::toggle(circ,&[(mask,true),(t,true),(s,true)],ha,g);circ.x(g);
    if inverse{circ.cx(ha,s);circ.cx(s,t);}
}
fn low_update(circ:&mut Circuit,g:&QReg,decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    let base=[(g,true),(decision,true),(&w1[0],false)];
    let mut change=|target:usize,extra:&[(&QReg,bool)]|{let mut cs=base.to_vec();cs.extend_from_slice(extra);gate(circ,&cs,&w2[target],dirty);};
    change(2,&[(&w2[256],true)]);change(2,&[(&w2[257],true),(&w2[1],false)]);
    change(2,&[(&w2[258],true),(&w2[0],false),(&w2[1],false)]);
    change(2,&[(&w2[258],true),(&w2[0],false),(&w2[257],true)]);
    change(1,&[(&w2[257],true)]);change(1,&[(&w2[258],true),(&w2[0],false)]);change(0,&[(&w2[258],true)]);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],support_end:usize){
    let start=circ.b.ops.len();let owned=(circ.b.next_qubit,circ.b.active_qubits);assert!(dirty.len()>=18);
    let n=support_end.min(256);assert!(n>=3);
    // Snew=0 exactly: the one lower boundary is a guarded toggle at bit0.
    circ.cx(g,mask);seed(circ,rank,c,sm,g,ha,w1,w2,dirty);
    let mut group=-1isize;let mut updates=Vec::new();
    for i in 3..n{
        let at=circ.b.ops.len();let value=255-i;let high=(value/64)as isize;
        high_transition(circ,rank,g,hs,dirty,group,high);group=high;
        let mut cs=vec![(hs,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        circ.x(g);super::paired_clean_mcx::toggle(circ,&cs,mask,g);circ.x(g);
        updates.push(circ.b.ops[at..].to_vec());carry(circ,g,mask,ha,&w2[258-i],&w1[258-i],false);
    }
    circ.cx(g,decision);circ.ccx(g,ha,decision);
    for i in (3..n).rev(){
        carry(circ,g,mask,ha,&w2[258-i],&w1[258-i],true);circ.cx(ha,&w2[258-i]);
        gate(circ,&[(g,true),(mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],dirty);circ.cx(ha,&w2[258-i]);
        circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    seed(circ,rank,c,sm,g,ha,w1,w2,dirty);low_update(circ,g,decision,w1,w2,dirty);circ.cx(g,mask);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A1S1 touched hole");}
        let parked=sm[3].id()as u64;assert!(op.q_target.0!=parked&&op.q_control1.0!=parked&&op.q_control2.0!=parked,"A1S1 read parked SM3");}
}
