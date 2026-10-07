//! Actual three-hole R01 with physical gap and conditional SM3 loans.
//! Entry and return use the decoded phase01 cargo convention, after pre-rotation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_remainder5_programs.rs"] mod programs;
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();for &(q,v)in cs{assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    mixed_mcx(circ,&unique,out,dirty);
}
fn aflags<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    programs::EQUAL[value/64].iter().map(|&(m,v)|a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0))).collect()).collect()
}
fn cflags<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    triples().iter().enumerate().filter(|(_,t)|t[1]==value/64).map(|(r,_)|c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0))).collect()).collect()
}
fn phase_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    let base=[(p1,false),(p2,true)];gate(circ,&base,g,dirty);
    for flag in aflags(rank,a,255){let mut cs=base.to_vec();cs.extend(flag);gate(circ,&cs,g,dirty);}
}
/// Metadata-only A+C=254/255 toggle. Original C on entry and return.
fn endpoint_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],value:usize){
    assert!([254,255].contains(&value));arithmetic::add(circ,a,c,None,false);
    for (rk,t)in triples().iter().enumerate(){
        let hi=t[0]+t[1];if hi!=3&&(value!=254||hi!=2){continue;}
        let mut cs=vec![(p1,false),(p2,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        cs.extend(rank.iter().enumerate().map(|(i,q)|(q,rk>>i&1!=0)));
        if hi==3{gate(circ,&cs,g,dirty);}
        if value==254{cs.extend(a.iter().map(|q|(q,true)));gate(circ,&cs,g,dirty);}
    }
    arithmetic::add(circ,a,c,None,true);
}
/// Exact phase01/A1/S1 normal-domain guard, read only before or after SM3 loan.
fn special_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize){
    if j&1==0{return;}
    for (rk,t)in triples().iter().enumerate(){if t[0]!=0||t[2]!=0{continue;}
        let mut cs=vec![(p1,false),(p2,true),(&c[0],j>>1!=0)];cs.extend(sm.iter().map(|q|(q,false)));
        cs.extend(a.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(rank.iter().enumerate().map(|(i,q)|(q,rk>>i&1!=0)));
        gate(circ,&cs,g,dirty);
        for cv in 253..256{for flag in cflags(rank,c,cv){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,g,dirty);}}
    }
}
fn terminal_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    for af in aflags(rank,a,255){for cf in cflags(rank,c,0){let mut cs=vec![(p1,false),(p2,true)];cs.extend(af.iter().copied());cs.extend(cf);gate(circ,&cs,g,dirty);}}
}
fn normal_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize){
    phase_guard(circ,rank,a,p1,p2,g,dirty);
    endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,254);endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,255);
    terminal_guard(circ,rank,a,c,p1,p2,g,dirty);
    special_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);
}
fn borrow_ha(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,ha:&QReg,w2:&[QReg],dirty:&[QReg]){
    mux::exchange(circ,rank,a,0,Some(g),ha,&w2[1..257].iter().collect::<Vec<_>>(),dirty,false);
}
/// M-addressed decision exchange: the only leaves are real W1[2..255].
fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,decision:&QReg,w1:&[QReg],dirty:&[QReg]){
    let start=circ.b.ops.len();arithmetic::add(circ,a,c,None,false);
    let mut nodes:Vec<_>=(0..256).map(|m|if m<=253{Some(&w1[m+2])}else{None}).collect();
    let d=&dirty[0];let rest=&dirty[1..];
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{
            if level<6{circ.cswap(&c[level],left,right);}else{
                let bit=level-6;let ts=triples();let ctrls:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
                let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
                arithmetic::add(circ,a,c,None,true);arithmetic::add(circ,a,c,Some(d),false);
                mux::truth_swap(circ,&ctrls,truth.clone(),left,right,rest);
                arithmetic::add(circ,a,c,None,true);arithmetic::add(circ,a,c,Some(d),false);
                mux::truth_swap(circ,&ctrls,truth,left,right,rest);
                mux::truth_swap(circ,&rank.iter().collect::<Vec<_>>(),ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect(),left,right,rest);
            }Some(left)
        },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let route=circ.b.ops[start..].to_vec();circ.cswap(g,nodes[0].unwrap(),decision);circ.b.ops.extend(route.into_iter().rev());
}
fn transpose(circ:&mut Circuit,b:[&QReg;3],base:&[(&QReg,bool)],left:usize,right:usize,dirty:&[QReg]){
    let mut at=left;let mut path=Vec::new();for bit in 0..3{if(left^right)>>bit&1!=0{path.push((bit,at));at^=1<<bit;}}
    assert_eq!(at,right);let mut edges=path.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
    for(bit,pattern)in edges{let mut cs=base.to_vec();cs.extend((0..3).filter(|&i|i!=bit).map(|i|(b[i],pattern>>i&1!=0)));gate(circ,&cs,b[bit],dirty);}
}
fn short_permutation(circ:&mut Circuit,b:[&QReg;3],base:&[(&QReg,bool)],x:usize,dirty:&[QReg]){
    let perm=match x{1=>[0,4,2,3,1,5,6,7],2=>[0,1,4,5,2,3,6,7],3=>[0,1,2,4,5,6,3,7],_=>unreachable!()};
    let mut visited=[false;8];for root in 0..8{if visited[root]{continue;}visited[root]=true;let mut next=perm[root];
        while next!=root{assert!(!visited[next]);visited[next]=true;transpose(circ,b,base,root,next,dirty);next=perm[next];}}
}
fn endpoints(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,254);
    // Logical t=1 at A0: cancel its physical-head interpretation.
    for flag in aflags(rank,a,0){let mut cs=vec![(g,true)];cs.extend(flag);gate(circ,&cs,p1,dirty);}
    // p1 is a zero cache only under g. It marks the excluded A0 branch.
    let shift=if j&1!=0{0}else{1};let b=[&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259]];
    let base=[(g,true),(p1,false),(&w1[0],false)];
    if shift==0{for x in 1..4{let mut cs=base.to_vec();cs.extend([(&w2[258],x&1!=0),(&w2[257],x&2!=0)]);short_permutation(circ,b,&cs,x,dirty);}}
    else{short_permutation(circ,b,&base,2,dirty);}
    for flag in aflags(rank,a,0){let mut cs=vec![(g,true)];cs.extend(flag);gate(circ,&cs,p1,dirty);}
    endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,254);
    endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,255);terminal_guard(circ,rank,a,c,p1,p2,g,dirty);
    for flag in aflags(rank,a,0){let mut cs=vec![(g,true)];cs.extend(flag);gate(circ,&cs,p1,dirty);}
    circ.cx(&w2[1],&w2[0]);gate(circ,&[(g,true),(p1,false),(&w1[0],false),(&w2[0],true)],&w2[1],dirty);circ.cx(&w2[1],&w2[0]);
    for flag in aflags(rank,a,0){let mut cs=vec![(g,true)];cs.extend(flag);gate(circ,&cs,p1,dirty);}
    terminal_guard(circ,rank,a,c,p1,p2,g,dirty);endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,255);
}
/// Three physical holes W1[256..258]. All helpers are borrowed dirty.
/// The global gap is W1[A+1] for A<255 and terminal W2[258] for A255.
/// A255 phase01 is outside the reachable nonterminal R01 domain.
pub(super) fn signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize){
    assert!(helpers.len()>=23);let start=circ.b.ops.len();let owned=(circ.b.next_qubit,circ.b.active_qubits);
    let g=&helpers[0];let ha=&helpers[1];let decision=&helpers[2];let dirty=&helpers[3..];
    super::q793_loans::global_a(circ,rank,a,g,w1,&w2[258],None,dirty);
    normal_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);
    borrow_ha(circ,rank,a,g,ha,w2,dirty);circ.cx(g,p2);quotient(circ,rank,a,c,g,decision,w1,dirty);
    super::q793_r01_normal_v2::emit(circ,rank,a,c,sm,g,p1,p2,ha,decision,w1,w2,dirty,j,support_end,false);
    quotient(circ,rank,a,c,g,decision,w1,dirty);circ.cx(g,p2);borrow_ha(circ,rank,a,g,ha,w2,dirty);
    normal_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);
    if j&1!=0{
        special_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);circ.cswap(g,ha,&sm[3]);circ.cx(g,p2);quotient(circ,rank,a,c,g,decision,w1,dirty);
        super::q793_r01_normal_v2::emit(circ,rank,a,c,sm,g,p1,p2,ha,decision,w1,w2,dirty,j,support_end,true);
        quotient(circ,rank,a,c,g,decision,w1,dirty);circ.cx(g,p2);circ.cswap(g,ha,&sm[3]);special_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);
    }
    endpoints(circ,rank,a,c,p1,p2,g,w1,w2,dirty,j);
    super::q793_loans::global_a(circ,rank,a,g,w1,&w2[258],None,dirty);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Q793 dynamic R01 touched omitted W1[{h}]");}}
}
#[path="q793_r01_dynamic_v1_check.rs"] mod check;
pub fn run(){check::run();}
