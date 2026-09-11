//! Timefix R01: normalize A1/S1 into the main HA donor and emit one carry scan.
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

fn echo_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
/// Grouped exact dirty echo for rank-guarded toggles of one target `g`.
///
/// `gates` are the exact control sets the direct code emits (each through `gate`, i.e. after
/// duplicate-literal merging and contradiction skipping). Every gate toggles the same `g`, with
/// controls disjoint from `g`, so the gates commute and may be regrouped. Gates are grouped by
/// their identical non-rank literal set `B`; within a group the XOR of the emitted rank cubes is
/// a function `H` of the five rank bits alone, tabulated on all 32 codes from the same normalized
/// control sets (no disjointness assumption). With arbitrary borrowed `d`, `D_B H_d D_B^-1 H_d`
/// toggles `g` by `B*H` and restores `d` (the q794_r01_factor identity). The echo is used only
/// when strictly cheaper than the direct group under the tree's `4n-8` dirty-ladder model.
pub(super) fn grouped_with_flag(circ:&mut Circuit,gates:&[Vec<(&QReg,bool)>],rank:&[QReg],g:&QReg,dirty:&[QReg],flag:&str){
    if !mux::active(flag)||dirty.len()<2{for cs in gates{gate(circ,cs,g,dirty);}return;}
    let pos=|q:&QReg|rank.iter().position(|r|r.id()==q.id());
    struct Group<'a>{key:Vec<(&'a QReg,bool)>,truth:Vec<bool>,direct:usize,members:Vec<usize>}
    let mut groups:Vec<Group>=Vec::new();
    for (n,cs) in gates.iter().enumerate(){
        let mut unique:Vec<(&QReg,bool)>=Vec::new();let mut skip=false;
        for &(q,v) in cs{assert_ne!(q.id(),g.id());if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{skip=true;break;}}else{unique.push((q,v));}}
        if skip{continue;}
        let mut key:Vec<(&QReg,bool)>=unique.iter().copied().filter(|(q,_)|pos(q).is_none()).collect();key.sort_by_key(|(q,_)|q.id());
        let lits:Vec<(usize,bool)>=unique.iter().filter_map(|&(q,v)|pos(q).map(|i|(i,v))).collect();
        let idx=match groups.iter().position(|gr|gr.key.len()==key.len()&&gr.key.iter().zip(&key).all(|(a,b)|a.0.id()==b.0.id()&&a.1==b.1)){Some(i)=>i,None=>{groups.push(Group{key,truth:vec![false;32],direct:0,members:Vec::new()});groups.len()-1}};
        for r in 0..32{if lits.iter().all(|&(i,v)|(r>>i&1!=0)==v){groups[idx].truth[r]^=true;}}
        groups[idx].direct+=echo_cost(unique.len());groups[idx].members.push(n);
    }
    let d=&dirty[0];let rest=&dirty[1..];
    for gr in groups{
        if gr.truth.iter().all(|&t|!t){continue;}
        let (pol,terms)=mux::swap_terms(gr.truth.clone(),5);
        let chart:usize=terms.iter().map(|&m|echo_cost(m.count_ones()as usize)).sum();
        let echo=2*chart+2*echo_cost(gr.key.len()+1);
        if gr.direct<=echo{for &n in &gr.members{gate(circ,&gates[n],g,rest_or_all(dirty));}continue;}
        for &(q,_) in &gr.key{assert_ne!(q.id(),d.id(),"echo scratch aliases a guard literal");}
        let compute=|circ:&mut Circuit|{
            for i in 0..5{if pol>>i&1!=0{circ.x(&rank[i]);}}
            for &m in &terms{let cs:Vec<(&QReg,bool)>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();
                match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}
            for i in (0..5).rev(){if pol>>i&1!=0{circ.x(&rank[i]);}}
        };
        let consume=|circ:&mut Circuit|{let mut cs=vec![(d,true)];cs.extend_from_slice(&gr.key);mixed_mcx(circ,&cs,g,rest);};
        consume(circ);compute(circ);consume(circ);compute(circ);
    }
}
fn grouped(circ:&mut Circuit,gates:&[Vec<(&QReg,bool)>],rank:&[QReg],g:&QReg,dirty:&[QReg]){grouped_with_flag(circ,gates,rank,g,dirty,"Q793_RANK_ECHO_R01")}
fn rest_or_all(dirty:&[QReg])->&[QReg]{dirty}
fn phase_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    let base=[(p1,false),(p2,true)];let mut gates=vec![base.to_vec()];
    for flag in aflags(rank,a,255){let mut cs=base.to_vec();cs.extend(flag);gates.push(cs);}
    grouped(circ,&gates,rank,g,dirty);
}
/// Metadata-only A+C=254/255 toggle. Original C on entry and return.
fn endpoint_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],value:usize){
    assert!([254,255].contains(&value));arithmetic::add(circ,a,c,None,false);
    let mut gates=Vec::new();
    for (rk,t)in triples().iter().enumerate(){
        let hi=t[0]+t[1];if hi!=3&&(value!=254||hi!=2){continue;}
        let mut cs=vec![(p1,false),(p2,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        cs.extend(rank.iter().enumerate().map(|(i,q)|(q,rk>>i&1!=0)));
        if hi==3{gates.push(cs.clone());}
        if value==254{cs.extend(a.iter().map(|q|(q,true)));gates.push(cs);}
    }
    grouped(circ,&gates,rank,g,dirty);
    arithmetic::add(circ,a,c,None,true);
}
/// Exact phase01/A1/S1 normal-domain guard, read only before or after SM3 loan.
fn special_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize){
    if j&1==0{return;}
    for (rk,t)in triples().iter().enumerate(){if t[0]!=0||t[2]!=0{continue;}
        let mut cs=vec![(p1,false),(p2,true),(&c[0],j>>1!=0)];cs.extend(sm.iter().map(|q|(q,false)));
        cs.extend(a.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(rank.iter().enumerate().map(|(i,q)|(q,rk>>i&1!=0)));
        let mut gates=vec![cs.clone()];
        for cv in 253..256{for flag in cflags(rank,c,cv){let mut ex=cs.clone();ex.extend(flag);gates.push(ex);}}
        grouped(circ,&gates,rank,g,dirty);
    }
}
fn terminal_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    let mut gates=Vec::new();
    for af in aflags(rank,a,255){for cf in cflags(rank,c,0){let mut cs=vec![(p1,false),(p2,true)];cs.extend(af.iter().copied());cs.extend(cf);gates.push(cs);}}
    grouped(circ,&gates,rank,g,dirty);
}
fn normal_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize){
    phase_guard(circ,rank,a,p1,p2,g,dirty);
    endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,254);endpoint_guard(circ,rank,a,c,p1,p2,g,dirty,255);
    terminal_guard(circ,rank,a,c,p1,p2,g,dirty);
}
fn borrow_ha(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,ha:&QReg,w2:&[QReg],dirty:&[QReg]){
    mux::exchange(circ,rank,a,0,Some(g),ha,&w2[1..257].iter().collect::<Vec<_>>(),dirty,false);
}
fn transpose(circ:&mut Circuit,b:[&QReg;3],base:&[(&QReg,bool)],left:usize,right:usize,dirty:&[QReg]){
    if super::metadata_muxlease::active("Q793_AFFINE_R01_TRANSPOSE"){
        // No base control aliases a word bit at any call site (b = W2 head cells, base = g/p1/W1[0] and
        // W2[258]/[257] literals only when b = W2[0..3]), so `gate`'s dedup is a no-op and the toggle is exact.
        for &(q,_) in base{for w in b{assert_ne!(q.id(),w.id(),"transpose base aliases word");}}
        super::metadata_rank5::affine_word_transposition(circ,&b,base,dirty,left,right);return;
    }
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
    circ.cx(g,p2);super::q793_r01_a1normalize_timefix_r01::normalize(circ,rank,a,c,sm,g,p1,w1,w2,dirty,j,false);
    borrow_ha(circ,rank,a,g,ha,w2,dirty);super::q793_r01_routes_v1::quotient(circ,rank,a,c,w1,g,p2,decision);
    super::q793_r01_normal_timefix_r01::emit(circ,rank,a,c,sm,g,p1,p2,ha,decision,w1,w2,dirty,j,support_end,false);
    super::q793_r01_routes_v1::quotient(circ,rank,a,c,w1,g,p2,decision);borrow_ha(circ,rank,a,g,ha,w2,dirty);
    super::q793_r01_a1normalize_timefix_r01::normalize(circ,rank,a,c,sm,g,p1,w1,w2,dirty,j,true);circ.cx(g,p2);
    normal_guard(circ,rank,a,c,sm,p1,p2,g,dirty,j);
    endpoints(circ,rank,a,c,p1,p2,g,w1,w2,dirty,j);
    super::q793_loans::global_a(circ,rank,a,g,w1,&w2[258],None,dirty);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Q793 dynamic R01 touched omitted W1[{h}]");}}
}
#[path="q793_r01_dynamic_timefix_r01_check.rs"] mod check;
pub fn run(){check::run();}
