//! Grouped exact dirty-echo factoring of rank-guarded toggles (shared by the Q793 step stages).
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_muxlease as mux,length_recompute::mixed_mcx};
/// Same normalization as the stages' `gate`: merge duplicate literals, skip contradictory sets.
pub(super) fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();for &(q,v)in cs{assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    mixed_mcx(circ,&unique,out,dirty);
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
pub(super) fn grouped(circ:&mut Circuit,flag:&str,gates:&[Vec<(&QReg,bool)>],rank:&[QReg],g:&QReg,dirty:&[QReg]){
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
fn rest_or_all(dirty:&[QReg])->&[QReg]{dirty}
