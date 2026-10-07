//! Exact low-seed metadata factoring. No new clean or physical qubit.
//!
//! Group the inherited ANF by its metadata monomial, F(metadata)*H(chart).
//! With arbitrary borrowed d, D_F H_d D_F^-1 H_d toggles the requested
//! product and restores d. Guards can belong to either factor. The cheapest
//! of both exact echoes and the original direct expansion is selected using
//! the actual dirty-ladder CCX cost, not a reachable-input probability.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

fn cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
fn normalize<'a>(cs:Vec<(&'a QReg,bool)>)->Option<Vec<(&'a QReg,bool)>>{
    let mut out:Vec<(&QReg,bool)>=Vec::new();
    for(q,v)in cs{if let Some(&(_,old))=out.iter().find(|&&(p,_)|p.id()==q.id()){
        if old!=v{return None;}
    }else{out.push((q,v));}}Some(out)
}

pub(super) fn emit(circ:&mut Circuit,chart:&[&QReg],g:&QReg,mask:&QReg,ha:&QReg,dirty:&[QReg],flags:&[Vec<Vec<(&QReg,bool)>>],anf:&[bool],shift:usize){
    assert!(dirty.len()>=18);assert_eq!(flags.len(),4);assert_eq!(anf.len(),2048);
    let mut groups=vec![Vec::new();16];
    for(m,&on)in anf.iter().enumerate(){
        if on&&(m&896).count_ones()<=1&&!(shift==1&&m&64!=0){groups[m>>7].push(m&127);}
    }
    let d=&dirty[0];let rest=&dirty[1..];
    for(fg,terms)in groups.into_iter().enumerate(){
        if terms.is_empty(){continue;}
        let mut predicates=vec![Vec::new()];
        for f in 0..4{if fg>>f&1==0{continue;}
            predicates=predicates.into_iter().flat_map(|old|flags[f].iter().filter_map(move|flag|{
                let mut cs=old.clone();cs.extend(flag.iter().copied());normalize(cs)
            })).collect();
        }
        let direct:usize=terms.iter().map(|m|predicates.iter().map(|p|cost(2+m.count_ones()as usize+p.len())).sum::<usize>()).sum();
        let echo_all=2*predicates.iter().map(|p|cost(p.len()+2)).sum::<usize>()+2*terms.iter().map(|m|cost(1+m.count_ones()as usize)).sum::<usize>();
        let echo_flags=2*predicates.iter().map(|p|cost(p.len())).sum::<usize>()+2*terms.iter().map(|m|cost(3+m.count_ones()as usize)).sum::<usize>();
        if direct<=echo_all.min(echo_flags){
            for m in terms{for p in &predicates{
                let mut cs=vec![(g,true),(mask,true)];cs.extend(chart.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,&q)|(q,true)));cs.extend(p.iter().copied());
                super::gate(circ,&cs,ha,dirty);
            }}continue;
        }
        let all=echo_all<=echo_flags;let at=circ.b.ops.len();
        for p in &predicates{let mut cs=p.clone();if all{cs.extend([(g,true),(mask,true)]);}super::gate(circ,&cs,d,rest);}
        let compute=circ.b.ops[at..].to_vec();
        let action=|circ:&mut Circuit|{for &m in &terms{
            let mut cs=vec![(d,true)];if !all{cs.extend([(g,true),(mask,true)]);}
            cs.extend(chart.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,&q)|(q,true)));
            super::gate(circ,&cs,ha,rest);
        }};
        action(circ);circ.b.ops.extend(compute.into_iter().rev());action(circ);
    }
}

#[path="q794_r01_factor_check.rs"] mod check;
pub(super) fn run(){check::run();}
