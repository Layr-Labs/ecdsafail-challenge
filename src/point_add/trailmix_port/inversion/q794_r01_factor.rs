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


fn price(terms:&[usize],predicates:&[Vec<(&QReg,bool)>])->usize{
 let direct:usize=terms.iter().map(|m|predicates.iter().map(|p|cost(2+m.count_ones()as usize+p.len())).sum::<usize>()).sum();
 let all=2*predicates.iter().map(|p|cost(p.len()+2)).sum::<usize>()+2*terms.iter().map(|m|cost(1+m.count_ones()as usize)).sum::<usize>();
 let flags=2*predicates.iter().map(|p|cost(p.len())).sum::<usize>()+2*terms.iter().map(|m|cost(3+m.count_ones()as usize)).sum::<usize>();
 direct.min(all.min(flags))
}
fn mobius(a:&mut[bool],bits:usize){for i in 0..bits{for m in 0..a.len(){if m>>i&1!=0{a[m]^=a[m^(1<<i)];}}}}
fn chart_terms(terms:&[usize],polarity:usize,bits:usize)->Vec<usize>{
 let mut table:Vec<bool>=(0..1usize<<bits).map(|x|terms.iter().fold(false,|v,&m|v^(((x^polarity)&m)==m))).collect();
 mobius(&mut table,bits);table.into_iter().enumerate().filter_map(|(m,v)|v.then_some(m)).collect()
}
// Exact ESOP cofactor on the actual controls, not sampled metadata support.
// Common literals are retained. Every remaining truth-table input is enumerated.
fn compact<'a>(original:&[Vec<(&'a QReg,bool)>],terms:&[usize])->Vec<Vec<(&'a QReg,bool)>>{
 if original.is_empty(){return Vec::new();}
 let common:Vec<_>=original[0].iter().copied().filter(|&(q,v)|original.iter().all(|p|p.iter().any(|&(r,w)|r.id()==q.id()&&v==w))).collect();
 let mut vars:Vec<&QReg>=Vec::new();
 for p in original{for &(q,_)in p{
  if common.iter().any(|&(r,_)|r.id()==q.id()){continue;}
  if !vars.iter().any(|r|r.id()==q.id()){vars.push(q);}
 }}
 vars.sort_by_key(|q|q.id());if vars.len()>5{return original.to_vec();}
 let truth:Vec<bool>=(0..1usize<<vars.len()).map(|x|original.iter().fold(false,|v,p|v^p.iter().all(|&(q,w)|{
  common.iter().any(|&(r,b)|r.id()==q.id()&&b==w)||((x>>vars.iter().position(|r|r.id()==q.id()).unwrap()&1!=0)==w)
 }))).collect();
 let mut best=original.to_vec();let mut best_cost=price(terms,&best);
 for polarity in 0..truth.len(){
  let mut anf:Vec<_>=(0..truth.len()).map(|x|truth[x^polarity]).collect();mobius(&mut anf,vars.len());
  let candidate:Vec<Vec<_>>=anf.into_iter().enumerate().filter_map(|(m,v)|v.then(||{
   let mut cs=common.clone();cs.extend(vars.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,&q)|(q,polarity>>i&1==0)));cs
  })).collect();
  let p=price(terms,&candidate);if p<best_cost{best_cost=p;best=candidate;}
 }
 best
}

pub(super) fn emit(circ:&mut Circuit,chart:&[&QReg],g:&QReg,mask:&QReg,ha:&QReg,dirty:&[QReg],flags:&[Vec<Vec<(&QReg,bool)>>],anf:&[bool],shift:usize){
    assert!(dirty.len()>=18);assert_eq!(flags.len(),4);assert_eq!(anf.len(),2048);
    let mut groups=vec![Vec::new();16];
    for(m,&on)in anf.iter().enumerate(){
        if on&&(m&896).count_ones()<=1&&!(shift==1&&m&64!=0){groups[m>>7].push(m&127);}
    }
    let d=&dirty[0];let rest=&dirty[1..];
    for(fg,mut terms)in groups.into_iter().enumerate(){
        if terms.is_empty(){continue;}
        let mut predicates=vec![Vec::new()];
        for f in 0..4{if fg>>f&1==0{continue;}
            predicates=predicates.into_iter().flat_map(|old|flags[f].iter().filter_map(move|flag|{
                let mut cs=old.clone();cs.extend(flag.iter().copied());normalize(cs)
            })).collect();
        }
        let mut polarity=0usize;
        if std::env::var("Q794_R01_SEED_POLARITY").ok().as_deref()==Some("1"){
            let proposed=match(shift,fg){(0,0)=>10,(0,1)=>66,(0,2)=>2,(1,0)|(1,1)=>42,(1,2)=>6,_=>0};
            let mut best_cost=price(&terms,&predicates);let original_terms=terms.clone();
            for p in [0,proposed]{
                let candidate_terms=chart_terms(&original_terms,p,if shift==0{7}else{6});
                let candidate_predicates=compact(&predicates,&candidate_terms);
                let candidate_cost=price(&candidate_terms,&candidate_predicates);
                if candidate_cost<best_cost{best_cost=candidate_cost;terms=candidate_terms;predicates=candidate_predicates;polarity=p;}
            }
        }
        let direct:usize=terms.iter().map(|m|predicates.iter().map(|p|cost(2+m.count_ones()as usize+p.len())).sum::<usize>()).sum();
        let echo_all=2*predicates.iter().map(|p|cost(p.len()+2)).sum::<usize>()+2*terms.iter().map(|m|cost(1+m.count_ones()as usize)).sum::<usize>();
        let echo_flags=2*predicates.iter().map(|p|cost(p.len())).sum::<usize>()+2*terms.iter().map(|m|cost(3+m.count_ones()as usize)).sum::<usize>();
        if direct<=echo_all.min(echo_flags){
            for m in terms{for p in &predicates{
                let mut cs=vec![(g,true),(mask,true)];cs.extend(chart.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,&q)|(q,polarity>>i&1==0)));cs.extend(p.iter().copied());
                super::gate(circ,&cs,ha,dirty);
            }}continue;
        }
        let all=echo_all<=echo_flags;let at=circ.b.ops.len();
        for p in &predicates{let mut cs=p.clone();if all{cs.extend([(g,true),(mask,true)]);}super::gate(circ,&cs,d,rest);}
        let compute=circ.b.ops[at..].to_vec();
        let action=|circ:&mut Circuit|{for &m in &terms{
            let mut cs=vec![(d,true)];if !all{cs.extend([(g,true),(mask,true)]);}
            cs.extend(chart.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,&q)|(q,polarity>>i&1==0)));
            super::gate(circ,&cs,ha,rest);
        }};
        action(circ);circ.b.ops.extend(compute.into_iter().rev());action(circ);
    }
}

#[path="q794_r01_factor_check.rs"] mod check;
pub(super) fn run(){check::run();}
