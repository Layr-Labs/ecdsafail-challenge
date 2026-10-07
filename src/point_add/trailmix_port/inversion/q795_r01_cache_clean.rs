//! R01 two-pass ONLY: closed cache updates may have arbitrary off-guard XORs.
//! Never substitute this extension into a standalone or non-literal cache caller.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::metadata_arithmetic5;
#[path="metadata_arithmetic5_programs.rs"] mod programs;

pub(super) fn enabled()->bool {super::metadata_muxlease::active("Q795_R01_CACHE_RANK_CLEAN")||super::metadata_muxlease::active("Q795_R01_CACHE_CARRY_CLEAN")}
fn clean(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,g:&QReg){
    circ.x(g);super::paired_clean_mcx::toggle(circ,cs,out,g);circ.x(g);
}
fn carry(circ:&mut Circuit,a:&[QReg],b:&[QReg],d:&QReg,g:&QReg){
    if !super::metadata_muxlease::active("Q795_R01_CACHE_CARRY_CLEAN") {
        metadata_arithmetic5::add(circ,a,b,None,true);metadata_arithmetic5::add(circ,a,b,Some(d),false);return;
    }
    assert_eq!(a.len(),b.len());
    let mut ids=vec![d.id(),g.id()];ids.extend(a.iter().chain(b).map(QReg::id));ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    // F excludes d. Its center changes only d, so reverse F restores ALL
    // metadata and g even when original g0 supplies a dirty initial borrow.
    circ.x(g);let start=circ.b.ops.len();
    for (s,t) in a.iter().zip(b){circ.cx(s,t);circ.cx(g,s);circ.ccx(t,s,g);}
    let forward=circ.b.ops[start..].to_vec();circ.cx(g,d);circ.b.ops.extend(forward.into_iter().rev());circ.x(g);
}
fn cost(n:usize)->usize{if n<2{0}else{2*n-3}}
fn anf(truth:&[bool])->(usize,Vec<usize>,usize){
    use std::collections::HashMap;use std::sync::{Mutex,OnceLock};
    static CACHE:OnceLock<Mutex<HashMap<Vec<bool>,(usize,Vec<usize>,usize)>>>=OnceLock::new();
    let mut cache=CACHE.get_or_init(||Mutex::new(HashMap::new())).lock().unwrap();if let Some(v)=cache.get(truth){return v.clone();}
    let width=truth.len().ilog2()as usize;assert_eq!(1<<width,truth.len());assert!(width<=6);
    let mut best=(0,Vec::new(),usize::MAX);let mut best_secondary=usize::MAX;
    for polarity in 0..truth.len(){
        let mut a:Vec<_>=(0..truth.len()).map(|x|truth[x^polarity]).collect();
        for bit in 0..width{for m in 0..a.len(){if m>>bit&1!=0{a[m]^=a[m^(1<<bit)];}}}
        let terms:Vec<_>=a.iter().enumerate().filter_map(|(m,&v)|v.then_some(m)).collect();
        let t:usize=terms.iter().map(|m|cost(m.count_ones()as usize)).sum();let secondary=terms.len()+2*polarity.count_ones()as usize;
        if(t,secondary)<(best.2,best_secondary){best=(polarity,terms,t);best_secondary=secondary;}
    }
    for(x,&v)in truth.iter().enumerate(){assert_eq!(best.1.iter().fold(false,|s,&m|s^(((x^best.0)&m)==m)),v);}
    cache.insert(truth.to_vec(),best.clone());best
}
fn emit_anf(circ:&mut Circuit,inputs:&[&QReg],polarity:usize,terms:&[usize],out:&QReg,g:&QReg){
    for(i,&q)in inputs.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    for &m in terms {let cs:Vec<_>=inputs.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(_,&q)|(q,true)).collect();clean(circ,&cs,out,g);}
    for(i,&q)in inputs.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}
fn terms(circ:&mut Circuit,rank:&[QReg],d:&QReg,g:&QReg,out:&QReg,helpers:&[QReg],from:isize,to:isize,zero:bool){
    if !super::metadata_muxlease::active("Q795_R01_CACHE_RANK_CLEAN") {
        metadata_arithmetic5::sum_terms(circ,rank,d,g,out,helpers,programs::SUM_EQUAL,from,to,zero);return;
    }
    let mut cubes=std::collections::BTreeSet::new();
    for h in [from,to]{if h<0||h as usize>=programs::SUM_EQUAL.len(){continue;}for &(mut m,mut v)in programs::SUM_EQUAL[h as usize]{
        if zero{if m&32!=0&&v&32!=0{continue;}m&=31;v&=31;}
        if !cubes.insert((m,v)){cubes.remove(&(m,v));}
    }}
    if !zero{
        let original=cubes.clone();cubes.clear();for &(m,v)in &original{if m&32!=0{let x=(m|32,(v&31)|32);if !cubes.insert(x){cubes.remove(&x);}}}
        for x in 0..64u16{let f=|y:u16|original.iter().fold(false,|b,&(m,v)|b^((y&m)==v));assert_eq!(cubes.iter().fold(false,|b,&(m,v)|b^((x&m)==v)),x&32!=0&&(f(x&31)^f((x&31)|32)));}
    }
    let width=if zero{5}else{6};let truth:Vec<_>=(0..1u16<<width).map(|x|cubes.iter().fold(false,|b,&(m,v)|b^((x&m)==v))).collect();
    let(polarity,monomials,anf_t)=anf(&truth);let direct_t:usize=cubes.iter().map(|(m,_)|cost(m.count_ones()as usize)).sum();
    let rank_truth:Vec<_>=(0..32u16).map(|x|cubes.iter().fold(false,|b,&(m,v)|b^(((x|if zero{0}else{32})&m)==v))).collect();
    let(rpol,rterms,rt)=anf(&rank_truth);let factored_t=2*rt+2*cost(if zero{1}else{2});
    if factored_t<direct_t.min(anf_t){
        assert!(!helpers.is_empty());let scratch=&helpers[0];let start=circ.b.ops.len();
        let inputs:Vec<_>=rank.iter().collect();emit_anf(circ,&inputs,rpol,&rterms,scratch,g);
        let compute=circ.b.ops[start..].to_vec();let mut cs=vec![(scratch,true)];if !zero{cs.push((d,true));}
        clean(circ,&cs,out,g);circ.b.ops.extend(compute.into_iter().rev());clean(circ,&cs,out,g);return;
    }
    let inputs:Vec<_>=rank.iter().chain((!zero).then_some(d)).collect();
    if anf_t<direct_t{emit_anf(circ,&inputs,polarity,&monomials,out,g);return;}
    for(m,v)in cubes{let cs:Vec<_>=inputs.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(i,&q)|(q,v>>i&1!=0)).collect();clean(circ,&cs,out,g);}
}
pub(super) fn transition(circ:&mut Circuit,rank:&[QReg],a:&[QReg],b:&[QReg],g:&QReg,flag:&QReg,d:&QReg,helpers:&[QReg],from:isize,to:isize){
    if from==to{return;}
    carry(circ,a,b,d,g);terms(circ,rank,d,g,flag,helpers,from,to,false);
    carry(circ,a,b,d,g);terms(circ,rank,d,g,flag,helpers,from,to,false);
    terms(circ,rank,d,g,flag,helpers,from,to,true);
}

pub mod verification {
    use super::*;use crate::sim::Simulator;use crate::circuit::OperationType;use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    pub fn run(){
        assert!(enabled());let mut total=0usize;
        for(from,to)in [(-1,4),(-1,3),(4,3),(3,2),(2,1),(1,0)]{
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("cache.rank",5);let a=circ.alloc_qreg_bits("cache.a",6);let b=circ.alloc_qreg_bits("cache.b",6);
            let g=circ.alloc_qreg("cache.g");let flag=circ.alloc_qreg("cache.flag");let d=circ.alloc_qreg("cache.d");let dirty=circ.alloc_qreg_bits("cache.dirty",16);let owned=circ.b.next_qubit;
            transition(&mut circ,&rank,&a,&b,&g,&flag,&d,&dirty,from,to);let candidate=circ.b.ops.clone();circ.b.ops.clear();
            metadata_arithmetic5::sum_flag_transition(&mut circ,&rank,&a,&b,&g,&flag,&d,&dirty,from,to);let reference=circ.b.ops.clone();assert_eq!(circ.b.next_qubit,owned);
            assert!(candidate.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let mut fixed=Fixed;let mut reference_fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);let mut old=Simulator::new(owned as usize,0,&mut reference_fixed);
            for batch in 0..(1usize<<20)/64{
                let mut before=vec![0u64;owned as usize];
                for lane in 0..64{let x=batch*64+lane;for(i,q)in rank.iter().chain(a.iter()).chain(b.iter()).chain([&g,&flag,&d]).enumerate(){before[q.id()as usize]|=(((x>>i)&1)as u64)<<lane;}}
                for(i,q)in dirty.iter().enumerate(){before[q.id()as usize]=(0x6a09e667f3bcc909u64.wrapping_mul((batch as u64+1).wrapping_mul(i as u64+3))).rotate_left((i*7)as u32);}
                sim.qubits.copy_from_slice(&before);old.qubits.copy_from_slice(&before);sim.apply_iter(candidate.iter());old.apply_iter(reference.iter());
                let on=before[g.id()as usize];for q in 0..owned as usize{if q==flag.id()as usize{assert_eq!((sim.qubits[q]^old.qubits[q])&on,0,"active output {from}->{to} batch{batch}");}else{assert_eq!(sim.qubits[q],before[q],"restore {from}->{to} q{q} batch{batch}");}}
                assert_eq!(sim.phase,0);sim.apply_iter(candidate.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            }
            eprintln!("R01_CACHE_CLEAN_UNIT transition={from}->{to} PASS T={} referenceT={}",candidate.iter().filter(|o|o.kind==OperationType::CCX).count(),reference.iter().filter(|o|o.kind==OperationType::CCX).count());
        }
        eprintln!("R01_CACHE_CLEAN_UNIT PASS {total} lanes; all rank/low metadata/g/output/d; active reference, arbitrary-offguard restoration, inverse, phase, no allocation");
    }
}
