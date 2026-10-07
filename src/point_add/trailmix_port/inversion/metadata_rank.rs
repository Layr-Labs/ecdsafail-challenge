//! Native component prototype for controlled updates of the10-bit high-nibble index.
//! This is not an integrated Q799 point adder. FrozenQ802 source is in another workspace.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{conditional_mcx,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeMap;
#[derive(Clone,Copy)]struct Edge {pattern:usize,target:usize}
fn swap(a:usize,b:usize)->Vec<Edge> {
    let mut edges=Vec::new();let mut cur=a;
    for bit in 0..10 {if (a^b)>>bit&1!=0 {edges.push(Edge{pattern:cur,target:bit});cur^=1<<bit;}}
    let n=edges.len();for i in (0..n.saturating_sub(1)).rev(){edges.push(edges[i]);}edges
}
fn program(row:&[usize],pivot:usize,adjacent:bool)->Vec<Edge> {
    let r:Vec<_>=(0..row.len()).map(|i|row[(i+pivot)%row.len()]).collect();let mut out=Vec::new();
    if adjacent {for i in (0..r.len()-1).rev(){out.extend(swap(r[i],r[i+1]));}}
    else {for &x in &r[1..]{out.extend(swap(r[0],x));}}out
}
fn dirty_t(k:usize)->usize {match k {0|1=>0,2=>1,_=>4*k-8}}
fn emit(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],scratch:&QReg,helpers:&[QReg],axis:usize,optimized:bool)->Vec<usize> {
    if optimized && std::env::var("LOWQ_CODEC_RANK_RECURSIVE").ok().as_deref()==Some("1") {
        return emit_recursive(circ,rank,guard,extras,scratch,helpers,axis);
    }
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();
    assert_eq!(triples.len(),966);let mut groups:BTreeMap<Vec<usize>,Vec<(usize,usize)>>=BTreeMap::new();
    for (i,t) in triples.iter().enumerate(){groups.entry(if axis<3 {t.iter().enumerate().filter(|(j,_)|*j!=axis).map(|(_,v)|*v).collect()} else {vec![t[0],t[1]+t[2]]}).or_default().push((if axis<3 {t[axis]} else {t[1]},i));}
    let mut expected:Vec<_>=(0..1024).collect();
    for pairs in groups.values_mut(){pairs.sort();let row:Vec<_>=pairs.iter().map(|p|p.1).collect();
        for i in 0..row.len(){expected[row[i]]=row[(i+1)%row.len()];}
        if row.len()==1 {continue;}
        let changing=row.iter().fold(0usize,|bits,&i|bits|(row[0]^i));let width=(usize::BITS-changing.leading_zeros())as usize;
        let mut edges=program(&row,0,false);let mut use_prefix=false;let mut best=(18+2*extras.len())*edges.len();
        if optimized {for pivot in 0..row.len(){for adjacent in [false,true]{
            let candidate=program(&row,pivot,adjacent);let plain=(18+2*extras.len())*candidate.len();
            let factored=2*dirty_t(10-width)+dirty_t(width+1+extras.len())*candidate.len();
            let use_factored=width<10 && width+1+extras.len()<=helpers.len()+2 && factored<plain;let cost=if use_factored{factored}else{plain};
            if cost<best {best=cost;edges=candidate;use_prefix=use_factored;}
        }}}
        if use_prefix {
            // Scratch is0 only under guard=1. Prefix compute/uncompute is
            // allowed on either branch; every rank action retains guard.
            // The low-bit permutation preserves the cached high prefix.
            let prefix:Vec<_>=(width..10).map(|i|(&rank[i],row[0]>>i&1!=0)).collect();
            length_recompute::mixed_mcx(circ,&prefix,scratch,helpers);
            for edge in edges {
                assert!(edge.target<width);let mut controls=vec![(guard,true),(scratch,true)];controls.extend_from_slice(extras);
                controls.extend((0..width).filter(|&i|i!=edge.target).map(|i|(&rank[i],edge.pattern>>i&1!=0)));
                length_recompute::mixed_mcx(circ,&controls,&rank[edge.target],helpers);
            }
            length_recompute::mixed_mcx(circ,&prefix,scratch,helpers);
        } else {for edge in edges {
            let mut others:Vec<_>=(0..10).filter(|&i|i!=edge.target).map(|i|(&rank[i],edge.pattern>>i&1!=0)).collect();others.extend_from_slice(extras);
            conditional_mcx::guarded(circ,guard,&others,&rank[edge.target],scratch,false,&helpers[0]);
        }}
    }expected
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,value:bool){let bit=1u64<<lane;let v=&mut w[q.id()as usize];*v=(*v&!bit)|if value{bit}else{0};}
pub fn run(){
    let extra_count:usize=std::env::var("LOWQ_CODEC_RANK_EXTRA_CONTROLS").ok().map(|s|s.parse().unwrap()).unwrap_or(0);assert!(extra_count<=4);
    let mut total=0;let mut baseline=[0usize;4];
    let axes=if std::env::var("LOWQ_CODEC_RANK_JOINT").ok().as_deref()==Some("1") {vec![3usize]} else {vec![0,1,2]};
    for optimized in [false,true]{for &axis in &axes{for known in [false,true]{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("codec.rank",10);
        let guard=circ.alloc_qreg("codec.guard");let scratch=circ.alloc_qreg("codec.LS0");let helpers=circ.alloc_qreg_bits("codec.dirty",8);
        let extra_regs=circ.alloc_qreg_bits("codec.extra.conditions",extra_count);
        let extras:Vec<_>=extra_regs.iter().enumerate().map(|(i,q)|(q,i%2==0)).collect();
        let owned=circ.b.next_qubit;if known{circ.x(&scratch);}
        let expected=emit(&mut circ,&rank,&guard,&extras,&scratch,&helpers,axis,optimized);if known{circ.x(&scratch);}
        assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let tof=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        if !optimized{baseline[axis]=tof}else{assert!(tof<baseline[axis]);}
        // All rank/guard inputs, four independent restored dirty patterns.
        let batches=32<<extra_count;
        for pattern in 0..4 {for batch in 0..batches{
            let mut random=0x3874a295621f8d1bu64^((pattern*32+batch)as u64);
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut after=before.clone();
            for lane in 0..64{let index=batch*64+lane;let input=index&1023;let on=index&1024!=0;
                let enabled=on && extras.iter().enumerate().all(|(i,(_,positive))|((index>>(11+i))&1!=0)==*positive);
                let value=if enabled{expected[input]}else{input};
                for (i,(q,_)) in extras.iter().enumerate(){let v=index>>(11+i)&1!=0;put(&mut before,q,lane,v);put(&mut after,q,lane,v);}
                for i in 0..10 {put(&mut before,&rank[i],lane,input>>i&1!=0);put(&mut after,&rank[i],lane,value>>i&1!=0);}
                for (q,v) in [(&guard,on),(&scratch,if on{known}else{(index+pattern)%2!=0})]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"rank axis={axis} optimized={optimized} known={known} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("CODEC_RANK_NATIVE axis={axis} optimized={optimized} known={known} T={tof} ops={} component_wires={owned} extra_controls={extra_count} cases={} forward_inverse_phase_dirty=PASS",b.ops.len(),batches*64*4);
    }}}
    eprintln!("CODEC_RANK_NATIVE_PASS lanes={total}; controlled high-index component only, no fullQ799 circuit");
}

/// XOR an exact predicate of the high-nibble index into an arbitrary target.
/// Disjoint aligned binary intervals need no clean ancilla and cannot cancel
/// each other accidentally. Values for all1024 codes are explicit.
fn query(circ:&mut Circuit,rank:&[QReg],target:&QReg,helpers:&[QReg],values:&[bool;1024]) {
    let mut pos=0usize;
    while pos<1024 {
        if !values[pos]{pos+=1;continue;}
        let mut end=pos+1;while end<1024 && values[end]{end+=1;}
        while pos<end {
            let align=if pos==0{10}else{(pos.trailing_zeros()as usize).min(10)};
            let remaining=end-pos;let width=align.min((usize::BITS-1-remaining.leading_zeros())as usize);
            let controls:Vec<_>=(width..10).map(|q|(&rank[q],pos>>q&1!=0)).collect();
            length_recompute::mixed_mcx(circ,&controls,target,helpers);
            pos+=1<<width;
        }
    }
}
#[path="metadata_predicate_programs.rs"]
mod predicate_programs;
pub fn run_queries(){
    let esop=std::env::var("LOWQ_CODEC_QUERY_ESOP").ok().as_deref()==Some("1");
    eprintln!("CODEC_QUERY_MODE esop={esop}");
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();
    let mut lanes=0;
    for kind in 0..5 {
        let mut tsum=0usize;let mut tmax=0;let mut osum=0;
        for bound in 0..=16 {
            let mut values=[false;1024];for (i,t) in triples.iter().enumerate(){
                let v=match kind{0=>t[0],1=>t[1],2=>t[2],3=>t[0]+t[1],_=>t[1]+t[2]};values[i]=v<=bound;
            }
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("codec.query.rank",10);
            let target=circ.alloc_qreg("codec.query.target");let helpers=circ.alloc_qreg_bits("codec.query.dirty",8);let owned=circ.b.next_qubit;
            if esop {
                for &(mask,ones) in predicate_programs::PROGRAMS[kind*17+bound] {
                    let controls:Vec<_>=(0..10).filter(|&q|mask>>q&1!=0).map(|q|(&rank[q],ones>>q&1!=0)).collect();
                    length_recompute::mixed_mcx(&mut circ,&controls,&target,&helpers);
                }
            } else {query(&mut circ,&rank,&target,&helpers,&values);}
            assert_eq!(owned,circ.b.next_qubit);let b=circ.into_builder();
            for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
            let tof=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();tsum+=tof;tmax=tmax.max(tof);osum+=b.ops.len();
            for pattern in 0..4 {for batch in 0..32 {
                let mut random=0x528efe49bd2a731cu64^((pattern*32+batch)as u64);
                let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut after=before.clone();
                for lane in 0..64{let index=batch*64+lane;let value=index&1023;let old=index&1024!=0;
                    for i in 0..10{put(&mut before,&rank[i],lane,value>>i&1!=0);put(&mut after,&rank[i],lane,value>>i&1!=0);}
                    put(&mut before,&target,lane,old);put(&mut after,&target,lane,old^values[value]);
                }
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);
                sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);
                sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
            }}
        }
        eprintln!("CODEC_QUERY_NATIVE kind={kind} bounds=17 sum_T={tsum} max_T={tmax} sum_ops={osum} wires=19 phase_inverse_dirty=PASS");
    }
    eprintln!("CODEC_QUERY_NATIVE_PASS lanes={lanes}; exact predicate component only, fullQ799 circuit absent");
}

#[path="metadata_rank_recursive_programs.rs"]
mod recursive_programs;
fn emit_recursive(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],scratch:&QReg,helpers:&[QReg],axis:usize)->Vec<usize> {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();
    assert_eq!(triples.len(),966);let mut groups:BTreeMap<Vec<usize>,Vec<(usize,usize)>>=BTreeMap::new();
    for (i,t) in triples.iter().enumerate(){groups.entry(if axis<3 {t.iter().enumerate().filter(|(j,_)|*j!=axis).map(|(_,v)|*v).collect()} else {vec![t[0],t[1]+t[2]]}).or_default().push((if axis<3 {t[axis]} else {t[1]},i));}
    let mut expected:Vec<_>=(0..1024).collect();
    for pairs in groups.values_mut(){pairs.sort();let row:Vec<_>=pairs.iter().map(|p|p.1).collect();
        for i in 0..row.len(){expected[row[i]]=row[(i+1)%row.len()];}
    }
    emit_update(circ,rank,guard,extras,scratch,helpers,axis,false,false);
    expected
}

/// Exact high-index update; supplied scratch is known only under guard.
pub(super) fn emit_update(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],scratch:&QReg,helpers:&[QReg],axis:usize,reverse:bool,known:bool) {
    if known {circ.x(scratch);}
    let program=recursive_programs::PROGRAMS[axis];
    for j in 0..program.len() {
        let (target,mask,ones)=program[if reverse {program.len()-1-j} else {j}];
        assert_eq!(mask>>target&1,0);assert_eq!(ones&!mask,0);
        let mut others:Vec<_>=(0..10).filter(|&i|mask>>i&1!=0).map(|i|(&rank[i],ones>>i&1!=0)).collect();
        others.extend_from_slice(extras);
        conditional_mcx::guarded(circ,guard,&others,&rank[target as usize],scratch,false,&helpers[0]);
    }
    if known {circ.x(scratch);}
}

/// Exchange exactly two high-index basis states under supplied controls.
/// Used to repair the modulo-wrap extension of composed coordinate updates.
pub(super) fn emit_index_swap(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],scratch:&QReg,helpers:&[QReg],left:usize,right:usize,known:bool) {
    if known {circ.x(scratch);}
    for edge in swap(left,right) {
        let mut others:Vec<_>=(0..10).filter(|&i|i!=edge.target).map(|i|(&rank[i],edge.pattern>>i&1!=0)).collect();others.extend_from_slice(extras);
        conditional_mcx::guarded(circ,guard,&others,&rank[edge.target],scratch,false,&helpers[0]);
    }
    if known {circ.x(scratch);}
}

pub(super) fn xor_high_a_equal(circ:&mut Circuit,rank:&[QReg],guard:&QReg,target:&QReg,s0:&QReg,helpers:&[QReg],bound:usize,known:bool) {
    assert!(bound<16);
    for b in std::iter::once(bound).chain(bound.checked_sub(1)) {
        for &(mask,ones) in predicate_programs::PROGRAMS[b] {
            let others:Vec<_>=(0..10).filter(|&i|mask>>i&1!=0).map(|i|(&rank[i],ones>>i&1!=0)).collect();
            conditional_mcx::guarded(circ,guard,&others,target,s0,known,&helpers[0]);
        }
    }
}
