//! Exact HMR leases. A direct symbolic product match AND an exact phase-receipt
//! cancellation certificate are required. No sampled-zero premises.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
use super::c86_vn::{Support,Affine};
use std::collections::{HashMap,HashSet};
#[derive(Clone)]struct Erased{at:usize,q:usize,value:Affine,fix:Affine,clean:bool,valid:bool}
fn diagonal(k:K)->bool{matches!(k,K::Neg|K::Z|K::CZ|K::CCZ)}
fn phase(s:&mut Support,o:&Op)->Affine{let mut f=Affine::constant(true);
    for q in [o.q_target,o.q_control1,o.q_control2]{if q!=NO_QUBIT{f=s.and(&f,&s.qubits[q.0 as usize].clone());}}
    s.and(&f,&s.base_condition.clone())
}
pub(crate) fn apply(ops:Vec<Op>)->Vec<Op>{
    let (_,_,_,regs)=crate::circuit::analyze_ops(ops.iter());
    let public_bits:HashSet<u64>=regs.into_iter().flatten().filter_map(|x|match x{crate::circuit::QubitOrBit::Bit(b)=>Some(b.0),_=>None}).collect();
    let mut s=Support::new(&ops);let mut erased:Vec<Erased>=vec![];let mut receipts:HashMap<u64,usize>=HashMap::new();
    let mut pending:HashMap<Affine,Vec<usize>>=HashMap::new();let mut idle=vec![None;s.qubits.len()];
    let mut candidates=vec![];let mut matches=0usize;let mut hmr=0usize;
    for (i,o) in ops.iter().enumerate(){
        if o.c_condition!=NO_BIT{if let Some(&id)=receipts.get(&o.c_condition.0){
            if diagonal(o.kind){let p=phase(&mut s,o);let fix=s.xor(&erased[id].fix,&p);erased[id].fix=fix;}
            else{erased[id].clean=false;}
        }}
        if o.c_target!=NO_BIT{if let Some(id)=receipts.remove(&o.c_target.0){erased[id].valid=erased[id].clean&&erased[id].fix==erased[id].value;}}
        if o.kind==K::CCX&&o.c_condition==NO_BIT&&s.condition_stack.is_empty(){
            let t=o.q_target.0 as usize;
            if s.qubits[t].is_zero(){let p=s.and(&s.qubits[o.q_control1.0 as usize].clone(),&s.qubits[o.q_control2.0 as usize].clone());
                if let Some(ids)=pending.get(&p){for &id in ids.iter().rev(){let e=&erased[id];
                    if idle[e.q]==Some(id){matches+=1;candidates.push((id,i,t));idle[e.q]=None;break;}
                }}
            }
        }
        // A kept value must be untouched, including by diagonal gates.
        for q in [o.q_target,o.q_control1,o.q_control2]{if q!=NO_QUBIT{idle[q.0 as usize]=None;}}
        if o.kind==K::Hmr&&o.c_condition==NO_BIT&&s.condition_stack.is_empty()&&!public_bits.contains(&o.c_target.0){
            hmr+=1;let q=o.q_target.0 as usize;let value=s.qubits[q].clone();
            if !value.is_zero()&&value.atoms.len()<=2048{let id=erased.len();
                erased.push(Erased{at:i,q,value:value.clone(),fix:Affine::constant(false),clean:true,valid:false});
                pending.entry(value).or_default().push(id);receipts.insert(o.c_target.0,id);idle[q]=Some(id);
            }
        }
        s.step(o);
    }
    for id in receipts.into_values(){erased[id].valid=erased[id].clean&&erased[id].fix==erased[id].value;}
    let mut replace=HashMap::new();let mut used=HashSet::new();let mut count=0usize;
    for (id,i,t) in candidates{let e=&erased[id];if !e.valid||!used.insert(id){continue;}
        let mut zero=Op::empty();zero.kind=K::BitStore0;zero.c_target=ops[e.at].c_target;
        assert!(replace.insert(e.at,Some(zero)).is_none());
        let swap=if e.q==t{None}else{let mut x=Op::empty();x.kind=K::Swap;x.q_control1=QubitId(e.q as u64);x.q_target=QubitId(t as u64);Some(x)};
        assert!(replace.insert(i,swap).is_none());count+=1;
    }
    let mut out=Vec::with_capacity(ops.len());for (i,o) in ops.into_iter().enumerate(){match replace.get(&i){Some(Some(x))=>{x.validate();out.push(*x);},Some(None)=>{},None=>out.push(o)}}
    eprintln!("C86_LEASE hmr_screened={hmr} erased_indexed={} direct_idle_matches={matches} phase_certified={} leases={count} measurements_removed={count}",erased.len(),erased.iter().filter(|e|e.valid).count());out
}
