use crate::circuit::{Op,OperationType as K,QubitId,BitId,NO_QUBIT,NO_BIT};
use std::collections::{HashMap,HashSet};
#[derive(Clone,Debug)]
struct Window {uses:Vec<usize>,start:usize,end:usize,proxy:f64,donors:Vec<usize>}
fn touches(o:&Op)->Vec<usize>{
    if o.kind==K::R{return vec![];}
    [o.q_control1,o.q_control2,o.q_target].into_iter().filter(|q|*q!=NO_QUBIT).map(|q|q.0 as usize).collect()
}
pub fn optimize(ops:Vec<Op>)->Vec<Op> {
    let split=true;
    optimize_impl(ops,split)
}
fn optimize_impl(ops:Vec<Op>,split:bool)->Vec<Op> {
    let nq=ops.iter().flat_map(|o|[o.q_control1,o.q_control2,o.q_target]).filter(|q|*q!=NO_QUBIT).map(|q|q.0 as usize).max().unwrap()+1;
    let nb=ops.iter().flat_map(|o|[o.c_target,o.c_condition]).filter(|b|*b!=NO_BIT).map(|b|b.0).max().map_or(0,|b|b+1);
    let mut depth=0usize;let mut fence=0usize;
    let mut starts=vec![0usize;ops.len()];let mut ends=vec![0usize;ops.len()];
    let mut weights=vec![0f64;ops.len()];
    for (i,o) in ops.iter().enumerate(){
        if depth==0 {fence=i;}starts[i]=fence;
        if o.kind==K::CCX {weights[i]=0.5f64.powi(depth as i32+if o.c_condition==NO_BIT{0}else{1});}
        match o.kind {K::PushCondition=>depth+=1,K::PopCondition=>depth-=1,_=>{}}
        ends[i]=if depth==0 {i+1}else{usize::MAX};
    }
    let mut next=vec![usize::MAX;nq];let mut end_ok=vec![false;ops.len()];let mut following=ops.len();
    for (i,o) in ops.iter().enumerate().rev(){
        if ends[i]!=usize::MAX {following=ends[i];}else{ends[i]=following;}
        if o.kind==K::CCX {end_ok[i]=[o.q_control1,o.q_control2].iter().all(|q|next[q.0 as usize]>=following);}
        match o.kind {K::X|K::CX|K::CCX|K::R|K::Hmr=>next[o.q_target.0 as usize]=i,
            K::Swap=>{next[o.q_target.0 as usize]=i;next[o.q_control1.0 as usize]=i;},_=>{}}
    }
    let mut symbolic=super::exact_wide_stage1_support::Support::new(&ops);
    let mut groups:HashMap<(bool,Vec<u64>),Vec<usize>>=HashMap::new();
    for (i,o) in ops.iter().enumerate(){
        if o.kind==K::CCX {groups.entry(symbolic.cache_product(o)).or_default().push(i);}
        symbolic.step(o);
    }
    if false {
        // Raw control writes are only a conservative fence. If immutable
        // symbolic support proves that the two controls have restored the
        // same product at cleanup, the measurement-phase correction is exact.
        let mut checks:HashMap<usize,Vec<(usize,(bool,Vec<u64>))>>=HashMap::new();
        for (key,uses) in &groups {if uses.len()>1 {for &i in uses {if !end_ok[i] {checks.entry(ends[i]).or_default().push((i,key.clone()));}}}}
        let mut proof=super::exact_wide_stage1_support::Support::new(&ops);let mut recovered=0;
        for i in 0..=ops.len() {
            if let Some(cs)=checks.get(&i){for (at,key) in cs {if proof.cache_product(&ops[*at])==*key {end_ok[*at]=true;recovered+=1;}}}
            if i<ops.len(){proof.step(&ops[i]);}
        }
        println!("LAZY_SEMANTIC_END recovered={recovered}");
    }
    let mut proposals=vec![];let mut repeated=0;let mut repetitions=0;
    for (_,mut uses) in groups {
        if uses.len()<2 {continue;}repeated+=1;repetitions+=uses.len()-1;
        // A long repeated-product group can span a busy lifetime even though
        // shorter contiguous pieces admit an existing clean wire. Enumerate
        // those pieces by stream structure alone; no sampled input is used.
        if split {
            for lo in 0..uses.len()-1 {for hi in lo+2..=uses.len().min(lo+64) {
                let us=uses[lo..hi].to_vec();
                if !end_ok[*us.last().unwrap()] {continue;}
                let weight_sum=us.iter().map(|i|weights[*i]).sum::<f64>();
                let union_proxy=1.0-us.iter().map(|i|1.0-weights[*i]).product::<f64>();
                proposals.push(Window{start:starts[us[0]],end:ends[*us.last().unwrap()],uses:us,proxy:weight_sum-union_proxy,donors:vec![]});
            }}
        } else {
            while uses.len()>1&&!end_ok[*uses.last().unwrap()] {uses.pop();}
            if uses.len()<2 {continue;}
            let weight_sum=uses.iter().map(|i|weights[*i]).sum::<f64>();
            let union_proxy=1.0-uses.iter().map(|i|1.0-weights[*i]).product::<f64>();
            proposals.push(Window{start:starts[uses[0]],end:ends[*uses.last().unwrap()],uses,proxy:weight_sum-union_proxy,donors:vec![]});
        }
    }
    proposals.sort_by(|a,b|(a.start,a.end,&a.uses).cmp(&(b.start,b.end,&b.uses)));
    let startset:HashSet<_>=proposals.iter().map(|w|w.start).collect();
    let mut nexttouch=vec![usize::MAX;nq];let mut snap=HashMap::new();
    for (i,o) in ops.iter().enumerate().rev(){for q in touches(o){nexttouch[q]=i;}if startset.contains(&i){snap.insert(i,nexttouch.clone());}}
    symbolic=super::exact_wide_stage1_support::Support::new(&ops);let mut wi=0;
    for (i,o) in ops.iter().enumerate(){
        while wi<proposals.len()&&proposals[wi].start==i {
            let w=&mut proposals[wi];
            w.donors=symbolic.cache_zeros().into_iter().filter(|q|snap[&i][*q]>=w.end).collect();wi+=1;
        }
        symbolic.step(o);
    }
    assert_eq!(wi,proposals.len());
    let eligible=proposals.iter().filter(|w|!w.donors.is_empty()).count();
    let available_proxy: f64=proposals.iter().filter(|w|!w.donors.is_empty()).map(|w|w.proxy).sum();
    let rank="density".to_string();
    if rank=="proxy" {proposals.sort_by(|a,b|b.proxy.total_cmp(&a.proxy).then((a.start,a.end,&a.uses).cmp(&(b.start,b.end,&b.uses))));}
    if rank=="density" {proposals.sort_by(|a,b|(b.proxy/(b.end-b.start) as f64).total_cmp(&(a.proxy/(a.end-a.start) as f64)).then((a.start,a.end,&a.uses).cmp(&(b.start,b.end,&b.uses))));}
    let mut occupied=vec![Vec::<(usize,usize)>::new();nq];let mut selected=0;let mut proxy=0.0;let mut used=HashSet::new();let mut structural=0;let mut chosen=vec![];
    for w in proposals {
        if w.uses.iter().any(|i|used.contains(i)){continue;}
        if let Some(&donor)=w.donors.iter().find(|q|occupied[**q].iter().all(|&(s,e)|e<=w.start||s>=w.end)){
            occupied[donor].push((w.start,w.end));selected+=1;proxy+=w.proxy;structural+=w.uses.len()-1;used.extend(w.uses.iter().copied());
            println!("LAZY_WINDOW donor={donor} start={} end={} proxy={} uses={:?}",w.start,w.end,w.proxy,w.uses);
            chosen.push((donor,w));
        }
    }
    println!("LAZY_SUMMARY width={nq} repeated_groups={repeated} raw_repetitions={repetitions} eligible={eligible} selected={selected} available_proxy={available_proxy} selected_proxy={proxy} structural_repetitions={structural}");
    render(ops,chosen,nb,nq)
}

fn gate(k:K,a:Option<u64>,b:Option<u64>,t:Option<u64>,bt:Option<u64>,c:Option<u64>)->Op {
    let mut o=Op::empty();o.kind=k;
    o.q_control1=QubitId(a.unwrap_or(u64::MAX));o.q_control2=QubitId(b.unwrap_or(u64::MAX));o.q_target=QubitId(t.unwrap_or(u64::MAX));
    o.c_target=BitId(bt.unwrap_or(u64::MAX));o.c_condition=BitId(c.unwrap_or(u64::MAX));o.validate();o
}
fn store(bit:u64,value:bool)->Op {gate(if value{K::BitStore1}else{K::BitStore0},None,None,None,Some(bit),None)}
fn push(bit:u64)->Op {gate(K::PushCondition,None,None,None,None,Some(bit))}
fn pop()->Op {gate(K::PopCondition,None,None,None,None,None)}

fn render(ops:Vec<Op>,chosen:Vec<(usize,Window)>,nb:u64,nq:usize)->Vec<Op>{
    let mut starts:HashMap<usize,Vec<usize>>=HashMap::new();let mut ends:HashMap<usize,Vec<usize>>=HashMap::new();let mut uses=HashMap::new();
    for (j,(_,w)) in chosen.iter().enumerate(){
        starts.entry(w.start).or_default().push(j);ends.entry(w.end).or_default().push(j);
        for &i in &w.uses {assert!(uses.insert(i,j).is_none());}
    }
    let mut active=vec![None;nq];let mut out=Vec::with_capacity(ops.len()+chosen.len()*25);let mut dropped_resets=0;
    for i in 0..=ops.len(){
        // End before start: adjacent leases may reuse the same physical wire.
        if let Some(js)=ends.get(&i){for &j in js {
            let (q,w)=&chosen[j];let valid=nb+3*j as u64;let temp=valid+1;let m=valid+2;
            let last=ops[*w.uses.last().unwrap()];
            out.push(push(valid));out.push(gate(K::Hmr,None,None,Some(*q as u64),Some(m),None));
            out.push(gate(K::CZ,Some(last.q_control1.0),None,Some(last.q_control2.0),None,Some(m)));out.push(pop());
            out.extend([store(valid,false),store(temp,false),store(m,false)]);
            assert_eq!(active[*q],Some(j));active[*q]=None;
        }}
        if let Some(js)=starts.get(&i){for &j in js {
            let (q,_)=&chosen[j];assert!(active[*q].is_none());active[*q]=Some(j);
            for b in nb+3*j as u64..nb+3*j as u64+3 {out.push(store(b,false));}
        }}
        if i==ops.len(){break;}let o=ops[i];
        if let Some(&j)=uses.get(&i){
            let q=chosen[j].0 as u64;let valid=nb+3*j as u64;let temp=valid+1;
            if o.c_condition!=NO_BIT {out.push(push(o.c_condition.0));}
            out.push(store(temp,true));out.push(gate(K::BitInvert,None,None,None,Some(temp),Some(valid)));
            out.push(push(temp));out.push(gate(K::CCX,Some(o.q_control1.0),Some(o.q_control2.0),Some(q),None,None));
            out.push(store(valid,true));out.push(pop());
            out.push(gate(K::CX,Some(q),None,Some(o.q_target.0),None,None));out.push(store(temp,false));
            if o.c_condition!=NO_BIT {out.push(pop());}
        }else if o.kind==K::R&&active[o.q_target.0 as usize].is_some(){
            // This wire was proved zero and otherwise untouched in the original
            // stream throughout the lease. Its original reset had no effect.
            dropped_resets+=1;
        }else{out.push(o);}
    }
    assert!(active.iter().all(|x|x.is_none()));
    println!("LAZY_RENDER windows={} dropped_original_zero_resets={dropped_resets} old_ops={} new_ops={}",chosen.len(),ops.len(),out.len());out
}

pub fn audit(ops:&[Op]) {let _=optimize(ops.to_vec());}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::RegisterId;
    use quantum_ecc::sim::Simulator;
    #[test]
    fn split_lease_reuses_clean_wire_around_busy_lifetime(){
        let mut p=program()[..10].to_vec();
        p.extend([
            gate(K::CCX,Some(0),Some(1),Some(4),None,None),
            gate(K::CCX,Some(0),Some(1),Some(4),None,None),
            gate(K::X,None,None,Some(5),None,None),
            gate(K::X,None,None,Some(5),None,None),
            gate(K::CCX,Some(0),Some(1),Some(4),None,None),
            gate(K::CCX,Some(0),Some(1),Some(4),None,None),
        ]);
        let q=optimize_impl(p.clone(),true);
        assert_eq!(q.iter().filter(|o|o.kind==K::Hmr).count(),2);
        assert_eq!(optimize_impl(p.clone(),false),p);
        for word in [0,u64::MAX,0xa5a5a5a5a5a5a5a5] {for batch in 0..8 {
            let (aq,bq,ab,bb,ap,bp,ac,bc)=run_case(&p,&q,batch,word);
            assert_eq!(aq,bq);assert_eq!(&ab[..4],&bb[..4]);assert_eq!(ap,bp);
            assert_eq!(ac-bc,128);
            assert!(bb[4..10].iter().all(|b|*b==0));
        }}
    }
    struct Word(u64);
    impl sha3::digest::XofReader for Word {fn read(&mut self,out:&mut [u8]){assert_eq!(out.len(),8);out.copy_from_slice(&self.0.to_le_bytes());}}
    fn program()->Vec<Op>{
        let mut p=vec![];let mut r=Op::empty();r.kind=K::Register;r.r_target=RegisterId(0);p.push(r);
        for q in 0..5 {let mut o=Op::empty();o.kind=K::AppendToRegister;o.r_target=RegisterId(0);o.q_target=QubitId(q);p.push(o);}
        for b in 0..4 {let mut o=Op::empty();o.kind=K::AppendToRegister;o.r_target=RegisterId(0);o.c_target=BitId(b);p.push(o);}
        p.extend([
            push(0),gate(K::BitInvert,None,None,None,Some(0),None),
            gate(K::CCX,Some(0),Some(1),Some(4),None,Some(1)),pop(),
            gate(K::CCX,Some(2),Some(3),Some(4),None,Some(2)),
            gate(K::R,None,None,Some(5),None,None),
            gate(K::X,None,None,Some(0),None,None),gate(K::CZ,Some(3),None,Some(4),None,None),
            gate(K::X,None,None,Some(0),None,None),
            push(3),gate(K::CCX,Some(0),Some(1),Some(2),None,Some(1)),pop(),
            gate(K::CCX,Some(0),Some(1),Some(4),None,None),
            gate(K::R,None,None,Some(7),None,None),
        ]);
        p
    }
    fn run_case(p:&[Op],q:&[Op],batch:usize,word:u64)->(Vec<u64>,Vec<u64>,Vec<u64>,Vec<u64>,u64,u64,u64,u64){
        let mut xa=Word(word);let mut xb=Word(word);
        let mut a=Simulator::new(8,64,&mut xa);let mut b=Simulator::new(8,64,&mut xb);
        for bit in 0..9 {let v=(0..64).fold(0u64,|v,l|v|((((batch*64+l)>>bit)&1) as u64)<<l);if bit<5 {a.qubits[bit]=v;}else{a.bits[bit-5]=v;}}
        for bit in 4..64{a.bits[bit]=0xa5a5a5a5a5a5a5a5;}
        a.phase=0x55aa55aa55aa55aa;b.qubits=a.qubits.clone();b.bits=a.bits.clone();b.phase=a.phase;
        a.apply_iter(p.iter());b.apply_iter(q.iter());
        (a.qubits,b.qubits,a.bits,b.bits,a.phase,b.phase,a.stats.toffoli_gates,b.stats.toffoli_gates)
    }
    #[test]
    fn lazy_cache_native_dirty_abi_guards_and_phase(){
        let p=program();let q=optimize(p.clone());assert!(q.len()>p.len());let mut saved=0;
        for word in [0,u64::MAX,0xa5a5a5a5a5a5a5a5,0x5a5a5a5a5a5a5a5,0x5555aaaaffff0000,0x0123456789abcdef] {
            for batch in 0..8 {
                let (aq,bq,ab,bb,ap,bp,ac,bc)=run_case(&p,&q,batch,word);
                assert_eq!(aq,bq);assert_eq!(&ab[..4],&bb[..4]);assert_eq!(ap,bp);assert!(bc<=ac);saved+=ac-bc;
                // Exactly the three fresh flags for the one selected lease are clean.
                for bit in 4..7 {assert_eq!(bb[bit],0);}
                assert_eq!(&ab[7..],&bb[7..]);
            }
        }
        assert!(saved>0);println!("LAZY_NATIVE cases=3072 saved={saved}");
    }
    #[test]
    fn lazy_cache_phase_fault_is_detected(){
        let p=program();let mut q=optimize(p.clone());let at=q.iter().position(|o|o.kind==K::CZ&&o.c_condition.0>=4&&o.c_condition!=NO_BIT).unwrap();q.remove(at);
        let mut detected=false;for batch in 0..8 {let (_,_,_,_,a,b,_,_)=run_case(&p,&q,batch,u64::MAX);detected|=a!=b;}assert!(detected);
    }
    #[test]
    fn lazy_cache_overlapping_leases_all_outcome_patterns(){
        let mut p=program()[..10].to_vec();
        p.extend([
            gate(K::CCX,Some(0),Some(1),Some(4),None,Some(0)),
            gate(K::CCX,Some(2),Some(3),Some(4),None,Some(1)),
            gate(K::R,None,None,Some(5),None,None),
            gate(K::CCX,Some(0),Some(1),Some(4),None,Some(2)),
            gate(K::CCX,Some(2),Some(3),Some(4),None,Some(3)),
            gate(K::R,None,None,Some(7),None,None),
        ]);
        let q=optimize(p.clone());assert_eq!(q,optimize(p.clone()));
        let mr=q.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).count();assert_eq!(mr,3);
        struct Events{pattern:usize,at:usize}
        impl sha3::digest::XofReader for Events{fn read(&mut self,out:&mut[u8]){assert_eq!(out.len(),8);let word=if self.pattern>>self.at&1==0{0u64}else{u64::MAX};self.at+=1;out.copy_from_slice(&word.to_le_bytes());}}
        for pattern in 0..1<<mr {for batch in 0..8 {
            let mut xa=Word(0);let mut xb=Events{pattern,at:0};
            let mut a=Simulator::new(8,64,&mut xa);let mut b=Simulator::new(8,64,&mut xb);
            for bit in 0..9{let v=(0..64).fold(0u64,|v,l|v|((((batch*64+l)>>bit)&1)as u64)<<l);if bit<5{a.qubits[bit]=v;}else{a.bits[bit-5]=v;}}
            for bit in 4..64{a.bits[bit]=0xa5a5a5a5a5a5a5a5;}
            a.phase=0x55aa55aa55aa55aa;b.qubits=a.qubits.clone();b.bits=a.bits.clone();b.phase=a.phase;
            a.apply_iter(p.iter());b.apply_iter(q.iter());
            assert_eq!(a.qubits,b.qubits);assert_eq!(&a.bits[..4],&b.bits[..4]);assert_eq!(a.phase,b.phase);assert!(b.stats.toffoli_gates<=a.stats.toffoli_gates);
            for bit in 4..10{assert_eq!(b.bits[bit],0);}assert_eq!(&a.bits[10..],&b.bits[10..]);
        }}
        println!("LAZY_OVERLAP_NATIVE cases=4096 independent_event_patterns=8 deterministic=true");
    }
}
