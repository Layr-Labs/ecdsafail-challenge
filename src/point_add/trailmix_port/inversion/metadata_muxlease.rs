//! Exact indexed exchange by a reversible binary selection tree. No allocation.
//! All word bits are arbitrary; gather/root exchange/ungather restores every
//! unselected bit. High address bits are Boolean functions of the rank5 code.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
pub(super) fn active(name:&str)->bool{std::env::var(name).ok().as_deref()==Some("1")}
/// Gather over an already-proved subset of addresses. Empty decision branches
/// require only compile-time rewiring; k reachable addresses use k-1 CSWAPs.
pub(super) fn gather_linear<'a>(circ:&mut Circuit,address:&[&QReg],candidates:&[(usize,&'a QReg)]) -> (&'a QReg,Vec<crate::circuit::Op>) {
    let start=circ.b.ops.len();let mut nodes=vec![None;1<<address.len()];for &(i,q)in candidates{assert!(nodes[i].is_none());nodes[i]=Some(q);}
    for control in address {let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(a),Some(b))=>{circ.cswap(control,a,b);Some(a)},(Some(a),None)|(None,Some(a))=>Some(a),(None,None)=>None});}nodes=next;}
    (nodes[0].expect("nonempty candidate support"),circ.b.ops[start..].to_vec())
}
fn triples()->Vec<[usize;3]> {(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
pub(super) fn predicate_swap(circ:&mut Circuit,rank:&[QReg],axis:usize,bit:usize,left:&QReg,right:&QReg,helpers:&[QReg]) {
    let anf:Vec<_>=triples().iter().map(|t|(t[axis]>>bit)&1!=0).collect();
    truth_swap(circ,&rank.iter().collect::<Vec<_>>(),anf,left,right,helpers);
}
// Choose a fixed input polarity for the exact Boolean truth table. This is
// an emission-time search, not quantum computation or sampled specialization.
pub(super) fn swap_terms(truth:Vec<bool>,width:usize)->(usize,Vec<usize>){
    use std::collections::HashMap;use std::sync::{Mutex,OnceLock};
    fn terms(truth:&[bool],width:usize,polarity:usize)->Vec<usize>{
        let mut a:Vec<_>=(0..truth.len()).map(|i|truth[i^polarity]).collect();
        for bit in 0..width{for m in 0..a.len(){if m>>bit&1!=0{a[m]^=a[m^(1<<bit)];}}}
        a.into_iter().enumerate().filter_map(|(m,v)|v.then_some(m)).collect()
    }
    fn cost(ts:&[usize],polarity:usize)->(usize,usize){
        let mut t=0;let mut gates=2*polarity.count_ones()as usize;
        for &m in ts{let k=m.count_ones()as usize+1;let n=match k{1=>0,2=>1,_=>4*k-8};t+=n;gates+=n.max(1);}(t,gates)
    }
    assert_eq!(truth.len(),1<<width);
    if std::env::var("Q796_MUX_POLARITY").ok().as_deref()==Some("0")||width>6{return(0,terms(&truth,width,0));}
    static CACHE:OnceLock<Mutex<HashMap<Vec<bool>,(usize,Vec<usize>)>>>=OnceLock::new();
    let mut cache=CACHE.get_or_init(||Mutex::new(HashMap::new())).lock().unwrap();
    if let Some(found)=cache.get(&truth){return found.clone();}
    let mut best=(0,terms(&truth,width,0));let mut best_cost=cost(&best.1,0);
    for polarity in 1..truth.len(){let ts=terms(&truth,width,polarity);let c=cost(&ts,polarity);if c<best_cost{best=(polarity,ts);best_cost=c;}}
    // Exhaustively verify the selected function on EVERY address, including
    // codes outside the EEA reachable set. The complete swap is unchanged.
    for (x,&wanted)in truth.iter().enumerate(){let y=x^best.0;let got=best.1.iter().fold(false,|v,&m|v^((y&m)==m));assert_eq!(got,wanted,"polarity synthesis changed truth table");}
    cache.insert(truth,best.clone());best
}
pub(super) fn truth_swap(circ:&mut Circuit,controls:&[&QReg],truth:Vec<bool>,left:&QReg,right:&QReg,helpers:&[QReg]) {
    let(polarity,terms)=swap_terms(truth,controls.len());
    for (i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    circ.cx(right,left);
    for m in terms {let mut cs=vec![(left,true)];cs.extend((0..controls.len()).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));mixed_mcx(circ,&cs,right,helpers);}
    circ.cx(right,left);
    for (i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}
/// Quotient address on the caller's existing active domain: A+C<=255 for
/// insertion, A+C<=256 for removal. Off guard, arbitrary addresses are safe.
pub(super) fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guards:&[(&QReg,bool)],passenger:&QReg,word:&[QReg],helpers:&[QReg],insert:bool) {
    use super::metadata_arithmetic5_encoded::add;
    add(circ,a,c,None,false);
    let word:Vec<_>=(0..256).map(|s|&word[if insert{s+2}else if s==0{257}else{s+1}]).collect();
    let start=circ.b.ops.len();let d=&helpers[0];let dirty=&helpers[1..];
    for level in 0..8 {let stride=1<<level;for base in (0..256).step_by(2*stride) {
        if level<6 {circ.cswap(&c[level],word[base],word[base+stride]);}else{
            let bit=level-6;let ts=triples();let ctrls:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
            let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
            // F(d xor carry) xor F(d) xor F(0) = F(carry), since F is
            // Boolean in one carry bit. These swaps share their same pair.
            add(circ,a,c,None,true);add(circ,a,c,Some(d),false);
            truth_swap(circ,&ctrls,truth.clone(),word[base],word[base+stride],dirty);
            add(circ,a,c,None,true);add(circ,a,c,Some(d),false);
            truth_swap(circ,&ctrls,truth,word[base],word[base+stride],dirty);
            let zero:Vec<_>=ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect();
            truth_swap(circ,&rank.iter().collect::<Vec<_>>(),zero,word[base],word[base+stride],dirty);
        }
    }}
    let gather=circ.b.ops[start..].to_vec();
    circ.cx(passenger,word[0]);let mut cs=guards.to_vec();cs.push((word[0],true));mixed_mcx(circ,&cs,passenger,helpers);circ.cx(passenger,word[0]);
    circ.b.ops.extend(gather.into_iter().rev());add(circ,a,c,None,true);
}
pub(super) fn exchange(circ:&mut Circuit,rank:&[QReg],low:&[QReg],axis:usize,guard:Option<&QReg>,passenger:&QReg,word:&[&QReg],helpers:&[QReg],skip_zero:bool) {
    assert_eq!(word.len(),256);assert_eq!(low.len(),6);assert!(axis<3);
    let start=circ.b.ops.len();
    let root=if super::q796_parity::enabled()&&skip_zero{
        // The zero address is never exchanged. It need not be physically
        // present, including when it denotes the omitted remainder bit.
        let mut nodes:Vec<_>=word.iter().enumerate().map(|(i,&q)|if i==0{None}else{Some(q)}).collect();
        for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
            (Some(left),Some(right))=>{if level<6{circ.cswap(&low[level],left,right);}else{predicate_swap(circ,rank,axis,level-6,left,right,helpers);}Some(left)},
            (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
        });}nodes=next;}nodes[0].unwrap()
    }else{for level in 0..8 {let stride=1<<level;for base in (0..256).step_by(2*stride) {
        if level<6 {circ.cswap(&low[level],word[base],word[base+stride]);}
        else {predicate_swap(circ,rank,axis,level-6,word[base],word[base+stride],helpers);}
    }}word[0]};
    let gather=circ.b.ops[start..].to_vec();
    if let Some(g)=guard {circ.cswap(g,root,passenger);}else{circ.cx(root,passenger);circ.cx(passenger,root);circ.cx(root,passenger);}
    if skip_zero {
        // Undo the root exchange exactly when the complete address is zero.
        circ.cx(passenger,root);
        for (r,t) in triples().iter().enumerate() {if t[axis]==0 {
            let mut cs=vec![(root,true)];if let Some(g)=guard{cs.push((g,true));}
            cs.extend(low.iter().map(|q|(q,false)));cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));
            mixed_mcx(circ,&cs,passenger,helpers);
        }}
        circ.cx(passenger,root);
    }
    circ.b.ops.extend(gather.into_iter().rev());
}

/// Same exact gather/exchange/ungather with an arbitrary conjunction of guards.
pub(super) fn exchange_guards(circ:&mut Circuit,rank:&[QReg],low:&[QReg],axis:usize,guards:&[(&QReg,bool)],passenger:&QReg,word:&[&QReg],helpers:&[QReg]) {
    assert_eq!(word.len(),256);assert_eq!(low.len(),6);assert!(axis<3);
    let start=circ.b.ops.len();
    for level in 0..8 {let stride=1<<level;for base in (0..256).step_by(2*stride) {
        if level<6 {circ.cswap(&low[level],word[base],word[base+stride]);}
        else {predicate_swap(circ,rank,axis,level-6,word[base],word[base+stride],helpers);}
    }}
    let gather=circ.b.ops[start..].to_vec();
    circ.cx(passenger,word[0]);let mut cs=guards.to_vec();cs.push((word[0],true));
    mixed_mcx(circ,&cs,passenger,helpers);circ.cx(passenger,word[0]);
    circ.b.ops.extend(gather.into_iter().rev());
}
pub fn run(){
    use crate::{sim::Simulator,circuit::OperationType};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    for axis in 0..2 {for guarded in [false,true] {for skip in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let low=circ.alloc_qreg_bits("low",6);let guard=circ.alloc_qreg("guard");let p=circ.alloc_qreg("passenger");let word=circ.alloc_qreg_bits("word",256);let help=circ.alloc_qreg_bits("dirty",24);let n=circ.b.next_qubit;
        exchange(&mut circ,&rank,&low,axis,if guarded{Some(&guard)}else{None},&p,&word.iter().collect::<Vec<_>>(),&help,skip);assert_eq!(n,circ.b.next_qubit);
        let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        for batch in 0..128 {let mut seed=799u64^batch;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let k=batch as usize*64+lane;let r=k&31;let lo=k>>5&63;let g=k>>11&1!=0;let addr=64*triples()[r][axis]+lo;
                for w in [&mut before,&mut after] {for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}for i in 0..6{put(w,&low[i],lane,lo>>i&1!=0);}put(w,&guard,lane,g);}
                if (!guarded||g)&&(!skip||addr!=0){let pv=before[p.id()as usize]>>lane&1!=0;let wv=before[word[addr].id()as usize]>>lane&1!=0;put(&mut after,&p,lane,wv);put(&mut after,&word[addr],lane,pv);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"axis={axis} guarded={guarded} skip={skip} batch={batch}");sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);
        }
        eprintln!("MUX_LEASE_PASS axis={axis} guarded={guarded} skip={skip} cases=8192 ops={} T={}",b.ops.len(),b.ops.iter().filter(|o|o.kind==OperationType::CCX).count());
    }}}
    for insert in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let g=circ.alloc_qreg("guard");let p=circ.alloc_qreg("passenger");let word=circ.alloc_qreg_bits("word",259);let help=circ.alloc_qreg_bits("dirty",24);let n=circ.b.next_qubit;
        quotient(&mut circ,&rank,&a,&c,&[(&g,true)],&p,&word,&help,insert);assert_eq!(n,circ.b.next_qubit);let b=circ.into_builder();
        for batch in 0..4096 {let mut seed=7993u64^batch;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let k=batch as usize*64+lane;let r=k&31;let al=k>>5&63;let cl=k>>11&63;let sum=64*(triples()[r][0]+triples()[r][1])+al+cl;let on=k>>17&1!=0&&sum<=if insert{255}else{256};
                for w in [&mut before,&mut after]{for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}for i in 0..6{put(w,&a[i],lane,al>>i&1!=0);put(w,&c[i],lane,cl>>i&1!=0);}put(w,&g,lane,on);}
                if on{let addr=if insert{sum+2}else if sum==0{257}else{sum+1};let pv=before[p.id()as usize]>>lane&1!=0;let wv=before[word[addr].id()as usize]>>lane&1!=0;put(&mut after,&p,lane,wv);put(&mut after,&word[addr],lane,pv);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"quotient insert={insert} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);
        }
        eprintln!("MUX_QUOTIENT_PASS insert={insert} cases=262144 ops={} T={}",b.ops.len(),b.ops.iter().filter(|o|o.kind==OperationType::CCX).count());
    }
}
