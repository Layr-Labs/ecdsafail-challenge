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
    if super::q793_table_harvest::enabled(){
        let observed=truth.clone();
        let out=swap_terms_selected(truth,width);
        super::q793_table_harvest::record(&observed,width,out.0,&out.1);
        return out;
    }
    swap_terms_selected(truth,width)
}
fn swap_terms_selected(truth:Vec<bool>,width:usize)->(usize,Vec<usize>){
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
/// Rank-echo chart emission (skip_zero/step/sign/timefix compute closures):
/// monomials on the rank wires only (E=0), target d, no skeleton. The framed
/// arm brackets the chart with the G frame and its reverse.
pub(super) fn emit_chart_compute(circ:&mut Circuit,rank:&[&QReg],plan:&SwapPlan,d:&QReg,rest:&[QReg]){
    let (frame,polarity,terms):(Vec<(usize,usize)>,usize,&Vec<usize>)=match plan{SwapPlan::Anf(p,t)=>(Vec::new(),*p,t),SwapPlan::Framed(f,p,t)=>(f.clone(),*p,t)};
    for &(c,t)in &frame{circ.cx(rank[c],rank[t]);}
    for i in 0..rank.len(){if polarity>>i&1!=0{circ.x(rank[i]);}}
    for &m in terms{let cs:Vec<(&QReg,bool)>=(0..rank.len()).filter(|&i|m>>i&1!=0).map(|i|(rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}
    for i in (0..rank.len()).rev(){if polarity>>i&1!=0{circ.x(rank[i]);}}
    for &(c,t)in frame.iter().rev(){circ.cx(rank[c],rank[t]);}
}
impl SwapPlan{
    /// Toffoli count of the rank chart alone (frame CXs are free), E=0.
    pub(super) fn chart_t(&self)->usize{match self{SwapPlan::Anf(_,ts)|SwapPlan::Framed(_,_,ts)=>ts.iter().map(|&m|nccx(m.count_ones()as usize)).sum()}}
}
pub(super) fn truth_swap(circ:&mut Circuit,controls:&[&QReg],truth:Vec<bool>,left:&QReg,right:&QReg,helpers:&[QReg]) {
    let plan=swap_plan(truth,controls.len(),1,McxModel::Dirty);
    emit_plan(circ,controls,plan,left,right,|circ|{circ.cx(right,left);},|circ|{circ.cx(right,left);},|circ,cs,right|{mixed_mcx(circ,&cs,right,helpers);});
}
/// W5 synthesis plan: the muxlease-A1 polarity winner, or a baked affine
/// frame winner (G basis-change CX network + polarity + reduced ANF) from
/// research/w5 scorer output. `Framed` emits f(x)=ANF(G*x^p) as
/// [frame CXs][X(p)][skeleton][X(p)][reverse frame]; the elimination network
/// implements G^-1, so its reverse implements G at identical length (the
/// scorer's cx_len convention, bank_common::w5_cx_len).
pub(super) enum SwapPlan{Anf(usize,Vec<usize>),Framed(Vec<(usize,usize)>,usize,Vec<usize>)}
fn nccx(k:usize)->usize{match k{0|1=>0,2=>1,_=>4*k-8}}
/// Site-exact monomial cost: dirty ladder (mixed_mcx) vs clean-scratch
/// paired MCX (paired_clean_mcx::toggle, 2n-3 T for n>=2). Ops replicate the
/// toggle's deterministic wire choices (ccx + scratch X pairs).
#[derive(Clone,Copy)]pub(super) enum McxModel{Dirty,Clean}
fn mono(model:McxModel,n:usize)->(usize,usize){
    match model{
        McxModel::Dirty=>{let t=nccx(n);(t,t.max(1))}
        McxModel::Clean=>match n{0|1=>(0,1),2=>(1,1),_=>{
            let mut marked=vec![false;n+1];marked[0]=true;let mut xs=0usize;
            loop{
                let mut choice=None;
                for t in (0..n+1).rev(){if !marked[t]{continue;}let un:Vec<_>=(t+1..n+1).filter(|&i|!marked[i]).take(2).collect();if un.len()==2{choice=Some((un[0],un[1],t));break;}}
                let Some((x,y,t))=choice else{break};
                if t!=0{xs+=2;}marked[t]=false;marked[x]=true;marked[y]=true;
            }
            (2*n-3,2*n-3+xs)
        }}
    }
}
pub(super) fn swap_plan(truth:Vec<bool>,width:usize,ext:usize,model:McxModel)->SwapPlan{
    let (polarity,terms)=swap_terms(truth.clone(),width);
    if std::env::var("Q793_TABLE_AFFINE").ok().as_deref()==Some("0"){return SwapPlan::Anf(polarity,terms);}
    let mask=truth.iter().enumerate().fold(0u64,|a,(i,&b)|a|if b{1u64<<i}else{0});
    let e=match super::q793_table_affine::lookup(width,mask){Some(e)=>e,None=>return SwapPlan::Anf(polarity,terms)};
    let mut a=e.g_rows;let mut elim:Vec<(usize,usize)>=Vec::new();
    for c in 0..width{
        let piv=(c..width).find(|&r|a[r]>>c&1!=0).expect("baked G invertible");
        if piv!=c{a.swap(c,piv);elim.push((c,piv));elim.push((piv,c));elim.push((c,piv));}
        for r in 0..width{if r!=c&&a[r]>>c&1!=0{a[r]^=a[c];elim.push((c,r));}}
    }
    let frame:Vec<(usize,usize)>=elim.iter().rev().cloned().collect();
    let p=e.polarity as usize;
    let new_terms:Vec<usize>=(0..64).filter(|&m|e.terms>>m&1!=0).collect();
    // Exhaustively re-verify the baked table on EVERY input, and that the
    // frame network composed with its reverse is the identity (phase/inverse).
    for (x,&wanted)in truth.iter().enumerate(){
        let mut y=0usize;for i in 0..width{let bit=((e.g_rows[i]as usize)&x).count_ones()as usize&1;y|=bit<<i;}
        let y=y^p;let got=new_terms.iter().fold(false,|v,&m|v^((y&m)==m));
        assert_eq!(got,wanted,"affine frame synthesis changed truth table");
    }
    for x in 0..1usize<<width{
        let mut v=x;for &(c,t)in &frame{if v>>c&1!=0{v^=1<<t;}}
        let mut y=0usize;for i in 0..width{let bit=((e.g_rows[i]as usize)&x).count_ones()as usize&1;y|=bit<<i;}
        assert_eq!(v,y,"affine frame network does not implement G");
        for &(c,t)in frame.iter().rev(){if v>>c&1!=0{v^=1<<t;}}
        assert_eq!(v,x,"affine frame network is not an involution pair");
    }
    let cost=|ts:&[usize],pol:usize,frame_len:usize|->(usize,usize){
        let mut t=0usize;let mut ops=2usize+2*pol.count_ones()as usize+2*frame_len;
        for &m in ts{let (mt,mo)=mono(model,m.count_ones()as usize+ext);t+=mt;ops+=mo;}
        (t,ops)
    };
    let (old_t,old_ops)=cost(&terms,polarity,0);
    let (new_t,new_ops)=cost(&new_terms,p,frame.len());
    // Accept only a strictly smaller T actual with ops not up (site-exact,
    // re-measured here; the analytic scorer verdict is only a proposal).
    if new_t<old_t&&new_ops<=old_ops{SwapPlan::Framed(frame,p,new_terms)}else{SwapPlan::Anf(polarity,terms)}
}
/// Emission shared by truth_swap and every same-shaped site: X-wrap, skeleton
/// pre/post pair, one monomial MCX per term under the site's external
/// control. The Anf arm reproduces each site's original op order exactly.
pub(super) fn emit_plan(circ:&mut Circuit,controls:&[&QReg],plan:SwapPlan,left:&QReg,right:&QReg,skel_pre:impl Fn(&mut Circuit),skel_post:impl Fn(&mut Circuit),mut toggle:impl FnMut(&mut Circuit,Vec<(&QReg,bool)>,&QReg)){
    let (frame,polarity,terms)=match plan{SwapPlan::Anf(p,t)=>(Vec::new(),p,t),SwapPlan::Framed(f,p,t)=>(f,p,t)};
    for &(c,t)in &frame{circ.cx(controls[c],controls[t]);}
    for (i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    skel_pre(circ);
    for m in &terms{let mut cs=vec![(left,true)];cs.extend((0..controls.len()).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));toggle(circ,cs,right);}
    skel_post(circ);
    for (i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
    for &(c,t)in frame.iter().rev(){circ.cx(controls[c],controls[t]);}
}
/// Quotient address on the caller's existing active domain: A+C<=255 for
/// insertion, A+C<=256 for removal. Off guard, arbitrary addresses are safe.
pub(super) fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guards:&[(&QReg,bool)],passenger:&QReg,word:&[QReg],helpers:&[QReg],insert:bool) {
    quotient_sequence(circ,rank,a,c,guards,&[passenger],word,helpers,insert);
}
/// Consecutive exchanges at the same unchanged quotient address share one
/// gather. Every passenger is excluded from the dirty lender set throughout.
pub(super) fn quotient_sequence(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guards:&[(&QReg,bool)],passengers:&[&QReg],word:&[QReg],helpers:&[QReg],insert:bool) {
    assert!(passengers.iter().all(|p|!helpers.iter().any(|q|q.id()==p.id())));
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
    for &passenger in passengers{circ.cx(passenger,word[0]);let mut cs=guards.to_vec();cs.push((word[0],true));mixed_mcx(circ,&cs,passenger,helpers);circ.cx(passenger,word[0]);}
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
    }else if axis==0&&circ.q797_a_support.is_some(){
        // A-addressed exchange inside a scheduled step: the block's analytic A support
        // (metadata_entry_head5::A_SUPPORTS, as used by gather_a) makes leaves outside [lo,hi)
        // unreachable; the terminal A255 leaf is retained exactly as gather_a retains it.
        let (lo,hi)=circ.q797_a_support.unwrap();
        let mut nodes:Vec<_>=word.iter().enumerate().map(|(i,&q)|if (lo..hi).contains(&i)||i==255{Some(q)}else{None}).collect();
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
        if !skip_zero_factored(circ,rank,low,axis,guard,root,passenger,helpers) {
            for (r,t) in triples().iter().enumerate() {if t[axis]==0 {
                let mut cs=vec![(root,true)];if let Some(g)=guard{cs.push((g,true));}
                cs.extend(low.iter().map(|q|(q,false)));cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));
                mixed_mcx(circ,&cs,passenger,helpers);
            }}
        }
        circ.cx(passenger,root);
    }
    circ.b.ops.extend(gather.into_iter().rev());
}

/// The zero-address undo is `H(rank) * B` with `B = root * guard * !low`, so the
/// direct form pays the same 7-or-8-control conjunction once per admissible rank
/// codeword (13 of them for a typical axis). Factor it with the tree's exact
/// dirty echo -- the same identity `q794_r01_factor` uses: with arbitrary
/// borrowed `d`, `D_B H_d D_B^-1 H_d` toggles `H*B` and restores `d`. `H` is a
/// function of the 5 rank bits alone, so its ANF cubes cost only their popcount,
/// and the polarity comes from the `swap_terms` already in this module.
///
/// Declines whenever the direct form is at least as cheap, under the same
/// `4n-8` dirty-ladder model, so it cannot regress.
fn skip_zero_factored(circ:&mut Circuit,rank:&[QReg],low:&[QReg],axis:usize,guard:Option<&QReg>,root:&QReg,passenger:&QReg,helpers:&[QReg])->bool{
    if !active("Q794_MUXLEASE_ZERO_FACTOR")||helpers.len()<2{return false;}
    fn cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
    let shared=1+usize::from(guard.is_some())+low.len();
    let truth:Vec<bool>=triples().iter().map(|t|t[axis]==0).collect();
    let plan=swap_plan(truth,5,0,McxModel::Dirty);
    let direct:usize=triples().iter().filter(|t|t[axis]==0).map(|_|cost(shared+5)).sum();
    let chart=plan.chart_t();
    let echo=2*chart+2*cost(shared+1);
    if direct<=echo{return false;}
    // `d` must be excluded from the lender slice the inner products borrow.
    let d=&helpers[0];let rest=&helpers[1..];
    let rank_ref:Vec<&QReg>=rank.iter().collect();
    let compute=|circ:&mut Circuit|emit_chart_compute(circ,&rank_ref,&plan,d,rest);
    let consume=|circ:&mut Circuit|{
        let mut cs=vec![(root,true),(d,true)];if let Some(g)=guard{cs.push((g,true));}
        cs.extend(low.iter().map(|q|(q,false)));
        mixed_mcx(circ,&cs,passenger,rest);
    };
    consume(circ);compute(circ);consume(circ);compute(circ);
    true
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
