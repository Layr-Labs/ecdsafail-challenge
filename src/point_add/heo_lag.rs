//! Exact predicates for a lagged orientation letter. Research prototype.
use super::*;

pub(crate) fn mcx(c: &mut Builder, controls: &[(QubitId, bool)], out: QubitId, dirty: &[QubitId]) {
    assert!(controls.iter().all(|&(q,_)|q!=out));
    for &(q,positive) in controls { if !positive { c.x(q); } }
    let n=controls.len();
    match n {
        0=>c.x(out),
        1=>c.cx(controls[0].0,out),
        2=>c.ccx(controls[0].0,controls[1].0,out),
        _=>{
            assert!(dirty.len()>=n-2);
            let d=&dirty[..n-2];
            assert!(d.iter().all(|q|*q!=out&&!controls.iter().any(|x|x.0==*q)));
            // Two conjugated ladders cancel every term containing a borrowed bit.
            c.ccx(controls[0].0,controls[1].0,d[0]);
            for i in 1..n-2 { c.ccx(controls[i+1].0,d[i-1],d[i]); }
            c.ccx(controls[n-1].0,d[n-3],out);
            for i in (1..n-2).rev() { c.ccx(controls[i+1].0,d[i-1],d[i]); }
            c.ccx(controls[0].0,controls[1].0,d[0]);
            for i in 1..n-2 { c.ccx(controls[i+1].0,d[i-1],d[i]); }
            c.ccx(controls[n-1].0,d[n-3],out);
            for i in (1..n-2).rev() { c.ccx(controls[i+1].0,d[i-1],d[i]); }
        }
    }
    for &(q,positive) in controls.iter().rev() { if !positive { c.x(q); } }
}

// Toggle [a < b] XOR ([a == b] AND each disjoint equality condition).
// Zero extension is virtual, all actual operand wires are restored, no clean scratch.
pub(crate) fn cmp(c:&mut Builder,a:&[QubitId],b:&[QubitId],out:QubitId,eq:&[Vec<(QubitId,bool)>],dirty:&[QubitId]) {
    if std::env::var_os("WALK_DENSE").is_some() && eq.len()==1 && eq[0].len()==1 && a.len().abs_diff(b.len())<=1 {let(q,positive)=eq[0][0];if !positive{c.x(q);}fast_cmp(c,a,b,q,out,dirty);if !positive{c.x(q);}return;} let n=a.len().max(b.len());
    for i in 0..a.len().min(b.len()) { c.cx(a[i],b[i]); }
    let diff:Vec<QubitId>=(0..n).map(|i|if i<b.len(){b[i]}else{a[i]}).collect();
    for i in 0..b.len() {
        let mut cs:Vec<(QubitId,bool)>=diff[i+1..].iter().map(|&q|(q,false)).collect();
        if i<a.len() { cs.push((a[i],false)); }
        cs.push((b[i],true));
        mcx(c,&cs,out,dirty);
    }
    for extra in eq {
        let mut cs:Vec<(QubitId,bool)>=diff.iter().map(|&q|(q,false)).collect();
        cs.extend(extra);
        mcx(c,&cs,out,dirty);
    }
    for i in (0..a.len().min(b.len())).rev() { c.cx(a[i],b[i]); }
}

/// Toggle out by [abs(R1) < abs(R2)] on parity-parked signed rails.
/// R2's omitted bit 0 is !R1[0]. The rails have opposite parity, hence unequal magnitudes.
/// Let a,b be their normalized upper bits, p=R1[0], sa,sb their signs.
/// The desired carry is that of ~a+b+cin, cin = (!p & !sa) XOR (p & sb).
/// Carry(cin)= [a<b] XOR ([a==b] & cin), allowing a zero-clean-wire construction.
pub(super) fn orientation(c:&mut Builder,r:&Rails,out:QubitId,dirty:&[QubitId]) {
    assert!(r.r1.len()>=2 && !r.r2.is_empty());
    let p=r.r1[0];
    let sa=*r.r1.last().unwrap();
    let sb=*r.r2.last().unwrap();
    let a=&r.r1[1..r.r1.len()-1];
    let b=&r.r2[..r.r2.len()-1];
    for &q in a { c.cx(sa,q); }
    for &q in b { c.cx(sb,q); }
    if std::env::var_os("WALK_DENSE").is_some() && a.len().abs_diff(b.len())<=1 {c.x(sa);fredkin(c,p,sa,sb);fast_cmp(c,a,b,sa,out,dirty);fredkin(c,p,sa,sb);c.x(sa);}else{cmp(c,a,b,out,&[vec![(p,false),(sa,false)],vec![(p,true),(sb,true)]],dirty);}
    for &q in b.iter().rev() { c.cx(sb,q); }
    for &q in a.iter().rev() { c.cx(sa,q); }
}

pub fn selftest() {
    use crate::sim::Simulator;
    use sha3::{Shake256,digest::{Update,ExtendableOutput}};
    let mut total=0usize;
    for wa in 2..=7usize { for wb in wa.saturating_sub(1).max(2)..=wa+1 {
        let mut c=Builder::new();
        let ra=c.alloc_qubits(wa); let rb=c.alloc_qubits(wb-1);
        let out=c.alloc_qubit(); let dirty=c.alloc_qubits(wa.max(wb)+4);
        let r=Rails{r1:ra.clone(),r2:rb.clone()};
        let start=c.op_count(); orientation(&mut c,&r,out,&dirty);
        let(nq,nb)=c.i13_dims();let ops=c.take_ops();let ops=&ops[start..];
        let mut h=Shake256::default();h.update(b"walk-orientation-exhaustive-v1");let mut rng=h.finalize_xof();
        let mut sim=Simulator::new(nq,nb,&mut rng);
        let mut cases=Vec::new();
        for a in -(1i64<<(wa-1))..(1i64<<(wa-1)) {for b in -(1i64<<(wb-1))..(1i64<<(wb-1)) {
            if (a^b)&1==1 {cases.push((a,b));}
        }}
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            for (lane,&(a,b)) in batch.iter().enumerate() {
                for(i,&q)in ra.iter().enumerate(){if(a>>i)&1!=0{*sim.qubit_mut(q)|=1u64<<lane;}}
                for(i,&q)in rb.iter().enumerate(){if(b>>(i+1))&1!=0{*sim.qubit_mut(q)|=1u64<<lane;}}
                if lane&1!=0{*sim.qubit_mut(out)|=1u64<<lane;}
                for(i,&q)in dirty.iter().enumerate(){if((lane*13+i*7+3)>>(i%5))&1!=0{*sim.qubit_mut(q)|=1u64<<lane;}}
            }
            let before:Vec<u64>=(0..nq).map(|q|sim.qubit(QubitId(q as u64))).collect();
            sim.apply_iter(ops.iter());
            let mut expected=before[out.0 as usize];
            for(lane,&(a,b))in batch.iter().enumerate(){if a.abs()<b.abs(){expected^=1u64<<lane;}}
            let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};
            assert_eq!(sim.qubit(out)&mask,expected&mask,"wa={wa} wb={wb}");
            for q in 0..nq {if q as u64!=out.0 {assert_eq!(sim.qubit(QubitId(q as u64))&mask,before[q]&mask,"operand/dirty changed");}}
            assert_eq!(sim.phase&mask,0); total+=batch.len();
        }
        eprintln!("LAG_CMP_TEST wa={wa} wb={wb} cases={} ccx={}",cases.len(),ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count());
    }}
    eprintln!("LAG_CMP_TEST PASS cases={total}");
}

const FIRST:usize=375;
pub(super) fn active(label:&str,t:usize)->bool {
    std::env::var_os("WALK_LAG").is_some() && ((label=="divfwd" && t>=FIRST) || (label=="mulrev" && t>=370))
}
fn pool(tape:&Tape,used:&[QubitId])->Vec<QubitId>{
    let mut out=Vec::new();
    for g in tape.groups.iter().flatten() {
        match g.state {
            GState::P3=>out.extend([g.a2,g.a1,g.a0,g.h3,g.l3]),
            GState::P5|GState::Chained=>out.extend([g.a2,g.a1,g.a0,g.h3,g.l3,g.b2,g.b1,g.b0]),
            _=>{}
        }
    }
    for ch in tape.chains.iter().flatten(){out.extend(&ch.state);}
    out.retain(|q|!used.contains(q));out.sort_by_key(|q|q.0);out.dedup();out
}
fn toggle(c:&mut Builder,w:&Walk,out:QubitId){
    let r=w.rails.as_ref().unwrap();
    let mut used=r.r1.clone();used.extend(&r.r2);used.push(out);
    let d=pool(&w.tape,&used);orientation(c,r,out,&d);
}
fn forget(c:&mut Builder,w:&mut Walk,t:usize){
    let (typ,s)=w.tape.raw[t].unwrap();assert_ne!(typ,crate::circuit::NO_QUBIT);
    toggle(c,w,typ);c.release_clean(typ);w.tape.raw[t]=Some((crate::circuit::NO_QUBIT,s));
}
pub(super) fn restore(c:&mut Builder,w:&mut Walk,t:usize)->QubitId{
    let (typ,s)=w.tape.raw[t].unwrap();assert_eq!(typ,crate::circuit::NO_QUBIT);
    let q=c.alloc_qubit();toggle(c,w,q);w.tape.raw[t]=Some((q,s));q
}
pub(super) fn begin_fwd(c:&mut Builder,w:&mut Walk,t:usize){
    if t==FIRST && w.tape.raw[t-1].unwrap().0!=crate::circuit::NO_QUBIT {forget(c,w,t-1);}
    assert_eq!(w.tape.raw[t-1].unwrap().0,crate::circuit::NO_QUBIT);
}
pub(super) fn finish_fwd(c:&mut Builder,w:&mut Walk,t:usize,parity:QubitId,s:QubitId,last:usize)->QubitId{
    if parity==crate::circuit::NO_QUBIT{assert!(w.tape.raw[t-1].is_none());w.tape.raw[t]=Some((crate::circuit::NO_QUBIT,s));return crate::circuit::NO_QUBIT;} toggle(c,w,parity); // c_t XOR typ_t = typ_(t-1), no new type wire.
    let (_,sp)=w.tape.raw[t-1].unwrap();w.tape.raw[t-1]=Some((parity,sp));
    w.tape.raw[t]=Some((crate::circuit::NO_QUBIT,s));
    let _=last; crate::circuit::NO_QUBIT
}
pub(super) fn begin_rev(c:&mut Builder,w:&mut Walk,t:usize,last:usize){
    if t==last {forget(c,w,t);}
}
pub(super) fn reverse_parity(c:&mut Builder,w:&mut Walk,t:usize)->QubitId{
    let (tp,sp)=w.tape.raw[t-1].unwrap();assert_ne!(tp,crate::circuit::NO_QUBIT);
    toggle(c,w,tp);w.tape.raw[t-1]=Some((crate::circuit::NO_QUBIT,sp));tp
}
pub(super) fn finish_rev(c:&mut Builder,w:&mut Walk,t:usize){
    if t==370 {restore(c,w,t-1);}
}

pub(super) fn end_pack(c:&mut Builder,w:&mut Walk,t:usize,last:usize) {
    if t==last && active("divfwd",t) {restore(c,w,t);}
}
// After reversing the add, hs is the normalized magnitude of the halved even
// operand H, p1 its sign, x2 the normalized odd operand O. Thus typ_t is
// [hs < x2/2] XOR ([hs == x2/2] AND !p1), including both signs of H and O.
pub(super) fn late_parity(c:&mut Builder,tape:&mut Tape,u:usize,hs:&[QubitId],p1:QubitId,x2:&[QubitId])->QubitId {
    tape.ensure_raw(c,u);
    let (tp,sp)=tape.raw[u].unwrap();
    assert_ne!(tp,crate::circuit::NO_QUBIT);
    let mut used=hs.to_vec();used.extend(x2);used.extend([p1,tp]);
    let dirty=pool(tape,&used);
    cmp(c,hs,&x2[1..],tp,&[vec![(p1,false)]],&dirty);
    tape.raw[u]=Some((crate::circuit::NO_QUBIT,sp));tp
}

// Complete and encode the preceding letter before allocating the new sign.
pub(super) fn prepack(c:&mut Builder,tape:&mut Tape,u:usize,hs:&[QubitId],p1:QubitId,x2:&[QubitId],parity:QubitId){
 let(tp,sp)=tape.raw[u].unwrap();assert_eq!(tp,crate::circuit::NO_QUBIT);
 let mut used=hs.to_vec();used.extend(x2);used.extend([p1,parity]);let dirty=pool(tape,&used);
 cmp(c,hs,&x2[1..],parity,&[vec![(p1,false)]],&dirty);
 tape.raw[u]=Some((parity,sp));tape.dense_pack_to(c,u);assert!(tape.raw[u].is_none());
}

pub(super) fn erase_mid_type(c:&mut Builder,hs:&[QubitId],p1:QubitId,x2:&[QubitId],typ:QubitId){
 let mut used=hs.to_vec();used.extend(x2);used.extend([p1,typ]);let dirty:Vec<_>=c.walk_live().into_iter().filter(|q|!used.contains(q)).collect();
 cmp(c,hs,&x2[1..],typ,&[vec![(p1,false)]],&dirty);c.release_clean(typ);
}

fn fast_cmp(c:&mut Builder,a:&[QubitId],b:&[QubitId],seed:QubitId,out:QubitId,dirty:&[QubitId]){
 use crate::point_add::width_composition::xor_lt_seed;
 if a.len()==b.len(){xor_lt_seed(c,a,b,Some(seed),out);return;}
 let n=a.len().min(b.len());let high=if a.len()>n{a[n]}else{b[n]};if b.len()>n{c.cx(high,out);}
 let q=*dirty.iter().find(|&&q|q!=out&&q!=seed&&q!=high&&!a.contains(&q)&&!b.contains(&q)).expect("borrowed comparator output");
 c.x(high);xor_lt_seed(c,&a[..n],&b[..n],Some(seed),q);c.ccx(high,q,out);xor_lt_seed(c,&a[..n],&b[..n],Some(seed),q);c.ccx(high,q,out);c.x(high);
}
