//! Bounded graph-chart compiler plus explicitly marked reachable-state macros.
//! The unfenced compiler is exact on its chart. Fences require the documented
//! reachable-state identities, separately exercised by full native lifecycles.
//! A successful result is an actual NCT program; a chart failure is not an
//! impossibility result for RRP or for a different representation.
use crate::circuit::{Op, OperationType as K, QubitId};
use std::collections::BTreeSet;
type Term = Vec<u32>;
type Poly = BTreeSet<Term>;
thread_local! {static FENCES:std::cell::RefCell<Option<Vec<(usize,u8)>>>=std::cell::RefCell::new(None);}
pub(crate) fn fence(circ:&crate::point_add::trailmix_port::circuit::Circuit,kind:u8) {
    FENCES.with(|f|{if let Some(v)=f.borrow_mut().as_mut(){v.push((circ.b.ops.len(),kind));}});
}
const NEG:u32=1<<31;
fn wire(lit:u32)->u32{lit&!NEG}
fn uses(term:&Term,q:u32)->bool{term.contains(&q)||term.contains(&(q|NEG))}

fn toggle(p: &mut Poly, mut t: Term) {
    if t.contains(&u32::MAX){return;}
    loop {
        if p.remove(&t){return;}
        let mut reduced=false;
        for i in 0..t.len() {
            let mut shorter=t.clone();let lit=shorter.remove(i);
            let mut opposite=shorter.clone();opposite.push(lit^NEG);opposite.sort_unstable();
            if p.remove(&shorter){t=opposite;reduced=true;break;}
            if p.remove(&opposite){t=shorter;reduced=true;break;}
        }
        if !reduced{p.insert(t);return;}
    }
}
fn product(a: &[u32], b: &[u32]) -> Term {
    let mut v:Vec<_> = a.iter().chain(b).copied().collect();v.sort_unstable();v.dedup();
    if v.iter().any(|&q|v.binary_search(&(q^NEG)).is_ok()){vec![u32::MAX]}else{v}
}
fn single(controls:&[u32],target:u32)->Op {
    assert!(controls.len()<=2 && !controls.contains(&target));
    let mut o=Op::empty();o.q_target=QubitId(target as u64);
    o.kind=match controls.len(){0=>K::X,1=>K::CX,_=>K::CCX};
    if !controls.is_empty(){o.q_control1=QubitId(controls[0] as u64);}
    if controls.len()==2{o.q_control2=QubitId(controls[1] as u64);}
    o
}
fn mcx(out:&mut Vec<Op>,cs:&[u32],target:u32,n:u32)->Result<(),String> {
    if cs.iter().any(|&q|q&NEG!=0) {
        let positives:Vec<_>=cs.iter().map(|&q|wire(q)).collect();
        for &q in cs {if q&NEG!=0{out.push(single(&[],wire(q)));}}
        mcx(out,&positives,target,n)?;
        for &q in cs.iter().rev() {if q&NEG!=0{out.push(single(&[],wire(q)));}}
        return Ok(());
    }
    if cs.contains(&target){return Err("MCX target in controls".into());}
    if cs.len()<=2 {out.push(single(cs,target));return Ok(());}
    let d:Vec<_>=(0..n).rev().filter(|q|*q!=target&&!cs.contains(q)).take(cs.len()-2).collect();
    if d.len()!=cs.len()-2{return Err("dirty lender shortage".into());}
    for seed in [true,false] {
        if seed{out.push(single(&cs[..2],d[0]));}
        for i in 1..d.len(){out.push(single(&[d[i-1],cs[i+1]],d[i]));}
        out.push(single(&[d[d.len()-1],cs[cs.len()-1]],target));
        for i in (1..d.len()).rev(){out.push(single(&[d[i-1],cs[i+1]],d[i]));}
        if seed{out.push(single(&cs[..2],d[0]));}
    }
    Ok(())
}

pub struct Chart {
    pub missing:u32,
    pub map:Vec<Option<u32>>,
    pub value:Poly,
    pub output:Vec<Op>,
    pub pivots:usize,
    pub max_terms:usize,
    pub processed:usize,
}

pub fn run() {
    use crate::point_add::trailmix_port::circuit::Circuit;
    for name in ["Q799_MUX_LEASE","Q799_MUX_QUOTIENT","Q799_XOR_LO","Q799_PREFIX_TREE","Q799_T11_FIRST","Q799_HEAD_TREE"] {std::env::set_var(name,"1");}
    std::env::set_var("Q799_CANCEL_WINDOW","2048");
    std::env::set_var("Q798_AFTER_T11_CHART","1");
    for block in [0usize,8,16,25] {for j in 0..4 {
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
        let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);
        let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");
        let sign=circ.alloc_qreg("sign");let it=circ.alloc_qreg("iteration");
        let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);
        let helpers=circ.alloc_qreg_bits("borrowed",24);
        super::metadata_full_step5::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&it,&w1,&w2,&helpers,j,block);
        let ops=circ.into_builder().ops;
        let mut chart=Chart::new(567,sign.id(),false);
        let phase_term=vec![chart.physical(p1.id()),chart.physical(p2.id())];
        toggle(&mut chart.value,phase_term);
        let mut failed=None;
        for (i,op) in ops.iter().enumerate(){if let Err(e)=chart.apply(op){failed=Some((i,e));break;}}
        eprintln!("Q798_SIGN_CHART block={block} j={j} logical_ops={} physical_ops={} missing={} pivots={} max_terms={} final_terms={} failure={failed:?}",ops.len(),chart.output.len(),chart.missing,chart.pivots,chart.max_terms,chart.value.len());
        if failed.is_some(){return;}
    }}
}
impl Chart {
    fn new(n:u32,missing:u32,value:bool)->Self {
        let map=(0..n).map(|q|if q==missing{None}else{Some(q-u32::from(q>missing))}).collect();
        let mut p=Poly::new();if value{p.insert(Vec::new());}
        Self{missing,map,value:p,output:Vec::new(),pivots:0,max_terms:0,processed:0}
    }
    fn physical(&self,q:u32)->u32 {self.map[q as usize].expect("physical requested for virtual")}
    fn apply(&mut self,op:&Op)->Result<(),String> {
        let n=self.map.len() as u32-1;
        let target=op.q_target.0 as u32;
        let cs=match op.kind {K::X=>vec![],K::CX=>vec![op.q_control1.0 as u32],K::CCX=>vec![op.q_control1.0 as u32,op.q_control2.0 as u32],_=>return Err("non-NCT".into())};
        if target==self.missing {
            let monomial=product(&cs.iter().map(|&q|self.physical(q)).collect::<Vec<_>>(),&[]);
            toggle(&mut self.value,monomial);
        } else if cs.contains(&self.missing) {
            let t=self.physical(target);
            // A target dependence may vanish under this gate's other control.
            // Inspect F*control, not F alone, before declaring a graph failure.
            let other:Vec<_>=cs.iter().filter(|&&q|q!=self.missing).map(|&q|self.physical(q)).collect();
            let mut controlled=Poly::new();for term in &self.value{toggle(&mut controlled,product(term,&other));}
            let occurrences:Vec<_>=controlled.iter().filter(|term|uses(term,t)).cloned().collect();
            if !occurrences.is_empty() {
                let pivot=self.value.iter().filter(|term|term.len()==1).filter_map(|term| {
                    let p=wire(term[0]);
                    if self.value.iter().filter(|a|uses(a,p)).count()!=1{return None;}
                    let logical=self.map.iter().position(|&m|m==Some(p)).unwrap() as u32;
                    if cs.contains(&logical){None}else{Some((logical,p,term[0]&NEG!=0))}
                }).next();
                let Some((logical,p,negative))=pivot else {
                    return Err(format!("nonunit graph pivot target={target}/p{t} cs={cs:?} missing={} coefficient_terms={} polynomial_terms={} value={:?} first={:?}",self.missing,occurrences.len(),self.value.len(),self.value,&occurrences[..occurrences.len().min(3)]));
                };
                let mut h:Vec<_>=self.value.iter().filter(|term|!uses(term,p)).cloned().collect();
                if negative{h.push(Vec::new());}
                for term in &h{mcx(&mut self.output,term,p,n)?;}
                self.map[self.missing as usize]=Some(p);
                self.map[logical as usize]=None;
                self.missing=logical;self.pivots+=1;
                return self.apply(op);
            } else {
                for term in &controlled{mcx(&mut self.output,term,t,n)?;}
            }
        } else {
            let t=self.physical(target);
            let controls:Vec<_>=cs.iter().map(|&q|self.physical(q)).collect();
            if controls.is_empty() {
                let old=std::mem::take(&mut self.value);
                for mut term in old {
                    for q in &mut term{if wire(*q)==t{*q^=NEG;}}
                    term.sort_unstable();toggle(&mut self.value,term);
                }
            } else {
                let changed:Vec<_>=self.value.iter().filter(|term|uses(term,t))
                    .map(|term|product(&term.iter().filter(|&&q|wire(q)!=t).copied().collect::<Vec<_>>(),&controls)).collect();
                for term in changed{toggle(&mut self.value,term);}
            }
            self.output.push(single(&controls,t));
        }
        self.max_terms=self.max_terms.max(self.value.len());self.processed+=1;
        if self.value.len()>16384{return Err("polynomial budget 16384 terms".into());}
        if self.output.len()>5_000_000{return Err("emission budget 5 million operations".into());}
        Ok(())
    }
}
