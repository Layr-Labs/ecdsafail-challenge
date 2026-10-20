//! Exact two-stage carry phase, without a carry workspace wire.
//! A component experiment. CCZ counts as a scored Toffoli in the harness.
use super::builder::Builder;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn literal_on(c:&mut Builder,row:&[QubitId],one:bool)->QubitId{
    let q=row[0];for &r in &row[1..]{c.cx(r,q);}if one{c.x(q);}q
}
fn literal_off(c:&mut Builder,row:&[QubitId],one:bool){
    let q=row[0];if one{c.x(q);}for &r in row[1..].iter().rev(){c.cx(r,q);}
}
fn xor_on(c:&mut Builder,row:&[QubitId],one:bool,q:QubitId){for &r in row{c.cx(r,q);}if one{c.x(q);}}
fn xor_off(c:&mut Builder,row:&[QubitId],one:bool,q:QubitId){if one{c.x(q);}for &r in row.iter().rev(){c.cx(r,q);}}
fn neg(c:&mut Builder,q:QubitId){c.cz(q,q);c.x(q);c.cz(q,q);c.x(q);}
fn valid(acc:&[QubitId],rows:&[Vec<QubitId>],cin:QubitId)->bool{
    if acc.len()!=rows.len()||acc.len()<2{return false;}
    let mut occupied=BTreeSet::from([cin.0]);
    if !acc.iter().all(|q|occupied.insert(q.0)){return false;}
    rows.iter().all(|row|{let mut seen=BTreeSet::new();row.iter().all(|q|!occupied.contains(&q.0)&&seen.insert(q.0))})
}

/// Phase carry (or NOT carry) after two unsigned full-adder stages.
/// `a`, `d` are XOR rows with independent constant terms. All operands restore.
/// GF(2) rank <=1 of the two source rows uses one CCZ; rank2 uses two.
pub(super) fn pair(c:&mut Builder,b:QubitId,e:QubitId,ci:QubitId,
    a:&[QubitId],a_one:bool,d:&[QubitId],d_one:bool,not_carry:bool)->bool{
    if !valid(&[b,e],&[a.to_vec(),d.to_vec()],ci){return false;}
    let aset:BTreeSet<_>=a.iter().map(|q|q.0).collect();let dset:BTreeSet<_>=d.iter().map(|q|q.0).collect();
    if a.is_empty(){
        // C2 = d*e XOR (d XOR e)*C1; C1=bc or b XOR c XOR bc.
        for &q in d{c.cz(q,e);}if d_one{c.cz(e,e);}
        xor_on(c,d,d_one,e);
        if a_one{c.cz(e,b);c.cz(e,ci);}c.ccz(e,b,ci);
        xor_off(c,d,d_one,e);
    }else if aset==dset{
        let q=literal_on(c,a,a_one);
        if a_one==d_one{c.cz(q,q);}else{c.cz(e,e);}
        c.cx(q,b);c.cx(q,e);c.cx(q,ci);
        if a_one!=d_one{c.x(e);}c.ccz(b,e,ci);if a_one!=d_one{c.x(e);}
        c.cx(q,ci);c.cx(q,e);c.cx(q,b);literal_off(c,a,a_one);
    }else if d.is_empty(){
        let q=literal_on(c,a,a_one);
        c.cz(e,q);if d_one{c.cz(e,e);c.cz(q,q);c.x(e);}
        c.cx(q,b);c.cx(q,ci);c.ccz(e,b,ci);c.cx(q,ci);c.cx(q,b);
        if d_one{c.x(e);}literal_off(c,a,a_one);
    }else{
        // C2 = d*e XOR (d XOR e)*a*b XOR (d XOR e)*(a XOR b)*ci.
        for &q in d{c.cz(q,e);}if d_one{c.cz(e,e);}
        xor_on(c,d,d_one,e);let q=literal_on(c,a,a_one);
        c.ccz(e,q,b);c.cx(b,q);c.ccz(e,q,ci);c.cx(b,q);
        literal_off(c,a,a_one);xor_off(c,d,d_one,e);
    }
    if not_carry{neg(c,ci);}true
}

/// A whole carry-phase ladder with only n-2 temporary carry wires.
pub(super) fn apply(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],comp:bool,cin:QubitId,not_carry:bool)->bool{
    if !valid(acc,rows,cin){return false;}let n=acc.len();let mut carry=vec![cin];
    for i in 0..n-2{
        let ci=carry[i];c.cx(ci,acc[i]);
        let q=if rows[i].is_empty(){ci}else{let q=literal_on(c,&rows[i],false);c.cx(ci,q);q};
        if comp{c.x(q);}let out=c.alloc_qubit();c.ccx(acc[i],q,out);
        if comp{c.x(q);}if !rows[i].is_empty(){c.cx(ci,q);literal_off(c,&rows[i],false);}
        c.cx(ci,out);c.cx(ci,acc[i]);carry.push(out);
    }
    assert!(pair(c,acc[n-2],acc[n-1],carry[n-2],&rows[n-2],comp,&rows[n-1],comp,not_carry));
    for i in(0..n-2).rev(){
        let ci=carry[i];let out=carry[i+1];c.cx(ci,out);c.cx(ci,acc[i]);
        let q=if rows[i].is_empty(){ci}else{let q=literal_on(c,&rows[i],false);c.cx(ci,q);q};
        if comp{c.x(q);}let m=c.alloc_bit();c.hmr(out,m);c.cz_if(acc[i],q,m);c.free_bit(m);c.release_clean(out);
        if comp{c.x(q);}if !rows[i].is_empty(){c.cx(ci,q);literal_off(c,&rows[i],false);}
        c.cx(ci,acc[i]);
    }true
}

#[cfg(test)]mod tests{
    use super::*;use crate::circuit::{analyze_ops,Op,OperationType};use crate::sim::Simulator;use sha3::digest::XofReader;
    struct Words{data:Vec<u8>,pos:usize}impl XofReader for Words{fn read(&mut self,b:&mut[u8]){let e=self.pos+b.len();assert!(e<=self.data.len());b.copy_from_slice(&self.data[self.pos..e]);self.pos=e;}}
    fn rng(words:&[u64])->Words{Words{data:words.iter().flat_map(|w|w.to_le_bytes()).collect(),pos:0}}
    fn scored(ops:&[Op])->usize{ops.iter().filter(|o|matches!(o.kind,OperationType::CCX|OperationType::CCZ)).count()}
    fn draws(ops:&[Op])->usize{ops.iter().filter(|o|matches!(o.kind,OperationType::Hmr|OperationType::R)).count()}
    fn put<R:XofReader>(s:&mut Simulator<'_,R>,q:QubitId,lane:usize,value:usize){if value&1!=0{s.qubits[q.0 as usize]|=1u64<<lane;}}
    #[test]fn every_pair_of_four_source_parities_and_both_constants(){
        for am in 0usize..16{for dm in 0usize..16{for ac in[false,true]{for dc in[false,true]{for inverse in[false,true]{
            let mut c=Builder::new();let src=c.alloc_qubits(4);let b=c.alloc_qubit();let e=c.alloc_qubit();let ci=c.alloc_qubit();
            let all:Vec<_>=src.iter().copied().chain([b,e,ci]).collect();c.declare_qubit_register(&all);
            let a:Vec<_>=(0..4).filter(|i|am>>i&1!=0).map(|i|src[i]).collect();let d:Vec<_>=(0..4).filter(|i|dm>>i&1!=0).map(|i|src[i]).collect();
            let count=c.active_qubits();assert!(pair(&mut c,b,e,ci,&a,ac,&d,dc,inverse));assert_eq!(c.active_qubits(),count);
            let ops=c.take_ops();assert_eq!(scored(&ops),if am==0||dm==0||am==dm{1}else{2});assert_eq!(draws(&ops),0);
            let(nq,nb,_,_)=analyze_ops(ops.iter());assert_eq!(nq,7);
            for start in[0usize,64]{let mut random=rng(&[]);let mut s=Simulator::new(nq as usize,nb as usize,&mut random);let mut phase=0u64;
                for lane in 0..64{let v=start+lane;for(i,&q)in all.iter().enumerate(){put(&mut s,q,lane,v>>i);}
                    let av=((v&am).count_ones()as usize&1)^usize::from(ac);let dv=((v&dm).count_ones()as usize&1)^usize::from(dc);
                    let c1=(av+(v>>4&1)+(v>>6&1))>>1;let c2=(dv+(v>>5&1)+c1)>>1;
                    if(c2!=0)^inverse{phase|=1u64<<lane;}}
                let original=s.qubits.clone();s.apply_iter(ops.iter());assert_eq!(s.qubits,original);assert_eq!(s.phase,phase,"am={am} dm={dm} ac={ac} dc={dc} inv={inverse}");
            }
        }}}}}
    }
    fn check_ladder(n:usize,comp:bool,empty:bool,repeated:bool,probe:Option<usize>){
        let mut c=Builder::new();let src=c.alloc_qubits(n);let acc=c.alloc_qubits(n);let ci=c.alloc_qubit();let shared=c.alloc_qubit();
        let all:Vec<_>=src.iter().chain(acc.iter()).copied().chain([ci,shared]).collect();c.declare_qubit_register(&all);
        let mut rows:Vec<Vec<QubitId>>=(0..n).map(|i|if empty&&i%3==2{vec![]}else if i%2==0{vec![src[i],shared]}else{vec![src[i]]}).collect();
        if repeated{rows[n-1]=rows[n-2].clone();}assert!(apply(&mut c,&acc,&rows,comp,ci,true));let ops=c.take_ops();
        let(nq,nb,_,_)=analyze_ops(ops.iter());assert_eq!(nq as usize,all.len()+n-2);let nr=draws(&ops);assert_eq!(nr,n-2);
        let expected_count=n-2+if rows[n-2].is_empty()||rows[n-1].is_empty()||rows[n-2]==rows[n-1]{1}else{2};assert_eq!(scored(&ops),expected_count);
        let starts:Vec<_>=if probe.is_some(){vec![0x397C0]}else{(0..1usize<<(2*n+2)).step_by(64).collect()};
        for start in starts{let words:Vec<_>=(0..nr).map(|j|match probe{Some(p)=>if p==j||p==nr{u64::MAX}else{0},None=>0x9E3779B97F4A7C15u64.wrapping_mul((start+j+1)as u64).rotate_left(j as u32)}).collect();
            let mut random=rng(&words);let mut s=Simulator::new(nq as usize,nb as usize,&mut random);let mut phase=0u64;
            for lane in 0..64{let v=start+lane;for(i,&q)in all.iter().enumerate(){put(&mut s,q,lane,v>>i);}
                let mut av=0usize;for(i,row)in rows.iter().enumerate(){let bit=row.iter().fold(usize::from(comp),|x,q|x^(v>>all.iter().position(|r|r==q).unwrap()&1));av|=bit<<i;}
                let cv=(av+(v>>n&((1<<n)-1))+(v>>(2*n)&1))>>n;if cv==0{phase|=1u64<<lane;}}
            let original=s.qubits.clone();s.apply_iter(ops.iter());assert_eq!(s.qubits,original);assert_eq!(s.phase,phase,"n={n} comp={comp} empty={empty} repeated={repeated}");drop(s);assert_eq!(random.pos,nr*8);
        }
    }
    #[test]fn whole_ladder_exhaustive_value_phase_and_clean_workspace(){for n in 2usize..=6{for comp in[false,true]{for empty in[false,true]{for repeated in[false,true]{check_ladder(n,comp,empty,repeated,None);}}}}}
    #[test]fn every_measurement_phase_coefficient_on_sixty_four_bases(){for p in 0..8{check_ladder(8,true,true,false,Some(p));check_ladder(8,false,false,true,Some(p));}}
    #[test]fn invalid_alias_rejected_before_any_emission(){let mut c=Builder::new();let q=c.alloc_qubits(5);let n=c.op_count();assert!(!pair(&mut c,q[0],q[1],q[2],&[q[0]],false,&[q[3]],false,false));assert!(!pair(&mut c,q[0],q[1],q[2],&[q[3],q[3]],false,&[],false,false));assert_eq!(c.op_count(),n);}
}
