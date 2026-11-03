//! Bumerängli: exact same-target CCX echoes through an affine influence cone.
//! No support assumptions, new wires, measurements, classical bits, or hashes.
//! If p=a*b is injected before a region which preserves a,b, and its Boolean
//! difference propagates linearly as p*v, a second identical CCX leaves
//! p*(v XOR e_target). Implement that residual with zero or one CCX.
//! Stop before a phase/measurement/nonlinear reader of the difference, any
//! control write, scope boundary, or branch-dependent affine propagation.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

const MAX_SPAN: usize = 512;
const MAX_SUPPORT: usize = 16;

#[derive(Debug, Default)]
pub(crate) struct Stats {
    pub input_ops: usize, pub output_ops: usize,
    pub input_ccx: usize, pub output_ccx: usize,
    pub starts: usize, pub scanned: usize, pub echoes: usize,
    pub cancel_two: usize, pub replace_one: usize, pub saved_ccx: usize,
    pub added_cx: usize, pub propagated: usize, pub max_support: usize,
    pub trivial_pairs: usize, pub barriers: [usize; 8],
}

#[derive(Clone, Debug)]
pub(crate) struct Certificate {
    pub first: usize, pub last: usize, pub a: u64, pub b: u64,
    pub target: u64, pub residual: Vec<u64>, pub affine_steps: usize,
}

fn toggle(s: &mut Vec<u64>, q: u64) {
    if let Some(i) = s.iter().position(|&v| v == q) { s.swap_remove(i); }
    else { s.push(q); }
}
fn pair(o: &Op) -> (u64, u64) {
    let (a,b)=(o.q_control1.0,o.q_control2.0); (a.min(b),a.max(b))
}
fn cx(a: u64, t: u64) -> Op {
    Op { kind: K::CX, q_control1: QubitId(a), q_target: QubitId(t), ..Op::empty() }
}
fn product(a: u64, b: u64, t: u64) -> Op {
    Op { kind: K::CCX, q_control1: QubitId(a), q_control2: QubitId(b), q_target: QubitId(t), ..Op::empty() }
}

pub(crate) fn emit(c: &Certificate, out: &mut Vec<Op>) {
    if let Some((&pivot, rest)) = c.residual.split_first() {
        // Conjugating by this fanout toggles p into every residual wire even
        // when pivot and all other destinations hold arbitrary dirty data.
        for &q in rest { out.push(cx(pivot,q)); }
        out.push(product(c.a,c.b,pivot));
        for &q in rest.iter().rev() { out.push(cx(pivot,q)); }
    }
}

fn seek(ops: &[Op], first: usize, s: &mut Stats) -> Option<Certificate> {
    let f=ops[first]; let (a,b)=pair(&f); let t=f.q_target.0;
    let protected=|q:u64| q==a || q==b;
    let mut diff=vec![t]; let mut affine=0;
    for j in first+1..ops.len().min(first+MAX_SPAN+2) {
        let o=&ops[j]; s.scanned+=1;
        if o.kind==K::CCX && o.c_condition==NO_BIT && pair(o)==(a,b) && o.q_target.0==t {
            if affine==0 { s.trivial_pairs+=1; return None; }
            toggle(&mut diff,t); diff.sort_unstable();
            if diff.len()>MAX_SUPPORT {s.barriers[6]+=1;return None;}
            return Some(Certificate{first,last:j,a,b,target:t,residual:diff,affine_steps:affine});
        }
        let touched=|q:u64| q!=NO_QUBIT.0 && diff.contains(&q);
        let writes_control=match o.kind {
            K::X|K::CX|K::CCX|K::Hmr|K::R=>protected(o.q_target.0),
            K::Swap=>protected(o.q_target.0)||protected(o.q_control1.0),
            _=>false,
        };
        if writes_control {s.barriers[0]+=1;return None;}
        if matches!(o.kind,K::PushCondition|K::PopCondition|K::Register|K::AppendToRegister|K::DebugPrint) {
            s.barriers[1]+=1;return None;
        }
        let hit=touched(o.q_target.0)||touched(o.q_control1.0)||touched(o.q_control2.0);
        if o.c_condition!=NO_BIT && hit {s.barriers[2]+=1;return None;}
        match o.kind {
            K::CX=>{
                if touched(o.q_control1.0) {toggle(&mut diff,o.q_target.0);affine+=1;}
            },
            K::Swap=>{
                let x=touched(o.q_control1.0);let y=touched(o.q_target.0);
                if x!=y {toggle(&mut diff,o.q_control1.0);toggle(&mut diff,o.q_target.0);affine+=1;}
            },
            K::CCX=>{
                if touched(o.q_control1.0)||touched(o.q_control2.0) {s.barriers[3]+=1;return None;}
            },
            K::Z|K::CZ|K::CCZ=>{
                if hit {s.barriers[4]+=1;return None;}
            },
            K::R|K::Hmr=>{
                if hit {s.barriers[5]+=1;return None;}
            },
            K::X|K::Neg|K::BitInvert|K::BitStore0|K::BitStore1=>{},
            _=>unreachable!(),
        }
        s.max_support=s.max_support.max(diff.len());
        if diff.len()>MAX_SUPPORT {s.barriers[6]+=1;return None;}
    }
    s.barriers[7]+=1;None
}

pub(crate) fn optimize(ops: Vec<Op>) -> (Vec<Op>, Stats, Vec<Certificate>) {
    let mut s=Stats::default();s.input_ops=ops.len();
    s.input_ccx=ops.iter().filter(|o|o.kind==K::CCX).count();
    let mut out=Vec::with_capacity(ops.len());let mut certs=vec![];let mut i=0;
    while i<ops.len() {
        if ops[i].kind==K::CCX && ops[i].c_condition==NO_BIT {
            s.starts+=1;
            if let Some(c)=seek(&ops,i,&mut s) {
                assert!(c.residual.iter().all(|&q|q!=c.a&&q!=c.b));
                out.extend_from_slice(&ops[i+1..c.last]);
                emit(&c,&mut out);
                s.echoes+=1;s.propagated+=c.affine_steps;
                if c.residual.is_empty() {s.cancel_two+=1;s.saved_ccx+=2;}
                else {s.replace_one+=1;s.saved_ccx+=1;s.added_cx+=2*(c.residual.len()-1);}
                i=c.last+1;certs.push(c);continue;
            }
        }
        out.push(ops[i]);i+=1;
    }
    s.output_ops=out.len();s.output_ccx=out.iter().filter(|o|o.kind==K::CCX).count();
    assert_eq!(s.input_ccx-s.output_ccx,s.saved_ccx);
    (out,s,certs)
}

pub(crate) fn apply(ops: Vec<Op>) -> Vec<Op> {
    let(out,s,_)=optimize(ops);eprintln!("BUMERANGLI {s:?}");out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use crate::circuit::BitId;
    use sha3::digest::{Update,ExtendableOutput,XofReader};
    fn gate(k:K,a:u64,b:u64,t:u64)->Op {
        let mut o=Op{kind:k,..Op::empty()};
        if !matches!(k,K::Neg) {o.q_target=QubitId(t);}
        if matches!(k,K::CX|K::CZ|K::Swap|K::CCX|K::CCZ){o.q_control1=QubitId(a);}
        if matches!(k,K::CCX|K::CCZ){o.q_control2=QubitId(b);}o
    }
    fn c(mut o:Op,b:u64)->Op{o.c_condition=BitId(b);o}
    fn bit(k:K,b:u64)->Op{Op{kind:k,c_target:BitId(b),..Op::empty()}}
    fn push(b:u64)->Op{Op{kind:K::PushCondition,c_condition:BitId(b),..Op::empty()}}
    fn pop()->Op{Op{kind:K::PopCondition,..Op::empty()}}
    fn check(p:&[Op],q:&[Op],random:bool) {
        for o in p.iter().chain(q.iter()){o.validate();}
        let events=|v:&[Op]|v.iter().filter(|o|matches!(o.kind,K::R|K::Hmr)).cloned().collect::<Vec<_>>();
        assert_eq!(events(p),events(q));
        // Exhaust all 6 quantum and 3 classical input bits, with 8 measurement
        // seeds. Random mode also dirties every other wire and classical slot.
        for seed in 0..8u64 {for batch in 0..8u64 {
            let mut h=sha3::Shake256::default();h.update(&seed.to_le_bytes());h.update(&batch.to_le_bytes());
            let mut init=h.clone().finalize_xof();let mut ar=h.clone().finalize_xof();let mut br=h.finalize_xof();
            let mut a=Simulator::new(10,6,&mut ar);let mut b=Simulator::new(10,6,&mut br);
            for j in 0..16usize {
                let v=if j<10 {j}else{j-10+6};
                let word=if random {let mut z=[0;8];init.read(&mut z);u64::from_le_bytes(z)}
                    else if j<6 || (10..13).contains(&j) {(0..64).filter(|i|((batch*64+i)>>v)&1!=0).fold(0u64,|w,i|w|(1<<i))}
                    else {0};
                if j<10 {a.qubits[j]=word;}else{a.bits[j-10]=word;}
            }
            b.qubits.clone_from(&a.qubits);b.bits.clone_from(&a.bits);
            a.apply_iter(p.iter());b.apply_iter(q.iter());
            assert_eq!(a.qubits,b.qubits,"quantum");assert_eq!(a.bits,b.bits,"classical");assert_eq!(a.phase,b.phase,"phase");
            let mut aa=[0;8];let mut bb=[0;8];a.xof.read(&mut aa);b.xof.read(&mut bb);assert_eq!(aa,bb,"RNG");
        }}
    }
    #[test]
    fn noncommuting_echo_becomes_one_gate_on_fanout() {
        let p=vec![product(0,1,2),cx(2,3),product(1,0,2)];
        let(q,s,_)=optimize(p.clone());assert_eq!(s.saved_ccx,1);assert_eq!(q,vec![cx(2,3),product(0,1,3)]);check(&p,&q,false);
    }
    #[test]
    fn dirty_multi_target_fanout_needs_no_clean_pivot() {
        let p=vec![product(0,1,2),cx(2,3),cx(3,4),cx(2,5),product(0,1,2)];
        let(q,s,cs)=optimize(p.clone());assert_eq!(s.saved_ccx,1);assert_eq!(cs[0].residual,vec![3,4,5]);
        assert_eq!(s.added_cx,4);check(&p,&q,false);check(&p,&q,true);
    }
    #[test]
    fn swap_transport_and_zero_residual_echo() {
        for middle in [vec![gate(K::Swap,2,0,3)],vec![cx(2,3),cx(2,3)]] {
            let mut p=vec![product(0,1,2)];p.extend(middle);p.push(product(0,1,2));
            let(q,s,_)=optimize(p.clone());assert!(s.saved_ccx>=1);check(&p,&q,false);check(&p,&q,true);
        }
    }
    #[test]
    fn conditions_and_independent_measurements_preserve_all_state() {
        let h=Op{kind:K::Hmr,q_target:QubitId(8),c_target:BitId(2),..Op::empty()};
        let p=vec![push(0),product(0,1,2),cx(2,3),h,bit(K::BitInvert,0),
            c(gate(K::X,0,0,7),2),product(0,1,2),pop()];
        let(q,s,_)=optimize(p.clone());assert_eq!(s.saved_ccx,1);check(&p,&q,false);check(&p,&q,true);
    }
    #[test]
    fn phase_measurement_nonlinear_and_control_barriers() {
        let h=Op{kind:K::Hmr,q_target:QubitId(3),c_target:BitId(2),..Op::empty()};
        for barrier in [gate(K::Z,0,0,3),gate(K::CZ,3,0,5),gate(K::CCZ,3,4,5),
            h,gate(K::R,0,0,3),product(3,4,5),gate(K::X,0,0,0),
            cx(4,1),c(cx(3,4),0),push(0)] {
            let mut p=vec![product(0,1,2),cx(2,3),barrier,product(0,1,2)];
            if barrier.kind==K::PushCondition {p.push(pop());}
            let(q,s,_)=optimize(p.clone());assert_eq!(s.echoes,0);assert_eq!(q,p);check(&p,&q,true);
        }
    }
    #[test]
    fn commuting_pair_is_deliberately_out_of_scope() {
        let p=vec![product(0,1,2),gate(K::X,0,0,2),product(0,1,2)];
        let(q,s,_)=optimize(p.clone());assert_eq!(s.echoes,0);assert_eq!(q,p);check(&p,&q,false);
    }
    #[test]
    fn wrong_dirty_pivot_and_ignored_phase_have_witnesses() {
        let p=vec![product(0,1,2),cx(2,3),cx(2,4),product(0,1,2)];
        let wrong=vec![cx(2,3),cx(2,4),product(0,1,3),cx(3,4)];
        assert!(std::panic::catch_unwind(||check(&p,&wrong,false)).is_err());
        let p=vec![product(0,1,2),cx(2,3),gate(K::Z,0,0,3),product(0,1,2)];
        let wrong=vec![cx(2,3),gate(K::Z,0,0,3),product(0,1,3)];
        assert!(std::panic::catch_unwind(||check(&p,&wrong,false)).is_err());
    }
    #[test]
    fn random_streams_and_planted_echoes() {
        let mut hits=0;
        for trial in 1..=24u64 {
            let mut state=trial;let mut next=||{state^=state<<13;state^=state>>7;state^=state<<17;state};
            let mut p=vec![];
            for _ in 0..200 {
                let a=next()%10;let mut b=next()%10;while b==a {b=next()%10;}
                let mut t=next()%10;while t==a||t==b {t=next()%10;}
                let k=[K::Neg,K::X,K::Z,K::CX,K::CZ,K::CCX,K::CCZ,K::Swap,K::Hmr,K::R][(next()%10)as usize];
                let mut o=gate(k,a,b,t);if k==K::Hmr {o.c_target=BitId(next()%6);}if next()%3==0 {o.c_condition=BitId(next()%6);}p.push(o);
                if next()%8==0 {p.extend([product(0,1,2),cx(2,3),cx(3,4),product(0,1,2)]);}
            }
            let(q,s,_)=optimize(p.clone());hits+=s.echoes;check(&p,&q,true);
        }
        assert!(hits>100);
    }
}
