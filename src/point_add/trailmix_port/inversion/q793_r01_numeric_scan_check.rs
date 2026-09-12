//! Differential falsifier for the numeric carry scan port: the rank-program
//! scan and the numeric scan must be the same map on the guard contract
//! (g=1, mask=hs=ha=0, valid rank code, A+C<=253, everything else arbitrary)
//! and both must restore every wire off guard.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;

struct Fixed;
impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x51)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:usize,l:usize,v:bool){let b=1u64<<l;w[q]=(w[q]&!b)|if v{b}else{0};}
fn set(w:&mut[u64],first:usize,n:usize,l:usize,v:usize){for i in 0..n{put(w,first+i,l,v>>i&1!=0);}}

fn build(j:usize,support_end:usize,scan:&str,prefix:&str)->(crate::point_add::B,usize){
    std::env::set_var("Q793_R01_NUMERIC_SCAN",scan);std::env::set_var("Q793_R01_A7_PREFIX",prefix);
    let mut c=Circuit::new();let rank=c.alloc_qreg_bits("rank",5);let a=c.alloc_qreg_bits("a",6);let cc=c.alloc_qreg_bits("c",6);
    let sm=c.alloc_qreg_bits("sm",4);let g=c.alloc_qreg("g");let mask=c.alloc_qreg("mask");let hs=c.alloc_qreg("hs");let ha=c.alloc_qreg("ha");
    let decision=c.alloc_qreg("decision");let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let dirty=c.alloc_qreg_bits("dirty",19);let owned=c.b.next_qubit;
    super::emit(&mut c,&rank,&a,&cc,&sm,&g,&mask,&hs,&ha,&decision,&w1,&w2,&dirty,j,support_end,false);
    let b=c.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}(b,owned as usize)
}
fn check_batch(reference:&crate::point_add::B,candidate:&crate::point_add::B,owned:usize,before:&[u64],label:&str){
    let mut f=Fixed;let mut r=Simulator::new(owned,0,&mut f);r.qubits.copy_from_slice(before);r.apply_iter(reference.ops.iter());
    let mut f=Fixed;let mut c=Simulator::new(owned,0,&mut f);c.qubits.copy_from_slice(before);c.apply_iter(candidate.ops.iter());
    if r.qubits!=c.qubits{let diffs:Vec<_>=r.qubits.iter().zip(&c.qubits).enumerate().filter(|(_,p)|p.0!=p.1).map(|(i,p)|(i,format!("{:016x}",p.0^p.1))).collect();panic!("numeric scan differential {label}: {diffs:?}");}
    assert_eq!(r.phase,c.phase);r.apply_iter(reference.ops.iter().rev());c.apply_iter(candidate.ops.iter().rev());assert_eq!(r.qubits,before);assert_eq!(c.qubits,before);assert_eq!(r.phase,0);assert_eq!(c.phase,0);
}
pub(super) fn run(){
    // Register offsets are fixed by build(): rank0, a5, c11, sm17, g21,
    // mask22, hs23, ha24, decision25, w1[26..285], w2[285..544], dirty544.
    let ts=super::triples();let mut lanes=0usize;
    for &(support_end,batches) in &[(259usize,8usize),(200,4),(97,4),(40,4),(9,4),(3,2)]{
    for j in 0..4{for prefix in ["1","0"]{
        let(reference,owned)=build(j,support_end,"0",prefix);let(candidate,owned2)=build(j,support_end,"2",prefix);assert_eq!(owned,owned2);
        let rt=reference.ops.iter().filter(|o|o.kind==K::CCX).count();let ct=candidate.ops.iter().filter(|o|o.kind==K::CCX).count();
        eprintln!("Q793_R01_NUMERIC_SCAN_BUILT j={j} n={support_end} prefix={prefix} reference_ops={} reference_T={rt} candidate_ops={} candidate_T={ct} delta_ops={} delta_T={}",reference.ops.len(),candidate.ops.len(),candidate.ops.len()as isize-reference.ops.len()as isize,ct as isize-rt as isize);
        // Every valid rank code with random low A/C on the guard domain
        // A+C<=253; clean guard loans; arbitrary SM, decision, work, dirty.
        for rk in 0..32{for batch in 0..batches{let mut seed=0x793_5ca1u64^((j as u64)<<48)^((rk as u64)<<32)^((support_end as u64)<<16)^batch as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{set(&mut before,0,5,lane,rk);
                let (t0,t1)=(ts[rk][0],ts[rk][1]);if 64*t0+64*t1>253{put(&mut before,21,lane,false);continue;}
                let mut al=(rnd(&mut seed)&63)as usize;let mut cl=(rnd(&mut seed)&63)as usize;
                let mut tries=0;while 64*t0+al+64*t1+cl>253{al=(rnd(&mut seed)&63)as usize;cl=(rnd(&mut seed)&63)as usize;tries+=1;if tries>64{al=0;cl=0;}}
                set(&mut before,5,6,lane,al);set(&mut before,11,6,lane,cl);
                put(&mut before,21,lane,true);put(&mut before,22,lane,false);put(&mut before,23,lane,false);put(&mut before,24,lane,false);}
            check_batch(&reference,&candidate,owned,&before,&format!("active-j{j}-n{support_end}-prefix{prefix}-rank{rk}-batch{batch}"));lanes+=64;
        }}
        // Off guard everything is arbitrary and both scans are identities.
        for batch in 0..8{let mut seed=0x793_0ffu64^((j as u64)<<48)^((support_end as u64)<<16)^batch;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{put(&mut before,21,lane,false);}
            let mut f=Fixed;let mut s=Simulator::new(owned,0,&mut f);s.qubits.copy_from_slice(&before);s.apply_iter(candidate.ops.iter());assert_eq!(s.qubits,before,"numeric scan off-guard identity j={j} n={support_end} batch={batch}");assert_eq!(s.phase,0);
            check_batch(&reference,&candidate,owned,&before,&format!("offguard-j{j}-n{support_end}-prefix{prefix}-batch{batch}"));lanes+=64;
        }
    }}}
    std::env::set_var("Q793_R01_NUMERIC_SCAN","1");std::env::set_var("Q793_R01_A7_PREFIX","1");
    eprintln!("Q793_R01_NUMERIC_SCAN_PASS lanes={lanes} all_rank guard_domain arbitrary_sm_decision_work_dirty offguard_identity literal_inverse phase0");
}
