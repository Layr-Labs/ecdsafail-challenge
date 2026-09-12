//! Differential falsifier for the partial86 shift-0 seed port.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;

struct Fixed;
impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x51)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:usize,l:usize,v:bool){let b=1u64<<l;w[q]=(w[q]&!b)|if v{b}else{0};}
fn set(w:&mut[u64],first:usize,n:usize,l:usize,v:usize){for i in 0..n{put(w,first+i,l,v>>i&1!=0);}}

fn build(j:usize,numeric:bool,support:Option<(usize,usize)>)->(crate::point_add::B,usize){
    let shift=1-j%2;std::env::set_var(if shift==0{"Q793_R01_NUMERIC_SEED"}else{"Q793_R01_NUMERIC_SEED1"},if numeric{"1"}else{"0"});
    let mut c=Circuit::new();c.q797_a_support=support;let rank=c.alloc_qreg_bits("rank",5);let a=c.alloc_qreg_bits("a",6);let cc=c.alloc_qreg_bits("c",6);
    let sm=c.alloc_qreg_bits("sm",4);let g=c.alloc_qreg("g");let mask=c.alloc_qreg("mask");let hs=c.alloc_qreg("hs");let ha=c.alloc_qreg("ha");
    let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let dirty=c.alloc_qreg_bits("dirty",18);let owned=c.b.next_qubit;
    super::seed(&mut c,&rank,&a,&cc,&sm,&g,&mask,&ha,&w1,&w2,&hs,&dirty,j,shift);
    let b=c.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}(b,owned as usize)
}
fn check_batch(reference:&crate::point_add::B,candidate:&crate::point_add::B,owned:usize,before:&[u64],label:&str){
    let mut f=Fixed;let mut r=Simulator::new(owned,0,&mut f);r.qubits.copy_from_slice(before);r.apply_iter(reference.ops.iter());
    let mut f=Fixed;let mut c=Simulator::new(owned,0,&mut f);c.qubits.copy_from_slice(before);c.apply_iter(candidate.ops.iter());
    if r.qubits!=c.qubits{let diffs:Vec<_>=r.qubits.iter().zip(&c.qubits).enumerate().filter(|(_,p)|p.0!=p.1).map(|(i,p)|(i,format!("{:016x}",p.0^p.1))).collect();panic!("numeric seed differential {label}: {diffs:?}");}
    assert_eq!(r.phase,c.phase);r.apply_iter(reference.ops.iter().rev());c.apply_iter(candidate.ops.iter().rev());assert_eq!(r.qubits,before);assert_eq!(c.qubits,before);assert_eq!(r.phase,0);assert_eq!(c.phase,0);
}
pub(super) fn run(){
    // Register offsets are fixed by build(): rank0, a5, c11, sm17,
    // g21, mask22, hs23, ha24, w1[25..284], w2[284..543], dirty543.
    let mut lanes=0usize;let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for support in [None,Some((2usize,40usize)),Some((100,200)),Some((240,256)),Some((253,256))]{
    for j in [1usize,3,0,2]{let shift=1-j%2;
        let(reference,owned)=build(j,false,support);let(candidate,owned2)=build(j,true,support);assert_eq!(owned,owned2);
        let rt=reference.ops.iter().filter(|o|o.kind==K::CCX).count();let ct=candidate.ops.iter().filter(|o|o.kind==K::CCX).count();
        eprintln!("Q793_R01_NUMERIC_SEED_BUILT j={j} shift={shift} support={support:?} reference_ops={} reference_T={rt} candidate_ops={} candidate_T={ct} delta_ops={} delta_T={}",reference.ops.len(),candidate.ops.len(),candidate.ops.len()as isize-reference.ops.len()as isize,ct as isize-rt as isize);
        // Every valid rank code and every low A value, with active seed
        // parity, clean guard loans, arbitrary work/passenger/dirty rails.
        for rk in 0..32{let mut seed=0x793_6015eedu64^((j as u64)<<48)^rk as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{set(&mut before,0,5,lane,rk);set(&mut before,5,6,lane,lane);let c0=((j>>1)&1)^shift;let cv=(((lane*29+rk*11)&31)<<1)|c0;set(&mut before,11,6,lane,cv);
                let av=64*ts[rk][0]+lane;let active=support.map_or(true,|(lo,hi)|lo<=av&&av<hi);
                set(&mut before,17,3,lane,0);put(&mut before,21,lane,active);put(&mut before,22,lane,true);put(&mut before,23,lane,false);put(&mut before,24,lane,false);}
            check_batch(&reference,&candidate,owned,&before,&format!("active-j{j}-rank{rk}"));lanes+=64;
        }
        // Off-guard space permits arbitrary rank, HS, HA, chart and lenders.
        for batch in 0..64{let mut seed=0x793_0ff5eedu64^((j as u64)<<48)^batch;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{put(&mut before,21,lane,batch&1!=0);put(&mut before,22,lane,if batch&1!=0{false}else{lane&1!=0});}
            check_batch(&reference,&candidate,owned,&before,&format!("offguard-j{j}-batch{batch}"));lanes+=64;
        }
    }}
    std::env::set_var("Q793_R01_NUMERIC_SEED","1");std::env::set_var("Q793_R01_NUMERIC_SEED1","1");
    eprintln!("Q793_R01_NUMERIC_SEED_PASS lanes={lanes} all_rank_lowA active_contract arbitrary_work_dirty offguard literal_inverse phase0");
}
