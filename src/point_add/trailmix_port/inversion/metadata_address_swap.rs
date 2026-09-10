//! Selected quotient-wire exchange from compressed metadata, using dirty echo.
//! High predicates are shared by16 mutually exclusive low-address swaps.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_sum_query,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
fn low_swaps(circ:&mut Circuit,low:&[QReg],flag:&QReg,guard:&QReg,sign:&QReg,word:&[QReg],helpers:&[QReg],high:usize,insert:bool) {
    for lo in 0..16 {
        let sum=high*16+lo;if sum>if insert {255}else{256} {continue;}
        // Insertion reads entry metadata before shared+=1, hence sum+2.
        // Removal reads the old nonempty quotient; raw shared zero means
        // truth256 and its sole raw-sum0 case addresses wire257.
        let target=&word[if insert {sum+2} else if sum==0 {257}else{sum+1}];
        let mut cs=vec![(flag,true),(guard,true)];cs.extend((0..4).map(|i|(&low[i],lo>>i&1!=0)));cs.push((sign,true));
        circ.cx(target,sign);length_recompute::mixed_mcx(circ,&cs,target,helpers);circ.cx(target,sign);
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],s0:&QReg,guard:&QReg,sign:&QReg,word:&[QReg],helpers:&[QReg],known:bool,insert:bool) {
    assert_eq!(word.len(),259);assert!(helpers.len()>=16);
    let flag=&helpers[0];let lenders=&helpers[1..];
    if known{circ.x(s0);}metadata_sum_query::add4(circ,a,c,s0,false);
    for hi in 0..=16 {
        metadata_sum_query::xor_high_equal(circ,rank,s0,guard,flag,lenders,hi);
        low_swaps(circ,c,flag,guard,sign,word,lenders,hi,insert);
        metadata_sum_query::xor_high_equal(circ,rank,s0,guard,flag,lenders,hi);
        low_swaps(circ,c,flag,guard,sign,word,lenders,hi,insert);
    }
    metadata_sum_query::add4(circ,a,c,s0,true);if known{circ.x(s0);}
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for insert in [false,true] {for known in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("swap.rank",10);let a=circ.alloc_qreg_bits("swap.a",4);let c=circ.alloc_qreg_bits("swap.c",4);let sm=circ.alloc_qreg_bits("swap.s23",2);let s0=circ.alloc_qreg("swap.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("swap.guard");let sign=circ.alloc_qreg("swap.sign");let word=circ.alloc_qreg_bits("swap.word",259);let helpers=circ.alloc_qreg_bits("swap.dirty",16);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&s0,&guard,&sign,&word,&helpers,known,insert);assert_eq!(owned,circ.b.next_qubit);let b=circ.into_builder();
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));for q in &sm{assert!(op.q_target.0!=q.id()as u64&&op.q_control1.0!=q.id()as u64&&op.q_control2.0!=q.id()as u64);}}
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();let cases=1024*16*16*2;
        for pattern in 0..4 {for batch in 0..cases/64 {
            let mut seed=0x597efd4825a613c9^batch as u64^((pattern as u64)<<28);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let n=batch*64+lane;let r=n&1023;let al=n>>10&15;let cl=n>>14&15;let on=n>>18&1!=0;
                for i in 0..10{put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,r>>i&1!=0);}
                for i in 0..4 {for (q,v) in [(&a[i],al>>i&1!=0),(&c[i],cl>>i&1!=0)]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}}
                let scratch=if on{known}else{(n+pattern)%2!=0};for (q,v) in [(&guard,on),(&s0,scratch)]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}
                if on&&r<966 {
                    let sum=16*(triples[r][0]+triples[r][1])+al+cl;
                    if sum<=if insert {255}else{256} {let target=&word[if insert{sum+2}else if sum==0{257}else{sum+1}];let sv=before[sign.id()as usize]>>lane&1!=0;let tv=before[target.id()as usize]>>lane&1!=0;put(&mut after,&sign,lane,tv);put(&mut after,target,lane,sv);}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"address swap insert={insert} known={known} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("CODEC_ADDRESS_SWAP insert={insert} known={known} T={tof} ops={} metadata_wires=21 component_wires={owned} all_rank_low_guard_data_dirty_phase_reverse=PASS",b.ops.len());
    }}
    eprintln!("CODEC_ADDRESS_SWAP_PASS lanes={total}; quotient-address component only, semantic guard and fullQ799 integration still required");
}

/// Borrow an existing selected zero, use it as a clean predicate flag and return
/// it. Scalar phase10 after quotient removal supplies this zero outside T's
/// selected prefix. This test does not yet run that complete arithmetic block.
pub fn run_zero_loan() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for known in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("loan.rank",10);let a=circ.alloc_qreg_bits("loan.a",4);let c=circ.alloc_qreg_bits("loan.c",4);let _sm=circ.alloc_qreg_bits("loan.s23",2);let s0=circ.alloc_qreg("loan.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("loan.guard");let aux=circ.alloc_qreg("loan.passenger");let word=circ.alloc_qreg_bits("loan.work1",259);let helpers=circ.alloc_qreg_bits("loan.dirty",16);let witness=circ.alloc_qreg("loan.other_data");let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&s0,&guard,&aux,&word,&helpers,known,false);let borrowed_at=circ.b.ops.len();
        if known{circ.x(&s0);}metadata_sum_query::add4(&mut circ,&a,&c,&s0,false);
        metadata_sum_query::xor_high_equal(&mut circ,&rank,&s0,&guard,&aux,&helpers,8);
        circ.ccx(&guard,&aux,&witness);
        metadata_sum_query::xor_high_equal(&mut circ,&rank,&s0,&guard,&aux,&helpers,8);
        metadata_sum_query::add4(&mut circ,&a,&c,&s0,true);if known{circ.x(&s0);}
        emit(&mut circ,&rank,&a,&c,&s0,&guard,&aux,&word,&helpers,known,false);assert_eq!(owned,circ.b.next_qubit);let b=circ.into_builder();
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();let cases=1024*16*16*2;
        for pattern in 0..4 {for batch in 0..cases/64 {
            let mut seed=0xa371ef9815c602db^batch as u64^((pattern as u64)<<28);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();let mut active_mask=0u64;
            for lane in 0..64 {
                let n=batch*64+lane;let r=n&1023;let al=n>>10&15;let cl=n>>14&15;let sum=if r<966 {16*(triples[r][0]+triples[r][1])+al+cl}else{usize::MAX};let on=n>>18&1!=0&&sum<=256;
                for i in 0..10{put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,r>>i&1!=0);}
                for i in 0..4 {for (q,v) in [(&a[i],al>>i&1!=0),(&c[i],cl>>i&1!=0)]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}}
                let scratch=if on{known}else{(n+pattern)%2!=0};for (q,v) in [(&guard,on),(&s0,scratch)]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}
                if on {active_mask|=1u64<<lane;let target=&word[if sum==0{257}else{sum+1}];put(&mut before,target,lane,false);put(&mut after,target,lane,false);
                    if sum/16==8 {after[witness.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(b.ops[..borrowed_at].iter());assert_eq!(sim.qubits[aux.id()as usize]&active_mask,0,"borrowed zero missing known={known} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops[borrowed_at..].iter());assert_eq!(sim.qubits,after,"zero loan known={known} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("CODEC_ZERO_LOAN known={known} T={tof} ops={} metadata_wires=21 component_wires={owned} clean_at_borrow_flag_use_all_wires_phase_reverse=PASS",b.ops.len());
    }
    eprintln!("CODEC_ZERO_LOAN_PASS lanes={total}; existing phase10 zero borrowing component, full arithmetic andQ799 integration absent");
}

/// Phase10 entry Sign=0 under guard. Remove the selected quotient bit into
/// Sign and simultaneously borrow that cleared wire into an arbitrary passenger.
/// Guard must imply an admissible quotient address. Metadata stays at entry.
pub(super) fn remove_and_borrow(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],s0:&QReg,guard:&QReg,sign:&QReg,aux:&QReg,word:&[QReg],helpers:&[QReg],known:bool) {
    if known{circ.x(s0);}metadata_sum_query::add4(circ,a,c,s0,false);
    for hi in 0..=16 {
        metadata_sum_query::xor_high_equal(circ,rank,s0,guard,sign,helpers,hi);
        low_swaps(circ,c,sign,guard,aux,word,helpers,hi,false);
        metadata_sum_query::xor_high_equal(circ,rank,s0,guard,sign,helpers,hi);
    }
    metadata_sum_query::add4(circ,a,c,s0,true);if known{circ.x(s0);}
    circ.cswap(guard,sign,aux);
}
pub fn run_fused_loan() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for known in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("fused.rank",10);let a=circ.alloc_qreg_bits("fused.a",4);let c=circ.alloc_qreg_bits("fused.c",4);let _sm=circ.alloc_qreg_bits("fused.s23",2);let s0=circ.alloc_qreg("fused.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("fused.guard");let sign=circ.alloc_qreg("fused.sign");let aux=circ.alloc_qreg("fused.passenger");let word=circ.alloc_qreg_bits("fused.work1",259);let helpers=circ.alloc_qreg_bits("fused.dirty",16);let witness=circ.alloc_qreg("fused.other_data");let owned=circ.b.next_qubit;
        remove_and_borrow(&mut circ,&rank,&a,&c,&s0,&guard,&sign,&aux,&word,&helpers,known);let borrowed_at=circ.b.ops.len();
        if known{circ.x(&s0);}metadata_sum_query::add4(&mut circ,&a,&c,&s0,false);
        metadata_sum_query::xor_high_equal(&mut circ,&rank,&s0,&guard,&aux,&helpers,8);circ.ccx(&guard,&aux,&witness);
        metadata_sum_query::xor_high_equal(&mut circ,&rank,&s0,&guard,&aux,&helpers,8);
        metadata_sum_query::add4(&mut circ,&a,&c,&s0,true);if known{circ.x(&s0);}
        emit(&mut circ,&rank,&a,&c,&s0,&guard,&aux,&word,&helpers,known,false);assert_eq!(owned,circ.b.next_qubit);let b=circ.into_builder();
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();let cases=1024*16*16*2;
        for pattern in 0..4 {for batch in 0..cases/64 {
            let mut seed=0x129cb7df58a406e3^batch as u64^((pattern as u64)<<28);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();let mut borrowed=before.clone();
            for lane in 0..64 {
                let n=batch*64+lane;let r=n&1023;let al=n>>10&15;let cl=n>>14&15;let sum=if r<966{16*(triples[r][0]+triples[r][1])+al+cl}else{usize::MAX};let on=n>>18&1!=0&&sum<=256;
                for i in 0..10 {for w in [&mut before,&mut after,&mut borrowed]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..4 {for (q,v) in [(&a[i],al>>i&1!=0),(&c[i],cl>>i&1!=0)]{for w in [&mut before,&mut after,&mut borrowed]{put(w,q,lane,v);}}}
                let scratch=if on{known}else{(n+pattern)%2!=0};let incoming_sign=if on{false}else{(n+pattern+1)%2!=0};
                for (q,v) in [(&guard,on),(&s0,scratch),(&sign,incoming_sign)]{for w in [&mut before,&mut after,&mut borrowed]{put(w,q,lane,v);}}
                if on {
                    let target=&word[if sum==0{257}else{sum+1}];let qbit=before[target.id()as usize]>>lane&1!=0;let passenger=before[aux.id()as usize]>>lane&1!=0;
                    put(&mut borrowed,&sign,lane,qbit);put(&mut borrowed,&aux,lane,false);put(&mut borrowed,target,lane,passenger);
                    put(&mut after,&sign,lane,qbit);put(&mut after,target,lane,false);
                    if sum/16==8 {after[witness.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(b.ops[..borrowed_at].iter());assert_eq!(sim.qubits,borrowed,"fused remove/borrow known={known} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops[borrowed_at..].iter());assert_eq!(sim.qubits,after,"fused complete known={known} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("CODEC_FUSED_LOAN known={known} T={tof} ops={} fused_prefix_ops={borrowed_at} metadata_wires=21 component_wires={owned} full_borrow_mapping_flag_use_return_phase_reverse=PASS",b.ops.len());
    }
    eprintln!("CODEC_FUSED_LOAN_PASS lanes={total}; phase10 quotient removal plus loan/use/return, completeT arithmetic andQ799 integration absent");
}
