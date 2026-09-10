//! Quarter-step cycle exit using a global padding loan and relocated passenger data.
//! Caller supplies post-entry state at j0, before S-zero phase flips.
//! Work1[A_raw+1] must be0 globally, including already-terminal inputs.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn triples()->Vec<[usize;3]> {
    (0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()
}
// axis0: Work[A_raw+1]; axis1: Work[259-C]. The latter is used only under
// the exit guard (S0,C1..255), so S0 rank rows suffice for its high selector.
fn addressed(circ:&mut Circuit,rank:&[QReg],low:&[QReg],guard:Option<&QReg>,passenger:Option<&QReg>,word:&[QReg],helpers:&[QReg],axis:usize) {
    if axis==0&&guard.is_none(){if let Some(p)=passenger{
        let(q,ops)=super::q798_handoffs::gather_a(circ,rank,low,word,1,helpers);
        circ.cx(q,p);circ.cx(p,q);circ.cx(q,p);circ.b.ops.extend(ops.into_iter().rev());return;
    }}
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..4 {for _echo in 0..2 {
        let cubes:Vec<_>=if axis==0 {programs::EQUAL[h].to_vec()} else {
            triples().iter().enumerate().filter(|(_,t)|t[1]==h&&t[2]==0).map(|(r,_)|(31u16,r as u16)).collect()
        };
        for (m,v) in cubes {
            let mut cs=Vec::new();if let Some(g)=guard{cs.push((g,true));}cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,flag,dirty);
        }
        for lo in 0..64 {
            let value=64*h+lo;if axis==1&&value==0{continue;}
            let target=&word[if axis==0 {value+1}else{259-value}];
            let mut cs=vec![(flag,true)];if let Some(g)=guard{cs.push((g,true));}cs.extend((0..6).map(|i|(&low[i],lo>>i&1!=0)));
            if let Some(p)=passenger {circ.cx(target,p);cs.push((p,true));mixed_mcx(circ,&cs,target,dirty);circ.cx(target,p);}
            else {mixed_mcx(circ,&cs,target,dirty);}
        }
    }}
}
// Under the independent exit guard S_mid is0: cache the high selector and
// use another S bit as conditional clean MCX scratch. Both restore off guard.
fn selected_exit(circ:&mut Circuit,rank:&[QReg],low:&[QReg],sm:&[QReg],g:&QReg,passenger:Option<&QReg>,word:&[QReg],helpers:&[QReg],axis:usize) {
    if axis==0{if let Some(p)=passenger{
        super::q797_cargo_moves::exchange_a(circ,rank,low,word,1,p,&[(g,true)],helpers);return;
    }}
    let flag=&sm[1];let scratch=&sm[2];let dirty=&helpers[0];
    for h in 0..4 {
        let cubes:Vec<_>=if axis==0 {programs::EQUAL[h].to_vec()} else {
            triples().iter().enumerate().filter(|(_,t)|t[1]==h&&t[2]==0).map(|(r,_)|(31u16,r as u16)).collect()
        };
        let high=|circ:&mut Circuit| {for &(m,v) in &cubes {
            let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
            super::conditional_mcx::guarded(circ,g,&cs,flag,scratch,false,dirty);
        }};
        high(circ);
        for lo in 0..64 {
            let value=64*h+lo;if axis==1&&value==0{continue;}
            let target=&word[if axis==0 {value+1}else{259-value}];
            let mut cs=vec![(flag,true)];cs.extend((0..6).map(|i|(&low[i],lo>>i&1!=0)));
            if let Some(p)=passenger {
                circ.cx(target,p);cs.push((p,true));
                super::conditional_mcx::guarded(circ,g,&cs,target,scratch,false,dirty);
                circ.cx(target,p);
            } else {super::conditional_mcx::guarded(circ,g,&cs,target,scratch,false,dirty);}
        }
        high(circ);
    }
}
fn exit_guard(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,g:&QReg,helpers:&[QReg]) {
    // j0 and phase11 make both implicit S bits0. Sign1 excludes trueS256 entry.
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(p2,true),(sign,false)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,helpers);
    }
}
pub(super) fn exit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    assert!(helpers.len()>=24);let start=circ.b.ops.len();let g=&helpers[0];let shuttle=&sm[3];let dirty=&helpers[2..];
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    exit_guard(circ,rank,sm,p1,p2,sign,g,dirty);
    for (x,y) in w1.iter().zip(w2) {circ.cx(y,x);circ.ccx(g,x,y);circ.cx(y,x);}
    // The old padding loan moved to Work2. S_mid[3] is0 under g, and
    // neither A update nor the A-address decoder observes it. Park cargo
    // here only across that interval, restoring it before interpreting S.
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w2,dirty,0);
    let a_start=circ.b.ops.len();
    super::metadata_Aupdate5::update(circ,rank,a,c,sm,g,w1,w2,dirty,lo,hi,false);
    for op in &circ.b.ops[a_start..] {
        let q=shuttle.id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes parked S bit");
    }
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w1,dirty,0);
    super::metadata_transfer5_compact::transfer(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,0,true);
    circ.cx(g,iteration);
    exit_guard(circ,rank,sm,p1,p2,sign,g,dirty);
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
fn exit_guard_signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,helpers:&[QReg]) {
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(p2,true)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,helpers);
    }
    let mut birth=vec![(p1,true),(p2,true)];birth.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));mixed_mcx(circ,&birth,g,helpers);
}
fn take_exit_head(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,passenger:&QReg,word:&[QReg],dirty:&[QReg]) {
    // C is positive on g. Prune C0 rather than aliasing another word position.
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v==0{None}else{Some(&word[259-v])}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let ops=circ.b.ops[start..].to_vec();circ.cswap(g,root,passenger);circ.cx(g,root);circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn exit_signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    exit_signless_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi,false);
}
pub(super) fn exit_phase_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    exit_signless_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi,true);
}
fn exit_signless_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize,cargo:bool) {
    assert!(helpers.len()>=23);let start=circ.b.ops.len();let g=&helpers[0];let shuttle=&sm[3];let dirty=&helpers[2..];
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    exit_guard_signless(circ,rank,a,c,sm,p1,p2,g,dirty);
    if super::metadata_muxlease::active("Q795_PHASE_LOAN"){super::q797_cargo_moves::exchange_a(circ,rank,a,w1,2,&sm[2],&[(g,true)],dirty);}
    if cargo {
        take_exit_head(circ,rank,c,g,&sm[0],w2,dirty);
    }
    for (i,(x,y)) in w1.iter().zip(w2).enumerate() {if !super::q796_parity::enabled()||i!=0&&i!=258{circ.cx(y,x);circ.ccx(g,x,y);circ.cx(y,x);}}
    if super::q796_parity::enabled(){super::q796_parity::cycle_swap(circ,&w1[0],&w2[0],&w2[258],g,dirty);}
    // The old padding loan moved to Work2. S_mid[3] is0 under g, and
    // neither A update nor the A-address decoder observes it. Park cargo
    // here only across that interval, restoring it before interpreting S.
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w2,dirty,0);
    if cargo {circ.cswap(g,&sm[0],&sm[1]);}
    let a_start=circ.b.ops.len();
    super::metadata_Aupdate5::update(circ,rank,a,c,sm,g,w1,w2,dirty,lo,hi,false);
    for op in &circ.b.ops[a_start..] {
        let q=shuttle.id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes parked S bit");
        if cargo {let q=sm[1].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes phase cargo");}
        if super::metadata_muxlease::active("Q795_PHASE_LOAN"){let q=sm[2].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes second phase cargo");}
    }
    if cargo {
        super::q797_cargo_moves::exchange_a(circ,rank,a,w1,0,&sm[1],&[(g,true)],dirty);
        circ.cx(g,&sm[1]); // New coefficient head was1; return S scratch to0.
    }
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w1,dirty,0);
    if super::metadata_muxlease::active("Q795_PHASE_LOAN"){super::q797_cargo_moves::exchange_a(circ,rank,a,w2,2,&sm[2],&[(g,true)],dirty);}
    // All four S_mid loans have now returned to zero on the exit guard.
    super::metadata_transfer5_compact::transfer_exit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty);
    circ.cx(g,iteration);
    exit_guard_signless(circ,rank,a,c,sm,p1,p2,g,dirty);
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
pub fn run() {
    if std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1") {count_supported();return;}
    let path=std::env::var("LOWQ_EXIT_BOUNDARY_CAPSULE").expect("explicit scalar entry capsule");
    let data=std::fs::read(path).expect("read entry capsule");assert_eq!(&data[..8],b"R5EXIT01");
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
    assert_eq!(data.len(),12+count*136);assert!(count>0&&count<=1_000_000);
    let mut total=0;
    for j in [0] {
        let rows:Vec<_>=data[12..].chunks_exact(136).collect();assert!(!rows.is_empty());
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);
        let helpers=circ.alloc_qreg_bits("borrowed",24);let owned=circ.b.next_qubit;
        exit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&iter,&w1,&w2,&helpers,0,256);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_EXIT_BOUNDARY5_BUILT j={j} T={} ops={} owned_inversion_wires=543 borrowed=24",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        for pattern in 0..4 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=0x79eb650f12a4dc38u64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let row=rows[(batch*64+lane)%rows.len()];
                for (w,record) in [(&mut before,&row[..68]),(&mut after,&row[68..136])] {
                    for i in 0..543 {put(w,i,lane,record[i/8]>>(i%8)&1!=0);}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after {let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("entry boundary j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        // Already-terminal phase00/Sign0 is identity for arbitrary history,
        // work data, and dirty helpers. The full terminal lifecycle is separate.
        for batch in 0..8 {
            let mut seed=0x8a145de782039b6fu64^batch;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {
                for i in 0..5 {put(&mut before,rank[i].id()as usize,lane,29>>i&1!=0);}
                for q in &a {put(&mut before,q.id()as usize,lane,true);}
                put(&mut before,w1[256].id()as usize,lane,false);
                for q in [&p1,&p2,&sign] {put(&mut before,q.id()as usize,lane,false);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_EXIT_BOUNDARY5_CASE j={j} scalar_records={} PASS",rows.len());
    }
    eprintln!("CODEC_EXIT_BOUNDARY5_PASS lanes={total} scalar_records={count}; funded exit guard, work swap, A update, C erasure, iteration parity and dirty restoration; S-zero phase flips and whole Q799 missing");
}

fn count_supported() {
    let lo:usize=std::env::var("LOWQ_CODEC_A_LO").unwrap().parse().unwrap();
    let hi:usize=std::env::var("LOWQ_CODEC_A_HI").unwrap().parse().unwrap();
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);
    let helpers=circ.alloc_qreg_bits("borrowed",24);let owned=circ.b.next_qubit;
    exit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&iter,&w1,&w2,&helpers,lo,hi);assert_eq!(circ.b.next_qubit,owned);
    eprintln!("CODEC_EXIT_BOUNDARY5_COUNT_ONLY lo={lo} hi={hi} T={} ops={} correctness_unchecked",circ.b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),circ.b.ops.len());
}
