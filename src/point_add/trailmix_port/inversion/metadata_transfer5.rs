//! Empty-C <-> residual-C recoding on rank5, with two phase-wire workspace bits.
//! Under independent guard: p1=p2=1; source first eligible one lies at i>=A_raw+2,
//! L=259-i, desired C=(L-S_raw) mod256 in1..255 and target rank is representable.
//! Forward starts with C0, inverse with that desired C. All lenders restore.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::{mixed_mcx,below_cubes};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_programs.rs"] mod programs;

fn rank_gate(circ:&mut Circuit,rank:&[QReg],terms:&[(u16,u16)],extra:&[(&QReg,bool)],out:&QReg,helpers:&[QReg]) {
    for &(m,v) in terms {
        let mut cs=extra.to_vec();cs.extend((0..5).filter(|&b|m>>b&1!=0).map(|b|(&rank[b],v>>b&1!=0)));
        mixed_mcx(circ,&cs,out,helpers);
    }
}
// XOR physical L modulo256, with zero for no eligible set bit. Rank C and S
// are never changed inside this linear oracle. The threshold is A_raw+2.
fn length_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],source:&[QReg],out:&[&QReg],guard:&QReg,prefix:&[QReg],helpers:&[QReg]) {
    assert_eq!(source.len(),259);assert_eq!(prefix.len(),259);assert_eq!(out.len(),8);
    let cell=|circ:&mut Circuit,i:usize| {
        let parent=if i==0{guard}else{&prefix[i-1]};circ.cx(parent,&prefix[i]);
        if i<2{return;}
        let bound=i-1;let high=bound/64;let low=bound%64;
        let extra=vec![(parent,true),(&source[i],true)];
        rank_gate(circ,rank,programs::A_BELOW[high],&extra,&prefix[i],helpers);
        if high<4 {
            for cube in below_cubes(6,low) {
                let mut cs=extra.clone();cs.extend(cube.iter().map(|&(b,v)|(&a[b],v)));
                rank_gate(circ,rank,programs::A_EQUAL[high],&cs,&prefix[i],helpers);
            }
        }
    };
    let zero_map=|circ:&mut Circuit| {
        for i in (1..259).rev(){cell(circ,i);}cell(circ,0);for i in 1..259{cell(circ,i);}
    };
    let writes=|circ:&mut Circuit| {
        for i in 0..259 {
            let delta=(259-i)^(258-i);
            for bit in 0..8 {if delta>>bit&1!=0 {circ.cx(&prefix[i],&out[bit]);}}
        }
    };
    for bit in 0..8 {if 259>>bit&1!=0 {circ.cx(guard,&out[bit]);}}
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
}
fn shift_add(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],word:&[&QReg],guard:&QReg,helpers:&[QReg],j:usize,inverse:bool) {
    let start=circ.b.ops.len();let low=(4-j)%4;
    for i in 0..8 {
        if i<2&&low>>i&1==0 {continue;}
        for k in (i..8).rev() {
            let mut cs=vec![(guard,true)];cs.extend(word[i..k].iter().map(|&q|(q,true)));
            if i<6 {if i>=2 {cs.push((&sm[i-2],true));}mixed_mcx(circ,&cs,&word[k],helpers);}
            else {rank_gate(circ,rank,programs::S_BIT[i-6],&cs,&word[k],helpers);}
        }
    }
    if inverse {circ.b.ops[start..].reverse();}
}
fn pack_high(circ:&mut Circuit,rank:&[QReg],high:&[&QReg],guard:&QReg,helpers:&[QReg]) {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for (left,t) in triples.iter().enumerate() {if t[1]!=0{continue;}
        for (right,u) in triples.iter().enumerate() {
            if u[0]!=t[0]||u[2]!=t[2]||u[1]==0{continue;}
            super::metadata_rank5::basis_swap(circ,rank,guard,&[(&high[0],u[1]&1!=0),(&high[1],u[1]&2!=0)],helpers,left,right);
        }
    }
    for bit in 0..2 {rank_gate(circ,rank,programs::C_BIT[bit],&[(guard,true)],&high[bit],helpers);}
}
pub(super) fn transfer(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(source).chain(prefix).chain(helpers).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),guard.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();circ.cx(guard,p1);circ.cx(guard,p2);
    let mut word:Vec<_>=c.iter().collect();word.extend([p1,p2]);
    length_xor(circ,rank,a,source,&word,guard,prefix,helpers);
    shift_add(circ,rank,sm,&word,guard,helpers,j,true);
    pack_high(circ,rank,&word[6..],guard,helpers);
    circ.cx(guard,p2);circ.cx(guard,p1);
    if inverse {circ.b.ops[start..].reverse();}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let count_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {for inverse in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("transfer.rank",5);let a=circ.alloc_qreg_bits("transfer.a",6);let c=circ.alloc_qreg_bits("transfer.c",6);let sm=circ.alloc_qreg_bits("transfer.sm",4);assert_eq!(circ.b.next_qubit,21);
        let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let guard=circ.alloc_qreg("independent_guard");let source=circ.alloc_qreg_bits("source",259);let prefix=circ.alloc_qreg_bits("dirty_word",259);let helpers=circ.alloc_qreg_bits("dirty_helpers",16);let owned=circ.b.next_qubit;
        transfer(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&guard,&source,&prefix,&helpers,j,inverse);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_TRANSFER5_BUILT j={j} inverse={inverse} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());if count_only{continue;}
        let mut cases=Vec::new();
        for (r,t) in triples.iter().enumerate() {if t[1]!=0{continue;}
            for sl in 0..16 {let sr=64*t[2]+4*sl+(4-j)%4;
                for ell in 1..258 {
                    if ell<=sr||ell+64*t[0]>257{continue;}
                    let diff=ell-sr;if diff>255&&!(sr==0&&ell==257){continue;}
                    let cv=diff%256;if cv==0{continue;}
                    let to=triples.iter().position(|q|*q==[t[0],cv>>6,t[2]]).unwrap();
                    let max_al=(257-ell-64*t[0]).min(63);
                    for al in [0,max_al] {for on in [false,true] {cases.push((r,to,64*t[0]+al,sl,ell,cv,on));}}
                }
            }
        }
        let batches=(cases.len()+63)/64;
        for batch in 0..batches {
            let mut seed=0x73591b2df68a40ceu64^batch as u64^((j as u64)<<32)^((inverse as u64)<<40);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let (r,to,av,sl,ell,cv,on)=cases[(batch*64+lane)%cases.len()];
                put(&mut before,&guard,lane,on);put(&mut after,&guard,lane,on);
                if !on{continue;}
                let (rin,rout,cin,cout)=if inverse{(to,r,cv&63,0)}else{(r,to,0,cv&63)};
                for i in 0..5{put(&mut before,&rank[i],lane,rin>>i&1!=0);put(&mut after,&rank[i],lane,rout>>i&1!=0);}
                for i in 0..6 {put(&mut before,&c[i],lane,cin>>i&1!=0);put(&mut after,&c[i],lane,cout>>i&1!=0);for w in [&mut before,&mut after]{put(w,&a[i],lane,av>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&p1,lane,true);put(w,&p2,lane,true);for i in av+2..259-ell {put(w,&source[i],lane,false);}put(w,&source[259-ell],lane,true);}
                if ell==257&&cv==1{wraps+=1;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("transfer j={j} inverse={inverse} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_TRANSFER5_CASE j={j} inverse={inverse} semantic_records={} PASS",cases.len());
    }}
    if count_only{eprintln!("CODEC_TRANSFER5_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_TRANSFER5_PASS lanes={total} S256_lanes={wraps}; phase-wire-funded length computation and rank packing, both directions, all lenders restored; caller boundary and full Q799 missing");
}
