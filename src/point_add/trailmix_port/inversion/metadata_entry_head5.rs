//! Phase-entry C transfer from the proved three-position residual head.
//! Requires true S=bit_length(q)>=1 and p>3*2^254; not a generic exit oracle.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_compact_programs.rs"] mod programs;

fn permutation(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)]) {
    for &(left,right) in swaps {
        assert_ne!(left,right);let mut value=left;let mut edges=Vec::new();
        for bit in 0..word.len(){if (left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}
        assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
        for (bit,value) in edges {
            let mut cs=vec![(guard,true)];cs.extend((0..word.len()).filter(|&i|i!=bit).map(|i|(word[i],value>>i&1!=0)));
            mixed_mcx(circ,&cs,word[bit],helpers);
        }
    }
}
fn clean(circ:&mut Circuit,guard:&QReg,scratch:&QReg,helpers:&[QReg],controls:&[(&QReg,bool)],out:&QReg) {
    let others:Vec<_>=controls.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();
    assert!(controls.iter().all(|(q,v)|q.id()!=guard.id()||*v));
    super::conditional_mcx::guarded(circ,guard,&others,out,scratch,false,&helpers[0]);
}
fn head_delta(circ:&mut Circuit,rank:&[QReg],a:&[QReg],source:&[QReg],c:&[QReg],guard:&QReg,helpers:&[QReg],lo:usize,hi:usize) {
    let mut address:Vec<_>=a.iter().collect();address.extend([&rank[0],&rank[1]]);
    if super::metadata_muxlease::active("Q799_HEAD_TREE"){
        // C4, like the existing C5 scratch, is zero under the transfer guard.
        // Save the first selected bit, inspect its neighbour, then uncompute.
        // The A support is exactly the caller's pre-existing lo..hi proof.
        let first:Vec<_>=(lo..hi.min(255)).map(|v|(v,&source[v+2])).collect();
        let second:Vec<_>=(lo..hi.min(255)).map(|v|(v,&source[v+3])).collect();
        if first.is_empty(){return;}
        let (root,gather)=super::metadata_muxlease::gather_linear(circ,&address,&first);circ.ccx(guard,root,&c[4]);circ.b.ops.extend(gather.into_iter().rev());
        let (root,gather)=super::metadata_muxlease::gather_linear(circ,&address,&second);
        mixed_mcx(circ,&[(guard,true),(&c[4],false),(root,true)],&c[0],helpers);
        mixed_mcx(circ,&[(guard,true),(&c[4],false),(root,false)],&c[1],helpers);circ.b.ops.extend(gather.into_iter().rev());
        let (root,gather)=super::metadata_muxlease::gather_linear(circ,&address,&first);circ.ccx(guard,root,&c[4]);circ.b.ops.extend(gather.into_iter().rev());return;
    }
    // Under guard1, C_low is still0; c[5] is untouched scratch during these writes.
    // For rawA0..254 the first residual one is at rawA+2, +3 or +4.
    for av in lo..hi.min(255) {
        let mut cs:Vec<_>=address.iter().enumerate().map(|(i,&q)|(q,av>>i&1!=0)).collect();
        cs.push((&source[av+2],false));
        for (out,polarity) in [(&c[0],true),(&c[1],false)] {
            cs.push((&source[av+3],polarity));
            clean(circ,guard,&c[5],helpers,&cs,out);
            cs.pop();
        }
    }
}
fn complement_and_subtract_a(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[&QReg],guard:&QReg,helpers:&[QReg]) {
    // ~delta + 2 = 257-delta (mod256), then subtract rawA.
    for &q in word {circ.cx(guard,q);}
    for k in (1..8).rev() {
        let cs:Vec<_>=word[1..k].iter().map(|&q|(q,true)).collect();
        clean(circ,guard,&rank[4],helpers,&cs,word[k]);
    }
    let start=circ.b.ops.len();
    for i in 0..8 {for k in (i..8).rev() {
        let mut cs:Vec<_>=word[i..k].iter().map(|&q|(q,true)).collect();
        cs.push((if i<6 {&a[i]} else {&rank[i-6]},true));
        clean(circ,guard,&rank[4],helpers,&cs,word[k]);
    }}
    circ.b.ops[start..].reverse();
}
fn shift_add(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],word:&[&QReg],guard:&QReg,helpers:&[QReg],j:usize) {
    let start=circ.b.ops.len();let low=(4-j)%4;
    for i in 0..8 {
        if i<2&&low>>i&1==0{continue;}
        for k in (i..8).rev() {
            let mut cs=Vec::new();cs.extend(word[i..k].iter().map(|&q|(q,true)));
            if i>=2 {cs.push((if i<6{&sm[i-2]}else{&rank[i-4]},true));}
            clean(circ,guard,&rank[4],helpers,&cs,word[k]);
        }
    }
    circ.b.ops[start..].reverse();
}
pub(super) fn transfer(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool) {
    transfer_with_support(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,j,inverse,0,256);
}
pub(super) fn transfer_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool,lo:usize,hi:usize) {
    assert!(lo<hi&&hi<=256);
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert_eq!(source.len(),259);assert_eq!(prefix.len(),259);assert!(helpers.len()>=16);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(source).chain(prefix).chain(helpers).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),guard.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();circ.cx(guard,p1);circ.cx(guard,p2);
    let mut word:Vec<_>=c.iter().collect();word.extend([p1,p2]);let mut high:Vec<_>=rank.iter().collect();
    permutation(circ,&high,guard,helpers,programs::UNPACK_SWAPS);
    head_delta(circ,rank,a,source,c,guard,helpers,lo,hi);
    complement_and_subtract_a(circ,rank,a,&word,guard,helpers);
    shift_add(circ,rank,sm,&word,guard,helpers,j);
    high.extend([p1,p2]);permutation(circ,&high,guard,helpers,programs::PACK_SWAPS);
    circ.cx(guard,p2);circ.cx(guard,p1);
    if inverse{circ.b.ops[start..].reverse();}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
fn check_permutations() {
    for (width,swaps,mapping) in [(5,programs::UNPACK_SWAPS,programs::UNPACK_MAP),(7,programs::PACK_SWAPS,programs::PACK_MAP)] {
        let mut circ=Circuit::new();let qs=circ.alloc_qreg_bits("permutation",width);let guard=circ.alloc_qreg("guard");let helpers=circ.alloc_qreg_bits("dirty",16);let owned=circ.b.next_qubit;
        permutation(&mut circ,&qs.iter().collect::<Vec<_>>(),&guard,&helpers,swaps);let b=circ.into_builder();
        for pattern in 0..2 {for batch in 0..((1usize<<width)*2/64) {
            let mut seed=0x859c72d81fe634b1^batch as u64^((pattern as u64)<<30);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let k=batch*64+lane;let value=k&((1<<width)-1);let on=k>>width&1!=0;let want=if on{mapping[value]}else{value};
                for bit in 0..width {put(&mut before,&qs[bit],lane,value>>bit&1!=0);put(&mut after,&qs[bit],lane,want>>bit&1!=0);}for w in [&mut before,&mut after]{put(w,&guard,lane,on);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
        }}
    }
    eprintln!("CODEC_ENTRY_HEAD5_PERM_PASS lanes=640; total5bit/7bit extension and inverse");
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let lo:usize=std::env::var("LOWQ_CODEC_A_LO").ok().map(|s|s.parse().unwrap()).unwrap_or(0);
    let hi:usize=std::env::var("LOWQ_CODEC_A_HI").ok().map(|s|s.parse().unwrap()).unwrap_or(256);
    assert!(lo<hi&&hi<=256);
    let count_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    if !count_only{check_permutations();}
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {for inverse in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("transfer.rank",5);let a=circ.alloc_qreg_bits("transfer.a",6);let c=circ.alloc_qreg_bits("transfer.c",6);let sm=circ.alloc_qreg_bits("transfer.sm",4);assert_eq!(circ.b.next_qubit,21);
        let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let guard=circ.alloc_qreg("independent_guard");let source=circ.alloc_qreg_bits("source",259);let prefix=circ.alloc_qreg_bits("dirty_word",259);let helpers=circ.alloc_qreg_bits("dirty_helpers",16);let owned=circ.b.next_qubit;
        transfer_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&guard,&source,&prefix,&helpers,j,inverse,lo,hi);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_ENTRY_HEAD5_BUILT j={j} inverse={inverse} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());if count_only{continue;}
        let mut cases=Vec::new();
        for av in lo..hi.min(255) {for st in 1..=256 {
            let sr=st%256;
            if sr%4!=(4-j)%4 {continue;}
            for delta in 0..3 {
                if av+st+delta>=257 {continue;}
                let cv=257-av-st-delta;
                if cv>255 {continue;}
                let r=triples.iter().position(|q|*q==[av>>6,0,sr>>6]).unwrap();
                let to=triples.iter().position(|q|*q==[av>>6,cv>>6,sr>>6]).unwrap();
                let sl=(sr%64)>>2;let ell=cv+st;
                for on in [false,true] {cases.push((r,to,av,sl,ell,cv,on));}
            }
        }}
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
        eprintln!("CODEC_ENTRY_HEAD5_CASE j={j} inverse={inverse} semantic_records={} PASS",cases.len());
    }}
    if count_only{eprintln!("CODEC_ENTRY_HEAD5_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_ENTRY_HEAD5_PASS lanes={total} S256_lanes={wraps}; two addressed head bits and rank packing, both directions, all lenders restored; caller boundary and full Q799 missing");
}

/// Monotone length bounds extend from old/new cycle-exit A to the entire cycle.
/// See metadata-entry-support-proof.md; bounds are outward-rounded per64 steps.
pub(super) const A_SUPPORTS:[(usize,usize);26]=[
    (0,19),
    (0,35),
    (0,51),
    (0,67),
    (0,83),
    (0,99),
    (0,115),
    (0,131),
    (0,147),
    (0,163),
    (0,179),
    (0,195),
    (0,211),
    (0,227),
    (0,243),
    (0,256),
    (0,256),
    (25,256),
    (52,256),
    (80,256),
    (107,256),
    (135,256),
    (163,256),
    (190,256),
    (218,256),
    (246,256),
];
