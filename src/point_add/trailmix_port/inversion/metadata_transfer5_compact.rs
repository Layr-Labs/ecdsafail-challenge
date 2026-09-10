//! Rank5 transfer using a temporary four-bit (A_high,S_high) representation.
//! C_high0 frees rank[4] as conditional clean scratch; no extra qubits.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_compact_programs.rs"] mod programs;

fn permutation(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)]) {
    permutation_inner(circ,word,guard,helpers,swaps,None);
}
fn permutation_inner(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)],scratch:Option<&[QReg]>) {
    let flag=if word.len()==5{"Q794_EXIT_UNPACK_AFFINE"}else{"Q794_EXIT_PACK_AFFINE"};
    if scratch.is_some()&&super::metadata_muxlease::active(flag){for &(left,right) in swaps{super::q794_affine_frames::swap(circ,word,guard,&[],helpers,left,right,scratch);}return;}
    for &(left,right) in swaps {
        assert_ne!(left,right);let mut value=left;let mut edges=Vec::new();
        for bit in 0..word.len(){if (left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}
        assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
        for (bit,value) in edges {
            let mut cs=vec![(guard,true)];cs.extend((0..word.len()).filter(|&i|i!=bit).map(|i|(word[i],value>>i&1!=0)));
            if let Some(s)=scratch{exit_guarded_toggle(circ,guard,&cs[1..],word[bit],s,helpers);}else{mixed_mcx(circ,&cs,word[bit],helpers);}
        }
    }
}
// All four S bits are zero on the independent exit guard before and after
// each rank-permutation edge. The sole target action retains that guard.
pub(super) fn exit_guarded_toggle(circ:&mut Circuit,guard:&QReg,cs:&[(&QReg,bool)],out:&QReg,scratch:&[QReg],helpers:&[QReg]) {
    assert!(cs.len()>=2);let n=(cs.len()-1).min(scratch.len());assert!(n>0);
    for &(q,v) in cs{if !v{circ.x(q);}}
    circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    for i in 2..=n{circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
    let action:Vec<_>=std::iter::once((guard,true)).chain(std::iter::once((&scratch[n-1],true))).chain(cs[n+1..].iter().map(|&(q,_)|(q,true))).collect();
    mixed_mcx(circ,&action,out,helpers);
    for i in (2..=n).rev(){circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
    circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    for &(q,v) in cs.iter().rev(){if !v{circ.x(q);}}
}
fn clean(circ:&mut Circuit,guard:&QReg,scratch:&QReg,helpers:&[QReg],controls:&[(&QReg,bool)],out:&QReg) {
    let others:Vec<_>=controls.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();
    assert!(controls.iter().all(|(q,v)|q.id()!=guard.id()||*v));
    super::conditional_mcx::guarded(circ,guard,&others,out,scratch,false,&helpers[0]);
}
// Pure target-toggle extension for arbitrary scratch, exact conjunction when
// scratch is zero. Every intermediate lender restores, including off guard.
fn exit_clean_toggle(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,scratch:&[QReg]) {
    assert!((2..=5).contains(&cs.len()));assert!(scratch.len()>=cs.len()-2);
    for &(q,v) in cs{if !v{circ.x(q);}}
    if cs.len()==2{circ.ccx(cs[0].0,cs[1].0,out);}else{
        circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
        for i in 2..cs.len()-1{circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
        circ.ccx(&scratch[cs.len()-3],cs[cs.len()-1].0,out);
        for i in (2..cs.len()-1).rev(){circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
        circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    }
    for &(q,v) in cs.iter().rev(){if !v{circ.x(q);}}
}
fn length_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],source:&[QReg],out:&[&QReg],guard:&QReg,prefix:&[QReg],helpers:&[QReg],exit_cache:Option<(&[QReg],usize)>) {
    let mut boundary:Vec<_>=a.iter().collect();boundary.extend([&rank[0],&rank[1]]);let mask=&rank[4];
    let cache_key=std::cell::Cell::new(None);
    let cache_toggle=|circ:&mut Circuit,value:usize|{let(sm,bits)=exit_cache.unwrap();let cs:Vec<_>=boundary[8-bits..].iter().enumerate().map(|(i,&q)|(q,value>>i&1!=0)).collect();exit_clean_toggle(circ,&cs,&sm[0],&sm[1..]);};
    // On guard1 the unused bit starts0. On guard0 it can be arbitrary:
    // the prefix conjugation has root0 and is identity for either mask offset.
    let update=|circ:&mut Circuit,i:usize| {
        if !(2..=257).contains(&i){return;}
        let value=i-2;
        if let Some((sm,bits))=exit_cache{
            let key=value>>(8-bits);if cache_key.get()!=Some(key){if let Some(old)=cache_key.get(){cache_toggle(circ,old);}cache_toggle(circ,key);cache_key.set(Some(key));}
            let controls:Vec<_>=std::iter::once((&sm[0],true)).chain(boundary[..8-bits].iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0))).collect();
            exit_clean_toggle(circ,&controls,mask,&sm[1..]);
        }else{
            let controls:Vec<_>=boundary.iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0)).collect();
            mixed_mcx(circ,&controls,mask,helpers);
        }
    };
    let cell=|circ:&mut Circuit,i:usize| {
        let parent=if i==0{guard}else{&prefix[i-1]};circ.cx(parent,&prefix[i]);
        if i>0 {if i==258&&super::q796_parity::enabled(){mixed_mcx(circ,&[(parent,true),(mask,true)],&prefix[i],helpers);}else{mixed_mcx(circ,&[(parent,true),(&source[i],true),(mask,true)],&prefix[i],helpers);}}
    };
    let zero_map=|circ:&mut Circuit| {
        circ.x(mask);
        for i in (1..259).rev(){cell(circ,i);update(circ,i);}
        cell(circ,0);
        for i in 1..259{update(circ,i);cell(circ,i);}
        circ.x(mask);
    };
    let writes=|circ:&mut Circuit| {
        for i in 0..259{let delta=(259-i)^(258-i);for bit in 0..8{if delta>>bit&1!=0{circ.cx(&prefix[i],out[bit]);}}}
    };
    for bit in 0..8{if 259>>bit&1!=0{circ.cx(guard,out[bit]);}}
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
    if let Some(key)=cache_key.take(){cache_toggle(circ,key);}
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
    transfer_inner(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,j,inverse,false);
}
/// Exit caller has restored all four S_mid cargo loans and proves S=0.
pub(super) fn transfer_exit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg]) {
    transfer_inner(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,0,true,true);
}
fn transfer_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool,is_exit:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert_eq!(source.len(),259);assert_eq!(prefix.len(),259);assert!(helpers.len()>=16);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(source).chain(prefix).chain(helpers).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),guard.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();circ.cx(guard,p1);circ.cx(guard,p2);
    let mut word:Vec<_>=c.iter().collect();word.extend([p1,p2]);let mut high:Vec<_>=rank.iter().collect();
    let perm_scratch=if is_exit&&super::metadata_muxlease::active("Q795_EXIT_PERM_CLEAN"){Some(sm)}else{None};
    permutation_inner(circ,&high,guard,helpers,programs::UNPACK_SWAPS,perm_scratch);
    let cache_bits=if is_exit{std::env::var("Q795_EXIT_PREFIX").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(0)}else{0};assert!(cache_bits==0||cache_bits==4||cache_bits==5);
    length_xor(circ,rank,a,source,&word,guard,prefix,helpers,if cache_bits==0{None}else{Some((sm,cache_bits))});
    shift_add(circ,rank,sm,&word,guard,helpers,j);
    high.extend([p1,p2]);permutation_inner(circ,&high,guard,helpers,programs::PACK_SWAPS,perm_scratch);
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
    eprintln!("CODEC_TRANSFER5_COMPACT_PERM_PASS lanes=640; total5bit/7bit extension and inverse");
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
/// Dedicated is_exit=true check: every A boundary, scalar C removal, arbitrary
/// source/prefix/helper data and entirely arbitrary off-guard S scratch.
pub fn run_exit() {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let cases:Vec<_>=(0..256).flat_map(|a|(1..=255.min(257-a)).map(move|c|(a,c))).collect();
    let mut seen=[false;256];let mut total=0;
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("exit.rank",5);let a=circ.alloc_qreg_bits("exit.a",6);let c=circ.alloc_qreg_bits("exit.c",6);let sm=circ.alloc_qreg_bits("exit.sm",4);
    let p1=circ.alloc_qreg("exit.p1");let p2=circ.alloc_qreg("exit.p2");let g=circ.alloc_qreg("exit.guard");let source=circ.alloc_qreg_bits("exit.source",259);let prefix=circ.alloc_qreg_bits("exit.prefix",259);let helpers=circ.alloc_qreg_bits("exit.helpers",16);let owned=circ.b.next_qubit;
    transfer_exit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&g,&source,&prefix,&helpers);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
    for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
    eprintln!("EXIT_TRANSFER_BUILT ops={} T={} owned={owned}",b.ops.len(),b.ops.iter().filter(|op|op.kind==OperationType::CCX).count());
    for pattern in 0..4{for batch in 0..(2*cases.len()).div_ceil(64){
        let mut seed=0xa21c740985de631bu64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
        for lane in 0..64{
            let k=batch*64+lane;let(av,cv)=cases[(k/2)%cases.len()];let on=k%2==1;
            for w in [&mut before,&mut after]{put(w,&g,lane,on);}if !on{continue;}seen[av]=true;
            let rin=triples.iter().position(|t|*t==[av>>6,cv>>6,0]).unwrap();let rout=triples.iter().position(|t|*t==[av>>6,0,0]).unwrap();
            for i in 0..5{put(&mut before,&rank[i],lane,rin>>i&1!=0);put(&mut after,&rank[i],lane,rout>>i&1!=0);}
            for i in 0..6{for w in [&mut before,&mut after]{put(w,&a[i],lane,av>>i&1!=0);}put(&mut before,&c[i],lane,cv>>i&1!=0);put(&mut after,&c[i],lane,false);}
            for w in [&mut before,&mut after]{for q in &sm{put(w,q,lane,false);}put(w,&p1,lane,true);put(w,&p2,lane,true);for i in av+2..259-cv{put(w,&source[i],lane,false);}put(w,&source[259-cv],lane,true);}
        }
        let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
        if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("exit transfer pattern={pattern} batch={batch} diffs={diffs:?}");}
        assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}
    assert!(seen.into_iter().all(|v|v));eprintln!("EXIT_TRANSFER_PASS lanes={total} A_boundaries=256 semantic_pairs={}; scalar S0 C removal, arbitrary offguard metadata and all source/prefix/helper restoration, zero phase and literal inverse",cases.len());
}
pub fn run() {
    let count_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    if !count_only{check_permutations();}
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {for inverse in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("transfer.rank",5);let a=circ.alloc_qreg_bits("transfer.a",6);let c=circ.alloc_qreg_bits("transfer.c",6);let sm=circ.alloc_qreg_bits("transfer.sm",4);assert_eq!(circ.b.next_qubit,21);
        let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let guard=circ.alloc_qreg("independent_guard");let source=circ.alloc_qreg_bits("source",259);let prefix=circ.alloc_qreg_bits("dirty_word",259);let helpers=circ.alloc_qreg_bits("dirty_helpers",16);let owned=circ.b.next_qubit;
        transfer(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&guard,&source,&prefix,&helpers,j,inverse);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_TRANSFER5_COMPACT_BUILT j={j} inverse={inverse} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());if count_only{continue;}
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
        eprintln!("CODEC_TRANSFER5_COMPACT_CASE j={j} inverse={inverse} semantic_records={} PASS",cases.len());
    }}
    if count_only{eprintln!("CODEC_TRANSFER5_COMPACT_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_TRANSFER5_COMPACT_PASS lanes={total} S256_lanes={wraps}; phase-wire-funded length computation and rank packing, both directions, all lenders restored; caller boundary and full Q799 missing");
}
