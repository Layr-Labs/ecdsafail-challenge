//! Phase-entry C transfer from the proved three-position residual head.
//! Requires true S=bit_length(q)>=1 and p>3*2^254; not a generic exit oracle.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_compact_programs.rs"] mod programs;

fn permutation(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)]) {
    let affine=super::metadata_muxlease::active("Q793_AFFINE_ENTRY_HEAD");
    for &(left,right) in swaps {
        assert_ne!(left,right);
        if affine {super::metadata_rank5::affine_word_transposition(circ,word,&[(guard,true)],helpers,left,right);continue;}
        let mut value=left;let mut edges=Vec::new();
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
        let output_erase=super::metadata_muxlease::active("Q795_ENTRY_OUTPUT_ERASE");
        if output_erase {
            // Exact paired fanout: the old C0 offset cancels on every branch.
            circ.cx(&c[0],&c[1]);mixed_mcx(circ,&[(guard,true),(&c[4],false)],&c[1],helpers);
            mixed_mcx(circ,&[(guard,true),(&c[4],false),(root,true)],&c[0],helpers);circ.cx(&c[0],&c[1]);
        } else {
            mixed_mcx(circ,&[(guard,true),(&c[4],false),(root,true)],&c[0],helpers);
            mixed_mcx(circ,&[(guard,true),(&c[4],false),(root,false)],&c[1],helpers);
        }
        circ.b.ops.extend(gather.into_iter().rev());
        if output_erase {
            // On guard C_low started zero. The output is one-hot, and
            // first = 1 XOR C0 XOR C1, so it erases the saved first bit.
            // Explicit guard preserves arbitrary C data off branch.
            circ.cx(guard,&c[4]);circ.ccx(guard,&c[0],&c[4]);circ.ccx(guard,&c[1],&c[4]);
        } else {let (root,gather)=super::metadata_muxlease::gather_linear(circ,&address,&first);circ.ccx(guard,root,&c[4]);circ.b.ops.extend(gather.into_iter().rev());}
        return;
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
pub(super) const A_SUPPORTS:[(usize,usize);404]=[
    (0,5), // steps 1..4
    (0,5), // steps 5..8
    (0,7), // steps 9..12
    (0,7), // steps 13..16
    (0,9), // steps 17..20
    (0,9), // steps 21..24
    (0,11), // steps 25..28
    (0,11), // steps 29..32
    (0,13), // steps 33..36
    (0,13), // steps 37..40
    (0,15), // steps 41..44
    (0,15), // steps 45..48
    (0,17), // steps 49..52
    (0,17), // steps 53..56
    (0,19), // steps 57..60
    (0,19), // steps 61..64
    (0,21), // steps 65..68
    (0,21), // steps 69..72
    (0,23), // steps 73..76
    (0,23), // steps 77..80
    (0,25), // steps 81..84
    (0,25), // steps 85..88
    (0,27), // steps 89..92
    (0,27), // steps 93..96
    (0,29), // steps 97..100
    (0,29), // steps 101..104
    (0,31), // steps 105..108
    (0,31), // steps 109..112
    (0,33), // steps 113..116
    (0,33), // steps 117..120
    (0,35), // steps 121..124
    (0,35), // steps 125..128
    (0,37), // steps 129..132
    (0,37), // steps 133..136
    (0,39), // steps 137..140
    (0,39), // steps 141..144
    (0,41), // steps 145..148
    (0,41), // steps 149..152
    (0,43), // steps 153..156
    (0,43), // steps 157..160
    (0,45), // steps 161..164
    (0,45), // steps 165..168
    (0,47), // steps 169..172
    (0,47), // steps 173..176
    (0,49), // steps 177..180
    (0,49), // steps 181..184
    (0,51), // steps 185..188
    (0,51), // steps 189..192
    (0,53), // steps 193..196
    (0,53), // steps 197..200
    (0,55), // steps 201..204
    (0,55), // steps 205..208
    (0,57), // steps 209..212
    (0,57), // steps 213..216
    (0,59), // steps 217..220
    (0,59), // steps 221..224
    (0,61), // steps 225..228
    (0,61), // steps 229..232
    (0,63), // steps 233..236
    (0,63), // steps 237..240
    (0,65), // steps 241..244
    (0,65), // steps 245..248
    (0,67), // steps 249..252
    (0,67), // steps 253..256
    (0,69), // steps 257..260
    (0,69), // steps 261..264
    (0,71), // steps 265..268
    (0,71), // steps 269..272
    (0,73), // steps 273..276
    (0,73), // steps 277..280
    (0,75), // steps 281..284
    (0,75), // steps 285..288
    (0,77), // steps 289..292
    (0,77), // steps 293..296
    (0,79), // steps 297..300
    (0,79), // steps 301..304
    (0,81), // steps 305..308
    (0,81), // steps 309..312
    (0,83), // steps 313..316
    (0,83), // steps 317..320
    (0,85), // steps 321..324
    (0,85), // steps 325..328
    (0,87), // steps 329..332
    (0,87), // steps 333..336
    (0,89), // steps 337..340
    (0,89), // steps 341..344
    (0,91), // steps 345..348
    (0,91), // steps 349..352
    (0,93), // steps 353..356
    (0,93), // steps 357..360
    (0,95), // steps 361..364
    (0,95), // steps 365..368
    (0,97), // steps 369..372
    (0,97), // steps 373..376
    (0,99), // steps 377..380
    (0,99), // steps 381..384
    (0,101), // steps 385..388
    (0,101), // steps 389..392
    (0,103), // steps 393..396
    (0,103), // steps 397..400
    (0,105), // steps 401..404
    (0,105), // steps 405..408
    (0,107), // steps 409..412
    (0,107), // steps 413..416
    (0,109), // steps 417..420
    (0,109), // steps 421..424
    (0,111), // steps 425..428
    (0,111), // steps 429..432
    (0,113), // steps 433..436
    (0,113), // steps 437..440
    (0,115), // steps 441..444
    (0,115), // steps 445..448
    (0,117), // steps 449..452
    (0,117), // steps 453..456
    (0,119), // steps 457..460
    (0,119), // steps 461..464
    (0,121), // steps 465..468
    (0,121), // steps 469..472
    (0,123), // steps 473..476
    (0,123), // steps 477..480
    (0,125), // steps 481..484
    (0,125), // steps 485..488
    (0,127), // steps 489..492
    (0,127), // steps 493..496
    (0,129), // steps 497..500
    (0,129), // steps 501..504
    (0,131), // steps 505..508
    (0,131), // steps 509..512
    (0,133), // steps 513..516
    (0,133), // steps 517..520
    (0,135), // steps 521..524
    (0,135), // steps 525..528
    (0,137), // steps 529..532
    (0,137), // steps 533..536
    (0,139), // steps 537..540
    (0,139), // steps 541..544
    (0,141), // steps 545..548
    (0,141), // steps 549..552
    (0,143), // steps 553..556
    (0,143), // steps 557..560
    (0,145), // steps 561..564
    (0,145), // steps 565..568
    (0,147), // steps 569..572
    (0,147), // steps 573..576
    (0,149), // steps 577..580
    (0,149), // steps 581..584
    (0,151), // steps 585..588
    (0,151), // steps 589..592
    (0,153), // steps 593..596
    (0,153), // steps 597..600
    (0,155), // steps 601..604
    (0,155), // steps 605..608
    (0,157), // steps 609..612
    (0,157), // steps 613..616
    (0,159), // steps 617..620
    (0,159), // steps 621..624
    (0,161), // steps 625..628
    (0,161), // steps 629..632
    (0,163), // steps 633..636
    (0,163), // steps 637..640
    (0,165), // steps 641..644
    (0,165), // steps 645..648
    (0,167), // steps 649..652
    (0,167), // steps 653..656
    (0,169), // steps 657..660
    (0,169), // steps 661..664
    (0,171), // steps 665..668
    (0,171), // steps 669..672
    (0,173), // steps 673..676
    (0,173), // steps 677..680
    (0,175), // steps 681..684
    (0,175), // steps 685..688
    (0,177), // steps 689..692
    (0,177), // steps 693..696
    (0,179), // steps 697..700
    (0,179), // steps 701..704
    (0,181), // steps 705..708
    (0,181), // steps 709..712
    (0,183), // steps 713..716
    (0,183), // steps 717..720
    (0,185), // steps 721..724
    (0,185), // steps 725..728
    (0,187), // steps 729..732
    (0,187), // steps 733..736
    (0,189), // steps 737..740
    (0,189), // steps 741..744
    (0,191), // steps 745..748
    (0,191), // steps 749..752
    (0,193), // steps 753..756
    (0,193), // steps 757..760
    (0,195), // steps 761..764
    (0,195), // steps 765..768
    (0,197), // steps 769..772
    (0,197), // steps 773..776
    (0,199), // steps 777..780
    (0,199), // steps 781..784
    (0,201), // steps 785..788
    (0,201), // steps 789..792
    (0,203), // steps 793..796
    (0,203), // steps 797..800
    (0,205), // steps 801..804
    (0,205), // steps 805..808
    (0,207), // steps 809..812
    (0,207), // steps 813..816
    (0,209), // steps 817..820
    (0,209), // steps 821..824
    (0,211), // steps 825..828
    (0,211), // steps 829..832
    (0,213), // steps 833..836
    (0,213), // steps 837..840
    (0,215), // steps 841..844
    (0,215), // steps 845..848
    (0,217), // steps 849..852
    (0,217), // steps 853..856
    (0,219), // steps 857..860
    (0,219), // steps 861..864
    (0,221), // steps 865..868
    (0,221), // steps 869..872
    (0,223), // steps 873..876
    (0,223), // steps 877..880
    (0,225), // steps 881..884
    (0,225), // steps 885..888
    (0,227), // steps 889..892
    (0,227), // steps 893..896
    (0,229), // steps 897..900
    (0,229), // steps 901..904
    (0,231), // steps 905..908
    (0,231), // steps 909..912
    (0,233), // steps 913..916
    (0,233), // steps 917..920
    (0,235), // steps 921..924
    (0,235), // steps 925..928
    (0,237), // steps 929..932
    (0,237), // steps 933..936
    (0,239), // steps 937..940
    (0,239), // steps 941..944
    (0,241), // steps 945..948
    (0,241), // steps 949..952
    (0,243), // steps 953..956
    (0,243), // steps 957..960
    (0,245), // steps 961..964
    (0,245), // steps 965..968
    (0,247), // steps 969..972
    (0,247), // steps 973..976
    (0,249), // steps 977..980
    (0,249), // steps 981..984
    (0,251), // steps 985..988
    (0,251), // steps 989..992
    (0,253), // steps 993..996
    (0,253), // steps 997..1000
    (0,255), // steps 1001..1004
    (0,255), // steps 1005..1008
    (0,256), // steps 1009..1012
    (0,256), // steps 1013..1016
    (0,256), // steps 1017..1020
    (0,256), // steps 1021..1024
    (0,256), // steps 1025..1028
    (0,256), // steps 1029..1032
    (0,256), // steps 1033..1036
    (0,256), // steps 1037..1040
    (4,256), // steps 1041..1044
    (4,256), // steps 1045..1048
    (7,256), // steps 1049..1052
    (7,256), // steps 1053..1056
    (11,256), // steps 1057..1060
    (11,256), // steps 1061..1064
    (14,256), // steps 1065..1068
    (14,256), // steps 1069..1072
    (18,256), // steps 1073..1076
    (18,256), // steps 1077..1080
    (21,256), // steps 1081..1084
    (21,256), // steps 1085..1088
    (25,256), // steps 1089..1092
    (25,256), // steps 1093..1096
    (28,256), // steps 1097..1100
    (28,256), // steps 1101..1104
    (31,256), // steps 1105..1108
    (31,256), // steps 1109..1112
    (35,256), // steps 1113..1116
    (35,256), // steps 1117..1120
    (38,256), // steps 1121..1124
    (38,256), // steps 1125..1128
    (42,256), // steps 1129..1132
    (42,256), // steps 1133..1136
    (45,256), // steps 1137..1140
    (45,256), // steps 1141..1144
    (49,256), // steps 1145..1148
    (49,256), // steps 1149..1152
    (52,256), // steps 1153..1156
    (52,256), // steps 1157..1160
    (56,256), // steps 1161..1164
    (56,256), // steps 1165..1168
    (59,256), // steps 1169..1172
    (59,256), // steps 1173..1176
    (63,256), // steps 1177..1180
    (63,256), // steps 1181..1184
    (66,256), // steps 1185..1188
    (66,256), // steps 1189..1192
    (69,256), // steps 1193..1196
    (69,256), // steps 1197..1200
    (73,256), // steps 1201..1204
    (73,256), // steps 1205..1208
    (76,256), // steps 1209..1212
    (76,256), // steps 1213..1216
    (80,256), // steps 1217..1220
    (80,256), // steps 1221..1224
    (83,256), // steps 1225..1228
    (83,256), // steps 1229..1232
    (87,256), // steps 1233..1236
    (87,256), // steps 1237..1240
    (90,256), // steps 1241..1244
    (90,256), // steps 1245..1248
    (94,256), // steps 1249..1252
    (94,256), // steps 1253..1256
    (97,256), // steps 1257..1260
    (97,256), // steps 1261..1264
    (101,256), // steps 1265..1268
    (101,256), // steps 1269..1272
    (104,256), // steps 1273..1276
    (104,256), // steps 1277..1280
    (107,256), // steps 1281..1284
    (107,256), // steps 1285..1288
    (111,256), // steps 1289..1292
    (111,256), // steps 1293..1296
    (114,256), // steps 1297..1300
    (114,256), // steps 1301..1304
    (118,256), // steps 1305..1308
    (118,256), // steps 1309..1312
    (121,256), // steps 1313..1316
    (121,256), // steps 1317..1320
    (125,256), // steps 1321..1324
    (125,256), // steps 1325..1328
    (128,256), // steps 1329..1332
    (128,256), // steps 1333..1336
    (132,256), // steps 1337..1340
    (132,256), // steps 1341..1344
    (135,256), // steps 1345..1348
    (135,256), // steps 1349..1352
    (139,256), // steps 1353..1356
    (139,256), // steps 1357..1360
    (142,256), // steps 1361..1364
    (142,256), // steps 1365..1368
    (145,256), // steps 1369..1372
    (145,256), // steps 1373..1376
    (149,256), // steps 1377..1380
    (149,256), // steps 1381..1384
    (152,256), // steps 1385..1388
    (152,256), // steps 1389..1392
    (156,256), // steps 1393..1396
    (156,256), // steps 1397..1400
    (159,256), // steps 1401..1404
    (159,256), // steps 1405..1408
    (163,256), // steps 1409..1412
    (163,256), // steps 1413..1416
    (166,256), // steps 1417..1420
    (166,256), // steps 1421..1424
    (170,256), // steps 1425..1428
    (170,256), // steps 1429..1432
    (173,256), // steps 1433..1436
    (173,256), // steps 1437..1440
    (177,256), // steps 1441..1444
    (177,256), // steps 1445..1448
    (180,256), // steps 1449..1452
    (180,256), // steps 1453..1456
    (183,256), // steps 1457..1460
    (183,256), // steps 1461..1464
    (187,256), // steps 1465..1468
    (187,256), // steps 1469..1472
    (190,256), // steps 1473..1476
    (190,256), // steps 1477..1480
    (194,256), // steps 1481..1484
    (194,256), // steps 1485..1488
    (197,256), // steps 1489..1492
    (197,256), // steps 1493..1496
    (201,256), // steps 1497..1500
    (201,256), // steps 1501..1504
    (204,256), // steps 1505..1508
    (204,256), // steps 1509..1512
    (208,256), // steps 1513..1516
    (208,256), // steps 1517..1520
    (211,256), // steps 1521..1524
    (211,256), // steps 1525..1528
    (215,256), // steps 1529..1532
    (215,256), // steps 1533..1536
    (218,256), // steps 1537..1540
    (218,256), // steps 1541..1544
    (221,256), // steps 1545..1548
    (221,256), // steps 1549..1552
    (225,256), // steps 1553..1556
    (225,256), // steps 1557..1560
    (228,256), // steps 1561..1564
    (228,256), // steps 1565..1568
    (232,256), // steps 1569..1572
    (232,256), // steps 1573..1576
    (235,256), // steps 1577..1580
    (235,256), // steps 1581..1584
    (239,256), // steps 1585..1588
    (239,256), // steps 1589..1592
    (242,256), // steps 1593..1596
    (242,256), // steps 1597..1600
    (246,256), // steps 1601..1604
    (246,256), // steps 1605..1608
    (249,256), // steps 1609..1612
    (249,256), // steps 1613..1616
];
