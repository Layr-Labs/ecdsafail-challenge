//! Phase-entry C transfer from the proved three-position residual head.
//! Requires true S=bit_length(q)>=1 and p>3*2^254; not a generic exit oracle.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_compact_programs.rs"] mod programs;
#[path="q794_entry_numeric.rs"] pub(crate) mod numeric;

fn permutation(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)]) {
    let flag=if word.len()==5{"Q794_ENTRY_UNPACK_AFFINE"}else{"Q794_ENTRY_PACK_AFFINE"};
    if super::metadata_muxlease::active(flag){for &(left,right) in swaps{super::q794_affine_frames::swap(circ,word,guard,&[],helpers,left,right,None);}return;}
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
    if numeric::enabled(){numeric::transfer(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,j,inverse,lo,hi);return;}
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
pub(super) const A_SUPPORTS:[(usize,usize);202]=[
    (0,5), // steps 1..8
    (0,7), // steps 9..16
    (0,9), // steps 17..24
    (0,11), // steps 25..32
    (0,13), // steps 33..40
    (0,15), // steps 41..48
    (0,17), // steps 49..56
    (0,19), // steps 57..64
    (0,21), // steps 65..72
    (0,23), // steps 73..80
    (0,25), // steps 81..88
    (0,27), // steps 89..96
    (0,29), // steps 97..104
    (0,31), // steps 105..112
    (0,33), // steps 113..120
    (0,35), // steps 121..128
    (0,37), // steps 129..136
    (0,39), // steps 137..144
    (0,41), // steps 145..152
    (0,43), // steps 153..160
    (0,45), // steps 161..168
    (0,47), // steps 169..176
    (0,49), // steps 177..184
    (0,51), // steps 185..192
    (0,53), // steps 193..200
    (0,55), // steps 201..208
    (0,57), // steps 209..216
    (0,59), // steps 217..224
    (0,61), // steps 225..232
    (0,63), // steps 233..240
    (0,65), // steps 241..248
    (0,67), // steps 249..256
    (0,69), // steps 257..264
    (0,71), // steps 265..272
    (0,73), // steps 273..280
    (0,75), // steps 281..288
    (0,77), // steps 289..296
    (0,79), // steps 297..304
    (0,81), // steps 305..312
    (0,83), // steps 313..320
    (0,85), // steps 321..328
    (0,87), // steps 329..336
    (0,89), // steps 337..344
    (0,91), // steps 345..352
    (0,93), // steps 353..360
    (0,95), // steps 361..368
    (0,97), // steps 369..376
    (0,99), // steps 377..384
    (0,101), // steps 385..392
    (0,103), // steps 393..400
    (0,105), // steps 401..408
    (0,107), // steps 409..416
    (0,109), // steps 417..424
    (0,111), // steps 425..432
    (0,113), // steps 433..440
    (0,115), // steps 441..448
    (0,117), // steps 449..456
    (0,119), // steps 457..464
    (0,121), // steps 465..472
    (0,123), // steps 473..480
    (0,125), // steps 481..488
    (0,127), // steps 489..496
    (0,129), // steps 497..504
    (0,131), // steps 505..512
    (0,133), // steps 513..520
    (0,135), // steps 521..528
    (0,137), // steps 529..536
    (0,139), // steps 537..544
    (0,141), // steps 545..552
    (0,143), // steps 553..560
    (0,145), // steps 561..568
    (0,147), // steps 569..576
    (0,149), // steps 577..584
    (0,151), // steps 585..592
    (0,153), // steps 593..600
    (0,155), // steps 601..608
    (0,157), // steps 609..616
    (0,159), // steps 617..624
    (0,161), // steps 625..632
    (0,163), // steps 633..640
    (0,165), // steps 641..648
    (0,167), // steps 649..656
    (0,169), // steps 657..664
    (0,171), // steps 665..672
    (0,173), // steps 673..680
    (0,175), // steps 681..688
    (0,177), // steps 689..696
    (0,179), // steps 697..704
    (0,181), // steps 705..712
    (0,183), // steps 713..720
    (0,185), // steps 721..728
    (0,187), // steps 729..736
    (0,189), // steps 737..744
    (0,191), // steps 745..752
    (0,193), // steps 753..760
    (0,195), // steps 761..768
    (0,197), // steps 769..776
    (0,199), // steps 777..784
    (0,201), // steps 785..792
    (0,203), // steps 793..800
    (0,205), // steps 801..808
    (0,207), // steps 809..816
    (0,209), // steps 817..824
    (0,211), // steps 825..832
    (0,213), // steps 833..840
    (0,215), // steps 841..848
    (0,217), // steps 849..856
    (0,219), // steps 857..864
    (0,221), // steps 865..872
    (0,223), // steps 873..880
    (0,225), // steps 881..888
    (0,227), // steps 889..896
    (0,229), // steps 897..904
    (0,231), // steps 905..912
    (0,233), // steps 913..920
    (0,235), // steps 921..928
    (0,237), // steps 929..936
    (0,239), // steps 937..944
    (0,241), // steps 945..952
    (0,243), // steps 953..960
    (0,245), // steps 961..968
    (0,247), // steps 969..976
    (0,249), // steps 977..984
    (0,251), // steps 985..992
    (0,253), // steps 993..1000
    (0,255), // steps 1001..1008
    (0,256), // steps 1009..1016
    (0,256), // steps 1017..1024
    (0,256), // steps 1025..1032
    (0,256), // steps 1033..1040
    (4,256), // steps 1041..1048
    (7,256), // steps 1049..1056
    (11,256), // steps 1057..1064
    (14,256), // steps 1065..1072
    (18,256), // steps 1073..1080
    (21,256), // steps 1081..1088
    (25,256), // steps 1089..1096
    (28,256), // steps 1097..1104
    (31,256), // steps 1105..1112
    (35,256), // steps 1113..1120
    (38,256), // steps 1121..1128
    (42,256), // steps 1129..1136
    (45,256), // steps 1137..1144
    (49,256), // steps 1145..1152
    (52,256), // steps 1153..1160
    (56,256), // steps 1161..1168
    (59,256), // steps 1169..1176
    (63,256), // steps 1177..1184
    (66,256), // steps 1185..1192
    (69,256), // steps 1193..1200
    (73,256), // steps 1201..1208
    (76,256), // steps 1209..1216
    (80,256), // steps 1217..1224
    (83,256), // steps 1225..1232
    (87,256), // steps 1233..1240
    (90,256), // steps 1241..1248
    (94,256), // steps 1249..1256
    (97,256), // steps 1257..1264
    (101,256), // steps 1265..1272
    (104,256), // steps 1273..1280
    (107,256), // steps 1281..1288
    (111,256), // steps 1289..1296
    (114,256), // steps 1297..1304
    (118,256), // steps 1305..1312
    (121,256), // steps 1313..1320
    (125,256), // steps 1321..1328
    (128,256), // steps 1329..1336
    (132,256), // steps 1337..1344
    (135,256), // steps 1345..1352
    (139,256), // steps 1353..1360
    (142,256), // steps 1361..1368
    (145,256), // steps 1369..1376
    (149,256), // steps 1377..1384
    (152,256), // steps 1385..1392
    (156,256), // steps 1393..1400
    (159,256), // steps 1401..1408
    (163,256), // steps 1409..1416
    (166,256), // steps 1417..1424
    (170,256), // steps 1425..1432
    (173,256), // steps 1433..1440
    (177,256), // steps 1441..1448
    (180,256), // steps 1449..1456
    (183,256), // steps 1457..1464
    (187,256), // steps 1465..1472
    (190,256), // steps 1473..1480
    (194,256), // steps 1481..1488
    (197,256), // steps 1489..1496
    (201,256), // steps 1497..1504
    (204,256), // steps 1505..1512
    (208,256), // steps 1513..1520
    (211,256), // steps 1521..1528
    (215,256), // steps 1529..1536
    (218,256), // steps 1537..1544
    (221,256), // steps 1545..1552
    (225,256), // steps 1553..1560
    (228,256), // steps 1561..1568
    (232,256), // steps 1569..1576
    (235,256), // steps 1577..1584
    (239,256), // steps 1585..1592
    (242,256), // steps 1593..1600
    (246,256), // steps 1601..1608
    (249,256), // steps 1609..1616
];
