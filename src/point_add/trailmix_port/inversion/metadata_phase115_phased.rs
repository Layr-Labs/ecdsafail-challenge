//! Rank5 phase11 coefficient comparison, preserving arbitrary incoming Sign.
//! Guard contract: 1<=C<=255, 1<=S<=256, C+S<=257, S mod4=-j mod4.
//! Work1[258-C] is zero under guard; all16 helpers initially arbitrary.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::{mixed_mcx,below_cubes};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_phase115_programs.rs"] mod programs;

fn borrow(circ:&mut Circuit,rank:&[QReg],c:&[QReg],guard:&QReg,passenger:&QReg,word:&[QReg],helpers:&[QReg]) {
    if super::metadata_muxlease::active("Q799_MUX_LEASE"){super::metadata_muxlease::exchange(circ,rank,c,1,Some(guard),passenger,&(0..256).map(|v|&word[258-v]).collect::<Vec<_>>(),helpers,true);return;}
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..4 {for _ in 0..2 {
        for &(m,v) in programs::C_EQUAL[h] {
            let mut cs=vec![(guard,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
            mixed_mcx(circ,&cs,flag,dirty);
        }
        for lo in 0..64 {
            let cv=64*h+lo;if cv==0 {continue;}
            let q=&word[258-cv];let mut cs=vec![(guard,true),(flag,true),(passenger,true)];
            cs.extend((0..6).map(|i|(&c[i],lo>>i&1!=0)));
            circ.cx(q,passenger);mixed_mcx(circ,&cs,q,dirty);circ.cx(q,passenger);
        }
    }}
}

// Add virtual S_low to C_low (and optionally XOR carry into an independent bit).
// Every increment is guarded; helpers may be dirty. Literal reverse subtracts.
pub(super) fn prepare(circ:&mut Circuit,c:&[QReg],sm:&[QReg],guard:&QReg,carry:Option<&QReg>,helpers:&[QReg],j:usize,inverse:bool) {
    let word:Vec<_>=c.iter().chain(carry.into_iter()).collect();let n=word.len();
    let low=(4-j)%4;let start=circ.b.ops.len();
    for i in 0..6 {
        if i<2&&low>>i&1==0 {continue;}
        for k in (i..n).rev() {
            let mut cs=vec![(guard,true)];if i>=2 {cs.push((&sm[i-2],true));}
            cs.extend(word[i..k].iter().map(|&q|(q,true)));
            mixed_mcx(circ,&cs,word[k],helpers);
        }
    }
    if inverse {circ.b.ops[start..].reverse();}
}
fn carry_xor(circ:&mut Circuit,c:&[QReg],sm:&[QReg],guard:&QReg,d:&QReg,helpers:&[QReg],j:usize) {
    prepare(circ,c,sm,guard,None,helpers,j,true);
    prepare(circ,c,sm,guard,Some(d),helpers,j,false);
}
fn high(circ:&mut Circuit,rank:&[QReg],guard:&QReg,d:&QReg,flag:&QReg,helpers:&[QReg],h:usize,zero:bool) {
    for &(m,v) in programs::SUM_EQUAL[h] {
        if zero&&m>>5&1!=0&&v>>5&1!=0 {continue;}
        let mut cs=vec![(guard,true)];
        cs.extend((0..6).filter(|&i|m>>i&1!=0&&!(zero&&i==5)).map(|i|(if i==5{d}else{&rank[i]},v>>i&1!=0)));
        mixed_mcx(circ,&cs,flag,helpers);
    }
}
pub(super) fn sum_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,flag:&QReg,helpers:&[QReg],j:usize,h:usize) {
    let d=&helpers[0];let dirty=&helpers[1..];
    carry_xor(circ,c,sm,guard,d,dirty,j);high(circ,rank,guard,d,flag,dirty,h,false);
    carry_xor(circ,c,sm,guard,d,dirty,j);high(circ,rank,guard,d,flag,dirty,h,false);
    high(circ,rank,guard,d,flag,dirty,h,true);
    // S_raw0 means true256. On the active domain this forces C1;
    // transfer the selected high group from0 to4 while keeping low sum1.
    if j==0&&(h==0||h==4) {
        for &(m,v) in programs::S_ZERO[0] {
            let mut cs=vec![(guard,true)];cs.extend(sm.iter().map(|q|(q,false)));
            cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
            mixed_mcx(circ,&cs,flag,helpers);
        }
    }
}
/// Literal S0 version for the post-boundary Sign erasure; the S256 birth is
/// represented separately and disabled by its caller.
pub(super) fn sum_flag_raw(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,flag:&QReg,helpers:&[QReg],j:usize,h:usize) {
    let d=&helpers[0];let dirty=&helpers[1..];
    carry_xor(circ,c,sm,guard,d,dirty,j);high(circ,rank,guard,d,flag,dirty,h,false);
    carry_xor(circ,c,sm,guard,d,dirty,j);high(circ,rank,guard,d,flag,dirty,h,false);
    high(circ,rank,guard,d,flag,dirty,h,true);
}
pub(super) fn sum_flag_raw_transition(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,flag:&QReg,helpers:&[QReg],j:usize,from:isize,to:isize){
    if from==to{return;}let d=&helpers[0];let dirty=&helpers[1..];
    carry_xor(circ,c,sm,guard,d,dirty,j);super::metadata_arithmetic5::sum_terms(circ,rank,d,guard,flag,dirty,programs::SUM_EQUAL,from,to,false);
    carry_xor(circ,c,sm,guard,d,dirty,j);super::metadata_arithmetic5::sum_terms(circ,rank,d,guard,flag,dirty,programs::SUM_EQUAL,from,to,false);
    super::metadata_arithmetic5::sum_terms(circ,rank,d,guard,flag,dirty,programs::SUM_EQUAL,from,to,true);
}
fn prefix(circ:&mut Circuit,source:&[QReg],target:&[QReg],low:&[QReg],guard:&QReg,cache:&QReg,sign:Option<&QReg>,output_control:&QReg,helpers:&[QReg],h:usize,inverse:bool,support_end:usize) {
    let extent=259-64*h;let n=extent.min(support_end);let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev() {if let Some(z)=sign {cells.push((i,1,vec![&source[i]],z));}if i+1<n {cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n {if i+1<n {cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign {cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev() {cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1 {cells.push((i+1,2,vec![&source[i]],&source[i+1]));}
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}
    if inverse {cells.reverse();}
    for (i,tag,data,out) in cells {
        if tag==2 {circ.cx(data[0],out);continue;}
        let bound=if tag==1 {extent-1-i}else{extent-i};
        let cubes=if tag==3 {vec![Vec::new()]}else if tag==1 {
            if bound<64 {vec![(0..6).map(|b|(b,bound>>b&1!=0)).collect()]}else{Vec::new()}
        }else{below_cubes(6,bound)};
        for cube in cubes {
            let mut cs=vec![(guard,true),(cache,true)];cs.extend(data.iter().map(|&q|(q,true)));cs.extend(cube.iter().map(|&(b,v)|(&low[b],v)));
            if tag==1{cs.push((output_control,true));}
            mixed_mcx(circ,&cs,out,helpers);
        }
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize) {
    emit_with_support(circ,rank,c,sm,guard,p2,sign,w1,w2,helpers,j,259);
}
/// Caller proves selected prefix length259-C-S<=support_end.
pub(super) fn emit_with_support(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize) {
    assert!((2..=259).contains(&support_end));let start=circ.b.ops.len();
    assert_eq!(rank.len(),5);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);
    let cache=&helpers[0];let dirty=&helpers[1..];
    borrow(circ,rank,c,guard,cache,w1,dirty);prepare(circ,c,sm,guard,None,dirty,j,false);
    for h in 0..5 {
        sum_flag(circ,rank,c,sm,guard,cache,dirty,j,h);
        prefix(circ,w1,w2,c,guard,cache,None,p2,dirty,h,true,support_end);mixed_mcx(circ,&[(guard,true),(p2,true),(cache,true)],sign,dirty);
        prefix(circ,w1,w2,c,guard,cache,Some(sign),p2,dirty,h,false,support_end);
        sum_flag(circ,rank,c,sm,guard,cache,dirty,j,h);
    }
    prepare(circ,c,sm,guard,None,dirty,j,true);borrow(circ,rank,c,guard,cache,w1,dirty);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let resource_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let support_end:usize=std::env::var("LOWQ_CODEC_SUPPORT_END").ok().map(|v|v.parse().unwrap()).unwrap_or(259);
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("p115.rank",5);let _a=circ.alloc_qreg_bits("p115.a",6);let c=circ.alloc_qreg_bits("p115.c",6);let sm=circ.alloc_qreg_bits("p115.s25",4);assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("p115.phase1");let p2=circ.alloc_qreg("p115.phase2");let sign=circ.alloc_qreg("p115.sign");let w1=circ.alloc_qreg_bits("p115.work1",259);let w2=circ.alloc_qreg_bits("p115.work2",259);let helpers=circ.alloc_qreg_bits("p115.dirty",24);let owned=circ.b.next_qubit;
        emit_with_support(&mut circ,&rank,&c,&sm,&guard,&p2,&sign,&w1,&w2,&helpers,j,support_end);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
        for op in &b.ops {assert!(op.q_control1.0!=sign.id()as u64&&op.q_control2.0!=sign.id()as u64);op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_T11_PHASED5_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned} support_end={support_end}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        if resource_only {continue;}
        for pattern in 0..4 {for batch in 0..32*64*16*2/64 {
            let mut seed=0xfacd67983b54e102^batch as u64^((pattern as u64)<<26)^((j as u64)<<30);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let cl=k>>5&63;let sl=k>>11&15;
                let cv=64*triples[r][1]+cl;let raw_s=64*triples[r][2]+4*sl+(4-j)%4;let sv=if raw_s==0 {256}else{raw_s};let on=k>>15&1!=0&&cv>0&&cv+sv<=257&&259-cv-sv<=support_end;
                for i in 0..5 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6 {for w in [&mut before,&mut after]{put(w,&c[i],lane,cl>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                let phase=if on{3}else{(k+pattern)%3};
                for w in [&mut before,&mut after]{put(w,&guard,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);}
                if on {
                    let address=258-cv;let n=259-cv-sv;assert!(address>=n&&n>=2);if sv==256{wraps+=1;}
                    put(&mut before,&w1[address],lane,false);put(&mut after,&w1[address],lane,false);
                    if pattern>=2 {for i in 0..n {
                        let av=before[w1[i].id()as usize]>>lane&1!=0;
                        for w in [&mut before,&mut after] {put(w,&w2[i],lane,if pattern==2{av}else{!av});}
                    }}
                    let mut less=false;
                    for i in 0..n {let av=before[w1[i].id()as usize]>>lane&1!=0;let bv=before[w2[i].id()as usize]>>lane&1!=0;if av!=bv {less=av;}}
                    if !less {after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"phase115 j={j} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_T11_PHASED5_PATTERN j={j} pattern={pattern} PASS");}
    }
    if resource_only {eprintln!("CODEC_T11_PHASED5_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_T11_PHASED5_PASS support_end={support_end} lanes={total} true_S256_lanes={wraps}; existing-zero loan, virtual low sum, dirty carry query, actual comparison, return; full Q799 missing");
}
