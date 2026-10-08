//! Phase11 coefficient comparison on the 21-wire metadata code.
//! Existing Work1[258-C] supplies the zero; no unpacked length registers.
//! Guard implies 1<=C<=255, S>=1 and C+S<=257. Input normalization
//! x<=p/2 and decreasing residuals imply residual length C<=255.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{conditional_mcx,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_phase11_programs.rs"] mod programs;
#[path="metadata_predicate_programs.rs"] mod rank_programs;

fn c_high(circ:&mut Circuit,rank:&[QReg],s0:&QReg,guard:&QReg,flag:&QReg,helpers:&[QReg],h:usize,known:bool) {
    for b in std::iter::once(h).chain(h.checked_sub(1)) {
        for &(m,v) in rank_programs::PROGRAMS[17+b] {
            let others:Vec<_>=(0..10).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
            conditional_mcx::guarded(circ,guard,&others,flag,s0,known,&helpers[0]);
        }
    }
}
fn low_swaps(circ:&mut Circuit,c:&[QReg],guard:&QReg,flag:&QReg,passenger:&QReg,work:&[QReg],helpers:&[QReg],h:usize) {
    for lo in 0..16 {
        let value=16*h+lo;if value==0 {continue;}
        let target=&work[258-value];let mut cs=vec![(guard,true),(flag,true),(passenger,true)];
        cs.extend((0..4).map(|i|(&c[i],lo>>i&1!=0)));
        circ.cx(target,passenger);length_recompute::mixed_mcx(circ,&cs,target,helpers);circ.cx(target,passenger);
    }
}
fn borrow(circ:&mut Circuit,rank:&[QReg],c:&[QReg],s0:&QReg,guard:&QReg,cache:&QReg,work:&[QReg],helpers:&[QReg],known:bool) {
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..16 {
        c_high(circ,rank,s0,guard,flag,dirty,h,known);
        low_swaps(circ,c,guard,flag,cache,work,dirty,h);
        c_high(circ,rank,s0,guard,flag,dirty,h,known);
        low_swaps(circ,c,guard,flag,cache,work,dirty,h);
    }
}
// Add the virtual low S nibble to C with carry in LS0. Phase11 has
// S mod4=-j mod4. Every increment is guarded; reverse restores off-lane data.
fn prepare(circ:&mut Circuit,c:&[QReg],sm:&[QReg],s0:&QReg,guard:&QReg,helpers:&[QReg],j:usize,inverse:bool) {
    let known=j%2!=0;if !inverse&&known {circ.x(s0);}
    let word:Vec<_>=c.iter().chain(std::iter::once(s0)).collect();
    let mut cells=Vec::new();let low=(4-j)%4;
    for i in 0..4 {
        if i<2&&low>>i&1==0 {continue;}
        for k in (i..5).rev() {cells.push((i,k));}
    }
    if inverse {cells.reverse();}
    for (i,k) in cells {
        let mut cs=vec![(guard,true)];if i>=2 {cs.push((&sm[i-2],true));}
        cs.extend(word[i..k].iter().map(|&q|(q,true)));
        length_recompute::mixed_mcx(circ,&cs,word[k],helpers);
    }
    if inverse&&known {circ.x(s0);}
}
fn high_sum(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],s0:&QReg,guard:&QReg,cache:&QReg,helpers:&[QReg],j:usize,h:usize) {
    prepare(circ,c,sm,s0,guard,helpers,j,false);
    for &(m,v) in programs::HIGH_EQUAL[h] {
        let mut cs=vec![(guard,true)];cs.extend((0..11).filter(|&i|m>>i&1!=0).map(|i|(if i==10 {s0}else{&rank[i]},v>>i&1!=0)));
        length_recompute::mixed_mcx(circ,&cs,cache,helpers);
    }
    prepare(circ,c,sm,s0,guard,helpers,j,true);
    // In active phase11 a raw-zero S denotes true256, never true0.
    // C+S<=257 and C>=1 then force C=1. Move this high-sum selection
    // from group0 to group16, without materializing an extra carry wire.
    if j==0&&(h==0||h==16) {
        for &(m,v) in rank_programs::PROGRAMS[34] {
            let mut cs=vec![(&sm[0],false),(&sm[1],false)];
            cs.extend((0..10).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
            conditional_mcx::guarded(circ,guard,&cs,cache,s0,false,&helpers[0]);
        }
    }
}
fn prefix(circ:&mut Circuit,source:&[QReg],target:&[QReg],c:&[QReg],sm:&[QReg],s0:&QReg,guard:&QReg,cache:&QReg,sign:Option<&QReg>,helpers:&[QReg],j:usize,h:usize,inverse:bool) {
    let n=259-16*h;let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev() {if let Some(z)=sign {cells.push((i,1,vec![&source[i]],z));}if i+1<n {cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n {if i+1<n {cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign {cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    if inverse {cells.reverse();}
    let low:Vec<_>=c.iter().chain(sm).collect();
    for (i,tag,data,out) in cells {
        let bound=if tag==1 {n-1-i}else{n-i};
        let terms=if tag>=2 {&[(0u16,0u16)][..]}else if tag==1&&bound>15 {&[][..]}else if tag==0&&bound>=16 {&[(0u16,0u16)][..]}else{programs::LOW[j*34+if tag==1 {17+bound}else{bound}]};
        for &(m,v) in terms {
            let mut cs=vec![(cache,true)];cs.extend(data.iter().map(|&q|(q,true)));cs.extend((0..6).filter(|&i|m>>i&1!=0).map(|i|(low[i],v>>i&1!=0)));
            conditional_mcx::guarded(circ,guard,&cs,out,s0,j%2!=0,&helpers[0]);
        }
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],s0:&QReg,guard:&QReg,cache:&QReg,sign:&QReg,work1:&[QReg],work2:&[QReg],helpers:&[QReg],j:usize) {
    borrow(circ,rank,c,s0,guard,cache,work1,helpers,j%2!=0);
    for h in 0..17 {
        high_sum(circ,rank,c,sm,s0,guard,cache,helpers,j,h);
        prefix(circ,work1,work2,c,sm,s0,guard,cache,None,helpers,j,h,true);
        circ.ccx(guard,cache,sign);
        prefix(circ,work1,work2,c,sm,s0,guard,cache,Some(sign),helpers,j,h,false);
        high_sum(circ,rank,c,sm,s0,guard,cache,helpers,j,h);
    }
    borrow(circ,rank,c,s0,guard,cache,work1,helpers,j%2!=0);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("p11.rank",10);let _a=circ.alloc_qreg_bits("p11.a",4);let c=circ.alloc_qreg_bits("p11.c",4);let sm=circ.alloc_qreg_bits("p11.s23",2);let s0=circ.alloc_qreg("p11.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("p11.guard");let cache=circ.alloc_qreg("p11.passenger");let sign=circ.alloc_qreg("p11.sign");let work1=circ.alloc_qreg_bits("p11.work1",259);let work2=circ.alloc_qreg_bits("p11.work2",259);let helpers=circ.alloc_qreg_bits("p11.dirty",16);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&c,&sm,&s0,&guard,&cache,&sign,&work1,&work2,&helpers,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_PHASE11_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        for pattern in 0..2 {for batch in 0..1024*16*4*2/64 {
            let mut seed=0xfacd67983b54e102^batch as u64^((pattern as u64)<<26);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&1023;let cl=k>>10&15;let sl=k>>14&3;
                let (cv,raw_s)=if r<966 {(16*triples[r][1]+cl,16*triples[r][2]+4*sl+(4-j)%4)}else{(0,0)};
                let sv=if raw_s==0 {256}else{raw_s};
                let on=k>>16&1!=0&&r<966&&cv>0&&cv+sv<=257;
                for i in 0..10 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&c[i],lane,cl>>i&1!=0);}}
                for i in 0..2 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for (q,v) in [(&guard,on),(&s0,if on {j%2!=0}else{(k+pattern)%2!=0})] {for w in [&mut before,&mut after]{put(w,q,lane,v);}}
                if on {
                    let address=258-cv;let n=259-cv-sv;assert!(address>=n&&n>=2);
                    put(&mut before,&work1[address],lane,false);put(&mut after,&work1[address],lane,false);
                    let mut less=false;
                    for i in 0..n {let av=before[work1[i].id()as usize]>>lane&1!=0;let bv=before[work2[i].id()as usize]>>lane&1!=0;if av!=bv {less=av;}}
                    // Subtraction wraps iff b<a; restoration addition then carries.
                    // The explicit Sign flip therefore yields old Sign XOR (b>=a).
                    if !less {after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"phase11 j={j} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_PHASE11_PATTERN j={j} pattern={pattern} PASS");}
    }
    eprintln!("CODEC_PHASE11_PASS lanes={total}; actual existing-zero borrow/virtual endpoint arithmetic/return on21 metadata; full Q799 missing");
}
