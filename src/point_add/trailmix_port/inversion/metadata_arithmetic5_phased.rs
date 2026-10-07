//! Rank5 quotient exchange and phase10 arithmetic with actual phase controls.
//! Fused quotient removal lends an existing zero for cached prefix selection.
//! All supplied helpers may start dirty and must be restored.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::{mixed_mcx,above_cubes};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_arithmetic5_programs.rs"] mod programs;
// Fixed-width no-carry-register addition. An optional independent bit gets carry XOR.
pub(super) fn add(circ:&mut Circuit,a:&[QReg],b:&[QReg],carry:Option<&QReg>,inverse:bool) {
    let n=a.len();assert_eq!(n,b.len());assert!(n>=2);let start=circ.b.ops.len();
    for i in 0..n {circ.cx(&a[i],&b[i]);}circ.cx(&a[0],&b[0]);
    for i in (1..n).rev(){if i==n-1 {if let Some(z)=carry{circ.cx(&a[i],z);}}if i+1<n{circ.cx(&a[i],&a[i+1]);}}
    for i in 0..n {if i+1<n{circ.ccx(&a[i],&b[i],&a[i+1]);}else if let Some(z)=carry{circ.ccx(&a[i],&b[i],z);}}
    for i in (1..n).rev(){circ.cx(&a[i],&b[i]);circ.ccx(&a[i-1],&b[i-1],&a[i]);}
    for i in 1..n-1 {circ.cx(&a[i],&a[i+1]);}
    for i in 0..n {circ.cx(&a[i],&b[i]);}
    if inverse{circ.b.ops[start..].reverse();}
}
// Input b contains the low sum. Subtraction then restoration XORs [b<a] into d.
fn carry_xor(circ:&mut Circuit,a:&[QReg],b:&[QReg],d:&QReg) {add(circ,a,b,None,true);add(circ,a,b,Some(d),false);}
fn high_sum(circ:&mut Circuit,rank:&[QReg],d:&QReg,guard:&QReg,out:&QReg,helpers:&[QReg],h:usize,zero:bool) {
    for &(m,v) in programs::SUM_EQUAL[h] {
        if zero&&m>>5&1!=0&&v>>5&1!=0 {continue;}
        let mut cs=vec![(guard,true)];cs.extend((0..6).filter(|&i|m>>i&1!=0&&!(zero&&i==5)).map(|i|(if i==5{d}else{&rank[i]},v>>i&1!=0)));mixed_mcx(circ,&cs,out,helpers);
    }
}
// For a Boolean function F of one carry bit, F(d^c)^F(d)^F(0)=F(c).
// Each F XORs the same flag, so dirty echo is valid without assuming flag or d zero.
pub(super) fn sum_flag(circ:&mut Circuit,rank:&[QReg],a:&[QReg],b:&[QReg],guard:&QReg,flag:&QReg,d:&QReg,helpers:&[QReg],h:usize) {
    carry_xor(circ,a,b,d);high_sum(circ,rank,d,guard,flag,helpers,h,false);
    carry_xor(circ,a,b,d);high_sum(circ,rank,d,guard,flag,helpers,h,false);
    high_sum(circ,rank,d,guard,flag,helpers,h,true);
}
fn low_swaps(circ:&mut Circuit,low:&[QReg],guard:&QReg,phase:(&QReg,bool),flag:&QReg,sign:&QReg,word:&[QReg],helpers:&[QReg],h:usize,insert:bool) {
    for lo in 0..64 {let sum=64*h+lo;if sum>if insert{255}else{256}{continue;}
        let address=if insert{sum+2}else if sum==0{257}else{sum+1};let target=&word[address];
        let mut cs=vec![(guard,true),phase,(flag,true),(sign,true)];cs.extend((0..6).map(|i|(&low[i],lo>>i&1!=0)));
        circ.cx(target,sign);mixed_mcx(circ,&cs,target,helpers);circ.cx(target,sign);
    }
}
fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guard:&QReg,phase:(&QReg,bool),sign:&QReg,word:&[QReg],helpers:&[QReg],insert:bool) {
    if super::metadata_muxlease::active("Q799_MUX_QUOTIENT"){super::metadata_muxlease::quotient(circ,rank,a,c,&[(guard,true),phase],sign,word,helpers,insert);return;}
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert!(helpers.len()>=9);let flag=&helpers[0];let d=&helpers[1];let dirty=&helpers[2..];
    add(circ,a,c,None,false);
    for h in 0..5 {
        sum_flag(circ,rank,a,c,guard,flag,d,dirty,h);low_swaps(circ,c,guard,phase,flag,sign,word,dirty,h,insert);
        sum_flag(circ,rank,a,c,guard,flag,d,dirty,h);low_swaps(circ,c,guard,phase,flag,sign,word,dirty,h,insert);
    }
    add(circ,a,c,None,true);
}
fn prefix(circ:&mut Circuit,source:&[QReg],target:&[QReg],low:&[QReg],guard:&QReg,p2:&QReg,cache:&QReg,sign_out:Option<&QReg>,sign_control:Option<&QReg>,helpers:&[QReg],h:usize,subtract:bool,support_end:usize) {
    let base=64*h;let n=(base+65).min(support_end);let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev(){if let Some(z)=sign_out{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign_out{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    if subtract{cells.reverse();}
    for(i,tag,data,out)in cells{
        if tag==2{circ.cx(data[0],out);continue;}
        let cubes=if tag==3||(tag==0&&i<base+2){vec![Vec::new()]}
        else if tag==1{if (base+1..=base+64).contains(&i){vec![(0..6).map(|b|(b,(i-base-1)>>b&1!=0)).collect()]}else{Vec::new()}}
        else{above_cubes(6,i-base-2)};
        for cube in cubes{
            let mut cs=vec![(guard,true),(p2,false),(cache,true)];if let Some(z)=sign_control{cs.push((z,false));}cs.extend(data.iter().map(|&q|(q,true)));cs.extend(cube.iter().map(|&(i,v)|(&low[i],v)));mixed_mcx(circ,&cs,out,helpers);
        }
    }
}
fn a_flag(circ:&mut Circuit,rank:&[QReg],guard:&QReg,cache:&QReg,helpers:&[QReg],h:usize){
    for &(m,v)in programs::A_EQUAL[h]{let mut cs=vec![(guard,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,cache,helpers);}
}
pub(super) fn phase10(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg]) {
    phase10_with_support(circ,rank,a,c,guard,p2,sign,w1,w2,helpers,259);
}
/// Caller proves coefficient prefix A_raw+2<=support_end.
pub(super) fn phase10_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],support_end:usize) {
    assert!((2..=259).contains(&support_end));let start=circ.b.ops.len();
    let cache=&helpers[0];let dirty=&helpers[1..];
    // Incoming Sign0: put the quotient into cache first, then exchange with
    // Sign. The selected quotient wire holds cache's old data outside T.
    quotient(circ,rank,a,c,guard,(p2,false),cache,w1,dirty,false);
    circ.cx(cache,sign);mixed_mcx(circ,&[(guard,true),(p2,false),(sign,true)],cache,dirty);circ.cx(cache,sign);
    for h in 0..4{
        a_flag(circ,rank,guard,cache,dirty,h);
        prefix(circ,w1,w2,a,guard,p2,cache,None,Some(sign),dirty,h,true,support_end);mixed_mcx(circ,&[(guard,true),(p2,false),(cache,true)],sign,dirty);
        prefix(circ,w1,w2,a,guard,p2,cache,Some(sign),None,dirty,h,false,support_end);
        a_flag(circ,rank,guard,cache,dirty,h);
    }
    quotient(circ,rank,a,c,guard,(p2,false),cache,w1,dirty,false);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}

/// Phase01 insertion: address preparation is paired, only data exchanges
/// carry both actual phase conditions. Canonical terminal phase00 is off.
pub(super) fn phase01(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,word:&[QReg],helpers:&[QReg]) {
    let start=circ.b.ops.len();circ.x(p1);
    quotient(circ,rank,a,c,p1,(p2,true),sign,word,helpers,true);
    circ.x(p1);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let resource_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let support_end:usize=std::env::var("LOWQ_CODEC_SUPPORT_END").ok().map(|v|v.parse().unwrap()).unwrap_or(259);
    let selected_mode:Option<usize>=std::env::var("LOWQ_CODEC_ARITH_MODE").ok().map(|v|v.parse().unwrap());
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;
    for mode in 0..2 {
        if selected_mode.is_some()&&selected_mode!=Some(mode){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("T5.rank",5);let a=circ.alloc_qreg_bits("T5.a",6);let c=circ.alloc_qreg_bits("T5.c",6);let _sm=circ.alloc_qreg_bits("T5.sm",4);assert_eq!(circ.b.next_qubit,21);
        let p1=circ.alloc_qreg("T5.P1");let p2=circ.alloc_qreg("T5.P2");let sign=circ.alloc_qreg("T5.sign");let _iter=circ.alloc_qreg("T5.iter");let w1=circ.alloc_qreg_bits("T5.w1",259);let w2=circ.alloc_qreg_bits("T5.w2",259);assert_eq!(circ.b.next_qubit,543);let helpers=circ.alloc_qreg_bits("T5.dirty",16);let owned=circ.b.next_qubit;
        if mode==0{phase10_with_support(&mut circ,&rank,&a,&c,&p1,&p2,&sign,&w1,&w2,&helpers,support_end);}else{phase01(&mut circ,&rank,&a,&c,&p1,&p2,&sign,&w1,&helpers);}
        assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_ARITH_PHASED5_BUILT mode={mode} T={} ops={} owned_wires=543 borrowed_wires=16 support_end={support_end}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        if resource_only {continue;}
        for pattern in 0..2 {for batch in 0..32*64*64*4/64{
            let mut seed=0xb829a31cf674d50e^batch as u64^((pattern as u64)<<30);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let k=batch*64+lane;let r=k&31;let al=k>>5&63;let cl=k>>11&63;let aa=64*triples[r][0]+al;let cc=64*triples[r][1]+cl;let sum=aa+cc;
                let valid=aa<255&&if mode==0{((cc>0&&sum<=256)||(cc==0&&aa==0))&&aa+2<=support_end}else{sum<=255};
                let target_phase=if mode==0{2}else{1};let mut phase=k>>17&3;
                if phase==target_phase&&!valid{phase=(phase+1)%4;}
                if r==29&&al==63{phase=0;}
                let on=phase==target_phase;
                for i in 0..5{for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6{for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);put(w,&c[i],lane,cl>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&p1,lane,phase>>1&1!=0);put(w,&p2,lane,phase&1!=0);}
                if on{
                    let address=if mode==1{sum+2}else if sum==0{257}else{sum+1};
                    if mode==1{let sv=before[sign.id()as usize]>>lane&1!=0;let qv=before[w1[address].id()as usize]>>lane&1!=0;put(&mut after,&sign,lane,qv);put(&mut after,&w1[address],lane,sv);}
                    else{
                        put(&mut before,&sign,lane,false);let qbit=(k+pattern)%2!=0;put(&mut before,&w1[address],lane,qbit);put(&mut after,&w1[address],lane,false);
                        let n=aa+2;assert!(address>=n);let mut carry=false;let mut ge=true;
                        for i in 0..n{let av=before[w1[i].id()as usize]>>lane&1!=0;let bv=before[w2[i].id()as usize]>>lane&1!=0;if av!=bv{ge=bv;}if qbit{put(&mut after,&w2[i],lane,av^bv^carry);carry=(av&&bv)||(av&&carry)||(bv&&carry);}}
                        put(&mut after,&sign,lane,if qbit{carry}else{ge});
                    }
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("arith phased5 mode={mode} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_ARITH_PHASED5_PATTERN mode={mode} pattern={pattern} PASS");}
    }
    if resource_only {eprintln!("CODEC_ARITH_PHASED5_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_ARITH_PHASED5_PASS support_end={support_end} lanes={total}; actual phase10 Q+T and phase01 insertion, all phases, dirty off-phase words/Sign/helpers, exact inverse; no whole Q799 claim");
}
