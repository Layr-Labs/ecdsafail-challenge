//! Actual phase10 T subtraction/addition controlled by21-bit metadata.
//! High LT selectors use an existing zero loan; LS0 remains a parity lender.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_rank,metadata_address_swap,conditional_mcx,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
fn prefix(circ:&mut Circuit,source:&[QReg],target:&[QReg],low:&[QReg],guard:&QReg,cache:&QReg,s0:&QReg,helpers:&[QReg],high:usize,sign_out:Option<&QReg>,sign_control:Option<&QReg>,subtract:bool,known:bool) {
    let base=16*high;let n=base+17;assert!(n<=source.len()&&n<=target.len());
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev() {if let Some(z)=sign_out{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n {if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign_out{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    if subtract{cells.reverse();}
    for (i,tag,data,out) in cells {
        let cubes=if tag>=2 {vec![Vec::new()]} else if tag==1 {
            if i>=base+1&&i<=base+16 {vec![(0..4).map(|bit|(bit,(i-base-1)>>bit&1!=0)).collect()]} else {Vec::new()}
        } else if i<base+2 {vec![Vec::new()]} else {length_recompute::above_cubes(4,i-base-2)};
        for cube in cubes {
            let mut others=vec![(cache,true)];if let Some(z)=sign_control {others.push((z,false));}
            others.extend(data.iter().map(|&q|(q,true)));others.extend(cube.iter().map(|&(i,v)|(&low[i],v)));
            conditional_mcx::guarded(circ,guard,&others,out,s0,known,&helpers[0]);
        }
    }
}
pub(super) fn phase10(circ:&mut Circuit,rank:&[QReg],a_low:&[QReg],s0:&QReg,guard:&QReg,cache:&QReg,sign:&QReg,work1:&[QReg],work2:&[QReg],helpers:&[QReg],known:bool) {
    for high in 0..16 {
        metadata_rank::xor_high_a_equal(circ,rank,guard,cache,s0,helpers,high,known);
        prefix(circ,work1,work2,a_low,guard,cache,s0,helpers,high,None,Some(sign),true,known);
        circ.ccx(guard,cache,sign);
        prefix(circ,work1,work2,a_low,guard,cache,s0,helpers,high,Some(sign),None,false,known);
        metadata_rank::xor_high_a_equal(circ,rank,guard,cache,s0,helpers,high,known);
    }
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for known in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("T.rank",10);let a=circ.alloc_qreg_bits("T.a",4);let c=circ.alloc_qreg_bits("T.c",4);let _sm=circ.alloc_qreg_bits("T.s23",2);let s0=circ.alloc_qreg("T.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("T.guard");let sign=circ.alloc_qreg("T.sign");let cache=circ.alloc_qreg("T.passenger");let work1=circ.alloc_qreg_bits("T.work1",259);let work2=circ.alloc_qreg_bits("T.work2",259);let helpers=circ.alloc_qreg_bits("T.dirty",16);let owned=circ.b.next_qubit;
        metadata_address_swap::remove_and_borrow(&mut circ,&rank,&a,&c,&s0,&guard,&sign,&cache,&work1,&helpers,known);let borrow_at=circ.b.ops.len();
        phase10(&mut circ,&rank,&a,&s0,&guard,&cache,&sign,&work1,&work2,&helpers,known);let arithmetic_end=circ.b.ops.len();
        metadata_address_swap::emit(&mut circ,&rank,&a,&c,&s0,&guard,&cache,&work1,&helpers,known,false);assert_eq!(owned,circ.b.next_qubit);let b=circ.into_builder();
        for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();let cases=1024*16*16*2;
        eprintln!("CODEC_PHASE10_T_BUILT known={known} T={tof} ops={} arithmetic_ops={} metadata_wires=21 component_wires={owned}",b.ops.len(),arithmetic_end-borrow_at);
        for pattern in 0..2 {for batch in 0..cases/64 {
            let mut seed=0x27fd18b4e35a690c^batch as u64^((pattern as u64)<<28);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();let mut active_mask=0u64;
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&1023;let al=k>>10&15;let cl=k>>14&15;
                let (aa,cc)=if r<966{(16*triples[r][0]+al,16*triples[r][1]+cl)}else{(usize::MAX,usize::MAX)};
                let valid=r<966&&((cc>0&&aa+cc<=256)||(cc==0&&aa==0));let on=k>>18&1!=0&&valid;
                for i in 0..10{for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..4{for (q,v) in [(&a[i],al>>i&1!=0),(&c[i],cl>>i&1!=0)]{for w in [&mut before,&mut after]{put(w,q,lane,v);}}}
                let scratch=if on{known}else{(k+pattern)%2!=0};let sign_in=if on{false}else{(k+pattern+1)%2!=0};
                for (q,v) in [(&guard,on),(&s0,scratch),(&sign,sign_in)]{for w in [&mut before,&mut after]{put(w,q,lane,v);}}
                if on {
                    active_mask|=1u64<<lane;let sum=aa+cc;let address=if sum==0{257}else{sum+1};let n=aa+2;assert!(address>=n);
                    let qbit=(k+pattern)%2!=0;put(&mut before,&work1[address],lane,qbit);put(&mut after,&work1[address],lane,false);
                    let mut carry=false;let mut ge=true;
                    for i in 0..n {
                        let av=before[work1[i].id()as usize]>>lane&1!=0;let bv=before[work2[i].id()as usize]>>lane&1!=0;
                        if av!=bv{ge=bv;}
                        if qbit {let value=av^bv^carry;let next=(av&&bv)||(av&&carry)||(bv&&carry);put(&mut after,&work2[i],lane,value);carry=next;}
                    }
                    put(&mut after,&sign,lane,if qbit{carry}else{ge});
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(b.ops[..borrow_at].iter());assert_eq!(sim.qubits[cache.id()as usize]&active_mask,0);assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops[borrow_at..arithmetic_end].iter());assert_eq!(sim.qubits[cache.id()as usize]&active_mask,0,"T cache not restored");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops[arithmetic_end..].iter());assert_eq!(sim.qubits,after,"phase10T known={known} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_PHASE10_T_PATTERN known={known} pattern={pattern} PASS");}
    }
    eprintln!("CODEC_PHASE10_T_PASS lanes={total}; actualQ removal/borrow/T subtraction-addition-sign/return,21metadata wires; otherphases andwholeQ799 missing");
}
