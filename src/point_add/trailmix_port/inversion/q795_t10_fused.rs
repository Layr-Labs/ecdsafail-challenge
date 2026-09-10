//! Fused general T10 ADD and quotient cleanup, inverse of compare/conditional SUB.
//! P1 is arbitrary: exact scalar extension equals the original arithmetic pair.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_arithmetic5_programs.rs"] mod programs;

fn top_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,carry:&QReg,source:&[QReg],dirty:&[QReg]) {
    let(root,gather)=super::q798_handoffs::gather_a(circ,rank,a,source,1,dirty);
    circ.cswap(g,root,carry);circ.b.ops.extend(gather.into_iter().rev());
}
struct Range<'a>{rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],group:isize}
impl Range<'_>{
    fn high(&self,circ:&mut Circuit,h:isize){
        if !(0..4).contains(&h){return;}
        for &(m,v) in programs::A_EQUAL[h as usize] {
            let mut cs=vec![(self.g,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],v>>i&1!=0)));
            mixed_mcx(circ,&cs,self.cache,self.dirty);
        }
    }
    fn equality(&mut self,circ:&mut Circuit,value:usize){
        let(lo,hi)=if std::env::var("Q796_PREFIX_SUPPORT").ok().as_deref()==Some("0"){(0,256)}else{circ.q797_a_support.unwrap_or((0,256))};
        if value<lo||value>=hi{return;}
        let h=value/64;let factor=std::env::var("Q796_PREFIX_FACTORS").ok().as_deref()!=Some("0");
        let mut cs=vec![(self.g,true)];
        if !factor||lo/64!=(hi-1)/64 {
            if self.group!=h as isize{self.high(circ,self.group);self.high(circ,h as isize);self.group=h as isize;}
            cs.push((self.cache,true));
        }
        let left=lo.max(h*64);let right=hi.min((h+1)*64);
        for i in 0..6{if !factor||(left>>i)!=((right-1)>>i){cs.push((&self.a[i],value>>i&1!=0));}}
        if super::metadata_muxlease::active("Q795_T10_TOP_MASK_CLEAN") {
            // Only this mask consumer loses its external guard. On g1,
            // Xg supplies a zero scratch. Offg it is an arbitrary mask-XOR
            // extension, removed by the recorded literal per-cell inverse.
            // Restore g before high-cache transitions and all SUM/center reads.
            circ.x(self.g);super::paired_clean_mcx::toggle(circ,&cs[1..],self.mask,self.g);circ.x(self.g);
        } else {mixed_mcx(circ,&cs,self.mask,self.dirty);}
    }
}
fn cell(circ:&mut Circuit,s:&QReg,t:&QReg,carry:&QReg,mask:&QReg,g:&QReg,inverse:bool){
    if !inverse{circ.cx(s,t);circ.cx(carry,s);}
    circ.x(g);super::paired_clean_mcx::toggle(circ,&[(mask,true),(t,true),(s,true)],carry,g);circ.x(g);
    if inverse{circ.cx(carry,s);circ.cx(s,t);}
}

/// Exact inverse map q=p XOR [r>=x], y=r-q*x (mod2^(A+2)). Reversing
/// its COMPLETE circuit emits the old pair's map, including arbitrary P1.
pub(super) fn add_and_clear(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],a:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,p1:&QReg,helpers:&[QReg],n:usize){
    assert!((2..=257).contains(&n));assert!(helpers.len()>=17);
    let carry=&helpers[0];let dirty=&helpers[1..];let start=circ.b.ops.len();
    assert!(helpers.iter().all(|q|q.id()!=p1.id()&&q.id()!=g.id()&&q.id()!=cache.id()&&q.id()!=mask.id()));
    // Source[A+1] is zero on g after move_t10, distinct from the quotient
    // address funding mask. Carry starts0: NO source complement or carry^=g.
    top_loan(circ,rank,a,g,carry,source,dirty);circ.cx(g,mask);
    let mut range=Range{rank,a,g,cache,mask,dirty,group:-1};let mut updates=Vec::new();
    for i in 0..n{
        let at=circ.b.ops.len();if i>0{range.equality(circ,i-1);}updates.push(circ.b.ops[at..].to_vec());
        cell(circ,&source[i],&target[i],carry,mask,g,false);
    }
    let(target_top,target_gather)=super::q798_handoffs::gather_a(circ,rank,a,target,1,dirty);
    let(source_top,source_gather)=super::q798_handoffs::gather_a(circ,rank,a,source,1,dirty);
    // At masked-off top s'=passenger XOR b, t'=old_top XOR passenger.
    // Full borrow=b*(s' XOR t'). XOR threshold into ARBITRARY incoming P1.
    // W and both gathers exclude P1, including every dirty lender.
    circ.cx(g,p1);
    mixed_mcx(circ,&[(g,true),(carry,true),(source_top,true)],p1,dirty);
    mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
    circ.b.ops.extend(source_gather.into_iter().rev());
    mixed_mcx(circ,&[(g,true),(p1,true),(carry,true)],target_top,dirty);
    circ.b.ops.extend(target_gather.into_iter().rev());
    for i in (0..n).rev(){
        // Top changes cannot alter carry undo: its active mask is0. Retain
        // ALL masked-off CNOTs, including passenger and extra tail cells.
        cell(circ,&source[i],&target[i],carry,mask,g,true);
        circ.cx(carry,&source[i]);
        mixed_mcx(circ,&[(g,true),(mask,true),(&source[i],true),(p1,true)],&target[i],dirty);
        circ.cx(carry,&source[i]);circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    assert!(updates.is_empty());circ.cx(g,mask);top_loan(circ,rank,a,g,carry,source,dirty);
    circ.b.ops[start..].reverse();
}

pub mod verification{
    use super::*;use crate::sim::Simulator;use crate::circuit::OperationType;use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    pub fn run(){let mut total=0usize;
        for n in [2usize,3,5,7,9]{
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("fused.rank",5);let a=circ.alloc_qreg_bits("fused.a",6);
            let source=circ.alloc_qreg_bits("fused.source",259);let target=circ.alloc_qreg_bits("fused.target",259);
            let g=circ.alloc_qreg("fused.g");let cache=circ.alloc_qreg("fused.cache");let mask=circ.alloc_qreg("fused.mask");let p1=circ.alloc_qreg("fused.p1");let helpers=circ.alloc_qreg_bits("fused.dirty",21);let owned=circ.b.next_qubit;
            circ.q797_a_support=Some((0,n-1));
            add_and_clear(&mut circ,&rank,&source,&target,&a,&g,&cache,&mask,&p1,&helpers,n);let candidate=circ.b.ops.clone();circ.b.ops.clear();
            super::super::q795_t10_two_pass::prefix(&mut circ,&rank,&source,&target,&a,&g,&cache,&mask,None,Some(&p1),&helpers,true,n);circ.cx(&g,&p1);
            super::super::q795_t10_two_pass::prefix(&mut circ,&rank,&source,&target,&a,&g,&cache,&mask,Some(&p1),None,&helpers,false,n);
            let old=circ.b.ops.clone();assert_eq!(circ.b.next_qubit,owned);assert!(candidate.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let mut fixed=Fixed;let mut other=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);let mut reference=Simulator::new(owned as usize,0,&mut other);
            for k in 1..n{let modulus=1usize<<(k+1);let cases=1usize<<(2*k+4);
                for batch in 0..cases.div_ceil(64){
                    let mut before:Vec<_>=(0..owned).map(|i|0x9e3779b97f4a7c15u64.wrapping_mul((i as u64+3).wrapping_mul(batch as u64+17)).rotate_left(i%61)).collect();
                    for lane in 0..64{let z=(batch*64+lane)%cases;let x=z&((1<<k)-1);let y=(z>>k)&(modulus-1);let q=z>>(2*k+1)&1!=0;let on=z>>(2*k+2)&1!=0;let cargo=z>>(2*k+3)&1!=0;
                        for b in &rank{put(&mut before,b,lane,false);}for(i,b)in a.iter().enumerate(){put(&mut before,b,lane,(k-1)>>i&1!=0);}
                        for i in 0..k{put(&mut before,&source[i],lane,x>>i&1!=0);}for i in 0..k+1{put(&mut before,&target[i],lane,y>>i&1!=0);}
                        put(&mut before,&g,lane,on);put(&mut before,&p1,lane,q);put(&mut before,&helpers[0],lane,cargo);
                        if on{put(&mut before,&source[k],lane,false);put(&mut before,&cache,lane,false);put(&mut before,&mask,lane,false);}
                    }
                    let mut expected=before.clone();for lane in 0..64{if before[g.id()as usize]>>lane&1==0{continue;}
                        let x=(0..k).map(|i|(((before[source[i].id()as usize]>>lane)&1)as usize)<<i).sum::<usize>();let y=(0..k+1).map(|i|(((before[target[i].id()as usize]>>lane)&1)as usize)<<i).sum::<usize>();let q=(before[p1.id()as usize]>>lane&1)as usize;let r=(y+q*x)%modulus;
                        for i in 0..k+1{put(&mut expected,&target[i],lane,r>>i&1!=0);}put(&mut expected,&p1,lane,(q!=0)^(r>=x));
                    }
                    sim.qubits.copy_from_slice(&before);reference.qubits.copy_from_slice(&before);sim.apply_iter(candidate.iter());reference.apply_iter(old.iter());
                    assert_eq!(sim.qubits,reference.qubits,"fused old-pair mismatch n{n} k{k} batch{batch}");assert_eq!(sim.qubits,expected,"fused scalar mismatch n{n} k{k} batch{batch}");assert_eq!(sim.phase,0);
                    sim.apply_iter(candidate.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
                }
            }
            eprintln!("T10_FUSED_UNIT n={n} PASS T={} oldPairT={}",candidate.iter().filter(|o|o.kind==OperationType::CCX).count(),old.iter().filter(|o|o.kind==OperationType::CCX).count());
        }
        eprintln!("T10_FUSED_UNIT PASS {total} lanes; ALL small-width x/y/P1 including overflow and P1out1; top cargo, offguard dirty offsets, old-pair/scalar equality, inverse, phase/no allocation");
    }
}
