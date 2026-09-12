//! Independent all-metadata oracle for the new R01 actual-carry selectors.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let m=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!m)|if v{m}else{0};}
fn get(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
fn set(w:&mut[u64],qs:&[QReg],l:usize,v:usize){for(i,q)in qs.iter().enumerate(){put(w,q,l,v>>i&1!=0);}}
pub fn run(){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut supports=vec![(0,256)];supports.extend(super::metadata_entry_head5::A_SUPPORTS.iter().map(|&(lo,_)|(lo,256)));supports.sort_unstable();supports.dedup();
    let mut total=0usize;let mut active=0usize;let mut off=0usize;
    for &(lo,hi) in &supports{for offset in 0..3{
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;circ.q797_a_support=Some((lo,hi));
        let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let g=circ.alloc_qreg("g");let carry=circ.alloc_qreg("carry");let out=circ.alloc_qreg("out");let w1=circ.alloc_qreg_bits("w1",259);let nq=circ.b.next_qubit;
        let(root,route)=super::q793_r01_routes_v1::gather(&mut circ,&rank,&a,&c,&w1,&g,&carry,offset);
        if offset==2{circ.cswap(&g,root,&out);}else{circ.ccx(&g,root,&out);}
        circ.b.ops.extend(route.into_iter().rev());assert_eq!(circ.b.next_qubit,nq);let ops=circ.b.ops.clone();
        assert!(ops.iter().all(|op|matches!(op.kind,K::X|K::CX|K::CCX)));
        for op in &ops{for h in 256..259{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q);}}
        let mut fixed=Fixed;let mut sim=Simulator::new(nq as usize,0,&mut fixed);
        // The unpruned route covers every rank x A_low x C_low. Each other
        // distinct selector lower bound also covers all tuples; active rows enforce
        // A>=lo (a superset of any certified interval), while bypass data are arbitrary.
        for pattern in 0..3{for batch in 0..2048{
            let mut seed=0x793ca77f3e41u64^((lo as u64)<<32)^((offset as u64)<<24)^((pattern as u64)<<20)^batch as u64;
            let mut before:Vec<_>=(0..nq).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            let rk=batch&31;let cv=64*ts[rk][1]+(batch>>5);
            for lane in 0..64{
                let av=64*ts[rk][0]+lane;let sum=av+cv;let enabled=pattern==0&&sum<=253&&(lo..hi).contains(&av);
                set(&mut before,&rank,lane,rk);set(&mut before,&a,lane,lane);set(&mut before,&c,lane,cv&63);put(&mut before,&g,lane,enabled);put(&mut before,&carry,lane,pattern==2);
                for i in 0..nq as usize{let m=1u64<<lane;after[i]=(after[i]&!m)|(before[i]&m);}
                if enabled{
                    let q=&w1[sum+offset];let bit=get(&before,q,lane);let old=get(&before,&out,lane);
                    if offset==2{put(&mut after,q,lane,old);put(&mut after,&out,lane,bit);}else{put(&mut after,&out,lane,old^bit);}
                    active+=1;
                }else{off+=1;}
            }
            sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"R01 route lo={lo} hi={hi} offset={offset} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("Q793_R01_ROUTES_CLOCK_PASS support={lo}..{hi} offset={offset} ops={}",ops.len());
    }}
    eprintln!("Q793_R01_ROUTES_PASS total={total} active={active} offguard={off}; all rank/low-A/low-C/support intervals, dirty bypass carry, copy/swap centers, all wires/phase/inverse/three holes; component only");
}
