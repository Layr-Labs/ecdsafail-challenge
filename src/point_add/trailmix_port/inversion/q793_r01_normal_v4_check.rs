//! Actual scalar-capsule arithmetic test of the external-lease normal core.
use super::*;
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn bit(r:&[u8],i:usize)->bool{r[i/8]>>(i%8)&1!=0}
fn bits(r:&[u8],i:usize,n:usize)->usize{(0..n).map(|k|(bit(r,i+k)as usize)<<k).sum()}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let m=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!m)|if v{m}else{0};}
fn get(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
fn set(w:&mut[u64],qs:&[QReg],l:usize,v:usize){for(i,q)in qs.iter().enumerate(){put(w,q,l,v>>i&1!=0);}}
pub(super) fn run(){
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").expect("explicit own scalar capsule")).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let ts=triples();let mut total=0usize;let mut off=0usize;let mut counts=[0usize;4];let mut a2=0usize;let mut high_a=0usize;let mut rows_out=Vec::new();
    for normalized in [false,true]{for j in 0..4{
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
        let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let g=circ.alloc_qreg("external.g");let mask=circ.alloc_qreg("external.mask");let hs=circ.alloc_qreg("external.hs");let ha=circ.alloc_qreg("external.HA");let decision=circ.alloc_qreg("external.decision");
        let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("external.dirty",20);let nq=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&sm,&g,&mask,&hs,&ha,&decision,&w1,&w2,&dirty,j,259,normalized);
        assert_eq!(circ.b.next_qubit,nq);let ops=circ.b.ops.clone();for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let nt=ops.iter().filter(|o|o.kind==K::CCX).count();eprintln!("Q793_R01_CLEAN_ROUTE_CORE_BUILT j={j} ops={} T={nt}",ops.len());
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|row|{
            let time=u16::from_le_bytes(row[..2].try_into().unwrap())as usize;let r=&row[2..70];let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);
            (time+3)&3==j&&bits(r,21,2)==2&&av+cv<=253&&{let raw=64*ts[rk][2]+4*bits(r,17,4)+(j&1)+2*((j>>1)^(cv&1)); (av==1&&raw==1)==normalized}
        }).collect();
        if rows.is_empty(){continue;}
        let mut f=Fixed;let mut sim=Simulator::new(nq as usize,0,&mut f);let mut here=0;
        for pattern in 0..6{for batch in 0..rows.len().div_ceil(64){
            let mut seed=0x79301abc53fe102u64^((j as u64)<<40)^((pattern as u64)<<32)^batch as u64;
            let mut before:Vec<_>=(0..nq).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let r=&rows[(batch*64+lane)%rows.len()][2..70];let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);let sum=av+cv;
                let sraw=64*ts[rk][2]+4*bits(r,17,4)+(j&1)+2*((j>>1)^(cv&1));let sold=if sraw==0{256}else{sraw};let shift=sold-1;
                assert!(sum+sold<=256);let n=256-sum;
                set(&mut before,&rank,lane,rk);set(&mut before,&a,lane,av&63);set(&mut before,&c,lane,cv&63);set(&mut before,&sm,lane,bits(r,17,4));
                for i in 0..259{put(&mut before,&w1[i],lane,bit(r,25+i));put(&mut before,&w2[i],lane,bit(r,284+i));}
                let even=!bit(r,25);if even{for k in 0..3{put(&mut before,&w2[(259+k-sold%259)%259],lane,bit(r,25+258-k));}}
                assert!(bit(r,25+av));assert!(!bit(r,284+av+1));
                let first=if pattern<4{pattern&1!=0}else{rnd(&mut seed)&1!=0};let second=if pattern<4{pattern&2!=0}else{rnd(&mut seed)&1!=0};
                put(&mut before,&w1[av],lane,first);put(&mut before,&w2[av+1],lane,second);
                put(&mut before,&w1[av+1],lane,rnd(&mut seed)&1!=0);
                let rotated:Vec<_>=(0..259).map(|i|get(&before,&w2[(i+258)%259],lane)).collect();for i in 0..259{put(&mut before,&w2[i],lane,rotated[i]);}
                if normalized{put(&mut before,&sm[3],lane,rnd(&mut seed)&1!=0);}else{put(&mut before,&w2[av+1],lane,rnd(&mut seed)&1!=0);}
                let h=bit(r,25+sum+2);put(&mut before,&w1[sum+2],lane,rnd(&mut seed)&1!=0); // actual taken decision loan
                put(&mut before,&g,lane,true);put(&mut before,&mask,lane,false);put(&mut before,&hs,lane,false);put(&mut before,&ha,lane,false);put(&mut before,&decision,lane,h);
                for hole in [256,257,258]{put(&mut before,&w1[hole],lane,rnd(&mut seed)&1!=0);}
                for i in 0..nq as usize{let m=1u64<<lane;after[i]=(after[i]&!m)|(before[i]&m);}
                let x:Vec<_>=(0..n).map(|i|i>=shift&&get(&before,&w2[258-i],lane)).collect();let y:Vec<_>=(0..n).map(|i|bit(r,25+258-i)).collect();
                let ge=(0..n).rev().find(|&i|x[i]!=y[i]).map(|i|y[i]).unwrap_or(true);let q=h^ge;
                let mut out=y.clone();let mut borrow=false;if q{for i in 0..n{out[i]=y[i]^x[i]^borrow;borrow=(!y[i]&&(x[i]||borrow))||(x[i]&&borrow);}}
                for i in 3..n{put(&mut after,&w1[258-i],lane,out[i]);}
                if even{for k in 0..3{put(&mut after,&w2[(259+k-shift%259)%259],lane,out[k]);}}
                put(&mut after,&decision,lane,q);counts[shift.min(3)]+=1;a2+=usize::from(av==2);high_a+=usize::from(av>=252);here+=1;
            }
            sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,format!("{:016x}",a^b))).collect();panic!("Q793 R01 normal v4 normalized={normalized} j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        // Independent off-guard metadata/work values, including every rank,
        // low-A word and arbitrary SM leases/HA/masks/decision.
        for batch in 0..512{let mut seed=0x793f010ffu64^((j as u64)<<40)^batch as u64;let mut before:Vec<_>=(0..nq).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{set(&mut before,&rank,lane,batch&31);set(&mut before,&a,lane,lane);set(&mut before,&sm,lane,batch>>5);put(&mut before,&g,lane,false);}
            sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(ops.iter());assert_eq!(sim.qubits,before,"Q793 normal g0 j={j} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);off+=64;
        }
        rows_out.push(format!("{{\"normalized_sm3\":{normalized},\"clock\":{j},\"active_lanes\":{here},\"T\":{nt},\"ops\":{}}}",ops.len()));
    }
    }
    println!("{{\"kind\":\"Q793 R04 actual-carry normal R01 core\",\"active_lanes\":{total},\"offguard_lanes\":{off},\"shift0_1_2_ge3\":{counts:?},\"A2\":{a2},\"A252_253\":{high_a},\"results\":[{}],\"zero_lease_wrappers_tested\":false,\"whole_q793\":false}}",rows_out.join(","));
    eprintln!("Q793_R01_CLEAN_ROUTE_CORE_PASS active={total} offguard={off}; native phase/inverse,three physical holes, low3 qpre/borrow, A2head/two-passenger/highA, external leases only; no wholeQ793 claim");
}
