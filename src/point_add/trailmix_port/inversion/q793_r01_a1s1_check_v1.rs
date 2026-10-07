//! Independent bounded interval oracle for every C-address branch of A1/S1.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let m=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!m)|if v{m}else{0};}
fn get(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
fn set(w:&mut[u64],qs:&[QReg],l:usize,v:usize){for(i,q)in qs.iter().enumerate(){put(w,q,l,v>>i&1!=0);}}
pub fn run(){
    let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
    let rank=circ.alloc_qreg_bits("rank",5);let c=circ.alloc_qreg_bits("C",6);let sm=circ.alloc_qreg_bits("SM",4);
    let g=circ.alloc_qreg("g");let mask=circ.alloc_qreg("mask");let hs=circ.alloc_qreg("hs");let ha=circ.alloc_qreg("HA");let decision=circ.alloc_qreg("decision");
    let w1=circ.alloc_qreg_bits("W1",259);let w2=circ.alloc_qreg_bits("W2",259);let dirty=circ.alloc_qreg_bits("dirty",20);let nq=circ.b.next_qubit;
    super::q793_r01_a1s1_v1::emit(&mut circ,&rank,&c,&sm,&g,&mask,&hs,&ha,&decision,&w1,&w2,&dirty,259);
    assert_eq!(circ.b.next_qubit,nq);for op in &circ.b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
    let nt=circ.b.ops.iter().filter(|o|o.kind==K::CCX).count();eprintln!("Q793_A1S1_SYNTH_BUILT ops={} T={nt}",circ.b.ops.len());
    let mut f=Fixed;let mut sim=Simulator::new(nq as usize,0,&mut f);let mut active=0;
    for cv in 0..253{for batch in 0..32{
        let mut rng=0x793a151000u64^((cv as u64)<<32)^batch as u64;
        let mut before:Vec<_>=(0..nq).map(|_|rnd(&mut rng)).collect();let mut expected=before.clone();
        for lane in 0..64{
            let code=64*batch+lane;let odd=code&1!=0;let mut b=if odd{(code>>1&7)%3}else{code>>1&7};
            let v=if odd{code>>4&7}else{(code>>4&7)|1};let wanted=code>>7&3;let h=code>>9&1!=0;let n=255-cv;
            set(&mut before,&rank,lane,[0,4,8,11][cv/64]);set(&mut before,&c,lane,cv&63);
            for k in 0..3{put(&mut before,&sm[k],lane,false);} // SM3 keeps an arbitrary passenger.
            put(&mut before,&g,lane,true);for q in [&mask,&hs,&ha]{put(&mut before,q,lane,false);}put(&mut before,&decision,lane,h);
            put(&mut before,&w1[0],lane,odd);
            for k in 0..cv{put(&mut before,&w1[cv+2-k],lane,rnd(&mut rng)&1!=0);}
            for k in 0..cv.min(2){put(&mut before,&w1[cv+2-k],lane,wanted>>k&1!=0);}if cv>0{put(&mut before,&w1[3],lane,true);}
            let qp=(0..cv.min(2)).map(|k|(get(&before,&w1[cv+2-k],lane)as usize)<<(k+1)).sum::<usize>();
            if !odd{b=(b&4)|((7usize.wrapping_sub(v).wrapping_sub(2*qp*v)/2)&3);}
            let r=if odd{7usize.wrapping_sub(b*v).wrapping_mul(3).wrapping_sub(qp*v)&7}else{b};
            let t=if odd{3}else{2};let u=if odd{b}else{1};assert_eq!((t*r+u*v+qp*t*v)&7,7);
            for k in 0..3{put(&mut before,&w2[k],lane,b>>k&1!=0);put(&mut before,&w2[258-k],lane,v>>k&1!=0);}
            for i in 0..nq as usize{let m=1u64<<lane;expected[i]=(expected[i]&!m)|(before[i]&m);}
            let y:Vec<_>=(0..n).map(|i|if i<3{r>>i&1!=0}else{get(&before,&w1[258-i],lane)}).collect();
            let x:Vec<_>=(0..n).map(|i|get(&before,&w2[258-i],lane)).collect();
            let ge=(0..n).rev().find(|&i|x[i]!=y[i]).map(|i|y[i]).unwrap_or(true);let q=h^ge;
            let mut out=y.clone();if q{let mut borrow=false;for i in 0..n{out[i]=y[i]^x[i]^borrow;borrow=(!y[i]&&(x[i]||borrow))||(x[i]&&borrow);}}
            for i in 3..n{put(&mut expected,&w1[258-i],lane,out[i]);}if !odd{for i in 0..3{put(&mut expected,&w2[i],lane,out[i]);}}
            put(&mut expected,&decision,lane,q);
        }
        sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(circ.b.ops.iter());
        if sim.qubits!=expected{let diffs:Vec<_>=sim.qubits.iter().zip(&expected).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,format!("{:016x}",a^b))).collect();panic!("A1S1 synthetic C={cv} batch={batch} diffs={diffs:?}");}
        assert_eq!(sim.phase,0);sim.apply_iter(circ.b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);active+=64;
    }}
    let mut off=0;for rk in 0..32{for smv in 0..16{
        let mut rng=0x793a1ffu64^((rk as u64)<<32)^smv as u64;let mut before:Vec<_>=(0..nq).map(|_|rnd(&mut rng)).collect();
        for lane in 0..64{set(&mut before,&rank,lane,rk);set(&mut before,&c,lane,lane);set(&mut before,&sm,lane,smv);put(&mut before,&g,lane,false);}
        sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(circ.b.ops.iter());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
        sim.apply_iter(circ.b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);off+=64;
    }}
    println!("{{\"kind\":\"A1S1 exact bounded interval oracle\",\"C_values\":253,\"active_lanes\":{active},\"offguard_lanes\":{off},\"T\":{nt},\"ops\":{},\"whole_q793\":false}}",circ.b.ops.len());
    eprintln!("Q793_A1S1_SYNTH_PASS active={active} offguard={off}; every C0..252, bounded valid low charts, independent whole-interval subtraction, all dirty/phase/inverse/parked SM3");
}
