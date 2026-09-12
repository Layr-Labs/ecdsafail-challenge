//! Independent integer-capsule native whole-wrapper qualification.
use super::*;
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
fn bit(r:&[u8],field:usize,i:usize)->bool{r[field*32+i/8]>>(i%8)&1!=0}
pub fn run(){
    let path=std::env::var("Q793_SIGN_CAPSULE").expect("explicit own scalar capsule");let data=std::fs::read(path).unwrap();assert_eq!(&data[..8],b"Q793SIG1");
    let rowcount=u32::from_le_bytes(data[8..12].try_into().unwrap())as usize;assert_eq!(data.len(),12+132*rowcount);
    let count_only=std::env::var_os("Q793_SIGN_COUNT_ONLY").is_some();
    let ts=triples();let mut total=0usize;let mut active=0usize;let mut short=0usize;let mut s0=0usize;let mut a254=0usize;
    for j in 0..4{
        let rows:Vec<_>=data[12..].chunks_exact(132).filter(|r|(4-r[130]as usize%4)%4==j).collect();assert!(!rows.is_empty());
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("dirty",23);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&helpers,j,256);assert_eq!(circ.b.next_qubit,owned);let builder=circ.into_builder();
        for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Sign touched hole{h}");}}
        eprintln!("Q793_SIGN_R02_BUILT j={j} rows={} ops={} T={}",rows.len(),builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
        if count_only{continue;}
        for pattern in 0..11{for batch in 0..rows.len().div_ceil(64){
            let mut rng=0x79351999183u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
            for lane in 0..64{let r=rows[(64*batch+lane)%rows.len()];let av=r[128]as usize;let cv=r[129]as usize;let sv=r[130]as usize;let phase=if pattern<8{3}else{pattern-8};
                let rk=ts.iter().position(|&t|t==[av/64,cv/64,sv/64]).unwrap();assert!(av+cv+sv<=257);
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,rk>>i&1!=0);}
                    for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);put(w,&c[i],lane,cv>>i&1!=0);}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);put(w,&sign,lane,phase==3&&r[131]!=0);
                    for i in 0..259{
                        if i<256{put(w,&w1[i],lane,(i<=av&&bit(r,0,i))||(i>=259-cv&&bit(r,2,258-i)));}
                        let raw=(i+sv)%259;put(w,&w2[i],lane,(raw<257-cv&&bit(r,1,raw))||(raw>=259-cv&&bit(r,3,258-raw)));
                    }
                    if !bit(r,0,0){for i in 0..3{put(w,&w2[(259+i-sv)%259],lane,bit(r,2,i));}}
                    put(w,&w2[259-cv-sv],lane,pattern&1!=0);
                    put(w,&w1[av+1],lane,pattern&2!=0);
                    let second=if av==254{&w2[if sv==0{256}else{255}]}else{&w1[av+2]};put(w,second,lane,pattern&4!=0);
                }
                if phase==3{put(&mut after,&sign,lane,false);active+=1;if 257-cv-sv<=3{short+=1;}if sv==0{s0+=1;}if av==254{a254+=1;}}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
            if sim.qubits!=after{let bad:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();
                let lanes:u64=sim.qubits.iter().zip(&after).map(|(x,y)|x^y).fold(0,|x,y|x|y);let cases:Vec<_>=(0..64).filter(|&l|lanes>>l&1!=0).map(|l|{let r=rows[(64*batch+l)%rows.len()];(l,r[128],r[129],r[130],r[131])}).collect();panic!("Sign r02 j={j} pattern={pattern} batch={batch} diffs={bad:?} cases={cases:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }
    if count_only{eprintln!("Q793_SIGN_R02_COUNT_ONLY all4templates; no native PASS claim");return;}
    eprintln!("Q793_SIGN_R02_PASS lanes={total} active={active} short={short} S0={s0} A254={a254} scalar_rows={rowcount}; complete Sign wrapper, one funded mask, no clean carry, all three absent rails, all eight cargo patterns and three off phases, exact phase/inverse/allwire restoration; no whole-step claim");
}
