//! New independent general C>=2 full-wrapper checker; old C07 files untouched.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
fn get(r:&[u8],field:usize,bit:usize)->bool{r[field*32+bit/8]>>(bit%8)&1!=0}
pub fn run(){
    let path=std::env::var("Q794_SIGN_GENERAL_CAPSULE").expect("explicit own capsule path");
    let data=std::fs::read(path).unwrap();assert_eq!(&data[..8],b"Q794SIG1");
    assert_eq!(data.len(),12+132*u32::from_le_bytes(data[8..12].try_into().unwrap())as usize);
    std::env::set_var("Q796_PARITY","1");std::env::set_var("Q795_PHASE_LOAN","1");std::env::set_var("Q794_MOD4","1");
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0;let mut active=0;
    for j in 0..4{
        let rows:Vec<_>=data[12..].chunks_exact(132).filter(|r|(4-r[130]as usize%4)%4==j).collect();assert!(!rows.is_empty());
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let sign=circ.alloc_qreg("Sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("dirty",23);let owned=circ.b.next_qubit;
        super::q794_sign::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&dirty,j,258);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
        for o in &b.ops{o.validate();assert!(matches!(o.kind,K::X|K::CX|K::CCX));for h in [257,258]{let q=w1[h].id()as u64;assert!(o.q_target.0!=q&&o.q_control1.0!=q&&o.q_control2.0!=q,"hole{h}");}}
        eprintln!("Q794_SIGN_GENERAL_BUILT j={j} rows={} T={} ops={}",rows.len(),b.ops.iter().filter(|o|o.kind==K::CCX).count(),b.ops.len());
        for pattern in 0..11{for batch in 0..rows.len().div_ceil(64){let mut rng=0xa7945100ce1u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
            for lane in 0..64{let r=rows[(batch*64+lane)%rows.len()];let av=r[128]as usize;let cv=r[129]as usize;let sv=r[130]as usize;
                assert!(cv>=2&&cv<=255&&av<=254&&av+cv+sv<=257);
                let rk=ts.iter().position(|&t|t==[av/64,cv/64,sv/64]).unwrap();
                let phase=if pattern<8{3}else{pattern-8};
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,rk>>i&1!=0);}
                    for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);put(w,&c[i],lane,cv>>i&1!=0);}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);put(w,&sign,lane,phase==3&&r[131]!=0);
                    for i in 0..259{
                        let tbit=i<=av&&get(r,0,i);let rbit=i>=259-cv&&i<=256&&get(r,2,258-i);
                        put(w,&w1[i],lane,tbit||rbit);
                        let raw=(i+sv)%259;let ubit=raw<257-cv&&get(r,1,raw);let vbit=raw>=259-cv&&get(r,3,258-raw);
                        put(w,&w2[i],lane,ubit||vbit);
                    }
                    if !get(r,0,0){put(w,&w2[(259-sv)%259],lane,get(r,2,0));put(w,&w2[(260-sv)%259],lane,get(r,2,1));}
                    put(w,&w2[259-cv-sv],lane,pattern&1!=0);
                    put(w,&w1[av+1],lane,pattern&2!=0);
                    put(w,&w1[av+2],lane,pattern&4!=0);
                }
                if phase==3{put(&mut after,&sign,lane,false);active+=1;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let bad:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("Sign general j={j} pattern={pattern} batch={batch} diffs={bad:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }
    eprintln!("Q794_SIGN_GENERAL_PASS lanes={total} active={active}; independent Euclidean tuples C>=2, odd/even chart,S0/S1/highS, all8payloadpatterns+3offguards, sourceholes absent, phase/inverse/allwire restoration; not whole circuit");
}
