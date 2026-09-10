//! Own native checks: mask loan, exact C1 funding, full C1 wrapper, low chart.
use super::*;
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
fn bit(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
fn clean_ops(b:&crate::point_add::B,w1:&[QReg]){
    for o in &b.ops{o.validate();assert!(matches!(o.kind,K::X|K::CX|K::CCX));
        for h in [257,258]{let q=w1[h].id()as u64;assert!(o.q_target.0!=q&&o.q_control1.0!=q&&o.q_control2.0!=q,"Sign touched omitted{h}");}}
}
fn assert_same(got:&[u64],want:&[u64],tag:&str,j:usize,batch:usize){
    if got!=want{let bad:Vec<_>=got.iter().zip(want).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("{tag} j={j} batch={batch} diffs={bad:?}");}
}

fn mask_test()->usize{
    let ts=triples();let mut total=0;
    for j in 0..4{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let g=circ.alloc_qreg("g");let cache=circ.alloc_qreg("cache");let mask=circ.alloc_qreg("mask");let w1=circ.alloc_qreg_bits("w1",259);let dirty=circ.alloc_qreg_bits("dirty",21);let owned=circ.b.next_qubit;
        mask_loan(&mut circ,&rank,&c,&sm,&g,&cache,&mask,&w1,&dirty,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();clean_ops(&b,&w1);
        let cases:Vec<_>=(1..256).flat_map(|cv|(0..=257-cv).filter(move|&sv|sv<256&&sv%4==(4-j)%4).map(move|sv|(cv,sv))).collect();
        for pattern in 0..4{for batch in 0..cases.len().div_ceil(64){let mut rng=0xa794c1001u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
            for lane in 0..64{let(cv,sv)=cases[(batch*64+lane)%cases.len()];let r=ts.iter().position(|&t|t==[0,cv/64,sv/64]).unwrap();let on=pattern<2;
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}
                    for i in 0..6{put(w,&c[i],lane,cv>>i&1!=0);}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&g,lane,on);if on{put(w,&cache,lane,false);}
                }
                if on{let host=if cv==1{if sv==0{255}else{256}}else{258-cv};
                    // Both possible C1 hosts are zero, not merely the selected
                    // one: the selector's temporary source256 loan is exact.
                    for w in [&mut before,&mut after]{put(w,&w1[host],lane,false);if cv==1{put(w,&w1[255],lane,false);put(w,&w1[256],lane,false);}}
                    let old=bit(&before,&mask,lane);put(&mut after,&mask,lane,false);put(&mut after,&w1[host],lane,old);
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_same(&sim.qubits,&after,"mask",j,batch);assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }total
}

fn combined_top_test()->usize{
    let ts=triples();let mut total=0;
    for j in 0..4{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let g=circ.alloc_qreg("g");let cache=circ.alloc_qreg("cache");let mask=circ.alloc_qreg("mask");let carry=circ.alloc_qreg("carry");let w1=circ.alloc_qreg_bits("w1",259);let dirty=circ.alloc_qreg_bits("dirty",20);let owned=circ.b.next_qubit;
        top_flag_and_loan(&mut circ,&rank,&c,&sm,&g,&cache,&mask,&carry,&w1,&dirty,j);
        assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();clean_ops(&b,&w1);
        let cases:Vec<_>=(1..256).flat_map(|cv|(0..=257-cv).filter(move|&sv|sv<256&&sv%4==(4-j)%4).map(move|sv|(cv,sv))).collect();
        for pattern in 0..4{for batch in 0..cases.len().div_ceil(64){let mut rng=0xa794f05ed_u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
            for lane in 0..64{let(cv,sv)=cases[(batch*64+lane)%cases.len()];let r=ts.iter().position(|&t|t==[0,cv/64,sv/64]).unwrap();let on=pattern<2;let top=pattern&1!=0;let k=257-cv-sv;
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}
                    for i in 0..6{put(w,&c[i],lane,cv>>i&1!=0);}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&g,lane,on);put(w,&w1[k],lane,top);
                    if on{put(w,&cache,lane,false);put(w,&mask,lane,false);}
                }
                if on{put(&mut after,&mask,lane,top);if !top{let old=bit(&before,&carry,lane);put(&mut after,&carry,lane,false);put(&mut after,&w1[k],lane,old);}}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_same(&sim.qubits,&after,"combined top",j,batch);assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }total
}

fn c1_wrapper_test()->(usize,usize){
    let ts=triples();let mut total=0;let mut funded=0;
    const P:[u64;4]=[0xffff_fffe_ffff_fc2f,u64::MAX,u64::MAX,u64::MAX];
    for j in 0..4{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let g=circ.alloc_qreg("p1");let cache=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("Sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("dirty",23);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&sm,&g,&cache,&sign,&w1,&w2,&dirty,j,258);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();clean_ops(&b,&w1);
        eprintln!("Q794_SIGN_C1_BUILT j={j} ops={} T={}",b.ops.len(),b.ops.iter().filter(|o|o.kind==K::CCX).count());
        let mut pc=Circuit::new();pc.b.count_only=false;pc.b.fiat_hash=None;pc.b.next_qubit=owned;
        super::measurement::emit(&mut pc,&rank,&a,&c,&sm,&g,&cache,&sign,&w1,&w2,&dirty,j,258);
        assert_eq!(pc.b.next_qubit,owned);let phase_ops=pc.into_builder().ops;
        let mut fc=Circuit::new();fc.b.next_qubit=owned;
        // Funding circuit consumes recoded g=1/cache=0 directly, as the
        // adapter does after its phase-code permutation.
        super::super::q798_handoffs::move_t11(&mut fc,&rank,&a,&c,&sm,&g,&cache,&w1,&w2,&dirty,j);
        move_top_cargo(&mut fc,&rank,&a,&c,&sm,&g,&cache,&w1,&w2,&dirty,j);let fb=fc.into_builder();clean_ops(&fb,&w1);
        let cases:Vec<_>=(0..255).flat_map(|av|(0..=(256-av).min(255)).filter(move|&sv|sv%4==(4-j)%4).map(move|sv|(av,sv))).collect();
        for pattern in 0..8{for batch in 0..cases.len().div_ceil(64){let mut rng=0xa794c1be1u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();let mut fundin=before.clone();
            for lane in 0..64{let(av,sv)=cases[(batch*64+lane)%cases.len()];let r=ts.iter().position(|&t|t==[av/64,0,sv/64]).unwrap();
                let mut t=[0u64;4];for z in &mut t{*z=rnd(&mut rng);}for k in av+1..256{t[k/64]&=!(1u64<<(k%64));}t[av/64]|=1u64<<(av%64);
                if av==254{t[253/64]&=!(1u64<<(253%64));} // strict t<p/2
                if av>0{t[0]=(t[0]&!1)|(pattern&1)as u64;}
                let mut larger=false;for k in 0..256{let x=t[k/64]>>(k%64)&1!=0;let y=k+sv<256&&(P[(k+sv)/64]>>((k+sv)%64)&1!=0);if x!=y{larger=x;}}
                for w in [&mut before,&mut after,&mut fundin]{
                    for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}
                    for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);put(w,&c[i],lane,i==0);}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&g,lane,true);put(w,&cache,lane,true);put(w,&sign,lane,larger);
                    for i in 0..259{
                        put(w,&w1[i],lane,i<256&&(t[i/64]>>(i%64)&1!=0));
                        let raw=(i+sv)%259;let ubit=raw<256&&(P[raw/64]>>(raw%64)&1!=0);put(w,&w2[i],lane,ubit||raw==258);
                    }
                    if t[0]&1==0{put(w,&w2[(259-sv)%259],lane,false);put(w,&w2[(260-sv)%259],lane,false);}
                    // Entry-boundary passengers: residual head, Sign-gap
                    // host, and second cargo at A+2. All independent.
                    put(w,&w2[258-sv],lane,pattern&2!=0);
                    put(w,&w1[av+1],lane,pattern&4!=0);
                    put(w,&w1[av+2],lane,pattern&2==0);
                }
                put(&mut after,&sign,lane,false);put(&mut fundin,&cache,lane,false);
            }
            let mut f=Fixed;let mut fs=Simulator::new(owned as usize,0,&mut f);fs.qubits.copy_from_slice(&fundin);fs.apply_iter(fb.ops.iter());
            for lane in 0..64{assert!(!bit(&fs.qubits,&w1[255],lane),"C1 funding255 j={j} batch={batch}");assert!(!bit(&fs.qubits,&w1[256],lane),"C1 funding256 j={j} batch={batch}");}
            fs.apply_iter(fb.ops.iter().rev());assert_eq!(fs.qubits,fundin);assert_eq!(fs.phase,0);funded+=64;
            super::super::q794_mbu_native::check(&before,&b.ops,&phase_ops,crate::circuit::QubitId(sign.id()as u64));
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_same(&sim.qubits,&after,"fullC1",j,batch);assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }(total,funded)
}

pub fn run(){
    std::env::set_var("Q796_PARITY","1");std::env::set_var("Q795_PHASE_LOAN","1");std::env::set_var("Q794_MOD4","1");
    let mask=mask_test();let combined_top=combined_top_test();let(full,funding)=c1_wrapper_test();
    eprintln!("Q794_SIGN_COMBINED_TOP_PASS lanes={combined_top}; exhaustive valid C/S addresses, both top branches, arbitrary carry/dirty, offguard cache/mask, exact phase/inverse, noholes/noalloc");
    eprintln!("Q794_SIGN_NATIVE_PASS mask={mask} fullC1={full} C1_funding={funding}; phase0, inverse/allwire/dirty restoration, noholes, noalloc; C>=2 fullwrapper and whole step pending");
}
