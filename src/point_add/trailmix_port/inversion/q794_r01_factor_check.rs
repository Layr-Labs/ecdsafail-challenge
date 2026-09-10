//! Candidate-only exact Boolean/phase/dirty test of the factored low seed.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x96)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],qs:&[QReg],l:usize,v:usize){for(i,q)in qs.iter().enumerate(){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v>>i&1!=0{b}else{0};}}
fn truth(z:usize,shift:usize)->bool{
    let mut t=z&3;let mut b=z>>2&3;let mut v=z>>4&3;let mut q=z>>6&1;
    if z&128!=0{t=1;b=0;}else if z&256!=0{t|=2;}
    if shift==1&&z&512!=0{v&=1;}if z&1024!=0{q=0;}
    let r=if t&1!=0{3usize.wrapping_sub(b*v).wrapping_mul(t).wrapping_sub(if shift==0{2*q*v}else{0})&3}else{b};
    r<((v<<shift)&3)
}
pub(super) fn run(){
    let ts=super::super::triples();let mut total=0;let mut counts=Vec::new();
    for shift in 0..2{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);
        let chart=circ.alloc_qreg_bits("chart",7);let g=circ.alloc_qreg_bits("g",1);let mask=circ.alloc_qreg_bits("mask",1);let ha=circ.alloc_qreg_bits("carry",1);let dirty=circ.alloc_qreg_bits("borrowed",20);let owned=circ.b.next_qubit;
        let mut anf:Vec<_>=(0..2048).map(|z|truth(z,shift)).collect();for i in 0..11{for m in 0..2048{if m>>i&1!=0{anf[m]^=anf[m^(1<<i)];}}}
        let flags:Vec<_>=(0..4).map(|f|super::super::flag_terms(&rank,&a,&c,f)).collect();
        super::emit(&mut circ,&chart.iter().collect::<Vec<_>>(),&g[0],&mask[0],&ha[0],&dirty,&flags,&anf,shift);
        assert_eq!(circ.b.next_qubit,owned);let builder=circ.into_builder();for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let nt=builder.ops.iter().filter(|op|op.kind==K::CCX).count();
        // Focused exact metadata classes for the new common-literal/rank
        // cofactor: all32 ranks, A_low in {0,1,other,62}, C_low zero/nonzero,
        // each of four guards. Full chart/carry/lender coverage follows below.
        let n=32*4*2*4;let mut checked=0;
        for batch in 0..n/64{
            let mut seed=0x794fac702u64^((shift as u64)<<48)^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut expected=before.clone();
            for l in 0..64{
                let code=batch*64+l;let rk=(code>>5)&31;let av=[0usize,1,2,62][(code>>3)&3];let cv=(code>>2)&1;let guards=code&3;
                put(&mut before,&rank,l,rk);put(&mut before,&a,l,av);put(&mut before,&c,l,cv);put(&mut before,&g,l,guards&1);put(&mut before,&mask,l,guards>>1);
                let ch=(rnd(&mut seed)&127)as usize;put(&mut before,&chart,l,ch);
                for i in 0..owned as usize{expected[i]=(expected[i]&!(1u64<<l))|(before[i]&(1u64<<l));}
                let aa=64*ts[rk][0]+av;let cc=64*ts[rk][1]+cv;
                let z=ch|(usize::from(aa==0)<<7)|(usize::from(aa==1)<<8)|(usize::from(aa==254)<<9)|(usize::from(cc==0)<<10);
                if guards==3&&truth(z,shift){expected[ha[0].id()as usize]^=1u64<<l;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());assert_eq!(sim.qubits,expected,"lowseed shift={shift} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);checked+=64;
        }
        // All chart truth codes, guards and incoming carry/lender bit choices
        // at focused virtual/cargo metadata, not only random chart coverage.
        let metas=[(0usize,0usize,0usize),(0,1,0),(0,2,0),(0,0,1),(0,1,1),(0,2,1),(31,62,0),(29,62,0)];
        for &(rk,av,cv)in &metas{for batch in 0..128{
            let mut seed=0x794fac703u64^((shift as u64)<<48)^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut expected=before.clone();
            for l in 0..64{
                let code=batch*64+l;let ch=code&127;let guards=(code>>7)&3;let pattern=code>>9;
                put(&mut before,&rank,l,rk);put(&mut before,&a,l,av);put(&mut before,&c,l,cv);put(&mut before,&chart,l,ch);put(&mut before,&g,l,guards&1);put(&mut before,&mask,l,guards>>1);
                put(&mut before,&ha,l,pattern&1);put(&mut before,&dirty[..3],l,pattern>>1);
                for i in 0..owned as usize{expected[i]=(expected[i]&!(1u64<<l))|(before[i]&(1u64<<l));}
                let aa=64*ts[rk][0]+av;let cc=64*ts[rk][1]+cv;
                let z=ch|(usize::from(aa==0)<<7)|(usize::from(aa==1)<<8)|(usize::from(aa==254)<<9)|(usize::from(cc==0)<<10);
                if guards==3&&truth(z,shift){expected[ha[0].id()as usize]^=1u64<<l;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());assert_eq!(sim.qubits,expected,"lowseed focused shift={shift}");assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);checked+=64;
        }}
        assert_eq!(checked,66560);assert_eq!(nt,[1860,608][shift]);
        counts.push(format!("{{\"shift\":{shift},\"T\":{nt},\"ops\":{},\"lanes\":{checked},\"extra_allocations\":0}}",builder.ops.len()));total+=checked;eprintln!("Q794_SEED_FACTOR_PASS shift={shift} T={nt} lanes={checked}");
    }
    println!("{{\"kind\":\"exact R01 factored seed\",\"lanes\":{total},\"results\":[{}],\"whole_claim\":false}}",counts.join(","));
}
