//! Qualification of the new residual hold, against its exact predecessor map.
use super::*;
use crate::{circuit::{Op,OperationType as K},sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn build(block:usize,j:usize,on:bool,component:bool)->Vec<Op>{
    std::env::set_var(residual_hold::SWITCH,if on{"1"}else{"0"});
    let mut circ=Circuit::new();
    let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let it=circ.alloc_qreg("it");
    let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("helpers",23);
    if component{
        let pool:Vec<_>=helpers.iter().chain(std::iter::once(&it)).map(QReg::borrowed_alias).collect();
        residual_hold::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&pool[0],&w1,&w2,&pool[1..],j);
    }else{step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&helpers,j,block);}
    assert_eq!(circ.b.next_qubit,565);let ops=circ.into_builder().ops;
    for o in &ops{o.validate();assert!(matches!(o.kind,K::X|K::CX|K::CCX));for hole in [280,281,282]{assert!(o.q_target.0!=hole&&o.q_control1.0!=hole&&o.q_control2.0!=hole);}}
    ops
}
fn compare(base:&[Op],held:&[Op],before:&[u64],label:&str){
    let mut fa=Fixed;let mut fb=Fixed;let mut a=Simulator::new(565,0,&mut fa);let mut b=Simulator::new(565,0,&mut fb);
    a.qubits.copy_from_slice(before);b.qubits.copy_from_slice(before);a.apply_iter(base.iter());b.apply_iter(held.iter());
    assert_eq!(a.qubits,b.qubits,"forward {label}");assert_eq!(a.phase,0);assert_eq!(b.phase,0);
    a.apply_iter(base.iter().rev());b.apply_iter(held.iter().rev());
    assert_eq!(a.qubits,before,"base inverse {label}");assert_eq!(b.qubits,before,"held inverse {label}");assert_eq!(a.phase,0);assert_eq!(b.phase,0);
}
fn put(word:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;word[i]=(word[i]&!bit)|if v{bit}else{0};}
pub fn component(){
    let mut cases=0usize;
    for j in 0..4{
        let base=build(0,j,false,true);let held=build(0,j,true,true);
        if j%2==1{assert!(base.is_empty()&&held.is_empty());continue;}
        for av in [0,1,60,61,62,63]{for loans in 0..4{for batch in 0..2048{
            let mut seed=0x7935_2e51_d0a1_u64^((j as u64)<<48)^((av as u64)<<32)^((loans as u64)<<24)^batch as u64;
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();
            before[543]=if loans&1!=0{u64::MAX}else{0};before[544]=if loans&2!=0{u64::MAX}else{0};
            before[541]=if loans&2!=0{u64::MAX}else{0};
            for lane in 0..64{let code=batch*64+lane;
                for i in 0..5{put(&mut before,i,lane,code>>i&1!=0);}
                for i in 0..6{put(&mut before,5+i,lane,av>>i&1!=0);put(&mut before,11+i,lane,code>>(5+i)&1!=0);}
                for i in 0..4{put(&mut before,17+i,lane,code>>(11+i)&1!=0);}
                put(&mut before,21,lane,code>>15&1!=0);put(&mut before,22,lane,code>>16&1!=0);
            }
            compare(&base,&held,&before,&format!("component j={j} Araw={av} loans={loans} batch={batch}"));cases+=64;
        }}}
        let bt=base.iter().filter(|o|o.kind==K::CCX).count();let ht=held.iter().filter(|o|o.kind==K::CCX).count();
        eprintln!("Q793_RESIDUAL_COMPONENT j={j} base_ops={} held_ops={} base_T={bt} held_T={ht} delta_T={} PASS",base.len(),held.len(),ht as isize-bt as isize);
    }
    std::env::set_var(residual_hold::SWITCH,"1");
    eprintln!("Q793_RESIDUAL_COMPONENT_PASS lanes={cases} all_rank32_c64_sm16_phase4=true Araw=0,1,60,61,62,63 loan_patterns=4 peak_both=true full565_state=true phase=0 literal_inverse=true");
}
pub fn all_templates(){
    let mut cases=0usize;let(mut bn,mut hn,mut bt,mut ht)=(0usize,0usize,0usize,0usize);
    let blocks=super::super::shared_step::SCHEDULE_BLOCKS;let span=super::super::shared_step::SCHEDULE_BLOCK;
    for block in 0..blocks{for j in 0..4{
        let base=build(block,j,false,false);let held=build(block,j,true,false);
        let copies=((block*span+span).min(1616)-block*span)/4;
        let base_t=base.iter().filter(|o|o.kind==K::CCX).count();let held_t=held.iter().filter(|o|o.kind==K::CCX).count();
        bn+=copies*base.len();hn+=copies*held.len();bt+=copies*base_t;ht+=copies*held_t;
        for batch in 0..4{let mut seed=0x7935_2e51_aa51_u64^((block as u64)<<16)^((j as u64)<<8)^batch as u64;let before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();compare(&base,&held,&before,&format!("template block={block} j={j} batch={batch}"));cases+=64;}
        eprintln!("Q793_RESIDUAL_TEMPLATE block={block} j={j} base_T={base_t} held_T={held_t} delta_T={} copies={copies} PASS",held_t as isize-base_t as isize);
    }}
    assert!(ht<bt);std::env::set_var(residual_hold::SWITCH,"1");
    eprintln!("Q793_RESIDUAL_ALL_PASS templates={} lanes={cases} base_traversal_ops={bn} held_traversal_ops={hn} base_traversal_T={bt} held_traversal_T={ht} delta_ops={} delta_T={} full565_state=true phase=0 literal_inverse=true",blocks*4,hn as isize-bn as isize,ht as isize-bt as isize);
}

