//! Exact controlled modular subtraction with restored clean external phase work.
use crate::point_add::trailmix_port::circuit::Circuit;
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use alloy_primitives::U256;
    use sha3::digest::XofReader;
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    struct Random(u64);impl XofReader for Random{fn read(&mut self,b:&mut[u8]){for x in b{*x=rnd(&mut self.0)as u8;}}}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    let p=U256::from_le_bytes(crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE);
    let mut programs=Vec::new();
    for loan in [false,true]{
        let mut circ=Circuit::new();let acc=circ.alloc_qreg_bits("acc",257);let addend=circ.alloc_qreg_bits("addend",257);let ctrl=circ.alloc_qreg("control");let lender=circ.alloc_qreg("clean_multiplier_top");let _others=circ.alloc_qreg_bits("unrelated_passengers",16);
        crate::point_add::trailmix_port::mod_arith::controlled_mod_sub_canonical_mbu_with_phase_lender(&mut circ,&ctrl,&acc,&addend,loan.then_some(&lender));
        let b=circ.into_builder();assert_eq!(b.active_qubits,532);
        eprintln!("Q797_CMS_BUILT loan={loan} ops={} T={} peak={} bits={}",b.ops.len(),b.ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count(),b.peak_qubits,b.next_bit);programs.push(b);
    }
    let edges=[U256::ZERO,U256::from(1),p-U256::from(1),p-U256::from(2),p>>1,U256::from(47),U256::from(977),U256::from(1)<<255];
    let mut seed=0x797c0515b7u64;let mut lanes=0;
    for batch in 0..64{
        let mut values=Vec::new();for lane in 0..64{
            let x=if batch<2{edges[(lane/8)%8]}else{U256::from_limbs([rnd(&mut seed),rnd(&mut seed),rnd(&mut seed),rnd(&mut seed)])%p};
            let y=if batch<2{edges[lane%8]}else{U256::from_limbs([rnd(&mut seed),rnd(&mut seed),rnd(&mut seed),rnd(&mut seed)])%p};let ctrl=if batch<2{batch==1}else{rnd(&mut seed)&1!=0};
            let want=if !ctrl{x}else if x>=y{x-y}else{p-(y-x)};values.push((x,y,ctrl,want));
        }
        for (loan,b)in programs.iter().enumerate(){
            let mut before=vec![0;b.next_qubit as usize];for x in &mut before[516..532]{*x=rnd(&mut seed);}let mut after=before.clone();
            for (lane,&(x,y,ctrl,want))in values.iter().enumerate(){for i in 0..256{put(&mut before,i,lane,x.bit(i));put(&mut after,i,lane,want.bit(i));for w in [&mut before,&mut after]{put(w,257+i,lane,y.bit(i));}}for w in [&mut before,&mut after]{put(w,514,lane,ctrl);}}
            let mut r=Random(rnd(&mut seed));let mut sim=Simulator::new(b.next_qubit as usize,b.next_bit as usize,&mut r);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase,0,"phase loan={loan} batch={batch}");assert_eq!(sim.qubits,after,"value/ancilla loan={loan} batch={batch}");lanes+=64;
        }
    }
    eprintln!("Q797_CMS_PASS lanes={lanes}; independent integer modular subtraction, canonical endpoints, both controls, random HMR outcomes, clean lender and all other passengers restored");
}
