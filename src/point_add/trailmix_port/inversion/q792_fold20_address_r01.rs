//! Decoded A-addressed SWAP using a dirty XOR-address permutation.
//! XOR translations commute: R_d D_A R_d D_A = R_A, restoring arbitrary d.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q792_fold20_r01::table,length_recompute::mixed_mcx};
const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];
const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];
const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];
pub(super) fn read_a(c:&mut Circuit,m:&[QReg],out:&[QReg],dirty:&[QReg]){
    assert_eq!(out.len(),8);assert!(dirty.len()>=12);let ts=super::q792_fold20_rank_r01::triples();let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let t15:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();
    for i in 0..6{c.cx(&m[4+i],&out[i]);}
    let mut term=t15.clone();term.extend([(&m[5],true),(&m[4],false)]);mixed_mcx(c,&term,&out[0],rest);
    for i in 2..6{let mut cs=t15.clone();cs.push((&m[4+i],true));mixed_mcx(c,&cs,&out[i],rest);let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,&out[i],rest);}
    for i in 0..2{
        table(c,&tag,(0..16).map(|t|t<15&&ts[if t<10{LOW[t]}else{EDGE[2*(t-10)]}][0]>>i&1!=0).collect(),&[],&out[6+i],rest);
        let mut cs=t15.clone();cs.push((&m[5],false));table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|p|p<12&&ts[PEAK[p]][0]>>i&1!=0).collect(),&cs,&out[6+i],rest);
        let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,&out[6+i],rest);
    }
    let consume=|c:&mut Circuit|{
        for i in 0..6{table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[(d,true)],&out[i],rest);}
        for i in 0..2{table(c,&tag,(0..16).map(|t|(10..15).contains(&t)&&(ts[EDGE[2*(t-10)]][0]^ts[EDGE[2*(t-10)+1]][0])>>i&1!=0).collect(),&[(d,true)],&out[6+i],rest);}
    };
    let side=|c:&mut Circuit|{let q=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];table(c,&q,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],d,rest);};
    consume(c);side(c);consume(c);side(c);
}
fn read_bit(c:&mut Circuit,m:&[QReg],wanted:usize,out:&QReg,dirty:&[QReg]){
    assert!(wanted<8);assert!(dirty.len()>=12);let ts=super::q792_fold20_rank_r01::triples();let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let t15:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();
    for i in (0..6).filter(|&i|i==wanted){c.cx(&m[4+i],out);}
    let mut term=t15.clone();term.extend([(&m[5],true),(&m[4],false)]);if wanted==0{mixed_mcx(c,&term,out,rest);}
    for i in (2..6).filter(|&i|i==wanted){let mut cs=t15.clone();cs.push((&m[4+i],true));mixed_mcx(c,&cs,out,rest);let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,out,rest);}
    for i in (0..2).filter(|&i|i+6==wanted){
        table(c,&tag,(0..16).map(|t|t<15&&ts[if t<10{LOW[t]}else{EDGE[2*(t-10)]}][0]>>i&1!=0).collect(),&[],out,rest);
        let mut cs=t15.clone();cs.push((&m[5],false));table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|p|p<12&&ts[PEAK[p]][0]>>i&1!=0).collect(),&cs,out,rest);
        let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,out,rest);
    }
    let consume=|c:&mut Circuit|{
        for i in (0..6).filter(|&i|i==wanted){table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[(d,true)],out,rest);}
        for i in (0..2).filter(|&i|i+6==wanted){table(c,&tag,(0..16).map(|t|(10..15).contains(&t)&&(ts[EDGE[2*(t-10)]][0]^ts[EDGE[2*(t-10)+1]][0])>>i&1!=0).collect(),&[(d,true)],out,rest);}
    };
    let side=|c:&mut Circuit|{let q=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];table(c,&q,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],d,rest);};
    consume(c);side(c);consume(c);side(c);
}
pub(super) fn translation(c:&mut Circuit,addr:&[QReg],bank:&[&QReg]){
    for i in 0..8{for v in 0..256{if v>>i&1==0{c.cswap(&addr[i],bank[v],bank[v^(1<<i)]);}}}
}
pub(super) fn exchange(c:&mut Circuit,m:&[QReg],pass:&QReg,bank:&[&QReg],helpers:&[QReg]){
    assert_eq!(m.len(),20);assert_eq!(bank.len(),256);assert!(helpers.len()>=20);
    let at=c.b.ops.len();let selector=&helpers[0];let dirty=&helpers[1..];let mut nodes=bank.to_vec();
    for level in 0..8{
        // Disjoint pair swaps share the XOR-readout echo. The affine pair
        // frames commute with that metadata-only oracle and close literally.
        for pair in nodes.chunks_exact(2){c.cx(pair[1],pair[0]);}
        for pair in nodes.chunks_exact(2){c.ccx(selector,pair[0],pair[1]);}
        read_bit(c,m,level,selector,dirty);
        for pair in nodes.chunks_exact(2){c.ccx(selector,pair[0],pair[1]);}
        read_bit(c,m,level,selector,dirty);
        for pair in nodes.chunks_exact(2){c.cx(pair[1],pair[0]);}
        nodes=nodes.chunks_exact(2).map(|pair|pair[0]).collect();
    }
    let route=c.b.ops[at..].to_vec();let root=nodes[0];c.cx(root,pass);c.cx(pass,root);c.cx(root,pass);c.b.ops.extend(route.into_iter().rev());

}
fn a(code:usize)->usize{
    let tag=code&15;let low=code>>4;let mut al=low&63;let cl=low>>6&63;let sm=low>>12&15;let ts=super::q792_fold20_rank_r01::triples();
    let r=if tag<10{LOW[tag]}else if tag<15{let side=usize::from((al>>4)+(cl>>4)+(sm>>2)>=5);if side!=0{al^=63;}EDGE[2*(tag-10)+side]}else if al&2!=0{al=63;29}else{let r=if al>>2<12{PEAK[al>>2]}else{0};al&=1;r};64*ts[r][0]+al
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x19)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let pass=c.alloc_qreg("pass");let bank=c.alloc_qreg_bits("data",256);let d=c.alloc_qreg_bits("dirty",21);let n=c.b.next_qubit;
    exchange(&mut c,&m,&pass,&bank.iter().collect::<Vec<_>>(),&d);assert_eq!(n,c.b.next_qubit);let ops=c.into_builder().ops;
    eprintln!("FOLD20_ADDRESS_BUILT ops={} T={} clean_allocations=0",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut total=0;for pattern in 0..2{for first in (0..1usize<<20).step_by(64){let mut seed=0x792add00u64^first as u64^(pattern<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
        for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}let mut after=before.clone();
        for lane in 0..64{let q=bank[a(first+lane)].id()as usize;let p=pass.id()as usize;let delta=((before[q]^before[p])>>lane&1)<<lane;after[q]^=delta;after[p]^=delta;}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"address first={first} pattern={pattern}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_ADDRESS_NATIVE_PASS lanes={total} metadata20=true arbitrary_bank=true arbitrary_lenders=true inverse=true phase=0");
}

// XOR readout of any selected address bits. Adjacent low-bit differences
// cancel the shared fold reflection and terminal correction exactly.
fn read_mask(c:&mut Circuit,m:&[QReg],mask:usize,out:&QReg,dirty:&[QReg]){
    assert!(mask<256);assert!(dirty.len()>=12);
    let ts=super::q792_fold20_rank_r01::triples();let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let parity=|x:usize|(x.count_ones()&1)!=0;
    let t15:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();
    for i in 0..6{if mask>>i&1!=0{c.cx(&m[4+i],out);}}
    if mask&1!=0{let mut cs=t15.clone();cs.extend([(&m[5],true),(&m[4],false)]);mixed_mcx(c,&cs,out,rest);}
    for i in 2..6{if mask>>i&1!=0{let mut cs=t15.clone();cs.push((&m[4+i],true));mixed_mcx(c,&cs,out,rest);}}
    if parity(mask&60){let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,out,rest);}
    if mask>>6!=0{
        table(c,&tag,(0..16).map(|t|t<15&&parity(ts[if t<10{LOW[t]}else{EDGE[2*(t-10)]}][0]&(mask>>6))).collect(),&[],out,rest);
        let mut cs=t15.clone();cs.push((&m[5],false));table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|p|p<12&&parity(ts[PEAK[p]][0]&(mask>>6))).collect(),&cs,out,rest);
        if parity(mask>>6){let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,out,rest);}
    }
    let truth:Vec<_>=(0..16).map(|t|(10..15).contains(&t)&&(parity(mask&63)^parity((ts[EDGE[2*(t-10)]][0]^ts[EDGE[2*(t-10)+1]][0])&(mask>>6)))).collect();
    if truth.iter().any(|&b|b){
        let consume=|c:&mut Circuit|table(c,&tag,truth.clone(),&[(d,true)],out,rest);
        let side=|c:&mut Circuit|{let q=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];table(c,&q,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],d,rest);};
        consume(c);side(c);consume(c);side(c);
    }
}
/// Specialized A-pad loan: bank[A] is zero on entry, and pass is arbitrary.
/// After its swap, pass is zero and can fund the reverse route's selector.
/// The exact reversed sequence returns a held loan with pass initially zero.
pub(super) fn loan(c:&mut Circuit,m:&[QReg],pass:&QReg,bank:&[&QReg],helpers:&[QReg],inverse:bool){
    assert_eq!(bank.len(),256);assert!(helpers.len()>=20);let at=c.b.ops.len();
    let selector=&helpers[0];let dirty=&helpers[1..];let mut nodes=bank.to_vec();let mut levels=Vec::new();
    for level in 0..8{
        levels.push(nodes.clone());
        for pair in nodes.chunks_exact(2){c.cx(pair[1],pair[0]);}
        for pair in nodes.chunks_exact(2){c.ccx(selector,pair[0],pair[1]);}
        read_bit(c,m,level,selector,dirty);
        for pair in nodes.chunks_exact(2){c.ccx(selector,pair[0],pair[1]);}
        read_bit(c,m,level,selector,dirty);
        for pair in nodes.chunks_exact(2){c.cx(pair[1],pair[0]);}
        nodes=nodes.chunks_exact(2).map(|pair|pair[0]).collect();
    }
    let root=nodes[0];c.cx(root,pass);c.cx(pass,root);c.cx(root,pass);
    read_mask(c,m,128,pass,helpers);
    for level in (0..8).rev(){
        for pair in levels[level].chunks_exact(2){c.cswap(pass,pair[0],pair[1]);}
        read_mask(c,m,if level==0{1}else{(1<<level)|(1<<(level-1))},pass,helpers);
    }
    if inverse{c.b.ops[at..].reverse();}
}
pub fn run_loan(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x19)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let pass=c.alloc_qreg("pass");let bank=c.alloc_qreg_bits("data",256);let d=c.alloc_qreg_bits("dirty",21);let n=c.b.next_qubit;
    loan(&mut c,&m,&pass,&bank.iter().collect::<Vec<_>>(),&d,false);assert_eq!(n,c.b.next_qubit);let ops=c.into_builder().ops;
    eprintln!("FOLD20_ADDRESS_LOAN_BUILT ops={} T={} clean_allocations=0",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut total=0;for pattern in 0..2{for first in (0..1usize<<20).step_by(64){let mut seed=0x79210a00u64^first as u64^(pattern<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
        for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}
        for lane in 0..64{before[bank[a(first+lane)].id()as usize]&=!(1u64<<lane);}
        let mut after=before.clone();for lane in 0..64{let q=bank[a(first+lane)].id()as usize;let p=pass.id()as usize;let delta=((before[q]^before[p])>>lane&1)<<lane;after[q]^=delta;after[p]^=delta;}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"loan first={first} pattern={pattern}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_ADDRESS_LOAN_PASS lanes={total} metadata20=true selected_bank_zero=true arbitrary_other_bank=true arbitrary_pass=true arbitrary_lenders=true inverse=true phase=0");
}
