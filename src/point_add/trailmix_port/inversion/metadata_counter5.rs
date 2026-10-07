//! Complete active counter updates on rank5 + low6/low6/Sbits2..5.
//! S0/S1 are virtual; no physical parity wire or unpacked metadata copy.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_rank5,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
fn small(circ:&mut Circuit,word:&[QReg],controls:&[(&QReg,bool)],helpers:&[QReg],subtract:bool) {
    for k in 0..word.len() {let i=if subtract{k}else{word.len()-1-k};let mut cs=controls.to_vec();cs.extend(word[..i].iter().map(|q|(q,true)));length_recompute::mixed_mcx(circ,&cs,&word[i],helpers);}
}
fn implicit_ls1(phase:usize,j:usize,c:usize)->usize {let base=if phase<=1 {j}else{(4-j)%4};((base>>1)^if [1,2].contains(&phase){c&1}else{0})&1}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,helpers:&[QReg],phase:usize,j:usize) {
    assert_eq!(rank.len(),5);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(phase<4&&j<4);
    if phase==0||phase==3 {
        let sub=phase==3;let low=2*implicit_ls1(phase,j,0)+(j&1);let carry=if sub {low==0}else{low==3};
        if carry {let extras:Vec<_>=sm.iter().map(|q|(q,!sub)).collect();metadata_rank5::emit_mixed(circ,rank,guard,&extras,helpers,2,sub);small(circ,sm,&[(guard,true)],helpers,sub);}
        return;
    }
    let sub_s=phase==1;let carry_s=if sub_s {j%2==0}else{j%2!=0};let needed_c0=(usize::from(!sub_s)^implicit_ls1(phase,j,0))!=0;
    let mut s_extras:Vec<_>=sm.iter().map(|q|(q,!sub_s)).collect();s_extras.push((&c[0],needed_c0));let c_extras:Vec<_>=c.iter().map(|q|(q,phase==1)).collect();
    if sub_s {
        if carry_s {metadata_rank5::emit_mixed(circ,rank,guard,&s_extras,helpers,2,true);}
        metadata_rank5::emit_mixed(circ,rank,guard,&c_extras,helpers,1,false);
    } else {
        metadata_rank5::emit_mixed(circ,rank,guard,&c_extras,helpers,1,true);
        if carry_s {metadata_rank5::emit_mixed(circ,rank,guard,&s_extras,helpers,2,false);}
    }
    // Simultaneous modulo256 wrap: repair only the two affected row endpoints.
    if (phase==1&&j==2)||(phase==2&&j==1) {
        let mut both=c_extras.clone();both.extend(sm.iter().map(|q|(q,phase==2)));
        let (left,right)=if phase==1 {(1,3)}else{(4,11)};
        metadata_rank5::basis_swap(circ,rank,guard,&both,helpers,left,right);
    }
    if carry_s {small(circ,sm,&[(guard,true),(&c[0],needed_c0)],helpers,sub_s);}
    small(circ,c,&[(guard,true)],helpers,phase==2);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut index=[usize::MAX;64];for(i,t)in triples.iter().enumerate(){index[16*t[0]+4*t[1]+t[2]]=i;}let mut total=0;let mut active_total=0;
    for phase in 0..4 {for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("counter5.rank",5);let a=circ.alloc_qreg_bits("counter5.a",6);let c=circ.alloc_qreg_bits("counter5.c",6);let sm=circ.alloc_qreg_bits("counter5.sm",4);assert_eq!(circ.b.next_qubit,21);let guard=circ.alloc_qreg("counter5.guard");let helpers=circ.alloc_qreg_bits("counter5.dirty",16);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&c,&sm,&guard,&helpers,phase,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));for q in &a{assert!(op.q_target.0!=q.id()as u64&&op.q_control1.0!=q.id()as u64&&op.q_control2.0!=q.id()as u64);}}
        let mut active=0;
        for pattern in 0..4 {for batch in 0..32*64*16*2/64 {
            let mut seed=0x9234efca587db601^batch as u64^((pattern as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let cl=k>>5&63;let sl=k>>11&15;let request=k>>15&1!=0;let [ah,ch,sh]=triples[r];let av=64*ah;let cv=64*ch+cl;let sv=64*sh+4*sl+2*implicit_ls1(phase,j,cv)+(j&1);
                let cn=if phase==1 {(cv+1)&255}else if phase==2 {(cv+255)&255}else{cv};let sn=if [0,2].contains(&phase){(sv+1)&255}else{(sv+255)&255};let on=request&&av+cv+sv<=257&&av+cn+sn<=257;
                let rr=if on{index[16*ah+4*(cn>>6)+(sn>>6)]}else{r};assert_ne!(rr,usize::MAX);if on{assert_eq!((sn>>1)&1,implicit_ls1(phase,(j+1)%4,cn));active+=1;}
                for i in 0..5 {put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,rr>>i&1!=0);}
                for i in 0..6 {put(&mut before,&c[i],lane,cl>>i&1!=0);put(&mut after,&c[i],lane,(if on{cn&63}else{cl})>>i&1!=0);}
                for i in 0..4 {put(&mut before,&sm[i],lane,sl>>i&1!=0);put(&mut after,&sm[i],lane,(if on{sn>>2&15}else{sl})>>i&1!=0);}
                for w in [&mut before,&mut after]{put(w,&guard,lane,on);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"counter5 phase={phase} j={j} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        active_total+=active;eprintln!("CODEC_COUNTER5 phase={phase} j={j} T={} ops={} active_lanes={active} metadata_wires=21 component_wires={owned} PASS",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
    }}
    eprintln!("CODEC_COUNTER5_PASS lanes={total} active_lanes={active_total}; four phases with virtual S0/S1; no full Q799 circuit");
}
