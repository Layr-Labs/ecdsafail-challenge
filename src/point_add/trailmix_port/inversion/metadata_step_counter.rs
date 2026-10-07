//! Native 21-bit metadata counter composition for the counter updates within all four active phases.
//! Does not implement phase boundaries, packed arithmetic, or a wholeQ799 circuit.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_rank,length_recompute};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;

fn small_step(circ:&mut Circuit,word:&[QReg],controls:&[(&QReg,bool)],helpers:&[QReg],subtract:bool) {
    for offset in 0..word.len() {
        let j=if subtract {offset} else {word.len()-1-offset};
        let mut cs=controls.to_vec();cs.extend(word[..j].iter().map(|q|(q,true)));
        length_recompute::mixed_mcx(circ,&cs,&word[j],helpers);
    }
}
fn implicit_ls1(phase:usize,j:usize,c:usize)->usize {
    let base=if phase<=1 {j} else {(4-j)%4};((base>>1)^if [1,2].contains(&phase) {c&1} else {0})&1
}
/// Under guard, input LS0 equals j mod2. Phase is00..11, and j is the input
/// boundary clock modulo4. Output is interpreted at clock j+1 in the same phase.
/// LT is unchanged; shared changes by+1/-1 in phases01/10 and stays in00/11.
/// LS changes by+1 in00/10 and-1 in01/11, modulo256.
/// The endpoint metadata codes must be admissible; arbitrary other code words
/// remain a bijective extension, and guard0 is identity including dirty scratch.
fn emit(circ:&mut Circuit,rank:&[QReg],c_low:&[QReg],s_mid:&[QReg],s0:&QReg,guard:&QReg,helpers:&[QReg],phase:usize,j:usize) {
    assert!(phase<4);assert!(j<4);assert_eq!(rank.len(),10);assert_eq!(c_low.len(),4);assert_eq!(s_mid.len(),2);
    if phase==0 || phase==3 {
        let subtract=phase==3;let parity=j%2!=0;
        let low_two=(implicit_ls1(phase,j,0)<<1)|(j&1);
        let carry=if subtract {low_two==0} else {low_two==3};
        if carry {
            let extras=[(&s_mid[0],!subtract),(&s_mid[1],!subtract)];
            metadata_rank::emit_update(circ,rank,guard,&extras,s0,helpers,2,subtract,parity);
            small_step(circ,s_mid,&[(guard,true)],helpers,subtract);
        }
        circ.cx(guard,s0);return;
    }
    let subtract_s=phase==1;let parity=j%2!=0;
    let s_carry_possible=if subtract_s {!parity} else {parity};
    let desired_s1=usize::from(!subtract_s);
    let required_c0=(desired_s1^implicit_ls1(phase,j,0))!=0;
    let s_extras=[(&s_mid[0],!subtract_s),(&s_mid[1],!subtract_s),(&c_low[0],required_c0)];
    let c_extras:Vec<_>=c_low.iter().map(|q|(q,phase==1)).collect();
    // Decrement the high coordinate before incrementing the other one: when
    // both carry, this avoids leaving the high-nibble simplex transiently.
    if subtract_s {
        if s_carry_possible {metadata_rank::emit_update(circ,rank,guard,&s_extras,s0,helpers,2,true,parity);}
        metadata_rank::emit_update(circ,rank,guard,&c_extras,s0,helpers,1,false,parity);
    } else {
        metadata_rank::emit_update(circ,rank,guard,&c_extras,s0,helpers,1,true,parity);
        if s_carry_possible {metadata_rank::emit_update(circ,rank,guard,&s_extras,s0,helpers,2,false,parity);}
    }
    // Simultaneous modulo wrap is the sole exception to the decrement-first
    // simplex argument. With both low carries, endpoint admissibility forces
    // high sum<=15. The only wrapping pairs are (A,C,S)=(0,15,0)/(0,0,15).
    // Repair their composed permutation by one controlled basis transposition.
    if (phase==1 && j==2) || (phase==2 && j==1) {
        let mut both=c_extras.clone();both.extend(s_mid.iter().map(|q|(q,phase==2)));
        let (left,right)=if phase==1 {(1usize,15usize)} else {(16usize,149usize)};
        metadata_rank::emit_index_swap(circ,rank,guard,&both,s0,helpers,left,right,parity);
    }
    // Resolve the omitted LS1 from OLD c0 before changing the shared low word.
    if s_carry_possible {small_step(circ,s_mid,&[(guard,true),(&c_low[0],required_c0)],helpers,subtract_s);}
    small_step(circ,c_low,&[(guard,true)],helpers,phase==2);
    circ.cx(guard,s0);
}
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(words:&mut[u64],q:&QReg,lane:usize,value:bool) {let bit=1u64<<lane;let x=&mut words[q.id()as usize];*x=(*x&!bit)|if value {bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();
    let mut index=[usize::MAX;4096];for (i,t) in triples.iter().enumerate(){index[t[0]*256+t[1]*16+t[2]]=i;}
    let mut total=0usize;let mut active_total=0usize;
    for phase in 0usize..4 {for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("counter.rank",10);let a_low=circ.alloc_qreg_bits("counter.a_low",4);
        let c_low=circ.alloc_qreg_bits("counter.c_low",4);let s_mid=circ.alloc_qreg_bits("counter.s23",2);let s0=circ.alloc_qreg("counter.s0");
        assert_eq!(circ.b.next_qubit,21);let guard=circ.alloc_qreg("counter.guard");let helpers=circ.alloc_qreg_bits("counter.dirty",8);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&c_low,&s_mid,&s0,&guard,&helpers,phase,j);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));
            for q in &a_low {assert!(op.q_target.0!=q.id()as u64 && op.q_control1.0!=q.id()as u64 && op.q_control2.0!=q.id()as u64);}
        }
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();let mut active=0usize;
        // Every rank code and every low shared/LS2/LS3 pattern, both guard
        // branches, four arbitrary restored dirty patterns. a_low is proven
        // absent from all controls/targets and is randomized independently.
        let cases=1024*16*4*2;
        for pattern in 0..4 {for batch in 0..cases/64 {
            let mut random=0xd38cb1724a950eef^((phase*8192+j*2048+batch)as u64)^pattern as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let n=batch*64+lane;let r=n&1023;let cl=(n>>10)&15;let sm=(n>>14)&3;let request_on=n>>16&1!=0;
                let mut enabled=false;let mut rr=r;let mut cc=cl;let mut ss=sm;
                if r<966 {
                    let [ah,ch,sh]=triples[r];let a=ah*16;let c=ch*16+cl;let s=sh*16+sm*4+implicit_ls1(phase,j,c)*2+(j&1);
                    let cn=if phase==1 {(c+1)&255} else if phase==2 {(c+255)&255} else {c};let sn=if [0,2].contains(&phase) {(s+1)&255} else {(s+255)&255};
                    enabled=request_on && a+c+s<=257 && a+cn+sn<=257;
                    if enabled {rr=index[ah*256+(cn>>4)*16+(sn>>4)];assert_ne!(rr,usize::MAX);cc=cn&15;ss=(sn>>2)&3;
                        assert_eq!((sn>>1)&1,implicit_ls1(phase,(j+1)%4,cn));active+=1;
                    }
                }
                for i in 0..10 {put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,rr>>i&1!=0);}
                for i in 0..4 {put(&mut before,&c_low[i],lane,cl>>i&1!=0);put(&mut after,&c_low[i],lane,cc>>i&1!=0);}
                for i in 0..2 {put(&mut before,&s_mid[i],lane,sm>>i&1!=0);put(&mut after,&s_mid[i],lane,ss>>i&1!=0);}
                let low=if enabled {j%2!=0} else {(n+pattern)%2!=0};
                put(&mut before,&s0,lane,low);put(&mut after,&s0,lane,low^enabled);
                put(&mut before,&guard,lane,enabled);put(&mut after,&guard,lane,enabled);
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"counter phase={phase} j={j} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        active_total+=active;eprintln!("CODEC_COUNTER_NATIVE phase={phase} j={j} T={tof} ops={} metadata_wires=21 component_wires={owned} active_lanes={active} all_low_patterns_dirty_phase_reverse=PASS",b.ops.len());
    }}
    eprintln!("CODEC_COUNTER_NATIVE_PASS lanes={total} active_lanes={active_total};21-bit metadata counter component, no phase-boundary or wholeQ799 claim");
}
