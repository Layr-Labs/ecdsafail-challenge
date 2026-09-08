//! After the cycle word swap, change A_old to A_new using retained C and S0.
//! Guard requires both coefficient lengths to be truthful and inside support.
//! Work1 holds the new coefficient, Work2 the old; prefix length is259-C.
//! All source words, retained C, S and helpers restore. No extra allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_Aupdate5_programs.rs"] mod programs;

fn permute(circ:&mut Circuit,rank:&[QReg],guard:&QReg,helpers:&[QReg],inverse:bool) {
    let start=circ.b.ops.len();for &(a,b) in programs::SWAPS {super::metadata_rank5::basis_swap(circ,rank,guard,&[],helpers,a,b);}
    if inverse{circ.b.ops[start..].reverse();}
}
fn length_xor(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],out:&[&QReg],source:&[QReg],prefix:&[QReg],guard:&QReg,helpers:&[QReg],lo:usize,hi:usize) {
    let mut boundary:Vec<_>=c.iter().collect();boundary.extend([&rank[0],&rank[1]]);let mask=&rank[4];let scratch=&sm[0];let n=hi-lo;
    let update=|circ:&mut Circuit,i:usize| {
        let value=259-hi+i;if value>255{return;}
        let cs:Vec<_>=boundary.iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0)).collect();
        super::conditional_mcx::guarded(circ,guard,&cs,mask,scratch,false,&helpers[0]);
    };
    let cell=|circ:&mut Circuit,i:usize| {
        let parent=if i==0{guard}else{&prefix[i-1]};circ.cx(parent,&prefix[i]);
        if hi-1-i==0&&super::q796_parity::enabled(){mixed_mcx(circ,&[(parent,true),(mask,true)],&prefix[i],helpers);}else{mixed_mcx(circ,&[(parent,true),(&source[hi-1-i],true),(mask,true)],&prefix[i],helpers);}
    };
    // Selected coefficient top lies in [lo,hi), so C<=258-lo on guard1.
    // Initialize eligibility at the high reverse index; both sweeps restore
    // arbitrary mask offsets on guard0, where the conjugation root is zero.
    let zero_map=|circ:&mut Circuit| {
        circ.x(mask);for i in (1..n).rev(){cell(circ,i);update(circ,i);}cell(circ,0);
        for i in 1..n{update(circ,i);cell(circ,i);}circ.x(mask);
    };
    let writes=|circ:&mut Circuit| {
        for i in 0..n {let value=hi-1-i;let next=if i+1<n{value-1}else{255};let delta=value^next;
            for bit in 0..8 {if delta>>bit&1!=0{circ.cx(&prefix[i],out[bit]);}}
        }
    };
    for bit in 0..8 {if (hi-1)>>bit&1!=0{circ.cx(guard,out[bit]);}}
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
}
pub(super) fn update(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize,inverse:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(lo<hi&&hi<=256);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(w1).chain(w2).chain(helpers).map(QReg::id).collect();ids.push(guard.id());ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();permute(circ,rank,guard,helpers,false);
    let mut out:Vec<_>=a.iter().collect();out.extend([&rank[2],&rank[3]]);
    length_xor(circ,rank,c,sm,&out,w2,w1,guard,helpers,lo,hi);
    length_xor(circ,rank,c,sm,&out,w1,w2,guard,helpers,lo,hi);
    permute(circ,rank,guard,helpers,true);
    if inverse{circ.b.ops[start..].reverse();}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
fn check_permutation() {
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let guard=circ.alloc_qreg("guard");let helpers=circ.alloc_qreg_bits("dirty",16);let owned=circ.b.next_qubit;permute(&mut circ,&rank,&guard,&helpers,false);let b=circ.into_builder();
    for pattern in 0..2 {let mut seed=0x9851fab6ced04732^(pattern as u64);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
        for lane in 0..64 {let r=lane&31;let on=lane>>5!=0;let mapped=if on{programs::MAP[r]}else{r};for bit in 0..5{put(&mut before,&rank[bit],lane,r>>bit&1!=0);put(&mut after,&rank[bit],lane,mapped>>bit&1!=0);}for w in [&mut before,&mut after]{put(w,&guard,lane,on);}}
        let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
    }
    eprintln!("CODEC_AUPDATE5_PERM_PASS lanes=128");
}
pub fn run() {
    let resource_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let lo:usize=std::env::var("LOWQ_CODEC_A_LO").ok().map(|v|v.parse().unwrap()).unwrap_or(0);
    let hi:usize=std::env::var("LOWQ_CODEC_A_HI").ok().map(|v|v.parse().unwrap()).unwrap_or(256);assert!(lo<hi&&hi<=256);
    if !resource_only{check_permutation();}
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut terminal=0;
    let cases:Vec<_>=(1..256).flat_map(|c|{let end=hi.min(258-c);(lo..end).flat_map(move|old|(lo..end).map(move|new|(c,old,new)))}).collect();assert!(!cases.is_empty());
    for inverse in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("A.rank",5);let a=circ.alloc_qreg_bits("A.low",6);let c=circ.alloc_qreg_bits("C.low",6);let sm=circ.alloc_qreg_bits("S.mid",4);assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("independent_exit_guard");let w1=circ.alloc_qreg_bits("new_coefficient",259);let w2=circ.alloc_qreg_bits("old_coefficient",259);let helpers=circ.alloc_qreg_bits("dirty_helpers",16);let owned=circ.b.next_qubit;
        update(&mut circ,&rank,&a,&c,&sm,&guard,&w1,&w2,&helpers,lo,hi,inverse);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_AUPDATE5_BUILT lo={lo} hi={hi} inverse={inverse} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());if resource_only{continue;}
        let batches=(cases.len()*2+63)/64;
        for batch in 0..batches {
            let mut seed=0xbe98320a5cd1f674^batch as u64^((inverse as u64)<<35);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let (cv,old,new)=cases[(k/2)%cases.len()];let on=k%2!=0;for w in [&mut before,&mut after]{put(w,&guard,lane,on);}if !on{continue;}
                let (ain,aout)=if inverse{(new,old)}else{(old,new)};let rin=triples.iter().position(|t|*t==[ain>>6,cv>>6,0]).unwrap();let rout=triples.iter().position(|t|*t==[aout>>6,cv>>6,0]).unwrap();
                for i in 0..5{put(&mut before,&rank[i],lane,rin>>i&1!=0);put(&mut after,&rank[i],lane,rout>>i&1!=0);}
                for i in 0..6{put(&mut before,&a[i],lane,ain>>i&1!=0);put(&mut after,&a[i],lane,aout>>i&1!=0);for w in [&mut before,&mut after]{put(w,&c[i],lane,cv>>i&1!=0);}}
                for q in &sm{for w in [&mut before,&mut after]{put(w,q,lane,false);}}
                for (word,value) in [(&w1,new),(&w2,old)] {for w in [&mut before,&mut after]{for i in value+1..259-cv{put(w,&word[i],lane,false);}put(w,&word[value],lane,true);}}
                if new==255{terminal+=1;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("Aupdate lo={lo} hi={hi} inverse={inverse} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            if batch%32768==32767{eprintln!("CODEC_AUPDATE5_PROGRESS inverse={inverse} batches={}",batch+1);}
        }
        eprintln!("CODEC_AUPDATE5_DIRECTION inverse={inverse} semantic_pairs={} PASS",cases.len());
    }
    if resource_only{eprintln!("CODEC_AUPDATE5_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_AUPDATE5_PASS lo={lo} hi={hi} lanes={total} terminal_newA255_lanes={terminal}; exact coefficient update and inverse, retained C/S and all work restored; native boundary and full Q799 missing");
}
