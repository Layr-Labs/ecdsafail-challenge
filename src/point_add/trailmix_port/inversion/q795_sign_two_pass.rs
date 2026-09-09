//! Comparator-only T11 with a carry loaned from the cleared source top bit.
//! The existing top-flag/park_c1 wrapper must already have run. No allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn top_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,carry:&QReg,word:&[QReg],dirty:&[QReg],j:usize) {
    // Same prepared address as q795_t11_top: k=257-(C+S). This conjugated
    // exchange is an exact involution for arbitrary offguard metadata/data.
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let start=circ.b.ops.len();let mut nodes=vec![None;512];
    for value in 1..=257 {nodes[value]=Some(&word[257-value]);}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for level in 0..9 {
        let mut next=Vec::new();
        for pair in nodes.chunks_exact(2) {next.push(match(pair[0],pair[1]) {
            (Some(left),Some(right))=>{
                if level<6 {circ.cswap(&c[level],left,right);} else {
                    let controls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();
                    let truth:Vec<_>=(0..64).map(|r|((ts[r&31][1]+ts[r&31][2]+(r>>5))>>(level-6))&1!=0).collect();
                    super::metadata_muxlease::truth_swap(circ,&controls,truth,left,right,dirty);
                }Some(left)
            },
            (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
        });}nodes=next;
    }
    let root=nodes[0].unwrap();let gather=circ.b.ops[start..].to_vec();
    circ.cswap(g,root,carry);circ.b.ops.extend(gather.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

struct Range<'a>{rank:&'a[QReg],low:&'a[QReg],sm:&'a[QReg],guard:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],j:usize,group:isize}
impl Range<'_> {
    fn equality(&mut self,circ:&mut Circuit,value:usize){
        if !(1..=257).contains(&value){return;}
        let h=(value/64)as isize;
        if h!=self.group {
            super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,self.group,h);
            self.group=h;
        }
        // W only feeds a guarded carry read, then reverses. The mask oracle
        // may therefore omit the external guard; its offguard map is undone.
        let mut cs=vec![(self.cache,true)];cs.extend((0..6).map(|i|(&self.low[i],value>>i&1!=0)));
        mixed_mcx(circ,&cs,self.mask,self.dirty);
    }
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:&QReg,source:&[QReg],target:&[QReg],helpers:&[QReg],j:usize,n:usize) {
    assert!((1..=258).contains(&n));assert!(helpers.len()>=17);
    let carry=&helpers[0];let dirty=&helpers[1..];
    // Current mask loan lives at Work1[258-C], not at k: separation S+1.
    // Top-bit1 branches were parked. On the remaining guard, source[k]=0;
    // k is outside the shortened arithmetic prefix. Return this passenger
    // before park_c1 or top_flag is undone by the enclosing caller.
    top_loan(circ,rank,c,sm,guard,cache,carry,source,dirty,j);
    super::metadata_phase115_phased::prepare(circ,c,sm,guard,None,dirty,j,false);
    let start=circ.b.ops.len();let mut range=Range{rank,low:c,sm,guard,cache,mask,dirty,j,group:-1};
    circ.cx(guard,mask);
    range.equality(circ,257); // Empty prefix k=0, if supplied by a unit caller.
    for i in 0..n {
        if i>0 {range.equality(circ,257-i);}
        circ.cx(&source[i],&target[i]);circ.cx(carry,&source[i]);
        mixed_mcx(circ,&[(mask,true),(&target[i],true),(&source[i],true)],carry,dirty);
    }
    // W never reads, targets or borrows Sign. Both metadata and loaned DATA
    // are restored by its exact inverse regardless of their offguard state.
    let compute=circ.b.ops[start..].to_vec();circ.ccx(guard,carry,sign);
    circ.b.ops.extend(compute.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,guard,None,dirty,j,true);
    top_loan(circ,rank,c,sm,guard,cache,carry,source,dirty,j);
}

pub mod verification {
    use super::*;
    use crate::{circuit::OperationType,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let b=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!b)|if v{b}else{0};}
    pub fn run(){
        let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
        let n=std::env::var("LOWQ_CODEC_SUPPORT_END").ok().map(|v|v.parse().unwrap()).unwrap_or(258);
        let mut total=0;let mut active=0;
        for j in 0..4 {
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("sign.rank",5);let c=circ.alloc_qreg_bits("sign.c",6);let sm=circ.alloc_qreg_bits("sign.sm",4);
            let g=circ.alloc_qreg("sign.g");let cache=circ.alloc_qreg("sign.cache");let mask=circ.alloc_qreg("sign.mask");let sign=circ.alloc_qreg("sign.output");
            let source=circ.alloc_qreg_bits("sign.source",259);let target=circ.alloc_qreg_bits("sign.target",259);let helpers=circ.alloc_qreg_bits("sign.helpers",22);let owned=circ.b.next_qubit;
            emit(&mut circ,&rank,&c,&sm,&g,&cache,&mask,&sign,&source,&target,&helpers,j,n);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
            assert!(b.ops.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let hole=source[258].id()as u64;assert!(b.ops.iter().all(|o|o.q_target.0!=hole&&o.q_control1.0!=hole&&o.q_control2.0!=hole));
            eprintln!("SIGN_TWO_PASS_BUILT j={j} n={n} T={} ops={} wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
            for pattern in 0..4 {for batch in 0..1024 {
                let mut seed=0x7ab152984a4b6961u64^batch as u64^((pattern as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut expected=before.clone();
                for lane in 0..64 {
                    let index=batch*64+lane;let r=index&31;let cl=index>>5&63;let sl=index>>11&15;
                    let cv=64*ts[r][1]+cl;let sv=64*ts[r][2]+4*sl+(4-j)%4;
                    let on=index>>15&1!=0&&cv>0&&cv<=255&&cv+sv<=257;
                    for i in 0..5 {for w in [&mut before,&mut expected]{put(w,&rank[i],lane,r>>i&1!=0);}}
                    for i in 0..6 {for w in [&mut before,&mut expected]{put(w,&c[i],lane,cl>>i&1!=0);}}
                    for i in 0..4 {for w in [&mut before,&mut expected]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                    for w in [&mut before,&mut expected]{put(w,&g,lane,on);if on{put(w,&cache,lane,false);put(w,&mask,lane,false);put(w,&source[257-cv-sv],lane,false);}}
                    if on {
                        let mut less=false;for i in 0..n.min(257-cv-sv){let x=before[source[i].id()as usize]>>lane&1!=0;let y=before[target[i].id()as usize]>>lane&1!=0;if x!=y{less=x;}}
                        if less{expected[sign.id()as usize]^=1u64<<lane;}active+=1;
                    }
                }
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
                assert_eq!(sim.qubits,expected,"Sign two-pass j={j} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
                sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            }}
        }
        eprintln!("SIGN_TWO_PASS_PASS lanes={total} active={active}; all C/S endpoints/clocks, top loan0, arbitrary parked passengers/offguard helpers/output, scalar borrow, phase/inverse/allwire restoration, zero omitted rail touches");
    }
}
