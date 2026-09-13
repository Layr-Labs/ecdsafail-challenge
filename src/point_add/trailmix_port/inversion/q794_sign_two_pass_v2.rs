//! Own two-hole comparator-only T11; modulo4 virtual coefficient lowbits.
//! Derived from the public donor's two-pass carry architecture; no new rail.
//! The existing top-flag/park_c1 wrapper must already have run. No allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

// Only for gates inside W / literal W inverse. On guard1 the scratch is
// zero; offguard this is an arbitrary pure target-XOR extension. Restore
// guard before every decoder transition, loan operation and center read.
fn guard_scratch_toggle(circ:&mut Circuit,controls:&[(&QReg,bool)],target:&QReg,guard:&QReg) {
    circ.x(guard);
    super::paired_clean_mcx::toggle(circ,controls,target,guard);
    circ.x(guard);
}

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
        if super::metadata_muxlease::active("Q795_SIGN_G_SCRATCH_MASK") {
            guard_scratch_toggle(circ,&cs,self.mask,self.guard);
        } else {mixed_mcx(circ,&cs,self.mask,self.dirty);}
    }
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:&QReg,source:&[QReg],target:&[QReg],helpers:&[QReg],j:usize,n:usize) {
    let n=n.min(257);assert!((1..=257).contains(&n));assert!(helpers.len()>=17);
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
        let cs=[(mask,true),(&target[i],true),(&source[i],true)];
        if super::metadata_muxlease::active("Q795_SIGN_G_SCRATCH_DATA") {
            guard_scratch_toggle(circ,&cs,carry,guard);
        } else {mixed_mcx(circ,&cs,carry,dirty);}
        if i==1 { virtual_low_correction(circ,rank,c,sm,guard,mask,carry,source,target,dirty,j); }
    }
    // W never reads, targets or borrows Sign. Both metadata and loaned DATA
    // are restored by its exact inverse regardless of their offguard state.
    let compute=circ.b.ops[start..].to_vec();circ.ccx(guard,carry,sign);
    // C1/S0 has v=1,r=0,u=p and t<p/2, hence its comparison is certainly
    // false. Its mask passenger uses source255 and may poison W's carry;
    // disable only the center, leaving the exact W/W^-1 pair intact.
    if j==0 {
        let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
        for (r,t) in ts.iter().enumerate() {if t[1]!=0||t[2]!=0{continue;}
            let mut cs=vec![(guard,true),(carry,true)];
            cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));
            cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));
            cs.extend(sm.iter().map(|q|(q,false)));
            mixed_mcx(circ,&cs,sign,dirty);
        }
    }
    circ.b.ops.extend(compute.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,guard,None,dirty,j,true);
    top_loan(circ,rank,c,sm,guard,cache,carry,source,dirty,j);
}


fn virtual_low_correction(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,carry:&QReg,source:&[QReg],target:&[QReg],dirty:&[QReg],j:usize) {
    if j!=0{return;}
    // After MAJ0, even t implies borrow0=0. After MAJ1, source1=t1 and
    // target1=physical_b1 XOR t1. Change borrow=t1*!physical_b1 into
    // t1*(v1 XOR r0), without decoding or overwriting the retained r1.
    // Literal W inverse restores every temporarily changed DATA rail.
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for short_c in 0..=2 {
        let mut anf:Vec<_>=ts.iter().map(|t|t[2]==0 && (short_c==0||t[1]==0)).collect();
        for bit in 0..5 {for m in 0..32 {if m>>bit&1!=0 {anf[m]^=anf[m^(1<<bit)];}}}
        for (m,on) in anf.into_iter().enumerate() {if !on{continue;}
            let mut cs=vec![(g,true),(mask,true),(&source[0],false),(&source[1],true)];
            cs.extend(sm.iter().map(|q|(q,false)));
            cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)));
            if short_c!=0 {
                // C is in prepared C+S basis; on S0 it equals C.
                // C1: target257 is head-1 Sign-gap payload, semantic v1=0.
                // C2: target257 is the FIRST cargo/head, semantic v1=1.
                cs.extend(c.iter().enumerate().map(|(i,q)|(q,short_c>>i&1!=0)));
                if short_c==2 {mixed_mcx(circ,&cs,carry,dirty);}
                cs.push((&target[257],true));mixed_mcx(circ,&cs,carry,dirty);
            } else {
                for q in [&target[1],&target[257],&target[0]] {
                    let mut term=cs.clone();term.push((q,true));mixed_mcx(circ,&term,carry,dirty);
                }
            }
        }
    }
}

#[path="q794_sign_v2_low_check.rs"]
pub mod low_verification;
