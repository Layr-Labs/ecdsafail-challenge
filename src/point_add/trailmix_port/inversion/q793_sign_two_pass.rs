//! New three-hole Sign two-pass core; metadata range retained from own Q794.
//! Required low3 borrow increments and caller-funded scratch, no legacy loans.
//! Dynamic physical-reader/wrapper qualification remains separate.
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

/// Caller supplies already-funded zero-on-guard carry=helpers[0] and mask.
/// It owns all physical top/mask loans, including short-C and omitted hosts.
/// The mandatory callback XORs mask*(B_(i+1) XOR B_i) into carry, where B_i
/// is the exact borrow through the first i logical bits of t-(u>>S).
/// i is 0,1,2 and B_0=0. Inputs are not altered during these three calls.
/// Thus a prefix ending after k<3 bits telescopes to B_k automatically.
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:&QReg,source:&[QReg],target:&[QReg],helpers:&[QReg],j:usize,n:usize,
    seed:&mut dyn FnMut(&mut Circuit,&QReg,&QReg,&[QReg],usize,usize)) {
    let n=n.min(256);assert!((1..=256).contains(&n));assert!(helpers.len()>=17);
    assert_eq!(source.len(),259);assert_eq!(target.len(),259);
    let owned=circ.b.next_qubit;let all_start=circ.b.ops.len();
    let carry=&helpers[0];let dirty=&helpers[1..];
    // Top and mask loans are supplied by the caller, not legacy gathers.
    super::metadata_phase115_phased::prepare(circ,c,sm,guard,None,dirty,j,false);
    let start=circ.b.ops.len();let mut range=Range{rank,low:c,sm,guard,cache,mask,dirty,j,group:-1};
    circ.cx(guard,mask);
    range.equality(circ,257); // Empty prefix k=0, if supplied by a unit caller.
    for i in 0..n {
        if i>0 {range.equality(circ,257-i);}
        if i<3 {seed(circ,mask,carry,dirty,j,i);}
        else {
            circ.cx(&source[i],&target[i]);circ.cx(carry,&source[i]);
            let cs=[(mask,true),(&target[i],true),(&source[i],true)];
            if super::metadata_muxlease::active("Q795_SIGN_G_SCRATCH_DATA") {
                guard_scratch_toggle(circ,&cs,carry,guard);
            } else {mixed_mcx(circ,&cs,carry,dirty);}
        }
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
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[all_start..]{for h in [256usize,257,258]{
        let hole=source[h].id()as u64;
        assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,
            "Q793 Sign touched omitted source[{h}]");
    }}
}

