//! Production lowering of the tested fixed/shifted low3 T10 kernels.
//!
//! Explicit bits are intentional: this module makes NO dynamic address or
//! short-tail assertion. A caller must provide semantic v1/v2/r0 and the
//! remaining q1 after pop, replacing a known zero outside a short word with
//! Constant(false), not with an arbitrary passenger occupying that address.
//! The dynamic phase/cargo/quotient adapter is not supplied here yet.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
#[path="q793_t10_low_v2.rs"]mod plan;

#[derive(Clone,Copy)]
pub(super) enum Bit<'a>{Wire(&'a QReg),Constant(bool)}
#[derive(Clone,Copy)]
pub(super) struct Low<'a>{
    pub t:[Bit<'a>;3],pub target:[&'a QReg;3],
    pub v1:Bit<'a>,pub v2:Bit<'a>,pub r0:Bit<'a>,
    /// Remaining semantic q bit1 after the current S=0 digit was popped.
    /// It is irrelevant for S=1/2. C=1 provides Constant(false).
    pub h:Bit<'a>,pub carry:&'a QReg,pub decision:&'a QReg,pub guard:&'a QReg,
}
impl<'a> Low<'a>{
    fn get(self,i:usize)->Bit<'a>{match i{
        0..=2=>self.t[i],3..=5=>Bit::Wire(self.target[i-3]),
        7=>self.v1,8=>self.v2,9=>self.r0,11=>self.h,
        12=>Bit::Wire(self.carry),13=>Bit::Wire(self.decision),14=>Bit::Wire(self.guard),
        _=>panic!("unused low3 layout ID unexpectedly referenced: {i}"),
    }}
}
fn lower(circ:&mut Circuit,ops:&[plan::Gate],bits:Low<'_>,dirty:&[QReg]){
    let owned=circ.b.next_qubit;
    for op in ops{
        let target=match bits.get(op.target){Bit::Wire(q)=>q,Bit::Constant(_)=>panic!("low3 output is not a physical bit")};
        let mut cs:Vec<(&QReg,bool)>=Vec::new();let mut disabled=false;
        for &(id,value)in &op.controls{match bits.get(id){
            Bit::Constant(v)=>if v!=value{disabled=true;break;},
            Bit::Wire(q)=>{
                assert_ne!(q.id(),target.id(),"low3 read/write alias must be resolved before lowering");
                if let Some(&(_,old))=cs.iter().find(|&&(p,_)|p.id()==q.id()) {if old!=value{disabled=true;break;}}
                else{cs.push((q,value));}
            },
        }}
        if disabled{continue;}
        assert!(dirty.iter().all(|q|q.id()!=target.id()&&cs.iter().all(|&(p,_)|p.id()!=q.id())),"low3 dirty lender aliases a live operand");
        super::length_recompute::mixed_mcx(circ,&cs,target,dirty);
    }
    assert_eq!(circ.b.next_qubit,owned,"low3 T10 must not allocate");
}
/// XOR the exact three-bit subtraction borrow into an arbitrary target.
/// During the enclosing compare ladder, carry is required0 on guard.
pub(super) fn low_borrow(circ:&mut Circuit,shift:usize,bits:Low<'_>,dirty:&[QReg]){
    let mut out=Vec::new();plan::low_borrow(&mut out,plan::Layout::new(3,shift));lower(circ,&out,bits,dirty);
}
/// The low conditional SUB of the inverse T10 map. The surrounding high
/// borrow ladder must already be unwound, and low_borrow must be erased
/// before this operation alters any target or source used by that oracle.
pub(super) fn low_sub(circ:&mut Circuit,shift:usize,bits:Low<'_>,dirty:&[QReg]){
    let mut out=Vec::new();plan::low_sub(&mut out,plan::Layout::new(3,shift));lower(circ,&out,bits,dirty);
}
