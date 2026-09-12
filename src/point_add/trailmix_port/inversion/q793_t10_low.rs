//! Fixed-width, S=0 mod8 T10 inverse kernel. No dynamic addressing is assumed.
//!
//! On entry the quotient is semantically zero and t*r+u*v=7 (mod8).
//! Physical b=u for odd t, b=r for even t (then v is odd). The arbitrary
//! decision rail p is NOT part of that entry invariant. The map is
//! q=p XOR [u>=t], u'=u-q*t mod2^n, leaving t,r,v unchanged. On exit the
//! chart equation includes q*t*v. Only odd t changes physical b.
//! The funded carry must be zero on guard; it may be arbitrary off guard.
//! This module does NOT solve S=1/2 overlaps, short t, or dynamic cargo.

#[derive(Clone, Debug)]
pub struct Gate { pub controls: Vec<(usize,bool)>, pub target: usize }

#[derive(Clone, Copy, Debug)]
pub struct Layout { pub n: usize, pub carry: usize, pub p: usize, pub guard: usize, pub used: usize }
impl Layout {
    pub fn new(n:usize)->Self { assert!(n>=3); Self {n,carry:2*n+3,p:2*n+4,guard:2*n+5,used:2*n+6} }
    pub fn t(self,i:usize)->usize {assert!(i<self.n);i}
    pub fn b(self,i:usize)->usize {assert!(i<self.n);self.n+i}
    pub fn v(self,i:usize)->usize {assert!(i<3);2*self.n+i}
}

fn gate(out:&mut Vec<Gate>, controls:&[(usize,bool)],target:usize) {
    let mut unique=Vec::new();
    for &(q,v) in controls {
        assert_ne!(q,target,"target/control alias");
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p==q) {if old!=v{return;}}
        else {unique.push((q,v));}
    }
    out.push(Gate{controls:unique,target});
}
fn cx(out:&mut Vec<Gate>,a:usize,b:usize){gate(out,&[(a,true)],b)}

/// Exact little-endian ANF, with v0 fixed to the reachable value1 only on
/// the even-t branch. Thus the proposal is proved over every reachable chart,
/// not over arbitrary even-v invalid codes. Invalid codes retain a unitary
/// extension because all emitted operations remain reversible.
pub fn borrow_terms()->Vec<usize> {
    let mut truth:Vec<bool>=(0..256).map(|x|{
        let t=x&7;let b=(x>>3)&7;let v=1+2*((x>>6)&3);
        let u=if t&1!=0 {b} else {v*(71-t*b)&7};u<t
    }).collect();
    for bit in 0..8 {for mask in 0..256 {if mask>>bit&1!=0 {truth[mask]^=truth[mask^(1<<bit)];}}}
    truth.iter().enumerate().filter_map(|(i,&x)|x.then_some(i)).collect()
}

pub fn low_borrow(out:&mut Vec<Gate>,l:Layout) {
    let wires=[l.t(0),l.t(1),l.t(2),l.b(0),l.b(1),l.b(2),l.v(1),l.v(2)];
    for mask in borrow_terms(){let mut cs=vec![(l.guard,true)];
        cs.extend((0..8).filter(|&i|mask>>i&1!=0).map(|i|(wires[i],true)));
        gate(out,&cs,l.carry);
    }
}

/// Controlled subtraction on the odd-t chart, in high-to-low ripple-free
/// unit decrements. On even t, the physical r payload is unchanged; its
/// implicit u is adjusted by the newly produced quotient in the equation.
pub fn low_sub(out:&mut Vec<Gate>,l:Layout) {
    for source in 0..3 {for target in (source..3).rev(){
        let mut cs=vec![(l.guard,true),(l.t(0),true),(l.p,true),(l.t(source),true)];
        cs.extend((source..target).map(|i|(l.b(i),false)));
        gate(out,&cs,l.b(target));
    }}
}

fn cell(out:&mut Vec<Gate>,l:Layout,i:usize,inverse:bool) {
    if !inverse {cx(out,l.t(i),l.b(i));cx(out,l.carry,l.t(i));}
    gate(out,&[(l.guard,true),(l.b(i),true),(l.t(i),true)],l.carry);
    if inverse {cx(out,l.carry,l.t(i));cx(out,l.t(i),l.b(i));}
}

pub fn inverse_plan(n:usize)->Vec<Gate> {
    let l=Layout::new(n);let mut out=Vec::new();low_borrow(&mut out,l);
    for i in 3..n {cell(&mut out,l,i,false);}
    cx(&mut out,l.guard,l.p);
    gate(&mut out,&[(l.guard,true),(l.carry,true)],l.p);
    for i in (3..n).rev(){
        cell(&mut out,l,i,true);cx(&mut out,l.carry,l.t(i));
        gate(&mut out,&[(l.guard,true),(l.p,true),(l.t(i),true)],l.b(i));
        cx(&mut out,l.carry,l.t(i));
    }
    low_borrow(&mut out,l);low_sub(&mut out,l);out
}

pub fn apply_scalar(plan:&[Gate],state:&mut[bool]) {
    for op in plan {if op.controls.iter().all(|&(q,v)|state[q]==v){state[op.target]^=true;}}
}
