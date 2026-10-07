//! Fixed-width low3 T10 with real remaining quotient bit and S=0/1/2.
//! This is the normal (r has at least3 semantic bits) chart only. At S=0,
//! h is the remaining quotient's bit1 AFTER the current digit was popped.
//! At S=1/2 the remaining q contribution vanishes mod8 for even t.
//! The production source address/cargo boundary adapter is deliberately absent.

#[derive(Clone, Debug)]
pub struct Gate {pub controls:Vec<(usize,bool)>,pub target:usize}
#[derive(Clone, Copy, Debug)]
pub struct Layout {pub n:usize,pub shift:usize,pub h:usize,pub carry:usize,pub p:usize,pub guard:usize,pub used:usize}
impl Layout {
    pub fn new(n:usize,shift:usize)->Self{assert!(n>=3&&shift<=2);Self{n,shift,h:2*n+5,carry:2*n+6,p:2*n+7,guard:2*n+8,used:2*n+9}}
    pub fn t(self,i:usize)->usize{assert!(i<self.n);i}
    pub fn b(self,i:usize)->usize{assert!(i<self.n);self.n+i}
    pub fn v(self,i:usize)->usize{assert!(i<3);2*self.n+i}
    pub fn extra(self,i:usize)->usize{assert!(i<2);2*self.n+3+i}
    pub fn chart(self,i:usize)->usize{assert!(i<3);if i<self.shift{self.extra(i)}else{self.b(i-self.shift)}}
}
pub fn gate(out:&mut Vec<Gate>,controls:&[(usize,bool)],target:usize){let mut unique=Vec::new();for &(q,v)in controls{assert_ne!(q,target);if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p==q){if old!=v{return;}}else{unique.push((q,v));}}out.push(Gate{controls:unique,target});}
fn cx(out:&mut Vec<Gate>,a:usize,b:usize){gate(out,&[(a,true)],b)}
fn anf(mut values:Vec<bool>)->Vec<usize>{assert!(values.len().is_power_of_two());for bit in 0..values.len().trailing_zeros(){for mask in 0..values.len(){if mask>>bit&1!=0{values[mask]^=values[mask^(1<<bit)];}}}values.iter().enumerate().filter_map(|(i,&v)|v.then_some(i)).collect()}

/// Returns the exact guard-controlled carry oracle. The v0=1 promise is
/// used solely on even t. Every other input and output is arbitrary/restored.
pub fn borrow_spec(l:Layout)->(Vec<usize>,Vec<usize>){
    let mut wires=vec![l.t(0),l.t(1),l.t(2),l.b(0),l.b(1),l.b(2)];
    match l.shift{0=>wires.extend([l.v(1),l.v(2),l.h]),1=>wires.extend([l.extra(0),l.v(2)]),2=>(),_=>unreachable!()}
    let truth=(0..1usize<<wires.len()).map(|x|{
        let t=x&7;let b=x>>3&7;
        let u=if t&1!=0||l.shift==2{b}else if l.shift==0{
            let v=1+2*(x>>6&3);let h=x>>8&1;(v*(71-t*b)+16-2*h*t)&7
        }else{
            let r0=x>>6&1;let v2=x>>7&1;let t1=t>>1&1;let t2=t>>2&1;let r1=b&1;
            let u1=1^v2^(t1&r1)^(t2&r0);(b&5)|(u1<<1)
        };u<t
    }).collect();(wires,anf(truth))
}
pub fn low_borrow(out:&mut Vec<Gate>,l:Layout){let(wires,terms)=borrow_spec(l);for mask in terms{let mut cs=vec![(l.guard,true)];cs.extend((0..wires.len()).filter(|&i|mask>>i&1!=0).map(|i|(wires[i],true)));gate(out,&cs,l.carry);}}
fn ordinary_sub(out:&mut Vec<Gate>,l:Layout,odd:bool,first:usize){for source in first..3{for target in(source..3).rev(){let mut cs=vec![(l.guard,true),(l.t(0),odd),(l.p,true),(l.t(source),true)];cs.extend((source..target).map(|i|(l.b(i),false)));gate(out,&cs,l.b(target));}}}
pub fn low_sub(out:&mut Vec<Gate>,l:Layout){
    ordinary_sub(out,l,true,0);
    match l.shift{
        0=>(),
        1=>{let base=vec![(l.guard,true),(l.t(0),false),(l.p,true)];
            for extra in [vec![l.t(2)],vec![l.t(1),l.v(2)],vec![l.t(1),l.b(0)],vec![l.t(1),l.t(2),l.extra(0)]]{
                let mut cs=base.clone();cs.extend(extra.into_iter().map(|q|(q,true)));gate(out,&cs,l.b(2));
            }
        },
        2=>ordinary_sub(out,l,false,1),_=>unreachable!()
    }
}
fn cell(out:&mut Vec<Gate>,l:Layout,i:usize,inverse:bool){if!inverse{cx(out,l.t(i),l.b(i));cx(out,l.carry,l.t(i));}gate(out,&[(l.guard,true),(l.b(i),true),(l.t(i),true)],l.carry);if inverse{cx(out,l.carry,l.t(i));cx(out,l.t(i),l.b(i));}}
pub fn inverse_plan(n:usize,shift:usize)->Vec<Gate>{let l=Layout::new(n,shift);let mut out=Vec::new();low_borrow(&mut out,l);for i in 3..n{cell(&mut out,l,i,false);}cx(&mut out,l.guard,l.p);gate(&mut out,&[(l.guard,true),(l.carry,true)],l.p);for i in(3..n).rev(){cell(&mut out,l,i,true);cx(&mut out,l.carry,l.t(i));gate(&mut out,&[(l.guard,true),(l.p,true),(l.t(i),true)],l.b(i));cx(&mut out,l.carry,l.t(i));}low_borrow(&mut out,l);low_sub(&mut out,l);out}
pub fn apply_scalar(plan:&[Gate],state:&mut[bool]){for op in plan{if op.controls.iter().all(|&(q,v)|state[q]==v){state[op.target]^=true;}}}
