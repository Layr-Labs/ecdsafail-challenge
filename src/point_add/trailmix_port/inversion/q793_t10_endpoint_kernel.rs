//! Exact T10 short-tail quotient pop on the root's packed-P chart.
//! R2: X=v*2^S<4, r<v, S0/1. R1: v1,S0,r0.
//! Odd t stores b=u; even t stores b=r+2^R*(qstored mod2^(3-R)).
//! h1/h2 are genuine retained qstored bits, including constant head/cargo
//! cofactors which the physical adapter must supply. No physical addresses
//! or unproved boundary assumptions are embedded in this kernel.
#[derive(Clone,Debug)]pub struct Gate{pub controls:Vec<(usize,bool)>,pub target:usize}
// Layout t0..2=0..2, b0..2=3..5, v0..1=6..7,
// qstored h1/h2=8..9, pop=10, guard=11; supplied dirty starts12.
pub fn odd_pop(rwidth:usize,shift:usize,t:usize,b:usize,v:usize,h:usize)->bool{
    assert!(t&1!=0);
    if rwidth==1{return b&1==0;}
    assert_eq!(rwidth,2);assert!(shift<=1);
    let x=v<<shift;if v==0||x>=4{return false;}
    let qhigh=(h&3)<<1;
    let d=((71-b*v)*t+256-((qhigh<<shift)*v))&7;
    d>=x
}
pub fn pop_plan(rwidth:usize,shift:usize)->Vec<Gate>{
    assert!((rwidth==1&&shift==0)||(rwidth==2&&shift<=1));
    let mut values:Vec<_>=(0..1024).map(|x|{
        let t=x&7;let b=x>>3&7;let v=x>>6&3;let h=x>>8&3;
        if t&1==0{b>>rwidth&1!=0}else{odd_pop(rwidth,shift,t,b,v,h)}
    }).collect();
    for bit in 0..10{for mask in 0..1024{if mask>>bit&1!=0{values[mask]^=values[mask^(1<<bit)];}}}
    let mut out=Vec::new();for(mask,&value)in values.iter().enumerate(){if value{
        let mut controls=vec![(11,true)];controls.extend((0..10).filter(|&i|mask>>i&1!=0).map(|i|(i,true)));out.push(Gate{controls,target:10});
    }}
    // Offguard identity; onguard arbitrary pop is a reversible extension.
    // With the caller's pop0, this removes precisely the consumed q0 bit.
    out.push(Gate{controls:vec![(11,true),(0,false),(10,true)],target:3+rwidth});out
}
pub fn apply(plan:&[Gate],state:&mut[bool]){for op in plan{if op.controls.iter().all(|&(q,v)|state[q]==v){state[op.target]^=true;}}}
