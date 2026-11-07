//! SOURCE-ONLY whole-word coordinate for ordinary boundary size probes.
//! Align R's leading bit to lane225+S by rotating the complete257 ring UP Y.
//! S is then the highest index in the fixed32-lane window225..257.
//! The whole frame closes before returning. No extra physical owner.
use super::builder::{B,G};
use super::sum_size::SumSize;
use crate::circuit::QubitId;

fn mc(n:usize)->usize{match n{0|1=>0,2=>1,n=>4*(n-2)}}
fn query(n:usize,clean:usize)->usize{
    if n<=2{return mc(n);}let used=clean.min(n-2);
    if used==0{return mc(n);}let rest=n-used-1;
    if rest==1{return used+1;}
    let(mut available,mut pos,mut stack,mut prep)=(2*used,0,1,0);
    while rest-pos>=2{let take=(available+1).min(rest-pos);
        prep+=take-1;available=available-1+take;pos+=take;stack+=1;}
    used+2*prep+mc(stack+rest-pos)
}
fn interval(mut lo:usize,hi:usize)->usize{
    let mut cost=0;
    while lo<hi{
        let mut free=if lo==0{7}else{(lo.trailing_zeros()as usize).min(7)};
        while lo+(1usize<<free)>hi{free-=1;}
        cost+=query(7-free,2);lo+=1usize<<free;
    }cost
}
fn const5(mut amount:isize)->usize{
    let(mut i,mut cost)=(0,0);
    while amount!=0&&i<5{
        if amount&1!=0{let digit=2-(amount&3);
            cost+=[0,0,0,1,5,13][5-i];amount-=digit;}
        amount>>=1;i+=1;
    }cost
}
/// Public source formula only; never builds the rejected old/new tape.
pub(crate) fn preferred(bits:(usize,usize),gated:bool)->bool{
    let mut old=0;
    for l in bits.0..bits.1{
        let lo=(224isize-l as isize).clamp(0,128)as usize;
        let hi=(256isize-l as isize).clamp(0,128)as usize;
        if lo<hi{old+=2*interval(lo,hi)+2*query(7+usize::from(gated),1)
            +2*const5((l&31)as isize)+5;}
    }
    3584+(if gated{167}else{151})<=old
}

/// Active care: E=Y-1, the bottom number has its highest valid bit in
/// [225-Y,256-Y], and no larger set bit in that SAME window. Source bits
/// outside that window may be arbitrary, including the complete upper word.
/// S begins0 on gate1. On gate0 arbitrary S/source are returned exactly.
/// The old partial-window DL probes do not satisfy this stronger contract.
pub(crate) fn record(b:&mut B,size:&SumSize,ring:&[QubitId],
    gate:Option<(QubitId,bool)>,dirty:&[QubitId])->Vec<G>{
    assert_eq!(ring.len(),257);
    assert!(!ring.iter().any(|q|size.y.contains(q)||size.sum.contains(q)));
    if let Some((g,_))=gate{assert!(!ring.contains(&g)&&!size.y.contains(&g)&&!size.sum.contains(&g));}
    b.begin();
    for(k,&e)in size.y.iter().enumerate(){super::frogdrop::crot_up(b,e,ring,1usize<<k);}
    // Constant UP1: this is a wire permutation, charged as actual SWAPs.
    for i in 1..257{b.swap(ring[0],ring[i]);}
    let frame=b.end();
    let probe=super::frogdrop::binary_msb::record(b,&ring[225..257],&size.sum,gate,dirty);
    b.begin();b.play(&frame,false);b.play(&probe,false);b.play(&frame,true);b.end()
}
