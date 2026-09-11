//! Converter-open low-seed metadata. The partial86 chart stays OPEN across
//! factor::emit, so A8 = a ++ word[0..2] and C8 = c ++ word[2..4] are literal
//! registers: the four rank-minterm flag predicates (A==0, A==1, A==254,
//! C==0; 3/3/2/13 cubes of 7-11 literals) each collapse to ONE 8-literal cube.
//!
//! Shift 0 only. At shift 1 chart_seed never opens this converter today, so
//! the rank5+cache word is not yet proven to be a valid converter input there.
//!
//! No new qubit, no measurement, no approximation, compile-time selection.
//! The seed's Boolean function is NOT defined here: it comes from
//! super::seed_anf so exactly one copy exists.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{arithmetic,factor,numeric_route,seed_anf};
#[path="q794_r01_numeric_partial.rs"] mod chart;

pub(super) fn enabled()->bool{
    std::env::var("Q794_R01_NUMERIC_SEED").ok().as_deref()==Some("1")
}

/// Numeric replacement for super::flag_terms on an OPEN converter.
/// flag 0,1,2 -> A==0,1,254 over the 8-bit A; flag 3 -> C==0 over the 8-bit C.
fn open_flag_terms<'a>(aa:&'a[QReg],cc:&'a[QReg],flag:usize)->Vec<Vec<(&'a QReg,bool)>>{
    assert_eq!(aa.len(),8);assert_eq!(cc.len(),8);assert!(flag<4);
    if flag==3{return vec![cc.iter().map(|q|(q,false)).collect()];}
    let av=[0usize,1,254][flag];
    vec![aa.iter().enumerate().map(|(i,q)|(q,av>>i&1!=0)).collect()]
}

/// Drop-in for super::chart_seed at shift 0. Identical parameter list.
/// Entry and exit contract is chart_seed's: C is ORIGINAL on both sides and
/// every wire except `ha` is restored. The converter is a permutation of
/// `word` and is inverted here, so off-guard state is carried through exactly.
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],
                   g:&QReg,mask:&QReg,ha:&QReg,cache:&QReg,
                   w1:&[QReg],w2:&[QReg],dirty:&[QReg],shift:usize){
    assert_eq!(shift,0,"numeric seed helper is shift 0 only");
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);
    assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);
    assert!(dirty.len()>=18);
    let owned=circ.b.next_qubit;

    let word:Vec<QReg>=rank.iter().chain(std::iter::once(cache)).map(QReg::borrowed_alias).collect();
    let aa:Vec<QReg>=a.iter().chain(word[..2].iter()).map(QReg::borrowed_alias).collect();
    let cc:Vec<QReg>=c.iter().chain(word[2..4].iter()).map(QReg::borrowed_alias).collect();

    let mut ids:Vec<_>=word.iter().chain(a).chain(c)
        .chain([g,mask,ha]).map(QReg::id).collect();
    ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"numeric seed aliases");
    assert!(dirty.iter().all(|q|!ids.contains(&q.id())),"numeric seed dirty overlap");

    // Open the chart. C is original on entry, exactly as chart_seed requires.
    let converter_at=circ.b.ops.len();
    chart::emit(circ,&word,dirty);
    let converter=circ.b.ops[converter_at..].to_vec();

    // Route the qpre1 root on the 8-bit sum, then restore the sum.
    let route_at=circ.b.ops.len();
    arithmetic::add(circ,&aa,&cc,None,false);
    let root:&QReg=numeric_route::route(circ,&cc,w1,1);
    arithmetic::add(circ,&aa,&cc,None,true);
    let route_undo=circ.b.ops[route_at..].to_vec();

    let chart_bits=[&w1[0],&w1[1],&w2[(259-shift)%259],&w2[(260-shift)%259],
                    &w2[258-shift],&w2[257-shift]];
    let flags:Vec<Vec<Vec<(&QReg,bool)>>>=(0..4).map(|f|open_flag_terms(&aa,&cc,f)).collect();
    assert!(flags.iter().all(|f|f.len()==1&&f[0].len()==8),"numeric flag shape");

    let mut inputs:Vec<&QReg>=chart_bits.to_vec();
    inputs.push(root);
    factor::emit(circ,&inputs,g,mask,ha,dirty,&flags,seed_anf(shift),shift);

    circ.b.ops.extend(route_undo.into_iter().rev());
    circ.b.ops.extend(converter.into_iter().rev());
    assert_eq!(circ.b.next_qubit,owned);
}
