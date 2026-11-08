//! K4 complete Z-loop adapter; the qualified U6 body/decoder contracts are reused literally.
use super::*;
use super::super::direct_payload::k4_complete::Roles3;

pub(crate) fn leading_one_record3(b:&mut B,meta:&SumSize,ring:&[QubitId],
    r:Roles3,range:(usize,usize),dirty:&[QubitId])->Vec<G>{
    assert_eq!(ring.len(),257);assert!(98<=range.0&&range.0<=range.1&&range.1<=256);
    let mut held:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied()
        .chain([r.activity,r.flight,r.sign]).collect();
    let d:Vec<_>=dirty.iter().copied().filter(|q|held.insert(*q)).collect();
    let address=super::super::direct_frame::z_byte_record(b,meta,r.flight,&d);
    let byte:Vec<_>=meta.y.iter().copied().chain([r.flight]).collect();
    let leaves:Vec<_>=(range.0..=range.1).map(|z|(z-1,ring[z-1])).collect();
    let mut swaps=vec![];let root=super::super::midg::swap_tree(&byte,&leaves,8,&mut swaps);
    b.begin();b.play(&address,false);
    for &(c,a,z) in &swaps{b.cswap(c,a,z);}
    b.x(root);b.ccx(r.activity,root,r.sign);b.x(root);b.cx(r.sign,root);
    for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
    b.play(&address,true);b.end()
}


pub(crate) fn apply3(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],ring:&[QubitId],
    r:Roles3,ranges:Ranges,k:usize,inverse:bool,dirty:&[QubitId],forbidden:&[QubitId]){
    use super::super::size_window::{SizeWindow,WindowDecoder};
    use super::super::ttk_virtual_leading::Size;
    assert_eq!((q.len(),raw.len(),ring.len()),(128,259,257));assert!(k<30);
    let sum_limit=(if inverse{32}else{31})-k;
    let limit=sum_limit.min(31);let total=226+limit;
    let yl=ranges.y.0.max(226usize.saturating_sub(ranges.z.1));
    let yh=ranges.y.1.min(total.saturating_sub(ranges.z.0));
    if yl>yh{return;}
    let lo=ranges.z.0.max(226-yh);let hi=ranges.z.1.min(total-yl);
    if lo>hi{return;}
    assert!(98<=lo&&hi<=256&&k+hi<259);
    let target:Vec<_>=if inverse{(0..=hi).map(|i|raw[258-k-i]).collect()}
        else{raw[k..k+hi+1].to_vec()};
    let source=&ring[..hi+1];let scalar=r.ports();
    let held:Vec<_>=forbidden.iter().copied().chain([raw[258]]).collect();
    let mut occupied=BTreeSet::new();
    assert!(meta.y.iter().chain(&meta.sum).chain(q).chain(raw).chain(ring)
        .copied().chain(scalar).all(|p|occupied.insert(p)));
    assert!(forbidden.iter().all(|p|!occupied.contains(p)));
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().chain(scalar).chain(held.iter().copied()).collect();
    let coordinate_dirty:Vec<_>=dirty.iter().chain(raw).chain(ring).chain(q).copied()
        .filter(|p|used.insert(*p)).collect();
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).chain(q).copied().chain(scalar).chain(held.iter().copied()).collect();
    let kernel_dirty:Vec<_>=dirty.iter().chain(raw).chain(ring).copied()
        .filter(|p|used.insert(*p)).collect();
    if inverse{b.cx(r.sign,r.activity);}
    let guard=Guard{y:(1,128),sum_limit:sum_limit as isize}
        .witness_record(b,meta,r.activity,r.flight,&coordinate_dirty);
    b.play(&guard,false);
    match plan(lo,hi,yh,limit){
        Plan::Tree(leaves)=>{
            let coordinate=meta.z_epoch(b,&coordinate_dirty);b.play(&coordinate,false);
            let mut decoder=Decoder{meta,q,activity:r.activity,lo,hi,limit,leaves,cur:None};
            let arithmetic=super::super::maj_virtual_leading::physical_restoring_record3(
                b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                &kernel_dirty,&held,&mut decoder,super::super::maj_virtual_leading::K4Mutation::None)
                .expect("K4 U6 exact production decoder/operand contract").tape;
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
        Plan::Window{width,prefixes}=>{
            let window=SizeWindow::new(meta,Size::Z,lo,hi,limit);
            assert_eq!(window.width,width);
            let coordinate=window.entry_record(b,&coordinate_dirty);b.play(&coordinate,false);
            let pre:Vec<_>=window.spares().into_iter().chain(q[..128-yh].iter().copied())
                .take(prefixes).collect();assert_eq!(pre.len(),prefixes);
            let mut decoder=WindowDecoder::new(&window,&pre,r.activity);
            let arithmetic=super::super::maj_virtual_leading::physical_restoring_record3(
                b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                &kernel_dirty,&held,&mut decoder,super::super::maj_virtual_leading::K4Mutation::None)
                .expect("K4 U6 exact production decoder/operand contract").tape;
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
    }
    b.play(&guard,true);if inverse{b.cx(r.sign,r.activity);}
}
