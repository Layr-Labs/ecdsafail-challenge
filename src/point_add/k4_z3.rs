//! K4 complete Z-loop adapter; the qualified U6 body/decoder contracts are reused literally.
use super::*;
use super::super::direct_payload::k4_complete::Roles3;
use super::super::maj_virtual_leading::{K4BoundaryQuery,K4QueryContract};

/// C1: the complete original S guard is conjoined to the one B2 boundary
/// query.  This wrapper never narrows to an alias census and never reads a
/// borrowed S-prefix lane.
struct FullSumGuard<'a,'m,Q>{inner:&'a mut Q,meta:&'m SumSize,guard:Guard}
impl<Q:K4BoundaryQuery> BoundaryQuery for FullSumGuard<'_,'_,Q>{
    fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]){
        for term in self.guard.terms(self.meta,true){
            let mut controls=extra.to_vec();controls.extend(term);
            self.inner.xor(b,value,target,&controls,dirty);
        }
    }
    fn clear(&mut self,b:&mut B){self.inner.clear(b);}
}
impl<Q:K4BoundaryQuery> K4BoundaryQuery for FullSumGuard<'_,'_,Q>{
    fn k4_contract(&self)->K4QueryContract{self.inner.k4_contract()}
}

/// C1 direct G': only a decoded residue that has a skipped box alias needs
/// S gating. The exact direct interval for physical Z=v is derived from
/// Y+Z=226+S and the public Y box; this is not an observed-zero premise.
struct DirectSumGuard<'a,'m,Q>{
    inner:&'a mut Q,meta:&'m SumSize,ranges:Ranges,limit:usize,period:usize,
}
impl<Q:K4BoundaryQuery> DirectSumGuard<'_,'_,Q>{
    fn s_bounds(&self,z:usize)->Option<(usize,usize)>{
        let lo=(z as isize+self.ranges.y.0 as isize-226).max(0);
        let hi=(z as isize+self.ranges.y.1 as isize-226).min(31);
        (lo<=hi).then_some((lo as usize,hi as usize))
    }
    fn needs_gprime(&self,value:usize)->bool{
        (self.ranges.z.0..=self.ranges.z.1).any(|z|
            z%self.period==value%self.period &&
            self.s_bounds(z).is_some_and(|(_,hi)|hi>self.limit))
    }
    fn cover_sum(&self,mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
        let mut out=vec![];
        while lo<hi{
            let mut f=if lo==0{5}else{lo.trailing_zeros() as usize};
            f=f.min(5);while lo+(1usize<<f)>hi{f-=1;}
            out.push((f..5).map(|i|(self.meta.sum[i],lo>>i&1==0)).collect());
            lo+=1usize<<f;
        }
        out
    }
}
impl<Q:K4BoundaryQuery> BoundaryQuery for DirectSumGuard<'_,'_,Q>{
    fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]){
        if !self.needs_gprime(value){
            self.inner.xor(b,value,target,extra,dirty);return;
        }
        let Some((lo,hi))=self.s_bounds(value)else{return;};
        let hi=hi.min(self.limit);
        if lo>hi{return;}
        for term in self.cover_sum(lo,hi+1){
            let mut controls=extra.to_vec();controls.extend(term);
            self.inner.xor(b,value,target,&controls,dirty);
        }
    }
    fn clear(&mut self,b:&mut B){self.inner.clear(b);}
}
impl<Q:K4BoundaryQuery> K4BoundaryQuery for DirectSumGuard<'_,'_,Q>{
    fn k4_contract(&self)->K4QueryContract{self.inner.k4_contract()}
}

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
    let ds=inverse&&std::env::var("C658_WP3_DS").as_deref()==Ok("1")
        &&std::env::var("C658_WP3").as_deref()==Ok("1");
    let zh=!inverse&&std::env::var("C658_WP3_ZH").as_deref()==Ok("1")
        &&std::env::var("C658_WP3").as_deref()==Ok("1");
    let b2=std::env::var("C658_WP3_B2").as_deref()==Ok("1")
        &&std::env::var("C658_WP3").as_deref()==Ok("1");
    if inverse&&!ds{b.cx(r.sign,r.activity);}
    let g=Guard{y:(1,128),sum_limit:sum_limit as isize};
    let guard=if ds{vec![]}else{g.witness_record(b,meta,r.activity,r.flight,&coordinate_dirty)};
    if !ds{b.play(&guard,false);}
    match plan(lo,hi,yh,limit){
        Plan::Tree(mut leaves)=>{
            let coordinate=meta.z_epoch(b,&coordinate_dirty);b.play(&coordinate,false);
            if ds{for leaf in &mut leaves{leaf.prefixes=leaf.prefixes.min(leaf.q_zeros);}}
            let mut decoder=Decoder{meta,q,activity:r.activity,lo,hi,limit,leaves,cur:None};
            let arithmetic=if ds{
                if std::env::var("R14_DIG_DS_DIRECT_EXPERIMENT").as_deref()==Ok("1"){
                    let mut guarded=DirectSumGuard{inner:&mut decoder,meta,ranges,limit,period:128};
                    super::super::maj_virtual_leading::physical_restoring_record3_b2(
                        b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                        &kernel_dirty,&held,&meta.y,0,&mut guarded,false)
                }else{
                    let mut guarded=FullSumGuard{inner:&mut decoder,meta,guard:g};
                    super::super::maj_virtual_leading::physical_restoring_record3_b2(
                        b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                        &kernel_dirty,&held,&meta.y,0,&mut guarded,false)
                }
            }else if zh{
                super::super::maj_virtual_leading::physical_restoring_record3_b2(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,&meta.y,0,&mut decoder,true)
            }else if b2{
                super::super::maj_virtual_leading::physical_restoring_record3_b2(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,&meta.y,0,&mut decoder,false)
            }else{
                super::super::maj_virtual_leading::physical_restoring_record3(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,&mut decoder,super::super::maj_virtual_leading::K4Mutation::None)
            }.expect("K4 U6 exact production decoder/operand contract").tape;
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
        Plan::Window{width,prefixes}=>{
            let window=SizeWindow::new(meta,Size::Z,lo,hi,limit);
            assert_eq!(window.width,width);
            let coordinate=window.entry_record(b,&coordinate_dirty);b.play(&coordinate,false);
            let pre:Vec<_>=if ds{
                meta.y[width..].iter().chain(q[..128-yh].iter()).copied()
                    .take(prefixes).collect()
            }else{window.spares().into_iter().chain(q[..128-yh].iter().copied())
                .take(prefixes).collect()};
            if !ds{assert_eq!(pre.len(),prefixes);}
            if ds{assert!(pre.iter().all(|p|!meta.sum.contains(p)));}
            let mut decoder=WindowDecoder::new(&window,&pre,r.activity);
            let arithmetic=if ds{
                if std::env::var("R14_DIG_DS_DIRECT_EXPERIMENT").as_deref()==Ok("1"){
                    let mut guarded=DirectSumGuard{inner:&mut decoder,meta,ranges,limit,period:1usize<<width};
                    super::super::maj_virtual_leading::physical_restoring_record3_b2(
                        b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                        &kernel_dirty,&held,window.address(),lo,&mut guarded,false)
                }else{
                    let mut guarded=FullSumGuard{inner:&mut decoder,meta,guard:g};
                    super::super::maj_virtual_leading::physical_restoring_record3_b2(
                        b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                        &kernel_dirty,&held,window.address(),lo,&mut guarded,false)
                }
            }else if zh{
                super::super::maj_virtual_leading::physical_restoring_record3_b2(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,window.address(),lo,&mut decoder,true)
            }else if b2{
                super::super::maj_virtual_leading::physical_restoring_record3_b2(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,window.address(),lo,&mut decoder,false)
            }else{
                super::super::maj_virtual_leading::physical_restoring_record3(
                    b,&target,source,r.activity,r.flight,r.sign,q[127],lo,hi,
                    &kernel_dirty,&held,&mut decoder,super::super::maj_virtual_leading::K4Mutation::None)
            }.expect("K4 U6 exact production decoder/operand contract").tape;
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
    }
    if !ds{b.play(&guard,true);}
    if inverse&&!ds{b.cx(r.sign,r.activity);}
}
