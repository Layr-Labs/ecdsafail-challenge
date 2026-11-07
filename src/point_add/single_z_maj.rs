//! SOURCE-ONLY single-MAJ Z-source payload epoch. No candidate integration.
//!
//! Q is the unparked positive Y operand on retained activity. Normalize
//! Q128 UP(128-Y) for the complete named Z half, then X its leading ONE.
//! Q127 is a conditional-zero carry, never a decoder or dirty donor.
//! Every kernel has one sum witness, one Zmod128 coordinate, one complete
//! MAJ record, and their exact inverses. Source and carry tails are intact.
//! Public-only pricing selects an exact dyadic decoder or offset window;
//! it never constructs the rejected gate tape or examines input values.

use super::activity_guard::Guard;
use super::builder::{B,G};
use super::direct_payload::{Ranges,Roles};
use super::maj_virtual_leading::{BoundaryQuery,physical_restoring_record};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn bits(v:usize)->usize{if v==0{0}else{usize::BITS as usize-v.leading_zeros()as usize}}
fn mc_price(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*(n-2)}}
fn cover(mut lo:usize,hi:usize,width:usize)->Vec<(usize,usize)>{
    assert!(lo<=hi&&hi<=1usize<<width);let mut out=Vec::new();
    while lo<hi{
        let mut free=if lo==0{width}else{(lo.trailing_zeros()as usize).min(width)};
        while lo+(1usize<<free)>hi{free-=1;}
        out.push((lo,free));lo+=1usize<<free;
    }out
}
fn inc_price(n:usize)->usize{match n{0|1|2=>0,3=>1,4=>5,5=>13,_=>4*(n-1)}}
fn constant_price(amount:isize)->usize{
    let(mut left,mut bit,mut cost)=(amount.rem_euclid(128),0,0);
    while left!=0&&bit<7{
        if left&1!=0{let digit=2-(left&3);cost+=inc_price(7-bit);left-=digit;}
        left>>=1;bit+=1;
    }cost
}

/// The extra S condition is needed only when both residue aliases are
/// within A's public range. Guarded S-high cells are not read here.
fn sum_cover(value:usize,lo:usize,hi:usize,limit:usize)->Vec<(usize,usize)>{
    let width=bits(limit);
    let alias=(value>=128&&lo<=value-128&&value-128<=hi)
        ||(lo<=value+128&&value+128<=hi);
    if !alias{return vec![(0,width)];}
    if value<=128{
        let threshold=value-98;
        if threshold>=limit{vec![(0,width)]}else{cover(0,threshold+1,width)}
    }else{
        let threshold=value-225;
        if threshold==0{vec![(0,width)]}else{cover(threshold,1usize<<width,width)}
    }
}

#[derive(Clone)]
struct Leaf{base:usize,width:usize,prefixes:usize,q_zeros:usize}
#[derive(Clone)]
struct Tree{cost:usize,leaves:Vec<Leaf>}
enum Plan{Tree(Vec<Leaf>),Window{width:usize,prefixes:usize}}

/// Count the literal top-down partial AND ladder, including all clears.
/// A gap in actual Z values ends a run even if the same residue leaf is
/// visited again later. The two queries at one boundary share its cursor.
fn walk_price(width:usize,h:usize,values:&[usize])->usize{
    if h==0{return 0;}
    let mask=(1usize<<width)-1;let(mut old,mut cost)=(None,0);
    for &value in values{
        let v=value&mask;let mut keep=0;
        if let Some((prior,p))=old{
            if prior==value+1{
                while keep<h&&((p^v)>>(width-2-keep))==0{keep+=1;}
            }
            cost+=h-keep;
        }
        cost+=h-keep;old=Some((value,v));
    }
    cost+if old.is_some(){h}else{0}
}
fn tree(base:usize,width:usize,lo:usize,hi:usize,yhi:usize,limit:usize)->Tree{
    let values:Vec<_>=(lo..=hi).rev()
        .filter(|v|base<=v%128&&v%128<base+(1usize<<width)).collect();
    if values.is_empty(){return Tree{cost:0,leaves:Vec::new()};}
    let minimum=*values.iter().min().unwrap();
    let q_zeros=(128-yhi).max((128+minimum).saturating_sub(226+limit));
    assert!(q_zeros<=127);
    let h=width.saturating_sub(1).min(q_zeros+5-bits(limit));
    let query:usize=values.iter().map(|&v|sum_cover(v,lo,hi,limit).iter()
        .map(|&(_,free)|2*mc_price(8-h+bits(limit)-free)).sum::<usize>()).sum();
    let own=Tree{cost:query+walk_price(width,h,&values),
        leaves:vec![Leaf{base,width,prefixes:h,q_zeros}]};
    if width==0{return own;}
    let mut left=tree(base,width-1,lo,hi,yhi,limit);
    let right=tree(base+(1usize<<(width-1)),width-1,lo,hi,yhi,limit);
    if left.cost+right.cost<own.cost{
        left.cost+=right.cost;left.leaves.extend(right.leaves);left
    }else{own}
}
fn plan(lo:usize,hi:usize,yhi:usize,limit:usize)->Plan{
    let tree=tree(0,7,lo,hi,yhi,limit);
    if hi-lo<128{
        let width=bits(hi-lo);
        let h=width.saturating_sub(1).min(7-width+5-bits(limit)+128-yhi);
        let values:Vec<_>=(0..=hi-lo).rev().collect();
        let price=2*(hi-lo+1)*mc_price(width+1-h)
            +walk_price(width,h,&values)+2*constant_price(-(lo as isize));
        if price<tree.cost{return Plan::Window{width,prefixes:h};}
    }Plan::Tree(tree.leaves)
}

/// Literal conditional prefix. Only A AND the unchanged hard-address
/// class promises zero on its Q loans. Keep BOTH controls in every final
/// query; the partial prefix by itself does not imply activity or class.
struct Decoder<'a>{
    meta:&'a SumSize,q:&'a [QubitId],activity:QubitId,
    lo:usize,hi:usize,limit:usize,leaves:Vec<Leaf>,
    cur:Option<(usize,usize)>,
}
impl Decoder<'_>{
    fn ports(&self,leaf:&Leaf)->Vec<QubitId>{
        self.q[..leaf.q_zeros].iter().chain(&self.meta.sum[bits(self.limit)..])
            .copied().take(leaf.prefixes).collect()
    }
    fn cell(&self,b:&mut B,leaf:&Leaf,pre:&[QubitId],i:usize,value:usize){
        let n=leaf.width;
        let(a,na)=if i==0{(self.meta.y[n-1],value>>(n-1)&1==0)}else{(pre[i-1],false)};
        let(c,nc)=(self.meta.y[n-2-i],value>>(n-2-i)&1==0);
        if na{b.x(a);}if nc{b.x(c);}b.ccx(a,c,pre[i]);if nc{b.x(c);}if na{b.x(a);}
    }
    fn controls(&mut self,b:&mut B,value:usize)->Vec<(QubitId,bool)>{
        let index=self.leaves.iter().position(|l|l.base<=value%128
            &&value%128<l.base+(1usize<<l.width)).expect("public address leaf");
        if self.cur.is_some_and(|(old,_)|old!=index){self.clear(b);}
        let leaf=&self.leaves[index];let pre=self.ports(leaf);
        assert_eq!(pre.len(),leaf.prefixes);
        let n=leaf.width;let h=pre.len();let v=value&((1usize<<n)-1);
        if h>0{
            let mut keep=0;
            if let Some((_,old))=self.cur{
                while keep<h&&((old^v)>>(n-2-keep))==0{keep+=1;}
                for i in(keep..h).rev(){self.cell(b,leaf,&pre,i,old);}
            }
            for i in keep..h{self.cell(b,leaf,&pre,i,v);}
            self.cur=Some((index,v));
        }
        let mut out=vec![(self.activity,false)];
        out.extend((n..7).map(|i|(self.meta.y[i],value>>i&1==0)));
        let low=if h>0{out.push((pre[h-1],false));n-1-h}else{n};
        out.extend((0..low).map(|i|(self.meta.y[i],value>>i&1==0)));out
    }
}
impl BoundaryQuery for Decoder<'_>{
    fn clear(&mut self,b:&mut B){
        if let Some((index,old))=self.cur{
            let leaf=&self.leaves[index];let pre=self.ports(leaf);
            for i in(0..pre.len()).rev(){self.cell(b,leaf,&pre,i,old);}
        }self.cur=None;
    }
    fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]){
        assert!((self.lo..=self.hi).contains(&value));
        let common=self.controls(b,value);
        let mut excluded:BTreeSet<_>=self.meta.y.iter().chain(&self.meta.sum)
            .chain(self.q).copied().chain([target,self.activity]).collect();
        excluded.extend(extra.iter().map(|p|p.0));
        let bank:Vec<_>=dirty.iter().copied().filter(|p|excluded.insert(*p)).collect();
        for(base,free)in sum_cover(value,self.lo,self.hi,self.limit){
            let mut c=common.clone();
            c.extend((free..bits(self.limit)).map(|i|(self.meta.sum[i],base>>i&1==0)));
            let mut contradiction=false;
            for &(q,neg)in extra{
                assert!(q!=target);
                if let Some((_,old))=c.iter().find(|p|p.0==q){if *old!=neg{contradiction=true;break;}}
                else{c.push((q,neg));}
            }
            assert!(!c.iter().any(|p|p.0==target));
            if !contradiction{mc_xor(b,&c,target,&[],&bank);}
        }
    }
}

/// Whole named Z half only. The shell must keep this frame across all
/// k, restoring it before sign/reflection or widening. Park/fetch may use
/// Q as returned dirty donors but must not leave quotient data in Q.
pub(crate) fn frame_record(b:&mut B,meta:&SumSize,q:&[QubitId])->Vec<G>{
    assert_eq!(q.len(),128);
    assert!(!q.iter().any(|p|meta.y.contains(p)||meta.sum.contains(p)));
    b.begin();
    for &e in &meta.y{b.x(e);}
    for(k,&e)in meta.y.iter().enumerate(){super::frogdrop::crot_up(b,e,q,1usize<<k);}
    for &e in &meta.y{b.x(e);}
    b.x(q[127]);b.end()
}

/// Keep the virtual HR source leading ONE physical for the complete
/// thirty-bit Z epoch. Sign is otherwise unused until the later payload
/// sign read. It holds A*!old_head; the exact inverse restores it to0.
/// Flight/work are returned before any kernel or park is entered.
pub(crate) fn leading_one_record(b:&mut B,meta:&SumSize,ring:&[QubitId],
    r:Roles,range:(usize,usize),dirty:&[QubitId])->Vec<G>{
    assert_eq!(ring.len(),257);assert!(98<=range.0&&range.0<=range.1&&range.1<=256);
    let mut held:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied()
        .chain([r.activity,r.flight,r.sign,r.work]).collect();
    let d:Vec<_>=dirty.iter().copied().filter(|q|held.insert(*q)).collect();
    let address=super::direct_frame::z_byte_record(b,meta,r.work,&d);
    let byte:Vec<_>=meta.y.iter().copied().chain([r.work]).collect();
    let leaves:Vec<_>=(range.0..=range.1).map(|z|(z-1,ring[z-1])).collect();
    let mut swaps=vec![];let root=super::midg::swap_tree(&byte,&leaves,8,&mut swaps);
    b.begin();b.play(&address,false);
    for &(c,a,z) in &swaps{b.cswap(c,a,z);}
    b.x(root);b.ccx(r.activity,root,r.sign);b.x(root);b.cx(r.sign,root);
    for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
    b.play(&address,true);b.end()
}

/// One merged full-Y kernel. Q is already normalized; q127 is zero on
/// original A. The inverse sign toggle and sum witness may only narrow A.
/// Return Q, metadata, mask/membership roles and guard witnesses; forward
/// leaves its selected quotient bit on flight for the original park.
pub(crate) fn apply(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],ring:&[QubitId],
    r:Roles,ranges:Ranges,k:usize,inverse:bool,dirty:&[QubitId]){
    use super::size_window::{SizeWindow,WindowDecoder};
    use super::ttk_virtual_leading::Size;
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
    let source=&ring[..hi+1];let scalar=[r.activity,r.flight,r.sign,r.work];
    let mut occupied=BTreeSet::new();
    assert!(meta.y.iter().chain(&meta.sum).chain(q).chain(raw).chain(ring)
        .copied().chain(scalar).all(|p|occupied.insert(p)));
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().chain(scalar).collect();
    let coordinate_dirty:Vec<_>=dirty.iter().chain(raw).chain(ring).chain(q).copied()
        .filter(|p|used.insert(*p)).collect();
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).chain(q).copied().chain(scalar).collect();
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
            let arithmetic=physical_restoring_record(b,&target,source,r.activity,r.flight,
                r.work,q[127],lo,hi,&kernel_dirty,&mut decoder);
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
        Plan::Window{width,prefixes}=>{
            let window=SizeWindow::new(meta,Size::Z,lo,hi,limit);
            assert_eq!(window.width,width);
            let coordinate=window.entry_record(b,&coordinate_dirty);b.play(&coordinate,false);
            let pre:Vec<_>=window.spares().into_iter().chain(q[..128-yh].iter().copied())
                .take(prefixes).collect();assert_eq!(pre.len(),prefixes);
            let mut decoder=WindowDecoder::new(&window,&pre,r.activity);
            let arithmetic=physical_restoring_record(b,&target,source,r.activity,r.flight,
                r.work,q[127],lo,hi,&kernel_dirty,&mut decoder);
            b.play(&arithmetic,inverse);b.play(&coordinate,true);
        }
    }
    b.play(&guard,true);if inverse{b.cx(r.sign,r.activity);}
}
