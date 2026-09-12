//! General T10 only: source[A+1] is zero after the existing cargo handoff.
//! Loan that top as carry; retain the existing high-A cache and mask loans.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_arithmetic5_programs.rs"] mod programs;

fn top_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,carry:&QReg,source:&[QReg],dirty:&[QReg]) {
    let(root,gather)=super::q798_handoffs::gather_a(circ,rank,a,source,1,dirty);
    circ.cswap(g,root,carry);circ.b.ops.extend(gather.into_iter().rev());
}
struct Range<'a>{rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],group:isize}
impl Range<'_>{
    fn high(&self,circ:&mut Circuit,h:isize){
        if !(0..4).contains(&h){return;}
        for &(m,v) in programs::A_EQUAL[h as usize] {
            let mut cs=vec![(self.g,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],v>>i&1!=0)));
            mixed_mcx(circ,&cs,self.cache,self.dirty);
        }
    }
    fn equality(&mut self,circ:&mut Circuit,value:usize){
        let(lo,hi)=if std::env::var("Q796_PREFIX_SUPPORT").ok().as_deref()==Some("0"){(0,256)}else{circ.q797_a_support.unwrap_or((0,256))};
        if value<lo||value>=hi{return;}
        let h=value/64;let factor=std::env::var("Q796_PREFIX_FACTORS").ok().as_deref()!=Some("0");
        let mut cs=vec![(self.g,true)];
        if !factor||lo/64!=(hi-1)/64 {
            if self.group!=h as isize{self.high(circ,self.group);self.high(circ,h as isize);self.group=h as isize;}
            cs.push((self.cache,true));
        }
        let left=lo.max(h*64);let right=hi.min((h+1)*64);
        for i in 0..6{if !factor||(left>>i)!=((right-1)>>i){cs.push((&self.a[i],value>>i&1!=0));}}
        if super::metadata_muxlease::active("Q795_T10_TOP_MASK_CLEAN") {
            // Only this mask consumer loses its external guard. On g1,
            // Xg supplies a zero scratch. Offg it is an arbitrary mask-XOR
            // extension, removed by the recorded literal per-cell inverse.
            // Restore g before high-cache transitions and all SUM/center reads.
            circ.x(self.g);super::paired_clean_mcx::toggle(circ,&cs[1..],self.mask,self.g);circ.x(self.g);
        } else {mixed_mcx(circ,&cs,self.mask,self.dirty);}
    }
}
fn cell(circ:&mut Circuit,s:&QReg,t:&QReg,carry:&QReg,mask:&QReg,g:&QReg,inverse:bool){
    if !inverse{circ.cx(s,t);circ.cx(carry,s);}
    circ.x(g);super::paired_clean_mcx::toggle(circ,&[(mask,true),(t,true),(s,true)],carry,g);circ.x(g);
    if inverse{circ.cx(carry,s);circ.cx(s,t);}
}

pub(super) fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],a:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,sign_out:Option<&QReg>,sign_control:Option<&QReg>,helpers:&[QReg],subtract:bool,n:usize){
    assert!((2..=257).contains(&n));assert!(helpers.len()>=17);
    assert!(!subtract||sign_out.is_none());assert!(sign_out.is_none()||sign_control.is_none());
    let carry=&helpers[0];let dirty=&helpers[1..];let start=circ.b.ops.len();
    // All callers must supply zero source[A+1] on g and A+2<=n. Its parked
    // passenger is outside the shortened [0,A+1) arithmetic prefix.
    top_loan(circ,rank,a,g,carry,source,dirty);
    circ.cx(g,mask);circ.cx(g,carry);
    for q in &source[..n]{circ.x(q);}
    let mut range=Range{rank,a,g,cache,mask,dirty,group:-1};let mut updates=Vec::new();
    for i in 0..n {
        let at=circ.b.ops.len();if i>0{range.equality(circ,i-1);}
        updates.push(circ.b.ops[at..].to_vec());
        // Do not skip masked-off CNOTs: the endpoint formula below uses
        // the transformed source/target top, including the parked passenger.
        cell(circ,&source[i],&target[i],carry,mask,g,false);
    }
    let(target_top,target_gather)=super::q798_handoffs::gather_a(circ,rank,a,target,1,dirty);
    if let Some(sign)=sign_out {
        let(source_top,source_gather)=super::q798_handoffs::gather_a(circ,rank,a,source,1,dirty);
        // At the masked-off top: s'=~passenger XOR borrow and
        // t'=old_target XOR ~passenger. Full ADD carry=!borrow*(s' XOR t').
        mixed_mcx(circ,&[(g,true),(carry,false),(source_top,true)],sign,dirty);
        mixed_mcx(circ,&[(g,true),(carry,false),(target_top,true)],sign,dirty);
        circ.b.ops.extend(source_gather.into_iter().rev());
    }
    let mut top_cs=vec![(g,true),(carry,false)];if let Some(q)=sign_control{top_cs.push((q,false));}
    mixed_mcx(circ,&top_cs,target_top,dirty);
    circ.b.ops.extend(target_gather.into_iter().rev());
    for i in (0..n).rev(){
        cell(circ,&source[i],&target[i],carry,mask,g,true);
        circ.cx(carry,&source[i]);
        let mut cs=vec![(g,true),(mask,true),(&source[i],true)];if let Some(q)=sign_control{cs.push((q,false));}
        mixed_mcx(circ,&cs,&target[i],dirty);circ.cx(carry,&source[i]);
        circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    assert!(updates.is_empty());
    for q in &source[..n]{circ.x(q);}
    circ.cx(g,carry);circ.cx(g,mask);
    top_loan(circ,rank,a,g,carry,source,dirty);
    // The conditional SUB is the inverse of the COMPLETE ADD, including
    // top sum write, decoder transitions and both addressed carry exchanges.
    if subtract{circ.b.ops[start..].reverse();}
}
