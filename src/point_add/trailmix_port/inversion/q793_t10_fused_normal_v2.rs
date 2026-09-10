//! Mod8 normal-domain fused T10 ADD/pop. Requires A2..252, C>=1, M=A+C<=254.
//! Outside this active domain no claim is made. Full offguard identity required.
//! This is not the short-tail endpoint adapter.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_arithmetic5_programs.rs"] mod programs;

fn top_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,carry:&QReg,source:&[QReg],dirty:&[QReg]) {
    let(root,gather)=super::q794_handoffs::gather_a(circ,rank,a,&source[..256],1,dirty);
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

/// Exact inverse map q=p XOR [r>=x], y=r-q*x (mod2^(A+2)). Reversing
/// its COMPLETE circuit emits the old pair's map, including arbitrary P1.
pub(super) fn add_and_clear(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],a:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,p1:&QReg,helpers:&[QReg],n:usize,c:&[QReg],sm:&[QReg],j:usize,c1:bool){
    assert!((4..=257).contains(&n));assert!(helpers.len()>=19);let n=n.min(255);
    let carry=&helpers[0];let dirty=&helpers[1..];let start=circ.b.ops.len();
    assert!(helpers.iter().all(|q|q.id()!=p1.id()&&q.id()!=g.id()&&q.id()!=cache.id()&&q.id()!=mask.id()));
    // Source[A+1] is zero on g after move_t10, distinct from the quotient
    // address funding mask. Carry starts0: NO source complement or carry^=g.
    top_loan(circ,rank,a,g,carry,source,dirty);circ.cx(g,mask);
    let mut range=Range{rank,a,g,cache,mask,dirty,group:-1};let mut updates=Vec::new();
    super::q793_t10_predicates_v2::borrow(circ,rank,a,c,sm,g,source,target,carry,p1,dirty,j,c1);
    for i in 3..n{
        let at=circ.b.ops.len();if i>0{range.equality(circ,i-1);}updates.push(circ.b.ops[at..].to_vec());
        cell(circ,&source[i],&target[i],carry,mask,g,false);
    }
    let(target_top,target_gather)=super::q794_handoffs::gather_a(circ,rank,a,target,1,dirty);
    let(source_top,source_gather)=super::q794_handoffs::gather_a(circ,rank,a,&source[..256],1,dirty);
    // At masked-off top s'=passenger XOR b, t'=old_top XOR passenger.
    // Full borrow=b*(s' XOR t'). XOR threshold into ARBITRARY incoming P1.
    // W and both gathers exclude P1, including every dirty lender.
    circ.cx(g,p1);
    mixed_mcx(circ,&[(g,true),(carry,true),(source_top,true)],p1,dirty);
    mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
    circ.b.ops.extend(source_gather.into_iter().rev());
    mixed_mcx(circ,&[(g,true),(p1,true),(carry,true)],target_top,dirty);
    circ.b.ops.extend(target_gather.into_iter().rev());
    for i in (3..n).rev(){
        // Top changes cannot alter carry undo: its active mask is0. Retain
        // ALL masked-off CNOTs, including passenger and extra tail cells.
        cell(circ,&source[i],&target[i],carry,mask,g,true);
        circ.cx(carry,&source[i]);
        mixed_mcx(circ,&[(g,true),(mask,true),(&source[i],true),(p1,true)],&target[i],dirty);
        circ.cx(carry,&source[i]);circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    assert!(updates.is_empty());
    super::q793_t10_predicates_v2::borrow(circ,rank,a,c,sm,g,source,target,carry,p1,dirty,j,c1);
    super::q793_t10_predicates_v2::sub(circ,rank,a,c,sm,g,source,target,carry,p1,dirty,j,c1);
    circ.cx(g,mask);top_loan(circ,rank,a,g,carry,source,dirty);
    circ.b.ops[start..].reverse();
}
