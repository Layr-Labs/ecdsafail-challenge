//! New mod4 fused T10 ADD and quotient cleanup, inverse of compare/conditional SUB.
//! P1 is arbitrary: exact scalar extension equals the original arithmetic pair.
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

/// Exact inverse map q=p XOR [r>=x], y=r-q*x (mod2^(A+2)). Reversing
/// its COMPLETE circuit emits the old pair's map, including arbitrary P1.
pub(super) fn add_and_clear(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],a:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,p1:&QReg,helpers:&[QReg],n:usize,c:&[QReg],sm:&[QReg],j:usize,c1:bool){
    assert!((2..=257).contains(&n));assert!(helpers.len()>=17);
    let carry=&helpers[0];let dirty=&helpers[1..];let start=circ.b.ops.len();
    let special=special_terms(rank,c,sm,g,&source[0],j,c1);
    assert!(helpers.iter().all(|q|q.id()!=p1.id()&&q.id()!=g.id()&&q.id()!=cache.id()&&q.id()!=mask.id()));
    // Source[A+1] is zero on g after move_t10, distinct from the quotient
    // address funding mask. Carry starts0: NO source complement or carry^=g.
    top_loan(circ,rank,a,g,carry,source,dirty);circ.cx(g,mask);
    let mut range=Range{rank,a,g,cache,mask,dirty,group:-1};let mut updates=Vec::new();
    for i in 0..n{
        let at=circ.b.ops.len();if i>0{range.equality(circ,i-1);}updates.push(circ.b.ops[at..].to_vec());
        cell(circ,&source[i],&target[i],carry,mask,g,false);
        if i==1{low_correction(circ,rank,a,c,source,target,carry,&special,g,dirty,j,c1,false);}
    }
    let(target_top,target_gather)=super::q798_handoffs::gather_a(circ,rank,a,target,1,dirty);
    let(source_top,source_gather)=super::q798_handoffs::gather_a(circ,rank,a,source,1,dirty);
    // At masked-off top s'=passenger XOR b, t'=old_top XOR passenger.
    // Full borrow=b*(s' XOR t'). XOR threshold into ARBITRARY incoming P1.
    // W and both gathers exclude P1, including every dirty lender.
    circ.cx(g,p1);
    if super::metadata_muxlease::active("Q794_T10_POLISH") {
        // The two toggles together are `p1 ^= g*carry*(source_top ^ target_top)`.
        // One CNOT parks that XOR on target_top, so ONE toggle does both, and
        // the frame closes here -- before the line-70 source_gather unwind and
        // the line-71 consumer that reads target_top.
        circ.cx(source_top,target_top);
        mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
        circ.cx(source_top,target_top);
    } else {
    mixed_mcx(circ,&[(g,true),(carry,true),(source_top,true)],p1,dirty);
    mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
    }
    circ.b.ops.extend(source_gather.into_iter().rev());
    mixed_mcx(circ,&[(g,true),(p1,true),(carry,true)],target_top,dirty);
    circ.b.ops.extend(target_gather.into_iter().rev());
    for i in (0..n).rev(){
        // Top changes cannot alter carry undo: its active mask is0. Retain
        // ALL masked-off CNOTs, including passenger and extra tail cells.
        if i==1{low_correction(circ,rank,a,c,source,target,carry,&special,g,dirty,j,c1,true);}
        cell(circ,&source[i],&target[i],carry,mask,g,true);
        circ.cx(carry,&source[i]);
        mixed_mcx(circ,&[(g,true),(mask,true),(&source[i],true),(p1,true)],&target[i],dirty);
        if i==1{for term in &special{let mut cs=term.clone();cs.extend([(mask,true),(&source[1],true),(p1,true)]);super::q794_t10_quotient::gate(circ,&cs,&target[1],dirty);}}
        circ.cx(carry,&source[i]);circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    assert!(updates.is_empty());circ.cx(g,mask);top_loan(circ,rank,a,g,carry,source,dirty);
    circ.b.ops[start..].reverse();
}


fn special_terms<'a>(rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,t0:&'a QReg,j:usize,c1:bool)->Vec<Vec<(&'a QReg,bool)>>{
    if j%2!=0 || c1&&j!=2{return Vec::new();}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let(polarity,terms)=super::metadata_muxlease::swap_terms(ts.iter().map(|t|t[2]==0).collect(),5);
    terms.into_iter().map(|m|{let mut cs=vec![(g,true),(t0,false)];if !c1{cs.push((&c[0],j==2));}cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],polarity>>i&1==0)));cs}).collect()
}
/// Replace the ordinary first-two-cell output with the mod4 carry seed.
/// Before correction target1=b1 XOR t1, carry=t1*target1 on this domain.
fn low_correction(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],source:&[QReg],target:&[QReg],carry:&QReg,special:&[Vec<(&QReg,bool)>],g:&QReg,dirty:&[QReg],j:usize,c1:bool,inverse:bool){
    let flip=|circ:&mut Circuit|{for term in special{let mut cs=term.clone();cs.push((&source[1],true));correction_gate(circ,&cs,&target[1],g,dirty);}};
    if inverse{flip(circ);}
    if super::metadata_muxlease::active("Q794_T10_POLISH") {
        // The three contributions per term sum to
        // `term * source[1] * (target[1] ^ target[257] ^ target[0])`. Park that
        // parity on target[1] and one gate per term replaces three. The special
        // terms never read target cells, so the frame cannot disturb a control.
        circ.cx(&target[257],&target[1]);circ.cx(&target[0],&target[1]);
        for term in special{let mut cs=term.clone();cs.extend([(&source[1],true),(&target[1],true)]);correction_gate(circ,&cs,carry,g,dirty);}
        circ.cx(&target[0],&target[1]);circ.cx(&target[257],&target[1]);
    } else {
    for term in special{for q in [&target[1],&target[257],&target[0]]{let mut cs=term.clone();cs.extend([(&source[1],true),(q,true)]);correction_gate(circ,&cs,carry,g,dirty);}}
    }
    // M256 forces S0 and logical v1=0. Its physical v1 can carry the
    // second phase passenger; cancel precisely that unwanted seed term.
    if !c1{
        if super::metadata_muxlease::active("Q794_T10_ENDPOINT_LOCAL"){
            // Only A254 parks a passenger at physical v1=target257.
            // General T10 has C!=1; A254 then forces C2/M256/S0/j0.
            // Other endpoints read their true v1=0 and need no cancellation.
            let support=circ.q797_a_support.unwrap_or((0,256));
            if j==0 && (support.0..support.1).contains(&254){
                for &(m,v) in programs::A_EQUAL[3]{
                    let mut cs=vec![(g,true),(&source[0],false),(&source[1],true),(&target[257],true)];
                    cs.extend(a.iter().enumerate().map(|(i,q)|(q,62>>i&1!=0)));
                    cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
                    correction_gate(circ,&cs,carry,g,dirty);
                }
            }
        }else{super::q794_t10_quotient::endpoint(circ,rank,a,c,&[(g,true),(&source[0],false),(&source[1],true),(&target[257],true)],carry,dirty);}
    }
    if !inverse{flip(circ);}
}

/// Only the paired W/center/W^-1 low-correction gates may drop g as a
/// control. On g1 the X(g) scratch is clean; on g0 this pure target-XOR
/// extension is undone literally. Do not use this for conditional SUM.
fn correction_gate(circ:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg,g:&QReg,dirty:&[QReg]){
    if !super::metadata_muxlease::active("Q794_T10_PAIRED_LOW"){
        super::q794_t10_quotient::gate(circ,controls,out,dirty);return;
    }
    let mut cs=Vec::new();let mut saw_guard=false;
    for &(q,v) in controls{
        assert_ne!(q.id(),out.id());
        if q.id()==g.id(){assert!(v);saw_guard=true;continue;}
        if let Some(&(_,old))=cs.iter().find(|&&(p,_):&&(&QReg,bool)|p.id()==q.id()){
            if old!=v{return;}
        }else{cs.push((q,v));}
    }
    assert!(saw_guard);circ.x(g);super::paired_clean_mcx::toggle(circ,&cs,out,g);circ.x(g);
}
