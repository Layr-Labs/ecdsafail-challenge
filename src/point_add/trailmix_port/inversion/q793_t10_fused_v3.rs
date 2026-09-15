//! V3 physically remapped mod4 arithmetic inside a funded Q793 chart expansion.
//! P1 is arbitrary: exact scalar extension equals the original arithmetic pair.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::Op;
#[path="metadata_arithmetic5_programs.rs"] mod programs;

fn top_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,carry:&QReg,source:&[QReg],dirty:&[QReg]) {
    let(root,gather)=super::q794_handoffs::gather_a(circ,rank,a,source,1,dirty);
    circ.cswap(g,root,carry);circ.b.ops.extend(gather.into_iter().rev());
}
struct Range<'a>{rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],group:isize,
    prefix:Vec<&'a QReg>,prefix_key:Vec<Vec<(u32,bool)>>,prefix_ops:Vec<Vec<Op>>}
impl Range<'_>{
    fn clear_prefix_from(&mut self,circ:&mut Circuit,depth:usize){
        // Children must clear before their parent's predicate changes.
        for ops in self.prefix_ops[depth..].iter().rev(){circ.b.ops.extend(ops.iter().rev().cloned());}
        self.prefix_ops.truncate(depth);self.prefix_key.truncate(depth);
    }
    fn clear_prefix(&mut self,circ:&mut Circuit){self.clear_prefix_from(circ,0);}
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
            if self.group!=h as isize{self.clear_prefix(circ);self.high(circ,self.group);self.high(circ,h as isize);self.group=h as isize;}
            cs.push((self.cache,true));
        }
        let left=lo.max(h*64);let right=hi.min((h+1)*64);
        for i in 0..6{if !factor||(left>>i)!=((right-1)>>i){cs.push((&self.a[i],value>>i&1!=0));}}
        // A three-rail C1 tree benefits from a one-literal leaf. The
        // single non-C1 prefix retains two low literals. No extra host.
        let leaf=if self.prefix.len()>1{1}else{2};
        if !self.prefix.is_empty()&&cs.len()>=leaf+3 {
            let low_ids:Vec<_>=cs.iter().skip(1).filter(|(q,_)|self.a.iter().any(|a|a.id()==q.id()))
                .take(leaf).map(|(q,_)|q.id()).collect();
            // Stable high-group cache first, then the highest A literals.
            // Each next node appends a faster-changing address bit.
            let mut high:Vec<_>=cs.iter().skip(1).filter(|(q,_)|!self.a.iter().any(|a|a.id()==q.id())).copied().collect();
            high.extend(cs.iter().skip(1).rev().filter(|(q,_)|self.a.iter().any(|a|a.id()==q.id())&&!low_ids.contains(&q.id())).copied());
            if high.len()>=2 {
                let depth=self.prefix.len().min(high.len()-1);let root=high.len()-depth+1;
                for level in 0..depth {
                    let terms=if level==0{high[..root].to_vec()}else{vec![(self.prefix[level-1],true),high[root+level-1]]};
                    let key:Vec<_>=terms.iter().map(|(q,v)|(q.id(),*v)).collect();
                    if self.prefix_key.get(level)!=Some(&key) {
                        self.clear_prefix_from(circ,level);
                        let at=circ.b.ops.len();circ.x(self.g);
                        super::paired_clean_mcx::toggle(circ,&terms,self.prefix[level],self.g);circ.x(self.g);
                        self.prefix_ops.push(circ.b.ops[at..].to_vec());self.prefix_key.push(key);
                    }
                }
                self.clear_prefix_from(circ,depth);
                cs.retain(|(q,_)|q.id()==self.g.id()||low_ids.contains(&q.id()));
                cs.insert(1,(self.prefix[depth-1],true));
            }
        }
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
pub(super) fn add_and_clear(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],a:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,p1:&QReg,helpers:&[QReg],n:usize,c:&[QReg],sm:&[QReg],j:usize,c1:bool,low:bool){
    let n=n.min(if low{256}else{254});
    assert!((2..=256).contains(&n));assert!(helpers.len()>=17);
    let carry=&helpers[0];let dirty=&helpers[1..];let start=circ.b.ops.len();
    let a18=std::env::var("Q793_A18").ok().as_deref()==Some("1");
    // A37: on the last branch this slot is the original C0=1. The routine
    // emits in reverse, so these reads precede its first write to that slot.
    let c1_p1=c1&&super::metadata_muxlease::active("Q793_T10_C1_P1");
    // A38: the mask has not crossed any admitted A address for i<=lo.
    // Keep g on the SUM; its off-guard identity is required by the carry frame.
    let known_end=if super::metadata_muxlease::active("Q793_T10_SUM_MASK") {
        circ.q797_a_support.map(|(lo,_)|lo+1).unwrap_or(1).min(n)
    }else{0};
    assert!(!a18||(!c1_p1&&known_end==0),"A18 is not part of the Codex stack");
    let special=if low{special_terms(rank,c,sm,g,&source[0],j,c1)}else{Vec::new()};
    assert!(helpers.iter().all(|q|q.id()!=p1.id()&&q.id()!=g.id()&&q.id()!=cache.id()&&q.id()!=mask.id()));
    // Source[A+1] is zero on g after move_t10, distinct from the quotient
    // address funding mask. Carry starts0: NO source complement or carry^=g.
    top_loan(circ,rank,a,g,carry,source,dirty);circ.cx(g,mask);
    let prefix_free=super::metadata_muxlease::active("Q793_T10_PREFIX_FREE");
    assert!(!prefix_free||!super::metadata_muxlease::active("Q793_A19_SM0"),"SM0 is excluded from prefix funding");
    // On the C1 guard, original C3/C4/C5=0 and the chart restores them. On
    // non-C1, P2 is a clean unused high cache only for a single high group.
    // No SM0 or arithmetic helper is held. These rails can be arbitrary off g.
    let support=if std::env::var("Q796_PREFIX_SUPPORT").ok().as_deref()==Some("0"){(0,256)}else{circ.q797_a_support.unwrap_or((0,256))};
    let factor=std::env::var("Q796_PREFIX_FACTORS").ok().as_deref()!=Some("0");
    let prefix=if prefix_free&&super::metadata_muxlease::active("Q795_T10_TOP_MASK_CLEAN") {
        if c1{
            if super::metadata_muxlease::active("Q793_T10_PREFIX_TREE") {
                assert!(c.len()>5);vec![&c[5],&c[4],&c[3]]
            }else{assert!(c.len()>3);vec![&c[3]]}
        }else if factor&&support.0/64==(support.1-1)/64{vec![cache]}else{Vec::new()}
    }else{Vec::new()};
    assert!(prefix.iter().enumerate().all(|(i,p)|prefix[..i].iter().all(|q|q.id()!=p.id())));
    for &host in &prefix {
        assert!([g,mask,p1].iter().all(|q|q.id()!=host.id()));
        assert!(helpers.iter().chain(rank).chain(a).chain(source).chain(target).all(|q|q.id()!=host.id()));
        assert!(c1||host.id()==cache.id());
    }
    let mut range=Range{rank,a,g,cache,mask,dirty,group:-1,prefix,prefix_key:Vec::new(),prefix_ops:Vec::new()};let mut updates=Vec::new();
    for i in 0..n{
        let at=circ.b.ops.len();if i>0{range.equality(circ,i-1);}updates.push(circ.b.ops[at..].to_vec());
        cell(circ,&source[i],&target[i],carry,mask,g,false);
        if i==1{low_correction(circ,rank,a,c,source,target,carry,&special,g,dirty,j,c1,false);}
    }
    // Clear before either gather or any center work. Restoring this exact
    // producer before the cell inverse resumes the recorded decoder state.
    let center_prefix:Vec<_>=range.prefix_ops.iter().flat_map(|ops|ops.iter().cloned()).collect();range.clear_prefix(circ);
    let(target_top,target_gather)=super::q794_handoffs::gather_a(circ,rank,a,target,1,dirty);
    let(source_top,source_gather)=super::q794_handoffs::gather_a(circ,rank,a,source,1,dirty);
    // At masked-off top s'=passenger XOR b, t'=old_top XOR passenger.
    // Full borrow=b*(s' XOR t'). XOR threshold into ARBITRARY incoming P1.
    // W and both gathers exclude P1, including every dirty lender.
    circ.cx(g,p1);
    if super::metadata_muxlease::active("Q794_T10_POLISH") {
        // The pair is g*carry*(source_top XOR target_top).  Park that parity
        // on target_top, apply one toggle, then close the affine frame before
        // either gather is unwound.
        circ.cx(source_top,target_top);
        mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
        circ.cx(source_top,target_top);
    } else {
        mixed_mcx(circ,&[(g,true),(carry,true),(source_top,true)],p1,dirty);
        mixed_mcx(circ,&[(g,true),(carry,true),(target_top,true)],p1,dirty);
    }
    circ.b.ops.extend(source_gather.into_iter().rev());
    let mut top_controls=vec![(g,true)];
    if !c1_p1{top_controls.push((p1,true));}
    top_controls.push((carry,true));
    mixed_mcx(circ,&top_controls,target_top,dirty);
    circ.b.ops.extend(target_gather.into_iter().rev());
    circ.b.ops.extend(center_prefix);
    for i in (0..n).rev(){
        // Top changes cannot alter carry undo: its active mask is0. Retain
        // ALL masked-off CNOTs, including passenger and extra tail cells.
        if i==1{low_correction(circ,rank,a,c,source,target,carry,&special,g,dirty,j,c1,true);}
        cell(circ,&source[i],&target[i],carry,mask,g,true);
        circ.cx(carry,&source[i]);
        // A18: share P=mask∧source[i] in helpers[1]. cell() MUST NOT be touched
        // (off-g palindrome). Two bare CCXs sandwich a 3-control sum; exact for
        // arbitrary g and arbitrary helper B. Q793_A18=0 restores the 4-control.
        if a18 {
            let helper=&helpers[1];
            let dirty_a18=&helpers[2..];
            circ.ccx(mask,&source[i],helper);
            mixed_mcx(circ,&[(g,true),(p1,true),(helper,true)],&target[i],dirty_a18);
            circ.ccx(mask,&source[i],helper);
        } else {
            if c1_p1&&i>=known_end&&super::metadata_muxlease::active("Q793_T10_C1_SUM_LOAN") {
                // A37 already establishes incoming C0=P1=1 at these reads.
                // Borrow its complement for this one SUM, then restore it.
                // Off g the center is identity for arbitrary P1 and data.
                circ.x(p1);circ.ccx(mask,&source[i],p1);
                circ.ccx(g,p1,&target[i]);
                circ.ccx(mask,&source[i],p1);circ.x(p1);
            }else if !c1_p1&&i<known_end&&super::metadata_muxlease::active("Q793_T10_MASK_SUM_LOAN") {
                // A38 establishes mask=1 on g before the first A address.
                // Use its complement for a three-control SUM, then restore.
                // The g0 action is identity even if mask starts arbitrary.
                circ.x(mask);circ.ccx(&source[i],p1,mask);
                circ.ccx(g,mask,&target[i]);
                circ.ccx(&source[i],p1,mask);circ.x(mask);
            }else{
                let mut sum_controls=vec![(g,true)];
                if i>=known_end{sum_controls.push((mask,true));}
                sum_controls.push((&source[i],true));
                if !c1_p1{sum_controls.push((p1,true));}
                mixed_mcx(circ,&sum_controls,&target[i],dirty);
            }
        }
        if i==1{for term in &special{let mut cs=term.clone();cs.extend([(mask,true),(&source[1],true),(p1,true)]);super::q794_t10_quotient::gate(circ,&cs,&target[1],dirty);}}
        circ.cx(carry,&source[i]);circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
    }
    assert!(updates.is_empty());circ.cx(g,mask);top_loan(circ,rank,a,g,carry,source,dirty);
    circ.b.ops[start..].reverse();
}


fn special_terms<'a>(rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,t0:&'a QReg,j:usize,c1:bool)->Vec<Vec<(&'a QReg,bool)>>{
    if j%2!=0 || c1&&j!=2{return Vec::new();}
    // The surrounding held guard already proves original S<=2. SM1/2
    // hold endpoint flags and SM3 is the expanded physical tail rail.
    // C0 is mutable on C1, whose clock2 alone specifies S0.
    let _=(rank,sm);let mut cs=vec![(g,true),(t0,false)];
    if !c1{cs.push((&c[0],j==2));}vec![cs]
}
/// Replace the ordinary first-two-cell output with the mod4 carry seed.
/// Before correction target1=b1 XOR t1, carry=t1*target1 on this domain.
fn low_correction(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],source:&[QReg],target:&[QReg],carry:&QReg,special:&[Vec<(&QReg,bool)>],g:&QReg,dirty:&[QReg],j:usize,c1:bool,inverse:bool){
    let flip=|circ:&mut Circuit|{for term in special{let mut cs=term.clone();cs.push((&source[1],true));correction_gate(circ,&cs,&target[1],g,dirty);}};
    if inverse{flip(circ);}
    if super::metadata_muxlease::active("Q794_T10_POLISH") {
        // The three target contributions are one parity.  The special terms
        // do not read target cells, so this affine frame is exact and local.
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
