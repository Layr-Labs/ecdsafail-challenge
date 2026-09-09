//! Own Q794 two-hole dynamic R00 comparator; not yet wired to the whole step.
//! Rank5 phase00 R arithmetic using the existing zero C_low metadata field.
//! Guard implies C0 and S mod4=j. All C_low bits restore before phase updates.
//! Work registers and external helpers may contain arbitrary data.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::conditional_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn cache_clean_mode()->usize{static MODE:std::sync::OnceLock<usize>=std::sync::OnceLock::new();*MODE.get_or_init(||{let n=std::env::var("Q795_R00_CACHE_CLEAN").ok().map(|v|v.parse().unwrap()).unwrap_or(0);assert!(n<=2);n})}
// A closed cache lifetime permits a dirty off-domain target-toggle extension.
// On phase00 scratch is zero; otherwise this map still restores all controls
// and lenders, and an identical call uncomputes its arbitrary cached value.
fn cache_clean_toggle(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,scratch:&QReg,helpers:&[QReg]) {
    assert!((3..=7).contains(&cs.len()));
    for &(q,v) in cs{if !v{circ.x(q);}}
    circ.ccx(cs[0].0,cs[1].0,scratch);
    let rest:Vec<_>=std::iter::once((scratch,true)).chain(cs[2..].iter().map(|&(q,_)|(q,true))).collect();
    super::length_recompute::mixed_mcx(circ,&rest,out,helpers);
    circ.ccx(cs[0].0,cs[1].0,scratch);
    for &(q,v) in cs.iter().rev(){if !v{circ.x(q);}}
}
fn clean_gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,guard:&QReg,scratch:&QReg,helpers:&[QReg]) {
    assert!(cs.iter().any(|(q,v)|q.id()==guard.id()&&*v));
    let others:Vec<_>=cs.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();
    conditional_mcx::guarded(circ,guard,&others,out,scratch,false,&helpers[0]);
}
fn high(circ:&mut Circuit,rank:&[QReg],guard:&QReg,target:&QReg,helpers:&[QReg],scratch:&QReg,axis:usize,h:isize) {
    if !(0..4).contains(&h){return;}
    for &(m,v) in programs::EQUAL[if axis==0{h as usize}else{4+h as usize}] {
        let k=m.count_ones();let guarded_t=match k{0=>0,1=>1,2=>4,_=>2*k};let plain_t=match k{0|1=>0,2=>1,_=>4*k-8};
        if cache_clean_mode()==2&&matches!(k,3|4){
            let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
            cache_clean_toggle(circ,&cs,target,scratch,helpers);continue;
        }
        let unguarded=super::metadata_muxlease::active("Q795_DECODER_UNGUARDED")&&plain_t<guarded_t;
        let mut cs=if unguarded{Vec::new()}else{vec![(guard,true)]};cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        if unguarded{super::length_recompute::mixed_mcx(circ,&cs,target,helpers);}else{clean_gate(circ,&cs,target,guard,scratch,helpers);}
    }
}
struct Scan<'a> {rank:&'a[QReg],a:&'a[QReg],sm:&'a[QReg],mask:&'a QReg,guard:&'a QReg,hs:&'a QReg,ha:&'a QReg,helpers:&'a[QReg],output:&'a QReg,output_control:&'a QReg,scratch:&'a QReg,j:usize,support_end:usize,low_cache:&'a QReg,top_cache:&'a QReg,low_value:std::cell::Cell<Option<usize>>,top_value:std::cell::Cell<Option<usize>>,compare:bool}
impl Scan<'_> {
    fn lower_bits(&self)->usize{static BITS:std::sync::OnceLock<usize>=std::sync::OnceLock::new();*BITS.get_or_init(||{let n=std::env::var("Q795_R00_LOWER_BITS").ok().map(|v|v.parse().unwrap()).unwrap_or(2);assert!((2..=4).contains(&n));n})}
    fn upper_bits(&self)->usize{static BITS:std::sync::OnceLock<usize>=std::sync::OnceLock::new();*BITS.get_or_init(||{let n=std::env::var("Q795_R00_UPPER_BITS").ok().map(|v|v.parse().unwrap()).unwrap_or(3);assert!((2..=6).contains(&n));n})}
    fn prefix_mode(&self)->usize{if self.compare{return 2;}static MODE:std::sync::OnceLock<usize>=std::sync::OnceLock::new();*MODE.get_or_init(||{let n=std::env::var("Q795_R00_PREFIX").ok().map(|v|v.parse().unwrap()).unwrap_or(0);assert!(n<=3);n})}
    fn prefix_toggle(&self,circ:&mut Circuit,upper:bool,value:usize){
        let mut cs=vec![(self.guard,true),(if upper{self.ha}else{self.hs},true)];
        if upper{let n=self.upper_bits();cs.extend((0..n).map(|i|(&self.a[6-n+i],value>>i&1!=0)));}
        else{let n=self.lower_bits();cs.extend((0..n).map(|i|(&self.sm[4-n+i],value>>i&1!=0)));}
        if cache_clean_mode()!=0 {
            cache_clean_toggle(circ,&cs[1..],if upper{self.top_cache}else{self.low_cache},self.scratch,self.helpers);
        } else if !upper&&super::metadata_muxlease::active("Q795_DECODER_UNGUARDED") {
            super::length_recompute::mixed_mcx(circ,&cs[1..],self.low_cache,self.helpers);
        } else {clean_gate(circ,&cs,if upper{self.top_cache}else{self.low_cache},self.guard,self.scratch,self.helpers);}
    }
    fn prefix_clear(&self,circ:&mut Circuit,upper:bool){if let Some(v)=if upper{self.top_value.take()}else{self.low_value.take()}{self.prefix_toggle(circ,upper,v);}}
    fn prefix_select(&self,circ:&mut Circuit,upper:bool,value:usize){
        let slot=if upper{&self.top_value}else{&self.low_value};if slot.get()==Some(value){return;}
        if cache_clean_mode()!=0&&super::metadata_muxlease::active("Q795_R00_PREFIX_TRANSITION")&&slot.get().is_some_and(|old|old^value==1){
            // Our one-scratch producer is (scratch XOR high*key_bit0)*rest.
            // Flipping key_bit0 cancels the arbitrary scratch term exactly;
            // the transition is high*rest, with no conditional-clean premise.
            let mut cs=vec![(if upper{self.ha}else{self.hs},true)];
            if upper{let n=self.upper_bits();cs.extend((1..n).map(|i|(&self.a[6-n+i],value>>i&1!=0)));}
            else{let n=self.lower_bits();cs.extend((1..n).map(|i|(&self.sm[4-n+i],value>>i&1!=0)));}
            super::length_recompute::mixed_mcx(circ,&cs,if upper{self.top_cache}else{self.low_cache},self.helpers);
        }else{self.prefix_clear(circ,upper);self.prefix_toggle(circ,upper,value);}
        slot.set(Some(value));
    }
    fn gate(&self,circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg) {
        if out.id()==self.output.id() {
            let others:Vec<_>=cs.iter().copied().filter(|(q,_)|q.id()!=self.guard.id()).collect();
            super::conditional_pair::guarded_pair(circ,self.guard,(self.output_control,false),&others,out,self.scratch,false,self.helpers);
        } else {
            let others:Vec<_>=cs.iter().copied().filter(|(q,_)|q.id()!=self.guard.id()).collect();
            if self.compare {
                // Comparator mask production is inside literal W / W^-1.
                // Its sole external center guard permits arbitrary off-domain
                // target-XOR extensions, including these restored C3 loans.
                super::paired_clean_mcx::toggle(circ,&others,out,self.scratch);return;
            }
            let k=others.len();let guarded_t=match k{0=>0,1=>1,2=>4,_=>2*k};let plain_t=match k{0|1=>0,2=>1,_=>4*k-8};
            // Only paired DATA actions lose this guard. Mask updates retain
            // it, and Sign remains target-only with both phase guards explicit.
            // Outside phase00 the two non-Sign maps are inverse extensions;
            // their decoder and scratch lifetimes restore at every boundary.
            let paired=out.id()!=self.mask.id()&&super::metadata_muxlease::active("Q795_R00_PAIR_UNGUARDED");
            let extension_t=if k<2{0}else{2*k-3};
            if paired&&super::metadata_muxlease::active("Q795_R00_DATA_CLEAN_EXTENSION")&&extension_t<plain_t.min(guarded_t) {
                // C3 is zero on phase00. Off phase, this pure target-XOR
                // extension restores C3/controls; its paired inverse sees the
                // identical C3/lower-cache inputs. Mask and Sign stay guarded.
                super::paired_clean_mcx::toggle(circ,&others,out,self.scratch);
            } else if paired&&plain_t<guarded_t {
                super::length_recompute::mixed_mcx(circ,&others,out,self.helpers);
            } else {clean_gate(circ,cs,out,self.guard,self.scratch,self.helpers);}
        }
    }
    fn cache(&self,circ:&mut Circuit,group:isize,role:usize) {
        high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);
        if !(super::metadata_muxlease::active("Q796_R00_CACHE")&&matches!(role,0|2|5)){
            high(circ,self.rank,self.guard,self.ha,self.helpers,self.scratch,0,3-group);
        }
    }
    fn lo(&self,circ:&mut Circuit,i:usize,group:isize,data:&[&QReg],out:&QReg) {
        if i==0||i>256||(i-1)%4!=self.j {return;}
        let value=i-1;let wanted=(value/64)as isize;
        if wanted!=group {self.prefix_clear(circ,false);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,wanted);}
        let cached=matches!(self.prefix_mode(),1|2);if cached{self.prefix_select(circ,false,(value&63)>>(6-self.lower_bits()));}
        let mut cs=vec![(self.guard,true),(if cached{self.low_cache}else{self.hs},true)];cs.extend((0..if cached{4-self.lower_bits()}else{4}).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));self.gate(circ,&cs,out);
        if wanted!=group {self.prefix_clear(circ,false);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,wanted);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);}
    }
    fn top(&self,circ:&mut Circuit,i:usize,data:&[&QReg],out:&QReg,singleton:bool) {
        if i==0||i>256 {return;}
        let value=256-i;
        if super::metadata_muxlease::active("Q796_R00_SUPPORT"){if let Some((lo,hi))=circ.q797_a_support{if value<lo||value>=hi{return;}}}
        let cached=matches!(self.prefix_mode(),1|3);if cached{self.prefix_select(circ,true,(value&63)>>(6-self.upper_bits()));}
        let mut cs=vec![(self.guard,true),(if cached{self.top_cache}else{self.ha},true)];cs.extend((0..if cached{6-self.upper_bits()}else{6}).map(|b|(&self.a[b],value>>b&1!=0)));
        if singleton {
            if (i-1)%4!=self.j {return;}
            cs.push((self.hs,true));cs.extend((0..4).map(|b|(&self.sm[b],(i-1)>>(b+2)&1!=0)));
        }
        cs.extend(data.iter().map(|&q|(q,true)));self.gate(circ,&cs,out);
    }
    fn update(&self,circ:&mut Circuit,i:usize,group:isize) {
        self.lo(circ,i,group,&[],self.mask);self.top(circ,i,&[],self.mask,false);
    }
    fn scan(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,role:usize,reverse:bool) {
        let a:Vec<_>=source.iter().rev().collect();let b:Vec<_>=target.iter().rev().collect();let mut current=-99isize;
        for z in 0..self.support_end {let i=if reverse {self.support_end-1-z}else{z};let group=if i==0 {-1}else{((i-1)/64)as isize};
            if group!=current {self.prefix_clear(circ,false);self.prefix_clear(circ,true);if current!=-99 {self.cache(circ,current,role);}self.cache(circ,group,role);current=group;}
            let uses_mask=role==3||role==4;
            if uses_mask&&!reverse {self.update(circ,i,group);}
            match role {
                0=>self.lo(circ,i,group,&[a[i]],b[i]),
                1=>if let Some(s)=sign {self.top(circ,i,&[a[i]],s,false);self.top(circ,i,&[a[i]],s,true);},
                2=>if i+1<self.support_end {circ.cx(a[i],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);self.lo(circ,i+1,group,&[a[i]],a[i+1]);},
                3=>{
                    if i+1<self.support_end && !(i==0&&super::q796_parity::enabled()) {self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1]);}
                    if let Some(s)=sign {self.top(circ,i,&[a[i],b[i]],s,false);}
                },
                4=>if i+1<self.support_end {
                    self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i+1],true)],b[i+1]);
                    if !(i==0&&super::q796_parity::enabled()){self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1]);}
                },
                5=>if i+1<self.support_end {self.lo(circ,i+1,group,&[a[i]],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);circ.cx(a[i],a[i+1]);},
                _=>unreachable!(),
            }
            if uses_mask&&reverse {self.update(circ,i,group);}
        }
        self.prefix_clear(circ,false);self.prefix_clear(circ,true);self.cache(circ,current,role);
    }
    fn compare(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],carry:&QReg) {
        assert!(self.compare);assert_eq!(self.prefix_mode(),2);
        // The center is the only Sign write. W never changes its two external
        // controls, so W / guarded center / W^-1 is identity off phase00 even
        // for arbitrary metadata, cache, carry and scratch inputs.
        let start=circ.b.ops.len();let mut sh=-99isize;let mut ah=-99isize;
        // i=0 is always below S+1 and is the physically omitted Work1[258]
        // parity rail. Its active carry is initially0; omit the entire cell.
        for i in 1..self.support_end {
            let next_s=if i==0{-1}else{((i-1)/64)as isize};
            let next_a=if (2..=257).contains(&i){((257-i)/64)as isize}else{-1};
            if next_s!=sh {
                self.prefix_clear(circ,false);
                high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,sh);
                high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,next_s);sh=next_s;
            }
            if next_a!=ah {
                high(circ,self.rank,self.guard,self.ha,self.helpers,self.scratch,0,ah);
                high(circ,self.rank,self.guard,self.ha,self.helpers,self.scratch,0,next_a);ah=next_a;
            }
            self.lo(circ,i,sh,&[],self.mask);
            // Include upper boundary bit i=256-A; toggle mask one bit later.
            if i>0 {self.top(circ,i-1,&[],self.mask,false);}
            if i == 1 {
                super::q794_r00_seed::emit(circ, self.rank, self.a, source, target, self.mask, carry, self.helpers, self.j);
                continue;
            }
            let x=&target[258-i];let y=&source[258-i];
            // Only the carry update needs the interval mask: all DATA is
            // restored by W^-1. On an active bit x=t XOR s, y=s XOR carry.
            circ.cx(y,x);circ.cx(carry,y);
            super::paired_clean_mcx::toggle(circ,&[(self.mask,true),(x,true),(y,true)],carry,self.scratch);
        }
        self.prefix_clear(circ,false);
        high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,sh);
        high(circ,self.rank,self.guard,self.ha,self.helpers,self.scratch,0,ah);
        let compute=circ.b.ops[start..].to_vec();
        super::length_recompute::mixed_mcx(circ,&[(self.guard,true),(self.output_control,false),(carry,true)],self.output,self.helpers);
        circ.b.ops.extend(compute.into_iter().rev());
    }
    fn upper_loan(&self,circ:&mut Circuit,source:&[QReg]) {
        // C2 is zero on active R00 and unused by the lower-only decoder.
        let(root,route)=super::q798_handoffs::gather_a(circ,self.rank,self.a,source,1,self.helpers);
        circ.cswap(self.guard,root,self.ha);circ.b.ops.extend(route.into_iter().rev());
    }
    fn compare_partial_maj(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],seed:&QReg) {
        assert!(self.compare);assert_eq!(self.prefix_mode(),2);
        self.upper_loan(circ,source);
        let start=circ.b.ops.len();let mut sh=-99isize;
        // Two virtual residual cells: bit0 has borrow0; q794_r00_seed computes
        // the exact borrow into bit2 from the unchanged modulo4 chart. Keep
        // source257 intact: it remains chart DATA, not a MAJ history rail.
        for i in 1..self.support_end {
            let next_s=((i-1)/64)as isize;
            if next_s!=sh {
                self.prefix_clear(circ,false);
                high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,sh);
                high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,next_s);sh=next_s;
            }
            self.lo(circ,i,sh,&[],self.mask);
            if i==1 {
                super::q794_r00_seed::emit(circ,self.rank,self.a,source,target,self.mask,seed,self.helpers,self.j);
                continue;
            }
            let a=&source[258-i];let b=&target[258-i];let prev=if i==2{seed}else{&source[259-i]};
            circ.cx(a,b);circ.cx(a,prev);circ.cx(prev,a);
            super::paired_clean_mcx::toggle(circ,&[(self.mask,true),(prev,true),(b,true)],a,self.scratch);
        }
        self.prefix_clear(circ,false);
        high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,sh);
        let compute=circ.b.ops[start..].to_vec();
        // Nonterminal A<=254 implies U=257-A>=3. The desired carry_U lives
        // at source[A+2], XOR source[A+1] if the next cell was emitted. That
        // latter rail was loaned to C2 and is zero on the active branch.
        let(root,route)=super::q798_handoffs::gather_a(circ,self.rank,self.a,source,2,self.helpers);
        super::length_recompute::mixed_mcx(circ,&[(self.guard,true),(self.output_control,false),(root,true)],self.output,self.helpers);
        circ.b.ops.extend(route.into_iter().rev());circ.b.ops.extend(compute.into_iter().rev());
        self.upper_loan(circ,source);
    }
    fn add(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,subtract:bool) {
        let start=circ.b.ops.len();
        for i in 259-self.support_end..259 {if i!=258||!super::q796_parity::enabled(){circ.cx(&source[i],&target[i]);}}
        self.scan(circ,source,target,sign,0,false);
        if sign.is_some() {self.scan(circ,source,target,sign,1,true);}
        self.scan(circ,source,target,sign,2,true);
        self.scan(circ,source,target,sign,3,false);
        self.scan(circ,source,target,sign,4,true);
        self.scan(circ,source,target,sign,5,false);
        for i in 259-self.support_end..259 {if i!=258||!super::q796_parity::enabled(){circ.cx(&source[i],&target[i]);}}
        // Every primitive here is self-inverse; literal reversal implements subtraction.
        if subtract {circ.b.ops[start..].reverse();}
    }
}
pub(super) fn phase00(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize) {
    phase00_with_support(circ,rank,a,c,sm,guard,p2,sign,w1,w2,helpers,j,259);
}
/// Caller proves interval upper endpoint257-A_raw<=support_end.
pub(super) fn phase00_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize) {
    assert!((2..=259).contains(&support_end));let start=circ.b.ops.len();
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    let terminal:Vec<_>=(0..5).map(|i|(&rank[i],29>>i&1!=0)).chain(a.iter().map(|q|(q,true))).collect();
    super::length_recompute::mixed_mcx(circ,&terminal,guard,helpers);circ.x(guard);
    let compare=true; // This new two-hole component implements the direct comparator only.
    let scan=Scan{rank,a,sm,output:sign,output_control:p2,mask:&c[0],guard,hs:&c[1],ha:&c[2],scratch:&c[3],helpers,j,support_end,low_cache:&c[4],top_cache:&c[5],low_value:std::cell::Cell::new(None),top_value:std::cell::Cell::new(None),compare};
    if super::metadata_muxlease::active("Q794_R00_PARTIAL_MAJ") {scan.compare_partial_maj(circ,w2,w1,&c[5]);}
    else if compare {scan.compare(circ,w2,w1,&c[5]);}
    else {scan.add(circ,w2,w1,Some(sign),true);scan.add(circ,w2,w1,None,false);}
    circ.x(guard);super::length_recompute::mixed_mcx(circ,&terminal,guard,helpers);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
