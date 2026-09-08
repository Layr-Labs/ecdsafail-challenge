//! Rank5 phase01 R with a globally clean leased guard and reused phase wires.
//! Work1[A] must be zero on all branches; Work2[A] must be zero only in phase01.
//! Guard: C0..255, S1..256, A_raw+C+S<=256; pre-shift data, entry metadata.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use super::metadata_arithmetic5;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn high(circ:&mut Circuit,rank:&[QReg],guard:&QReg,target:&QReg,helpers:&[QReg],axis:usize,h:isize){
    if !(0..4).contains(&h){return;}
    for &(m,v) in programs::EQUAL[if axis==0{h as usize}else{4+h as usize}]{let mut cs=vec![(guard,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,target,helpers);}
}
fn borrow_word(circ:&mut Circuit,rank:&[QReg],a:&[QReg],guard:Option<&QReg>,passenger:&QReg,word:&[QReg],helpers:&[QReg]) {
    if super::metadata_muxlease::active("Q799_MUX_LEASE"){super::metadata_muxlease::exchange(circ,rank,a,0,guard,passenger,&word[1..257].iter().collect::<Vec<_>>(),helpers,false);return;}
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..4 {for _echo in 0..2 {
        for &(m,v) in programs::EQUAL[h] {
            let mut cs=Vec::new();if let Some(g)=guard{cs.push((g,true));}cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,flag,dirty);
        }
        for lo in 0..64 {let target=&word[64*h+lo+1];let mut cs=vec![(flag,true),(passenger,true)];if let Some(g)=guard{cs.push((g,true));}cs.extend((0..6).map(|i|(&a[i],lo>>i&1!=0)));circ.cx(target,passenger);mixed_mcx(circ,&cs,target,dirty);circ.cx(target,passenger);}
    }}
}
fn phase_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,helpers:&[QReg]) {
    mixed_mcx(circ,&[(p1,false),(p2,true)],g,helpers);
    // Exclude raw A255, impossible for active coefficients and used by terminal coding.
    for &(m,v) in programs::EQUAL[3] {
        let mut cs=vec![(p1,false),(p2,true)];cs.extend(a.iter().map(|q|(q,true)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,helpers);
    }
}
#[derive(Clone)]
struct Scan<'a> {rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],mask:&'a QReg,guard:&'a QReg,hs:&'a QReg,ha:&'a QReg,helpers:&'a[QReg],j:usize,restore:Option<&'a QReg>,support_end:usize,upper_trim:usize,restore_positive:bool,role:Option<usize>}
impl Scan<'_> {
    fn cache(&self,circ:&mut Circuit,group:(isize,isize)) {
        high(circ,self.rank,self.guard,self.hs,self.helpers,2,group.0);
        if (0..=4).contains(&group.1) {metadata_arithmetic5::sum_flag(circ,self.rank,self.a,self.c,self.guard,self.ha,&self.helpers[0],&self.helpers[1..],group.1 as usize);}
    }
    fn cache_transition(&self,circ:&mut Circuit,from:(isize,isize),to:(isize,isize)){
        if from.0!=to.0{high(circ,self.rank,self.guard,self.hs,self.helpers,2,from.0);high(circ,self.rank,self.guard,self.hs,self.helpers,2,to.0);}
        if from.1!=to.1{metadata_arithmetic5::sum_flag_transition(circ,self.rank,self.a,self.c,self.guard,self.ha,&self.helpers[0],&self.helpers[1..],from.1,to.1);}
    }
    fn lo(&self,circ:&mut Circuit,i:usize,group:isize,data:&[&QReg],out:&QReg,enabled:bool) {
        self.lo_extra(circ,i,group,data,out,enabled,&[]);
    }
    fn lo_extra(&self,circ:&mut Circuit,i:usize,group:isize,data:&[&QReg],out:&QReg,enabled:bool,extra:&[(&QReg,bool)]) {
        if i>255||(i+1)%2!=self.j%2{return;}
        let value=(i+1)%256;let wanted=(value/64)as isize;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,2,group);high(circ,self.rank,self.guard,self.hs,self.helpers,2,wanted);}
        if super::metadata_muxlease::active("Q799_XOR_LO") {
            // c holds A+C. Undo only its low-bit XOR in a temporary basis;
            // old C0 is then one control, instead of two disjoint cubes.
            circ.cx(&self.a[0],&self.c[0]);
            let mut cs=vec![(self.guard,true),(self.hs,true),(&self.c[0],old_c0)];cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));cs.extend_from_slice(extra);if enabled{if let Some(s)=self.restore{cs.push((s,self.restore_positive));}}
            if super::metadata_muxlease::active("Q796_R01_CACHE")&&super::metadata_muxlease::active("Q796_R01_CLEAN")&&matches!(self.role,Some(0|2|5)){
                // These roles never compute or read HA. Its preceding loan
                // makes HA zero on guard=1 and arbitrary on guard=0.
                super::conditional_mcx::guarded(circ,self.guard,&cs[1..],out,self.ha,false,&self.helpers[0]);
            }else{mixed_mcx(circ,&cs,out,self.helpers);}
            circ.cx(&self.a[0],&self.c[0]);
        } else {for av in [false,true] {
            let mut cs=vec![(self.guard,true),(self.hs,true),(&self.a[0],av),(&self.c[0],av^old_c0)];cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));cs.extend_from_slice(extra);if enabled{if let Some(s)=self.restore{cs.push((s,self.restore_positive));}}mixed_mcx(circ,&cs,out,self.helpers);
        }}
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,2,wanted);high(circ,self.rank,self.guard,self.hs,self.helpers,2,group);}
    }
    fn top(&self,circ:&mut Circuit,i:usize,data:&[&QReg],out:&QReg,singleton:bool,enabled:bool) {
        // A_raw+C+S<=256 implies interval width>=2, so singleton is impossible.
        if i>256-self.upper_trim||singleton{return;}
        let value=256-self.upper_trim-i;let mut cs=vec![(self.guard,true),(self.ha,true)];cs.extend((0..6).map(|b|(&self.c[b],value>>b&1!=0)));
        cs.extend(data.iter().map(|&q|(q,true)));if enabled{if let Some(s)=self.restore{cs.push((s,self.restore_positive));}}
        mixed_mcx(circ,&cs,out,self.helpers);
    }
    fn lo_even(&self,circ:&mut Circuit,group:isize,v:&QReg,t:&QReg,out:&QReg,enabled:bool){
        self.lo_extra(circ,0,group,&[v],out,enabled,&[(t,false)]);
        // A0 means logical t=1 even when its head contains Q797 phase cargo.
        for &(m,val) in programs::EQUAL[0]{
            let mut extra=vec![(t,false)];extra.extend(self.a.iter().map(|q|(q,false)));
            extra.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],val>>i&1!=0)));
            self.lo_extra(circ,0,group,&[v],out,enabled,&extra);
        }
    }
    fn update(&self,circ:&mut Circuit,i:usize,group:isize) {
        self.lo(circ,i,group,&[],self.mask,false);self.top(circ,i,&[],self.mask,false,false);
    }
    fn data(&self,circ:&mut Circuit,qs:&[&QReg],out:&QReg) {
        let mut cs=vec![(self.guard,true),(self.mask,true)];cs.extend(qs.iter().map(|&q|(q,true)));if let Some(s)=self.restore {cs.push((s,self.restore_positive));}mixed_mcx(circ,&cs,out,self.helpers);
    }
    fn scan(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,role:usize,reverse:bool) {
        let mut scoped=self.clone();scoped.role=Some(role);
        scoped.scan_body(circ,source,target,sign,role,reverse);
    }
    fn scan_body(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,role:usize,reverse:bool) {
        let a:Vec<_>=source.iter().rev().collect();let b:Vec<_>=target.iter().rev().collect();let mut current=(-99isize,-99isize);
        for z in 0..self.support_end {let i=if reverse {self.support_end-1-z}else{z};let mut group=(if i<=255{(((i+1)%256)/64)as isize}else{-1},if i<=256-self.upper_trim{((256-self.upper_trim-i)/64)as isize}else{-1});
            if super::metadata_muxlease::active("Q796_R01_CACHE"){
                // Roles0/2/5 consume only lower-bound predicates. Role1
                // consumes only upper-bound predicates. Neither needs both.
                if matches!(role,0|2|5){group.1=-1;}if role==1{group.0=-1;}
            }
            if group!=current {if super::metadata_muxlease::active("Q796_DECODER_TRANSITION"){self.cache_transition(circ,current,group);}else{if current.0!=-99 {self.cache(circ,current);}self.cache(circ,group);}current=group;}
            let uses_mask=role==3||role==4;
            if uses_mask&&!reverse {self.update(circ,i,group.0);}
            match role {
                0=>if i==0&&super::q796_parity::enabled(){self.lo_even(circ,group.0,a[0],&target[0],&source[0],true);}else{self.lo(circ,i,group.0,&[a[i]],b[i],true);},
                1=>if let Some(s)=sign {self.top(circ,i,&[a[i]],s,false,true);self.top(circ,i,&[a[i]],s,true,true);},
                2=>if i+1<self.support_end {circ.cx(a[i],a[i+1]);self.lo(circ,i,group.0,&[a[i]],a[i+1],false);self.lo(circ,i+1,group.0,&[a[i]],a[i+1],false);},
                3=>{
                    if i+1<self.support_end {self.data(circ,&[a[i],if i==0&&super::q796_parity::enabled(){&source[0]}else{b[i]}],a[i+1]);}
                    if let Some(s)=sign {self.top(circ,i,&[a[i],b[i]],s,false,true);}
                },
                4=>if i+1<self.support_end {self.data(circ,&[a[i+1]],b[i+1]);self.data(circ,&[a[i],if i==0&&super::q796_parity::enabled(){&source[0]}else{b[i]}],a[i+1]);},
                5=>if i+1<self.support_end {self.lo(circ,i+1,group.0,&[a[i]],a[i+1],false);self.lo(circ,i,group.0,&[a[i]],a[i+1],false);circ.cx(a[i],a[i+1]);},
                _=>unreachable!(),
            }
            if uses_mask&&reverse {self.update(circ,i,group.0);}
        }
        self.cache(circ,current);
    }
    fn add(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,subtract:bool) {
        let start=circ.b.ops.len();
        for i in 259-self.support_end..259 {if i!=258||!super::q796_parity::enabled(){circ.cx(&source[i],&target[i]);}}
        if super::q796_parity::enabled(){high(circ,self.rank,self.guard,self.hs,self.helpers,2,0);self.lo_even(circ,0,&source[258],&target[0],&source[0],false);high(circ,self.rank,self.guard,self.hs,self.helpers,2,0);}
        self.scan(circ,source,target,sign,0,false);
        if sign.is_some() {self.scan(circ,source,target,sign,1,true);}
        self.scan(circ,source,target,sign,2,true);self.scan(circ,source,target,sign,3,false);self.scan(circ,source,target,sign,4,true);self.scan(circ,source,target,sign,5,false);
        if super::q796_parity::enabled(){high(circ,self.rank,self.guard,self.hs,self.helpers,2,0);self.lo_even(circ,0,&source[258],&target[0],&source[0],false);high(circ,self.rank,self.guard,self.hs,self.helpers,2,0);}
        for i in 259-self.support_end..259 {if i!=258||!super::q796_parity::enabled(){circ.cx(&source[i],&target[i]);}}
        if subtract {circ.b.ops[start..].reverse();}
    }
}
pub(super) fn phase01(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize){
    phase01_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j,259);
}
/// Caller proves phase01 interval upper endpoint257-A_raw-C<=support_end.
pub(super) fn phase01_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize){
    assert!((2..=259).contains(&support_end));let start=circ.b.ops.len();
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);
    let g=&helpers[0];let ha=&helpers[1];let dirty=&helpers[2..];
    // Work1[A] is globally zero at an arithmetic-block boundary. The lease
    // therefore yields a clean aggregate guard on all phase branches.
    borrow_word(circ,rank,a,None,g,w1,dirty);phase_guard(circ,rank,a,p1,p2,g,dirty);
    borrow_word(circ,rank,a,Some(g),ha,w2,dirty);circ.cx(g,p2);
    metadata_arithmetic5::add(circ,a,c,None,false);
    let mut scan=Scan{rank,a,c,sm,mask:p1,guard:g,hs:p2,ha,helpers:dirty,j,restore:None,support_end,upper_trim:0,restore_positive:false,role:None};
    scan.add(circ,w2,w1,Some(sign),true);circ.cx(g,sign);scan.restore=Some(sign);scan.add(circ,w2,w1,None,false);
    metadata_arithmetic5::add(circ,a,c,None,true);circ.cx(g,p2);
    borrow_word(circ,rank,a,Some(g),ha,w2,dirty);phase_guard(circ,rank,a,p1,p2,g,dirty);borrow_word(circ,rank,a,None,g,w1,dirty);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
/// Fused R01 and quotient insertion, storing the decision in the existing
/// high subtraction bit. Caller supplies a reachable pre-rotated R01 state.
pub(super) fn signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize) {
    assert!(helpers.len()>=23);let start=circ.b.ops.len();
    let g=&helpers[0];let ha=&helpers[1];let borrow=&helpers[2];let dirty=&helpers[3..];
    borrow_word(circ,rank,a,None,g,w1,dirty);phase_guard(circ,rank,a,p1,p2,g,dirty);
    borrow_word(circ,rank,a,Some(g),ha,w2,dirty);circ.cx(g,p2);
    metadata_arithmetic5::add(circ,a,c,None,false);
    let mut scan=Scan{rank,a,c,sm,mask:p1,guard:g,hs:p2,ha,helpers:dirty,j,restore:None,support_end,upper_trim:0,restore_positive:true,role:None};
    scan.add(circ,w2,w1,None,true);
    metadata_arithmetic5::add(circ,a,c,None,true);
    if super::metadata_muxlease::active("Q795_PHASE_LOAN"){super::q795_step::r01_correction(circ,rank,a,c,g,w1,w2,dirty);}
    super::metadata_muxlease::quotient(circ,rank,a,c,&[(g,true)],borrow,w1,dirty,true);
    metadata_arithmetic5::add(circ,a,c,None,false);
    scan.restore=Some(borrow);scan.upper_trim=1;scan.add(circ,w2,w1,None,false);
    metadata_arithmetic5::add(circ,a,c,None,true);
    circ.cx(g,borrow);
    super::metadata_muxlease::quotient(circ,rank,a,c,&[(g,true)],borrow,w1,dirty,true);
    circ.cx(g,p2);borrow_word(circ,rank,a,Some(g),ha,w2,dirty);
    phase_guard(circ,rank,a,p1,p2,g,dirty);borrow_word(circ,rank,a,None,g,w1,dirty);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let resource_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let support_end:usize=std::env::var("LOWQ_CODEC_SUPPORT_END").ok().map(|v|v.parse().unwrap()).unwrap_or(259);
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("R01.rank",5);let a=circ.alloc_qreg_bits("R01.a",6);let c=circ.alloc_qreg_bits("R01.c",6);let sm=circ.alloc_qreg_bits("R01.s25",4);assert_eq!(circ.b.next_qubit,21);
        let p1=circ.alloc_qreg("R01.p1");let p2=circ.alloc_qreg("R01.p2");let sign=circ.alloc_qreg("R01.sign");let w1=circ.alloc_qreg_bits("R01.w1",259);let w2=circ.alloc_qreg_bits("R01.w2",259);let helpers=circ.alloc_qreg_bits("R01.dirty",16);let owned=circ.b.next_qubit;
        phase01_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&helpers,j,support_end);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_R015_FUNDED_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned} support_end={support_end}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        if resource_only {continue;}
        for batch in 0..32*64*64*16*4/64 {
            let mut seed=0x14de2637c98ab50f^batch as u64^((j as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let al=k>>5&63;let cl=k>>11&63;let sl=k>>17&15;
                let (av,cv,raw_s)=if r<32 {(64*triples[r][0]+al,64*triples[r][1]+cl,64*triples[r][2]+4*sl+(((j>>1)^(cl&1))&1)*2+(j&1))}else{(0,0,0)};
                let sv=if raw_s==0 {256}else{raw_s};let mut phase=k>>21&3;if phase==1&&av<=254&&(av+cv+sv>256||av+cv+support_end<257){phase=3;}let on=phase==1&&av<=254;
                for i in 0..5 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6 {for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);put(w,&c[i],lane,cl>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&p1,lane,phase>>1&1!=0);put(w,&p2,lane,phase&1!=0);put(w,&w1[av+1],lane,false);}
                if on {
                    let address=av+1;let lo=sv-1;let hi=257-av-cv;assert!(lo<hi);if sv==256 {wraps+=1;}
                    for q in [&w1[address],&w2[address]] {put(&mut before,q,lane,false);put(&mut after,q,lane,false);}
                    let mut borrow=false;
                    for i in lo..hi {
                        let x=before[w2[258-i].id()as usize]>>lane&1!=0;let y=before[w1[258-i].id()as usize]>>lane&1!=0;
                        put(&mut after,&w1[258-i],lane,x^y^borrow);borrow=(!y&&(x||borrow))||(x&&borrow);
                    }
                    let sign_out=(before[sign.id()as usize]>>lane&1!=0)^borrow^true;put(&mut after,&sign,lane,sign_out);
                    if !sign_out {for i in lo..hi {put(&mut after,&w1[258-i],lane,before[w1[258-i].id()as usize]>>lane&1!=0);}}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after {let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("R01 j={j} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            if batch%8192==8191 {eprintln!("CODEC_R015_FUNDED_PROGRESS j={j} batches={}",batch+1);}
        }
        eprintln!("CODEC_R015_FUNDED_CLOCK j={j} PASS");
    }
    if resource_only {eprintln!("CODEC_R015_FUNDED_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_R015_FUNDED_PASS support_end={support_end} lanes={total} true_S256_lanes={wraps}; phase01 guard/mask/high S funded by global padding and phase bits; all branches restore; full Q799 missing");
}
