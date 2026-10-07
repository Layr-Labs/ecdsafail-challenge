//! Rank5 phase00 R arithmetic using the existing zero C_low metadata field.
//! Guard implies C0 and S mod4=j. All C_low bits restore before phase updates.
//! Work registers and external helpers may contain arbitrary data.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::conditional_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn clean_gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,guard:&QReg,scratch:&QReg,helpers:&[QReg]) {
    assert!(cs.iter().any(|(q,v)|q.id()==guard.id()&&*v));
    let others:Vec<_>=cs.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();
    conditional_mcx::guarded(circ,guard,&others,out,scratch,false,&helpers[0]);
}
fn high(circ:&mut Circuit,rank:&[QReg],guard:&QReg,target:&QReg,helpers:&[QReg],scratch:&QReg,axis:usize,h:isize) {
    if !(0..4).contains(&h){return;}
    for &(m,v) in programs::EQUAL[if axis==0{h as usize}else{4+h as usize}] {
        let mut cs=vec![(guard,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));clean_gate(circ,&cs,target,guard,scratch,helpers);
    }
}
struct Scan<'a> {rank:&'a[QReg],a:&'a[QReg],sm:&'a[QReg],mask:&'a QReg,guard:&'a QReg,hs:&'a QReg,ha:&'a QReg,helpers:&'a[QReg],scratch:&'a QReg,j:usize,support_end:usize}
impl Scan<'_> {
    fn gate(&self,circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg) {clean_gate(circ,cs,out,self.guard,self.scratch,self.helpers);}
    fn cache(&self,circ:&mut Circuit,group:isize) {
        high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);
        high(circ,self.rank,self.guard,self.ha,self.helpers,self.scratch,0,3-group);
    }
    fn lo(&self,circ:&mut Circuit,i:usize,group:isize,data:&[&QReg],out:&QReg) {
        if i==0||i>256||(i-1)%4!=self.j {return;}
        let value=i-1;let wanted=(value/64)as isize;
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,wanted);}
        let mut cs=vec![(self.guard,true),(self.hs,true)];cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));self.gate(circ,&cs,out);
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,wanted);high(circ,self.rank,self.guard,self.hs,self.helpers,self.scratch,2,group);}
    }
    fn top(&self,circ:&mut Circuit,i:usize,data:&[&QReg],out:&QReg,singleton:bool) {
        if i==0||i>256 {return;}
        let value=256-i;let mut cs=vec![(self.guard,true),(self.ha,true)];cs.extend((0..6).map(|b|(&self.a[b],value>>b&1!=0)));
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
            if group!=current {if current!=-99 {self.cache(circ,current);}self.cache(circ,group);current=group;}
            let uses_mask=role==3||role==4;
            if uses_mask&&!reverse {self.update(circ,i,group);}
            match role {
                0=>self.lo(circ,i,group,&[a[i]],b[i]),
                1=>if let Some(s)=sign {self.top(circ,i,&[a[i]],s,false);self.top(circ,i,&[a[i]],s,true);},
                2=>if i+1<self.support_end {circ.cx(a[i],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);self.lo(circ,i+1,group,&[a[i]],a[i+1]);},
                3=>{
                    if i+1<self.support_end {self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1]);}
                    if let Some(s)=sign {self.top(circ,i,&[a[i],b[i]],s,false);}
                },
                4=>if i+1<self.support_end {
                    self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i+1],true)],b[i+1]);
                    self.gate(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1]);
                },
                5=>if i+1<self.support_end {self.lo(circ,i+1,group,&[a[i]],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);circ.cx(a[i],a[i+1]);},
                _=>unreachable!(),
            }
            if uses_mask&&reverse {self.update(circ,i,group);}
        }
        self.cache(circ,current);
    }
    fn add(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,subtract:bool) {
        let start=circ.b.ops.len();
        for i in 259-self.support_end..259 {circ.cx(&source[i],&target[i]);}
        self.scan(circ,source,target,sign,0,false);
        if sign.is_some() {self.scan(circ,source,target,sign,1,true);}
        self.scan(circ,source,target,sign,2,true);
        self.scan(circ,source,target,sign,3,false);
        self.scan(circ,source,target,sign,4,true);
        self.scan(circ,source,target,sign,5,false);
        for i in 259-self.support_end..259 {circ.cx(&source[i],&target[i]);}
        // Every primitive here is self-inverse; literal reversal implements subtraction.
        if subtract {circ.b.ops[start..].reverse();}
    }
}
pub(super) fn phase00(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize) {
    phase00_with_support(circ,rank,a,c,sm,guard,sign,w1,w2,helpers,j,259);
}
/// Caller proves interval upper endpoint257-A_raw<=support_end.
pub(super) fn phase00_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize) {
    assert!((2..=259).contains(&support_end));let start=circ.b.ops.len();
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    let scan=Scan{rank,a,sm,mask:&c[0],guard,hs:&c[1],ha:&c[2],scratch:&c[3],helpers,j,support_end};
    scan.add(circ,w2,w1,Some(sign),true);scan.add(circ,w2,w1,None,false);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let resource_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let support_end:usize=std::env::var("LOWQ_CODEC_SUPPORT_END").ok().map(|v|v.parse().unwrap()).unwrap_or(259);
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("R.rank",5);let a=circ.alloc_qreg_bits("R.a",6);let c=circ.alloc_qreg_bits("R.c",6);let sm=circ.alloc_qreg_bits("R.s25",4);assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("R.guard");let sign=circ.alloc_qreg("R.sign");let w1=circ.alloc_qreg_bits("R.w1",259);let w2=circ.alloc_qreg_bits("R.w2",259);let helpers=circ.alloc_qreg_bits("R.dirty",16);let owned=circ.b.next_qubit;
        phase00_with_support(&mut circ,&rank,&a,&c,&sm,&guard,&sign,&w1,&w2,&helpers,j,support_end);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_R005_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned} support_end={support_end}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        if resource_only {continue;}
        for pattern in 0..2 {for batch in 0..32*64*16*2/64 {
            let mut seed=0xc1a43ed723589b06^batch as u64^((pattern as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let al=k>>5&63;let sl=k>>11&15;
                let (av,sv,cv)=if r<32 {(64*triples[r][0]+al,64*triples[r][2]+4*sl+j,triples[r][1])}else{(0,0,1)};
                let on=k>>15&1!=0&&r<32&&cv==0&&av+sv<=255&&257-av<=support_end;
                for i in 0..5 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6 {for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);if on {put(w,&c[i],lane,false);}}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&guard,lane,on);}
                if on {
                    let lo=sv+1;let hi=257-av;assert!(lo<hi);
                    let mut less=false;
                    for i in lo..hi {let x=before[w2[258-i].id()as usize]>>lane&1!=0;let y=before[w1[258-i].id()as usize]>>lane&1!=0;if x!=y {less=x;}}
                    if less {after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after {let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("R00 j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_R005_PATTERN j={j} pattern={pattern} PASS");}
    }
    if resource_only {eprintln!("CODEC_R005_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("CODEC_R005_PASS support_end={support_end} lanes={total}; full phase00 signed subtract/restoration with empty C_low workspace on21 metadata; full Q799 missing");
}
