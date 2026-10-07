//! Phase00 R comparison with a scanned interval mask on 21 metadata wires.
//! Two existing zero wires Work1[A], Work2[A] lend the high selectors.
//! Guard must imply phase00: C=0, S mod4=j, raw A+S<=255.
//! Equality decoders deliberately use this domain; other ranks are unspecified.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_R00_programs.rs"] mod programs;
fn high(circ:&mut Circuit,rank:&[QReg],guard:&QReg,target:&QReg,helpers:&[QReg],axis:usize,h:isize) {
    if !(0..16).contains(&h) {return;}
    assert!(axis==0||axis==2);
    for &(m,v) in programs::EQUAL[if axis==0 {h as usize}else{16+h as usize}] {
        let mut cs=vec![(guard,true)];cs.extend((0..10).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,target,helpers);
    }
}
fn low_swap(circ:&mut Circuit,a:&[QReg],guard:&QReg,flag:&QReg,p0:&QReg,p1:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],h:usize) {
    for lo in 0..16 {let address=16*h+lo+1;
        for (p,w) in [(p0,w1),(p1,w2)] {
            let mut cs=vec![(guard,true),(flag,true),(p,true)];cs.extend((0..4).map(|i|(&a[i],lo>>i&1!=0)));
            circ.cx(&w[address],p);mixed_mcx(circ,&cs,&w[address],helpers);circ.cx(&w[address],p);
        }
    }
}
fn borrow(circ:&mut Circuit,rank:&[QReg],a:&[QReg],guard:&QReg,p0:&QReg,p1:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg]) {
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..16 {
        high(circ,rank,guard,flag,dirty,0,h as isize);low_swap(circ,a,guard,flag,p0,p1,w1,w2,dirty,h);
        high(circ,rank,guard,flag,dirty,0,h as isize);low_swap(circ,a,guard,flag,p0,p1,w1,w2,dirty,h);
    }
}
struct Scan<'a> {rank:&'a[QReg],a:&'a[QReg],sm:&'a[QReg],mask:&'a QReg,guard:&'a QReg,hs:&'a QReg,ha:&'a QReg,helpers:&'a[QReg],j:usize}
impl Scan<'_> {
    fn cache(&self,circ:&mut Circuit,group:isize) {
        high(circ,self.rank,self.guard,self.hs,self.helpers,2,group);
        high(circ,self.rank,self.guard,self.ha,self.helpers,0,15-group);
    }
    fn lo(&self,circ:&mut Circuit,i:usize,group:isize,data:&[&QReg],out:&QReg) {
        if i==0||i>256||(i-1)%4!=self.j {return;}
        let value=i-1;let wanted=(value/16)as isize;
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,2,group);high(circ,self.rank,self.guard,self.hs,self.helpers,2,wanted);}
        let mut cs=vec![(self.guard,true),(self.hs,true)];cs.extend((0..2).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,out,self.helpers);
        if wanted!=group {high(circ,self.rank,self.guard,self.hs,self.helpers,2,wanted);high(circ,self.rank,self.guard,self.hs,self.helpers,2,group);}
    }
    fn top(&self,circ:&mut Circuit,i:usize,data:&[&QReg],out:&QReg,singleton:bool) {
        if i==0||i>256 {return;}
        let value=256-i;let mut cs=vec![(self.guard,true),(self.ha,true)];cs.extend((0..4).map(|b|(&self.a[b],value>>b&1!=0)));
        if singleton {
            if (i-1)%4!=self.j {return;}
            cs.push((self.hs,true));cs.extend((0..2).map(|b|(&self.sm[b],(i-1)>>(b+2)&1!=0)));
        }
        cs.extend(data.iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,out,self.helpers);
    }
    fn update(&self,circ:&mut Circuit,i:usize,group:isize) {
        self.lo(circ,i,group,&[],self.mask);self.top(circ,i,&[],self.mask,false);
    }
    fn scan(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,role:usize,reverse:bool) {
        let a:Vec<_>=source.iter().rev().collect();let b:Vec<_>=target.iter().rev().collect();let mut current=-99isize;
        for z in 0..259 {let i=if reverse {258-z}else{z};let group=if i==0 {-1}else{((i-1)/16)as isize};
            if group!=current {if current!=-99 {self.cache(circ,current);}self.cache(circ,group);current=group;}
            let uses_mask=role==3||role==4;
            if uses_mask&&!reverse {self.update(circ,i,group);}
            match role {
                0=>self.lo(circ,i,group,&[a[i]],b[i]),
                1=>if let Some(s)=sign {self.top(circ,i,&[a[i]],s,false);self.top(circ,i,&[a[i]],s,true);},
                2=>if i<258 {circ.cx(a[i],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);self.lo(circ,i+1,group,&[a[i]],a[i+1]);},
                3=>{
                    if i<258 {mixed_mcx(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1],self.helpers);}
                    if let Some(s)=sign {self.top(circ,i,&[a[i],b[i]],s,false);}
                },
                4=>if i<258 {
                    mixed_mcx(circ,&[(self.guard,true),(self.mask,true),(a[i+1],true)],b[i+1],self.helpers);
                    mixed_mcx(circ,&[(self.guard,true),(self.mask,true),(a[i],true),(b[i],true)],a[i+1],self.helpers);
                },
                5=>if i<258 {self.lo(circ,i+1,group,&[a[i]],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1]);circ.cx(a[i],a[i+1]);},
                _=>unreachable!(),
            }
            if uses_mask&&reverse {self.update(circ,i,group);}
        }
        self.cache(circ,current);
    }
    fn add(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,subtract:bool) {
        let start=circ.b.ops.len();
        for i in 0..259 {circ.cx(&source[i],&target[i]);}
        self.scan(circ,source,target,sign,0,false);
        if sign.is_some() {self.scan(circ,source,target,sign,1,true);}
        self.scan(circ,source,target,sign,2,true);
        self.scan(circ,source,target,sign,3,false);
        self.scan(circ,source,target,sign,4,true);
        self.scan(circ,source,target,sign,5,false);
        for i in 0..259 {circ.cx(&source[i],&target[i]);}
        // Every primitive here is self-inverse; literal reversal implements subtraction.
        if subtract {circ.b.ops[start..].reverse();}
    }
}
pub(super) fn phase00(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sm:&[QReg],s0:&QReg,guard:&QReg,hs:&QReg,ha:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize) {
    borrow(circ,rank,a,guard,hs,ha,w1,w2,helpers);
    if j%2!=0 {circ.x(s0);}
    let scan=Scan{rank,a,sm,mask:s0,guard,hs,ha,helpers,j};
    scan.add(circ,w2,w1,Some(sign),true);scan.add(circ,w2,w1,None,false);
    if j%2!=0 {circ.x(s0);}
    borrow(circ,rank,a,guard,hs,ha,w1,w2,helpers);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();let mut total=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("R.rank",10);let a=circ.alloc_qreg_bits("R.a",4);let c=circ.alloc_qreg_bits("R.c",4);let sm=circ.alloc_qreg_bits("R.s23",2);let s0=circ.alloc_qreg("R.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("R.guard");let hs=circ.alloc_qreg("R.hs");let ha=circ.alloc_qreg("R.ha");let sign=circ.alloc_qreg("R.sign");let w1=circ.alloc_qreg_bits("R.w1",259);let w2=circ.alloc_qreg_bits("R.w2",259);let helpers=circ.alloc_qreg_bits("R.dirty",16);let owned=circ.b.next_qubit;
        phase00(&mut circ,&rank,&a,&sm,&s0,&guard,&hs,&ha,&sign,&w1,&w2,&helpers,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_R00_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        for pattern in 0..2 {for batch in 0..1024*16*4*2/64 {
            let mut seed=0xc1a43ed723589b06^batch as u64^((pattern as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&1023;let al=k>>10&15;let sl=k>>14&3;
                let (av,sv,cv)=if r<966 {(16*triples[r][0]+al,16*triples[r][2]+4*sl+j,triples[r][1])}else{(0,0,1)};
                let on=k>>16&1!=0&&r<966&&cv==0&&av+sv<=255;
                for i in 0..10 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);if on {put(w,&c[i],lane,false);}}}
                for i in 0..2 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for (q,v) in [(&guard,on),(&s0,if on {j%2!=0}else{(k+pattern)%2!=0})] {for w in [&mut before,&mut after]{put(w,q,lane,v);}}
                if on {
                    let address=av+1;let lo=sv+1;let hi=257-av;assert!(lo<hi);
                    for q in [&w1[address],&w2[address]] {put(&mut before,q,lane,false);put(&mut after,q,lane,false);}
                    let mut less=false;
                    for i in lo..hi {let x=before[w2[258-i].id()as usize]>>lane&1!=0;let y=before[w1[258-i].id()as usize]>>lane&1!=0;if x!=y {less=x;}}
                    if less {after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after {let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("R00 j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }eprintln!("CODEC_R00_PATTERN j={j} pattern={pattern} PASS");}
    }
    eprintln!("CODEC_R00_PASS lanes={total}; full phase00 borrow/signed subtract/restoration/return on21 metadata; full Q799 missing");
}
