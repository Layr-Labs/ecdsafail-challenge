//! Rank5 phase01 R interval arithmetic. Two existing zeros lend mask and high sum.
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
fn low_swap(circ:&mut Circuit,a:&[QReg],guard:&QReg,flag:&QReg,p0:&QReg,p1:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],h:usize) {
    for lo in 0..64 {let address=64*h+lo+1;
        for (p,w) in [(p0,w1),(p1,w2)] {
            let mut cs=vec![(guard,true),(flag,true),(p,true)];cs.extend((0..6).map(|i|(&a[i],lo>>i&1!=0)));
            circ.cx(&w[address],p);mixed_mcx(circ,&cs,&w[address],helpers);circ.cx(&w[address],p);
        }
    }
}
fn borrow(circ:&mut Circuit,rank:&[QReg],a:&[QReg],guard:&QReg,p0:&QReg,p1:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg]) {
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..4 {
        high(circ,rank,guard,flag,dirty,0,h as isize);low_swap(circ,a,guard,flag,p0,p1,w1,w2,dirty,h);
        high(circ,rank,guard,flag,dirty,0,h as isize);low_swap(circ,a,guard,flag,p0,p1,w1,w2,dirty,h);
    }
}
struct Scan<'a> {rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],mask:&'a QReg,guard:&'a QReg,ha:&'a QReg,helpers:&'a[QReg],j:usize,restore:Option<&'a QReg>}
impl Scan<'_> {
    fn cache(&self,circ:&mut Circuit,h:isize) {
        if !(0..=4).contains(&h){return;}
        metadata_arithmetic5::sum_flag(circ,self.rank,self.a,self.c,self.guard,self.ha,&self.helpers[0],&self.helpers[1..],h as usize);
    }
    fn lo(&self,circ:&mut Circuit,i:usize,_group:isize,data:&[&QReg],out:&QReg,enabled:bool) {
        if i>255||(i+1)%2!=self.j%2{return;}
        let value=(i+1)%256;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        for &(m,v) in programs::EQUAL[4+value/64] {for av in [false,true] {
            let mut cs=vec![(self.guard,true),(&self.a[0],av),(&self.c[0],av^old_c0)];
            cs.extend((0..5).filter(|&b|m>>b&1!=0).map(|b|(&self.rank[b],v>>b&1!=0)));
            cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));cs.extend(data.iter().map(|&q|(q,true)));
            if enabled{if let Some(s)=self.restore{cs.push((s,false));}}
            mixed_mcx(circ,&cs,out,self.helpers);
        }}
    }
    fn top(&self,circ:&mut Circuit,i:usize,data:&[&QReg],out:&QReg,singleton:bool,enabled:bool) {
        // A_raw+C+S<=256 implies interval width>=2, so singleton is impossible.
        if i>256||singleton{return;}
        let value=256-i;let mut cs=vec![(self.guard,true),(self.ha,true)];cs.extend((0..6).map(|b|(&self.c[b],value>>b&1!=0)));
        cs.extend(data.iter().map(|&q|(q,true)));if enabled{if let Some(s)=self.restore{cs.push((s,false));}}
        mixed_mcx(circ,&cs,out,self.helpers);
    }
    fn update(&self,circ:&mut Circuit,i:usize,group:isize) {
        self.lo(circ,i,group,&[],self.mask,false);self.top(circ,i,&[],self.mask,false,false);
    }
    fn data(&self,circ:&mut Circuit,qs:&[&QReg],out:&QReg) {
        let mut cs=vec![(self.guard,true),(self.mask,true)];cs.extend(qs.iter().map(|&q|(q,true)));if let Some(s)=self.restore {cs.push((s,false));}mixed_mcx(circ,&cs,out,self.helpers);
    }
    fn scan(&self,circ:&mut Circuit,source:&[QReg],target:&[QReg],sign:Option<&QReg>,role:usize,reverse:bool) {
        let a:Vec<_>=source.iter().rev().collect();let b:Vec<_>=target.iter().rev().collect();let mut current=-99isize;
        for z in 0..259 {let i=if reverse {258-z}else{z};let group=if i<=256{((256-i)/64)as isize}else{-1};
            if group!=current {if current!=-99 {self.cache(circ,current);}self.cache(circ,group);current=group;}
            let uses_mask=role==3||role==4;
            if uses_mask&&!reverse {self.update(circ,i,group);}
            match role {
                0=>self.lo(circ,i,group,&[a[i]],b[i],true),
                1=>if let Some(s)=sign {self.top(circ,i,&[a[i]],s,false,true);self.top(circ,i,&[a[i]],s,true,true);},
                2=>if i<258 {circ.cx(a[i],a[i+1]);self.lo(circ,i,group,&[a[i]],a[i+1],false);self.lo(circ,i+1,group,&[a[i]],a[i+1],false);},
                3=>{
                    if i<258 {self.data(circ,&[a[i],b[i]],a[i+1]);}
                    if let Some(s)=sign {self.top(circ,i,&[a[i],b[i]],s,false,true);}
                },
                4=>if i<258 {self.data(circ,&[a[i+1]],b[i+1]);self.data(circ,&[a[i],b[i]],a[i+1]);},
                5=>if i<258 {self.lo(circ,i+1,group,&[a[i]],a[i+1],false);self.lo(circ,i,group,&[a[i]],a[i+1],false);circ.cx(a[i],a[i+1]);},
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
        self.scan(circ,source,target,sign,2,true);self.scan(circ,source,target,sign,3,false);self.scan(circ,source,target,sign,4,true);self.scan(circ,source,target,sign,5,false);
        for i in 0..259 {circ.cx(&source[i],&target[i]);}
        if subtract {circ.b.ops[start..].reverse();}
    }
}
pub(super) fn phase01(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize){
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);
    let mask=&helpers[0];let ha=&helpers[1];let dirty=&helpers[2..];
    borrow(circ,rank,a,guard,mask,ha,w1,w2,dirty);
    metadata_arithmetic5::add(circ,a,c,None,false);
    let mut scan=Scan{rank,a,c,sm,mask,guard,ha,helpers:dirty,j,restore:None};
    scan.add(circ,w2,w1,Some(sign),true);circ.cx(guard,sign);scan.restore=Some(sign);scan.add(circ,w2,w1,None,false);
    metadata_arithmetic5::add(circ,a,c,None,true);
    borrow(circ,rank,a,guard,mask,ha,w1,w2,dirty);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("R01.rank",5);let a=circ.alloc_qreg_bits("R01.a",6);let c=circ.alloc_qreg_bits("R01.c",6);let sm=circ.alloc_qreg_bits("R01.s25",4);assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("R01.guard");let sign=circ.alloc_qreg("R01.sign");let w1=circ.alloc_qreg_bits("R01.w1",259);let w2=circ.alloc_qreg_bits("R01.w2",259);let helpers=circ.alloc_qreg_bits("R01.dirty",16);let owned=circ.b.next_qubit;
        phase01(&mut circ,&rank,&a,&c,&sm,&guard,&sign,&w1,&w2,&helpers,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_R015_BUILT j={j} T={} ops={} metadata_wires=21 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        for batch in 0..32*64*64*16*2/64 {
            let mut seed=0x14de2637c98ab50f^batch as u64^((j as u64)<<29);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let al=k>>5&63;let cl=k>>11&63;let sl=k>>17&15;
                let (av,cv,raw_s)=if r<32 {(64*triples[r][0]+al,64*triples[r][1]+cl,64*triples[r][2]+4*sl+(((j>>1)^(cl&1))&1)*2+(j&1))}else{(0,0,0)};
                let sv=if raw_s==0 {256}else{raw_s};let on=k>>21&1!=0&&r<32&&av+cv+sv<=256;
                for i in 0..5 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6 {for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);put(w,&c[i],lane,cl>>i&1!=0);}}
                for i in 0..4 {for w in [&mut before,&mut after]{put(w,&sm[i],lane,sl>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&guard,lane,on);}
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
            if batch%8192==8191 {eprintln!("CODEC_R015_PROGRESS j={j} batches={}",batch+1);}
        }
        eprintln!("CODEC_R015_CLOCK j={j} PASS");
    }
    eprintln!("CODEC_R015_PASS lanes={total} true_S256_lanes={wraps}; actual rank5 R01 arithmetic with borrowed mask and high sum; full Q799 missing");
}
