//! Entry-domain phase11 first, exposing P2 as clean-under-guard workspace.
//! Entry Sign=0 in phases00/01/10, arbitrary in11 (same domain as T10).
//! Old T11 was the identity outside11; other arithmetic is identity on11.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
pub(super) fn code(circ:&mut Circuit,p1:&QReg,p2:&QReg,sign:&QReg,helpers:&[QReg],inverse:bool){
    let start=circ.b.ops.len();let word=[p1,p2,sign];
    // 3->1, 7->5, 1->4, 0->0, 2->2. Thus P1 is phase11, P2=0 there.
    for(left,right)in[(1usize,4usize),(1,3),(5,7)]{let mut value=left;let mut edges=Vec::new();for bit in 0..3{if(left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());for(bit,v)in edges{let cs:Vec<_>=(0..3).filter(|&i|i!=bit).map(|i|(word[i],v>>i&1!=0)).collect();mixed_mcx(circ,&cs,word[bit],helpers);}}
    if inverse{circ.b.ops[start..].reverse();}
}
struct Range<'a>{rank:&'a[QReg],low:&'a[QReg],sm:&'a[QReg],guard:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],j:usize,group:isize,position:usize}
impl Range<'_>{
    fn high(&self,circ:&mut Circuit,h:isize){if(0..5).contains(&h){super::metadata_phase115_phased::sum_flag(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,h as usize);}}
    fn select(&mut self,circ:&mut Circuit,h:isize){if h!=self.group{self.high(circ,self.group);self.high(circ,h);self.group=h;}}
    fn equality(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg){if !(2..=257).contains(&value){return;}self.select(circ,(value/64)as isize);let mut cs=vec![(self.guard,true),(self.cache,true)];cs.extend((0..6).map(|i|(&self.low[i],value>>i&1!=0)));cs.extend_from_slice(extra);mixed_mcx(circ,&cs,target,self.dirty);}
    // mask = [position < 259-(C+S)] under guard, true at position0.
    fn set(&mut self,circ:&mut Circuit,p:usize){for k in self.position.min(p)..self.position.max(p){self.equality(circ,258-k,&[],self.mask);}self.position=p;}
}
fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:Option<&QReg>,dirty:&[QReg],j:usize,inverse:bool,n:usize){
    let start=circ.b.ops.len();let mut r=Range{rank,low,sm,guard,cache,mask,dirty,j,group:-1,position:0};circ.cx(guard,mask);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in(1..n).rev(){if let Some(z)=sign{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in(1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    for(i,tag,data,out)in cells{if tag==2{circ.cx(data[0],out);continue;}let extras:Vec<_>=data.iter().map(|&q|(q,true)).collect();if tag==1{r.equality(circ,258-i,&extras,out);continue;}let mut cs=vec![(guard,true)];if tag==0{r.set(circ,i);cs.push((mask,true));}cs.extend(extras);mixed_mcx(circ,&cs,out,dirty);}
    r.set(circ,0);r.select(circ,-1);circ.cx(guard,mask);if inverse{circ.b.ops[start..].reverse();}
}
fn compare(circ:&mut Circuit,rank:&[QReg],a:&[QReg],b:&[QReg],low:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:&QReg,dirty:&[QReg],j:usize,n:usize){
    // carry(a + NOT b) = [a>b]. Complementing that gives [b>=a].
    // Compute only the carry propagation, write its two terms, and undo;
    // no sum is needed or retained by phase11.
    for q in &b[..n]{circ.x(q);}
    let start=circ.b.ops.len();let mut r=Range{rank,low,sm,guard,cache,mask,dirty,j,group:-1,position:0};circ.cx(guard,mask);
    for i in 0..n{circ.cx(&a[i],&b[i]);}circ.cx(&a[0],&b[0]);
    for i in (1..n-1).rev(){circ.cx(&a[i],&a[i+1]);}
    for i in 0..n-1{r.set(circ,i+1);mixed_mcx(circ,&[(guard,true),(mask,true),(&a[i],true),(&b[i],true)],&a[i+1],dirty);}
    r.set(circ,0);r.select(circ,-1);circ.cx(guard,mask);let compute=circ.b.ops[start..].to_vec();
    for i in 1..n{r.equality(circ,258-i,&[(&a[i],true),(&b[i],true)],sign);}r.select(circ,-1);
    circ.b.ops.extend(compute.into_iter().rev());
    for i in 1..n{r.equality(circ,258-i,&[(&a[i],true)],sign);}r.select(circ,-1);
    for q in &b[..n]{circ.x(q);}circ.cx(guard,sign);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize){
    code(circ,p1,p2,sign,helpers,false);let mask=&helpers[0];let dirty=&helpers[1..];let addresses:Vec<_>=(0..256).map(|v|&w1[258-v]).collect();
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,false);
    if super::metadata_muxlease::active("Q799_T11_COMPARE"){compare(circ,rank,w1,w2,c,sm,p1,p2,mask,sign,dirty,j,n);}else{
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,None,dirty,j,true,n);circ.cx(p1,sign);
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,Some(sign),dirty,j,false,n);
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,true);
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);code(circ,p1,p2,sign,helpers,true);
}
pub fn run(){
    use crate::{sim::Simulator,circuit::OperationType};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for j in 0..4{let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let a=circ.alloc_qreg_bits("source",259);let b=circ.alloc_qreg_bits("target",259);let dirty=circ.alloc_qreg_bits("dirty",24);let n=circ.b.next_qubit;emit(&mut circ,&rank,&c,&sm,&p1,&p2,&sign,&a,&b,&dirty,j,259);assert_eq!(n,circ.b.next_qubit);let ops=circ.into_builder().ops;
        for batch in 0..2560{let mut seed=799115^batch^(j as u64*711);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();for l in 0..64{let k=batch as usize*64+l;let r=k&31;let cl=k>>5&63;let sl=k>>11&15;let cv=64*ts[r][1]+cl;let raw_s=64*ts[r][2]+4*sl+(4-j)%4;let sv=if raw_s==0{256}else{raw_s};let mut code=[0,1,2,3,7][k>>15];if cv==0||cv+sv>257{code=0;}let on=code==3||code==7;
            for w in [&mut before,&mut after]{for i in 0..5{put(w,&rank[i],l,r>>i&1!=0);}for i in 0..6{put(w,&c[i],l,cl>>i&1!=0);}for i in 0..4{put(w,&sm[i],l,sl>>i&1!=0);}put(w,&p1,l,code&1!=0);put(w,&p2,l,code&2!=0);put(w,&sign,l,code&4!=0);if on{put(w,&a[258-cv],l,false);}}
            if on{let mut ge=true;for i in 0..259-cv-sv{let av=before[a[i].id()as usize]>>l&1!=0;let bv=before[b[i].id()as usize]>>l&1!=0;if av!=bv{ge=bv;}}put(&mut after,&sign,l,(code&4!=0)^ge);}
        }let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("T11_UNIT j={j} batch={batch} diffs={diffs:?}");}assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);}
        eprintln!("T11_UNIT_PASS j={j} cases=163840 ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==OperationType::CCX).count());
    }
}
