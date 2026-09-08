//! One variable-width adder rather than four separately guarded adders.
//! The clean-under-guard mask is loaned from the extracted quotient slot.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_arithmetic5_programs.rs"] mod programs;
// The caller supplies an analytic half-open support for the unchanged A
// register during this arithmetic cell. Never infer it from sampled inputs.
fn support(circ:&Circuit)->(usize,usize){
    if std::env::var("Q796_PREFIX_SUPPORT").ok().as_deref()==Some("0"){(0,256)}
    else{circ.q797_a_support.unwrap_or((0,256))}
}
struct Range<'a>{rank:&'a[QReg],low:&'a[QReg],guard:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],scratch:Option<&'a[QReg]>,group:isize,threshold:usize}
// Preserve Q795 C1's independently validated six-bit conditional scratch bank.
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],scratch:Option<&[QReg]>){
    if let Some(s)=scratch {
        assert!(cs[0].1);let g=cs[0].0;let others=&cs[1..];let n=others.len();
        if n.saturating_sub(1)>s.len(){super::conditional_mcx::guarded(circ,g,others,out,&s[0],false,&dirty[0]);return;}
        let mut ids:Vec<_>=cs.iter().map(|(q,_)|q.id()).chain(std::iter::once(out.id())).chain(s.iter().map(QReg::id)).collect();ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
        for &(q,v)in others {if !v{circ.x(q);}}
        if n==0{circ.cx(g,out);}else if n==1{circ.ccx(g,others[0].0,out);}else{
            circ.ccx(others[0].0,others[1].0,&s[0]);
            for i in 2..n{circ.ccx(&s[i-2],others[i].0,&s[i-1]);}
            circ.ccx(g,&s[n-2],out);
            for i in (2..n).rev(){circ.ccx(&s[i-2],others[i].0,&s[i-1]);}
            circ.ccx(others[0].0,others[1].0,&s[0]);
        }
        for &(q,v)in others.iter().rev(){if !v{circ.x(q);}}
    }else{mixed_mcx(circ,cs,out,dirty);}
}
impl Range<'_>{
    fn high(&self,circ:&mut Circuit,h:isize){if !(0..4).contains(&h){return;}for &(m,v)in programs::A_EQUAL[h as usize]{let mut cs=vec![(self.guard,true)];cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],v>>i&1!=0)));gate(circ,&cs,self.cache,self.dirty,self.scratch);}}
    fn select(&mut self,circ:&mut Circuit,h:isize){if h!=self.group{self.high(circ,self.group);self.high(circ,h);self.group=h;}}
    fn equality(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg){
        self.equality_impl(circ,value,extra,target,false);
    }
    fn equality_impl(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg,clean_mask:bool){
        let(lo,hi)=support(circ);if value<lo||value>=hi{return;}
        let factor=std::env::var("Q796_PREFIX_FACTORS").ok().as_deref()!=Some("0");
        let h=value/64;let mut cs=vec![(self.guard,true)];
        // A single supported high group needs neither a decoded cache nor
        // its control. Otherwise cache restricts the low-bit domain below.
        if !factor||lo/64!=(hi-1)/64{self.select(circ,h as isize);cs.push((self.cache,true));}
        let left=lo.max(h*64);let right=hi.min((h+1)*64);
        for i in 0..6{
            // Same shifted endpoints imply this bit is constant throughout
            // the interval. value is already known to lie in that interval.
            if !factor||(left>>i)!=((right-1)>>i){cs.push((&self.low[i],value>>i&1!=0));}
        }
        cs.extend_from_slice(extra);
        if clean_mask&&self.scratch.is_none(){super::conditional_mcx::guarded(circ,self.guard,&cs[1..],target,self.mask,true,&self.dirty[0]);}
        else{gate(circ,&cs,target,self.dirty,self.scratch);}
    }
    // mask = [A >= threshold] on guard; threshold is clipped to 0..256.
    fn set(&mut self,circ:&mut Circuit,t:usize){let t=t.min(256);for value in self.threshold.min(t)..self.threshold.max(t){self.equality(circ,value,&[],self.mask);}self.threshold=t;}
}
pub(super) fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign_out:Option<&QReg>,sign_control:Option<&QReg>,dirty:&[QReg],subtract:bool,n:usize){
    prefix_with_scratch(circ,rank,source,target,low,guard,cache,mask,sign_out,sign_control,dirty,subtract,n,None);
}
pub(super) fn prefix_with_scratch(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign_out:Option<&QReg>,sign_control:Option<&QReg>,dirty:&[QReg],subtract:bool,n:usize,scratch:Option<&[QReg]>){
    let start=circ.b.ops.len();let mut r=Range{rank,low,guard,cache,mask,dirty,scratch,group:-1,threshold:0};circ.cx(guard,mask);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev(){if let Some(z)=sign_out{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign_out{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    let mut mask_pristine=true;
    for(i,tag,data,out)in cells{
        if tag==2{circ.cx(data[0],out);continue;}
        let mut extras:Vec<_>=data.iter().map(|&q|(q,true)).collect();if let Some(s)=sign_control{extras.push((s,false));}
        if tag==1{if i>=1{r.equality_impl(circ,i-1,&extras,out,mask_pristine&&super::metadata_muxlease::active("Q796_PREFIX_MASK_LOAN"));}continue;}
        let mut cs=vec![(guard,true)];if tag==0{
            mask_pristine=false;
            let t=i.saturating_sub(1);let(lo,hi)=support(circ);
            // A>=t is false above the support and true below it. Only the
            // variable middle needs a maintained mask and its extra control.
            if t>=hi{continue;}if t>lo{r.set(circ,t);cs.push((mask,true));}
        }cs.extend(extras);gate(circ,&cs,out,dirty,scratch);
    }
    r.set(circ,0);r.select(circ,-1);circ.cx(guard,mask);
    if subtract{circ.b.ops[start..].reverse();}
}
pub fn run(){
    use crate::{sim::Simulator,circuit::OperationType};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut domains=vec![None];if std::env::var("Q796_PREFIX_TEST_SUPPORT").ok().as_deref()==Some("1"){domains.extend(super::metadata_entry_head5::A_SUPPORTS.into_iter().map(Some));}
    for domain in domains{for sub in [false,true]{let mut circ=Circuit::new();circ.q797_a_support=domain;let rank=circ.alloc_qreg_bits("rank",5);let low=circ.alloc_qreg_bits("low",6);let g=circ.alloc_qreg("guard");let cache=circ.alloc_qreg("cache");let mask=circ.alloc_qreg("mask");let sign=circ.alloc_qreg("sign");let a=circ.alloc_qreg_bits("source",259);let b=circ.alloc_qreg_bits("target",259);let dirty=circ.alloc_qreg_bits("dirty",24);let n=circ.b.next_qubit;
        prefix(&mut circ,&rank,&a,&b,&low,&g,&cache,&mask,if sub{None}else{Some(&sign)},if sub{Some(&sign)}else{None},&dirty,sub,259);let ops=circ.into_builder().ops;
        for batch in 0..128{let mut seed=79955^batch;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();for l in 0..64{let k=batch as usize*64+l;let r=k&31;let lo=k>>5&63;let width=64*ts[r][0]+lo+2;let on=k>>11&1!=0&&domain.is_none_or(|(left,right)|width-2>=left&&width-2<right);
            for w in [&mut before,&mut after]{for i in 0..5{put(w,&rank[i],l,r>>i&1!=0);}for i in 0..6{put(w,&low[i],l,lo>>i&1!=0);}put(w,&g,l,on);if on{put(w,&cache,l,false);put(w,&mask,l,false);}}
            let sv=before[sign.id()as usize]>>l&1!=0;if on&&(!sub||!sv){let mut carry=false;for i in 0..width{let av=before[a[i].id()as usize]>>l&1!=0;let bv=before[b[i].id()as usize]>>l&1!=0;put(&mut after,&b[i],l,av^bv^carry);carry=if sub{(!bv&&(av||carry))||(av&&carry)}else{(av&&bv)||(av&&carry)||(bv&&carry)};}if !sub{put(&mut after,&sign,l,sv^carry);}}
        }let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("PREFIX_UNIT sub={sub} batch={batch} diffs={diffs:?}");}assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);}
        eprintln!("PREFIX_UNIT_PASS domain={domain:?} subtract={sub} cases=8192 ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==OperationType::CCX).count());
    }}
}
