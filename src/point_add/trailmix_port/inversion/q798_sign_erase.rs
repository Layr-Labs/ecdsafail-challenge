//! Post-entry Sign erasure with one shortened comparison bit and cargo handoff.
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
    fn high(&self,circ:&mut Circuit,h:isize){if(0..5).contains(&h){super::metadata_phase115_phased::sum_flag_raw(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,h as usize);}}
    fn select(&mut self,circ:&mut Circuit,h:isize){if h!=self.group{
        if super::metadata_muxlease::active("Q795_SIGN_TRANSITION"){super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,self.group,h);}
        else{self.high(circ,self.group);self.high(circ,h);}self.group=h;
    }}
    fn equality(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg){self.equality_impl(circ,value,extra,target,false);}
    fn equality_impl(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg,clean_mask:bool){
        if !(1..=257).contains(&value){return;}self.select(circ,(value/64)as isize);let mut cs=vec![(self.guard,true),(self.cache,true)];cs.extend((0..6).map(|i|(&self.low[i],value>>i&1!=0)));cs.extend_from_slice(extra);
        if clean_mask{super::conditional_mcx::guarded(circ,self.guard,&cs[1..],target,self.mask,true,&self.dirty[0]);}
        else{mixed_mcx(circ,&cs,target,self.dirty);}
    }
    // mask = [position < 259-(C+S)] under guard, true at position0.
    fn set(&mut self,circ:&mut Circuit,p:usize){let base=if super::metadata_muxlease::active("Q795_PHASE_LOAN"){256usize}else{257};for k in self.position.min(p)..self.position.max(p){if k<=base{self.equality(circ,base-k,&[],self.mask);}}self.position=p;}
}
fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:Option<&QReg>,dirty:&[QReg],j:usize,inverse:bool,n:usize){
    let start=circ.b.ops.len();let mut r=Range{rank,low,sm,guard,cache,mask,dirty,j,group:-1,position:0};circ.cx(guard,mask);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in(1..n).rev(){if let Some(z)=sign{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in(1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    let mut mask_pristine=true;
    for(i,tag,data,out)in cells{if tag==2{circ.cx(data[0],out);continue;}let extras:Vec<_>=data.iter().map(|&q|(q,true)).collect();if tag==1{let base=if super::metadata_muxlease::active("Q795_PHASE_LOAN"){256usize}else{257};if i<=base{r.equality_impl(circ,base-i,&extras,out,mask_pristine&&super::metadata_muxlease::active("Q796_SIGN_MASK_LOAN"));}continue;}let mut cs=vec![(guard,true)];if tag==0{mask_pristine=false;r.set(circ,i);cs.push((mask,true));}cs.extend(extras);mixed_mcx(circ,&cs,out,dirty);}
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
    for i in 1..n{r.equality(circ,257-i,&[(&a[i],true),(&b[i],true)],sign);}r.select(circ,-1);
    circ.b.ops.extend(compute.into_iter().rev());
    for i in 1..n{r.equality(circ,257-i,&[(&a[i],true)],sign);}r.select(circ,-1);
    for q in &b[..n]{circ.x(q);}circ.cx(guard,sign);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize){
    code(circ,p1,p2,sign,helpers,false);super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);let mask=&helpers[0];let dirty=&helpers[1..];let addresses:Vec<_>=(0..256).map(|v|&w1[258-v]).collect();
    let dual=super::metadata_muxlease::active("Q795_PHASE_LOAN");
    if dual{
        assert!(!super::metadata_muxlease::active("Q799_T11_COMPARE"),"top-loan direct comparator not adapted");
        super::q795_t11_top::move_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    }
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);
    if dual{
        super::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
        circ.cswap(p1,p2,mask);circ.ccx(p1,p2,sign);
        super::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,false);
    if super::metadata_muxlease::active("Q799_T11_COMPARE"){compare(circ,rank,w1,w2,c,sm,p1,p2,mask,sign,dirty,j,n);}else{
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,None,dirty,j,true,n);
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,Some(sign),dirty,j,false,n);
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,true);
    if dual{
        super::q795_t11::park_c1(circ,p1,p2,sign,helpers);circ.cswap(p1,p2,mask);
        super::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    }
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);
    if dual{super::q795_t11_top::move_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);}
    super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);code(circ,p1,p2,sign,helpers,true);
}
