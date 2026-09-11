//! Two-passenger sign recovery. Experimental until full lifecycle validation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_remainder5_programs.rs"] mod programs;
pub(super) fn c1_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg]){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for (r,t)in ts.iter().enumerate(){if t[1]!=0{continue;}let mut cs=vec![(g,true)];cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));mixed_mcx(circ,&cs,out,dirty);}
}
fn c_head(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,passenger:&QReg,w1:&[QReg],dirty:&[QReg]){
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v<2{None}else{Some(&w1[259-v])}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,l,r,dirty);}Some(l)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let ops=circ.b.ops[start..].to_vec();circ.cswap(g,root,passenger);circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn move_generic(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,w1:&[QReg],helpers:&[QReg],inverse:bool){
    let start=circ.b.ops.len();let shuttle=&helpers[0];let dirty=&helpers[1..];
    super::q797_cargo_moves::exchange_a(circ,rank,a,w1,2,shuttle,&[(g,true)],dirty);
    c_head(circ,rank,c,g,shuttle,w1,dirty);
    super::q797_cargo_moves::exchange_a(circ,rank,a,w1,2,shuttle,&[(g,true)],dirty);
    super::q797_cargo_moves::flip_a_terms(circ,rank,a,w1,2,&vec![vec![(g,true)]],dirty);
    if inverse{circ.b.ops[start..].reverse();}
}
struct Range<'a>{rank:&'a[QReg],sm:&'a[QReg],g:&'a QReg,second:&'a QReg,cache:&'a QReg,mask:&'a QReg,scratch:&'a QReg,dirty:&'a[QReg],j:usize,group:isize,pos:usize}
impl Range<'_>{
    fn gate(&self,circ:&mut Circuit,extra:&[(&QReg,bool)],out:&QReg){super::conditional_pair::guarded_pair(circ,self.g,(self.second,true),extra,out,self.scratch,false,self.dirty);}
    fn high(&self,circ:&mut Circuit,h:isize){if !(0..4).contains(&h){return;}for &(m,v)in programs::EQUAL[4+h as usize]{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],v>>i&1!=0)).collect();self.gate(circ,&cs,self.cache);}}
    fn select(&mut self,circ:&mut Circuit,h:isize){if h!=self.group{self.high(circ,self.group);self.high(circ,h);self.group=h;}}
    fn eq(&mut self,circ:&mut Circuit,value:usize,extras:&[(&QReg,bool)],out:&QReg){
        if !(1..=256).contains(&value){return;}let s=value-1;if s%4!=(4-self.j)%4{return;}self.select(circ,(s/64)as isize);
        let mut cs=vec![(self.cache,true)];cs.extend((0..4).map(|i|(&self.sm[i],s>>(i+2)&1!=0)));cs.extend_from_slice(extras);self.gate(circ,&cs,out);
    }
    fn set(&mut self,circ:&mut Circuit,p:usize){for k in self.pos.min(p)..self.pos.max(p){self.eq(circ,257-k,&[],self.mask);}self.pos=p;}
}
fn prefix(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],g:&QReg,second:&QReg,c:&[QReg],w1:&[QReg],w2:&[QReg],sign:Option<&QReg>,dirty:&[QReg],j:usize,n:usize,inverse:bool){
    let start=circ.b.ops.len();let mut r=Range{rank,sm,g,second,cache:&c[1],mask:&c[2],scratch:&c[3],dirty,j,group:-1,pos:0};circ.ccx(g,second,r.mask);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&w1[i]],&w2[i]));}cells.push((0,3,vec![&w1[0]],&w2[0]));
    for i in (1..n).rev(){if let Some(s)=sign{cells.push((i,1,vec![&w1[i]],s));}if i+1<n{cells.push((i+1,2,vec![&w1[i]],&w1[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&w1[i],&w2[i]],&w1[i+1]));}if let Some(s)=sign{cells.push((i,1,vec![&w1[i],&w2[i]],s));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&w1[i]],&w2[i]));cells.push((i,0,vec![&w1[i-1],&w2[i-1]],&w1[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&w1[i]],&w1[i+1]));}for i in 0..n{cells.push((i,2,vec![&w1[i]],&w2[i]));}
    for(i,tag,data,out)in cells{if tag==2{circ.cx(data[0],out);continue;}let mut cs:Vec<_>=data.iter().map(|&q|(q,true)).collect();if tag==1{r.eq(circ,257-i,&cs,out);continue;}if tag==0{r.set(circ,i);cs.push((r.mask,true));}r.gate(circ,&cs,out);}
    r.set(circ,0);r.select(circ,-1);circ.ccx(g,second,r.mask);if inverse{circ.b.ops[start..].reverse();}
}
pub(super) fn c1(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,second:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,n:usize){
    // g independently remembers C=1 while C0 holds the unknown cargo.
    let start=circ.b.ops.len();super::q797_cargo_moves::exchange_a(circ,rank,a,w1,2,&c[0],&[(g,true),(second,true)],dirty);
    super::q797_cargo_moves::flip_a_terms(circ,rank,a,w1,2,&vec![vec![(g,true),(second,true)]],dirty);
    let move_ops=circ.b.ops[start..].to_vec();
    prefix(circ,rank,sm,g,second,c,w1,w2,None,dirty,j,n,true);
    prefix(circ,rank,sm,g,second,c,w1,w2,Some(sign),dirty,j,n,false);
    circ.b.ops.extend(move_ops.into_iter().rev());
}
pub(super) fn park_c1(circ:&mut Circuit,p1:&QReg,p2:&QReg,sign:&QReg,dirty:&[QReg]){
    // After exact C1 sign erasure, state3 swaps with unused state6.
    // Off-domain states are a total reversible extension, never discarded.
    mixed_mcx(circ,&[(p2,true),(sign,false)],p1,dirty);
    mixed_mcx(circ,&[(p1,false),(p2,true)],sign,dirty);
    mixed_mcx(circ,&[(p2,true),(sign,false)],p1,dirty);
}
