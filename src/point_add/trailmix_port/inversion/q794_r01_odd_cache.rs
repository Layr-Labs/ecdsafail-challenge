//! Persistent high-S cache on existing odd-C lower selectors only.
//! C0/even-C fall back unchanged; a complemented A+2 payload loan funds H.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
const P:[usize;4]=[12,10,12,10];
pub(super) fn mode()->usize{let n=std::env::var("Q794_R01_ODD_CACHE").ok().map(|v|v.parse().unwrap()).unwrap_or(0);assert!(n<=2);n}
pub(super) fn eligible(i:usize,j:usize)->bool{i<=255&&(i+1)%2==j%2&&((((i+1)%256)>>1)^(j>>1))&1!=0}
pub(super) fn raw_margin(support:(usize,usize),n:usize,j:usize)->isize{
 let(lo,hi)=support;let mut nodes:Vec<_>=(0..256).map(|a|a>=lo&&a<hi&&a<=254).collect();let mut route=0;
 for level in 0..8{let mut next=Vec::new();for p in nodes.chunks_exact(2){if p[0]&&p[1]{route+=if level<6{1}else if level==6{53}else{21};}next.push(p[0]||p[1]);}nodes=next;}
 assert!(nodes[0]);let mut old=None;let mut producer=0;let mut saved=0;
 for i in 2..n{if !eligible(i,j){continue;}let h=((i+1)%256)/64;saved+=4*P[h];if old!=Some(h){if let Some(x)=old{producer+=P[x];}producer+=P[h];old=Some(h);}}
 saved as isize-(2*producer+4*route+2)as isize
}
pub(super) fn selected(c:&Circuit,n:usize,j:usize)->bool{let mode=mode();mode==2||mode==1&&raw_margin(c.q797_a_support.unwrap_or((0,256)),n,j)>0}
pub(super) fn loan(c:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,h:&QReg,w1:&[QReg],dirty:&[QReg],acquire:bool){
 assert!(w1.len()>=257);assert!(!dirty.iter().chain(rank).chain(a).chain(w1).any(|q|q.id()==h.id()));assert_ne!(h.id(),g.id());
 if !acquire{c.x(h);}
 let(root,ops)=super::q794_handoffs::gather_a(c,rank,a,&w1[..257],2,dirty);c.cswap(g,root,h);c.b.ops.extend(ops.into_iter().rev());
 if acquire{c.x(h);}
}
pub(super) fn lower(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,h:&QReg,dirty:&[QReg],i:usize,j:usize,group:&mut Option<usize>){
 assert!(eligible(i,j));let value=(i+1)%256;let next=value/64;
 if *group!=Some(next){c.x(g);if let Some(old)=*group{super::q795_r01_s_affine::emit(c,rank,old,h,g);}super::q795_r01_s_affine::emit(c,rank,next,h,g);c.x(g);*group=Some(next);}
 c.cx(&a[0],&cl[0]);let mut cs=vec![(h,true),(&cl[0],true)];cs.extend((0..4).map(|b|(&sm[b],value>>(b+2)&1!=0)));
 assert!(dirty.len()>=cs.len()-2);super::length_recompute::mixed_mcx(c,&cs,mask,dirty);c.cx(&a[0],&cl[0]);
}
