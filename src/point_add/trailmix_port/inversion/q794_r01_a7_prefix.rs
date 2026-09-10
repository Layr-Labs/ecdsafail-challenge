//! Existing numeric A7 is zero on M7=0 because true A<=M<256.
//! Cache lifetime is the forward/reverse upper-update stack, not a new rail.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::super::super::paired_clean_mcx;

fn cost(k:usize)->isize{if k<2{0}else{2*k as isize-3}}
pub(super) struct Prefix{low:usize,last:Option<usize>}
impl Prefix{
 pub(super) fn new(n:usize)->Option<Self>{
  if std::env::var("Q794_R01_A7_PREFIX").ok().as_deref()!=Some("1"){return None;}
  let mut best=(0isize,0usize);
  for low in 1..=5{let k=7-low;let mut last=None;let mut gain=0;
   for i in 2..n{let v=256-i;if v>=128{continue;}gain+=13-cost(low+2);let key=v>>low;
    if last!=Some(key){gain-=cost(if last.is_none(){k}else{k-1});last=Some(key);}
   }if gain>best.0{best=(gain,low);}
  }(best.0>0).then_some(Self{low:best.1,last:None})
 }
 fn toggle(c:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg,g:&QReg){
  c.x(g);paired_clean_mcx::toggle(c,controls,out,g);c.x(g);
 }
 /// Returns false for untouched high-M endpoint templates. Caller records
 /// this complete span with its existing update, then reverses it literally.
 pub(super) fn upper(&mut self,c:&mut Circuit,m:&[QReg],a7:&QReg,g:&QReg,mask:&QReg,v:usize)->bool{
  assert_eq!(m.len(),8);assert!(v<=254);if v>=128{return false;}
  let mut ids:Vec<_>=m.iter().map(QReg::id).collect();ids.extend([a7.id(),g.id(),mask.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
  let bits=&m[self.low..7];let key=v>>self.low;
  if self.last!=Some(key){
   if let Some(old)=self.last{
    let diff=old^key;let pivot=diff.trailing_zeros()as usize;let mut value=old;
    for b in 0..bits.len(){if b!=pivot&&diff>>b&1!=0{c.cx(&bits[pivot],&bits[b]);if old>>pivot&1!=0{value^=1<<b;}}}
    let cs:Vec<_>=bits.iter().enumerate().filter(|&(b,_)|b!=pivot).map(|(b,q)|(q,value>>b&1!=0)).collect();Self::toggle(c,&cs,a7,g);
    for b in(0..bits.len()).rev(){if b!=pivot&&diff>>b&1!=0{c.cx(&bits[pivot],&bits[b]);}}
   }else{let cs:Vec<_>=bits.iter().enumerate().map(|(b,q)|(q,key>>b&1!=0)).collect();Self::toggle(c,&cs,a7,g);}
   self.last=Some(key);
  }
  let mut cs=vec![(&m[7],false),(a7,true)];cs.extend(m[..self.low].iter().enumerate().map(|(b,q)|(q,v>>b&1!=0)));Self::toggle(c,&cs,mask,g);true
 }
}
