//! Closed numeric A/C/S chart on existing rank5+p2, zero new qubits.
//! Public reversible-circuit challenge research; no measurement or real-key work.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{Scan,arithmetic,chart_seed};
#[path="q794_r01_numeric_partial.rs"] mod partial;
#[path="q794_r01_a7_prefix.rs"] pub(crate) mod a7_prefix;
fn partial_enabled()->bool{std::env::var("Q794_R01_NUMERIC_PARTIAL").ok().as_deref()==Some("1")}
fn mode()->usize{let n=std::env::var("Q794_R01_NUMERIC").ok().map(|v|v.parse().unwrap()).unwrap_or(0);assert!(n<=2);n}
pub(super) fn selected(c:&Circuit,n:usize,j:usize)->bool{
 let m=mode();if m==0{return false;}if m==2{return true;}
 let cached=super::super::q794_r01_odd_cache::selected(c,n,j);let mut gain=-((if partial_enabled(){172}else{696})+8isize);
 for i in 2..n{gain-=4;if i<=255&&(i+1)%2==j%2{let h=((i+1)%256)/64;
  let old=if cached&&super::super::q794_r01_odd_cache::eligible(i,j){16}else{16+2*[12,10,12,10][h]};gain+=2*(old-11) as isize;
 }}gain>0
}
fn chart_map()->[usize;64]{
 let ts=super::triples();let mut map=[usize::MAX;64];let mut previous=[usize::MAX;64];
 for(r,t)in ts.iter().enumerate(){map[r]=t[0]+4*t[1]+16*t[2];previous[map[r]]=r;}
 for end in 32..64{let mut first=end;while previous[first]!=usize::MAX{first=previous[first];}map[end]=first;}
 let mut sorted=map;sorted.sort_unstable();assert_eq!(sorted,std::array::from_fn(|i|i));map
}
fn chart_swaps()->Vec<(usize,usize)>{
 let map=chart_map();let mut position:Vec<_>=(0..64).collect();let mut at=position.clone();let mut swaps=Vec::new();
 for input in 0..64{if position[input]==map[input]{continue;}let l=position[input];let r=map[input];let other=at[r];swaps.push((l,r));position[input]=r;position[other]=l;at[l]=other;at[r]=input;}
 assert_eq!(position,map);assert_eq!(swaps.len(),29);swaps
}
fn unpack(c:&mut Circuit,word:&[QReg],dirty:&[QReg]){
 if partial_enabled(){partial::emit(c,word,dirty);return;}
 assert_eq!(word.len(),6);assert!(dirty.len()>=3);
 let mut ids:Vec<_>=word.iter().chain(&dirty[..3]).map(QReg::id).collect();ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
 for(left,right)in chart_swaps(){let diff=left^right;let pivot=diff.trailing_zeros()as usize;let targets:Vec<_>=(0..6).filter(|&i|i!=pivot&&diff>>i&1!=0).collect();let mut value=left;
  for &i in &targets{c.cx(&word[pivot],&word[i]);if left>>pivot&1!=0{value^=1<<i;}}
  let cs:Vec<_>=(0..6).filter(|&i|i!=pivot).map(|i|(&word[i],value>>i&1!=0)).collect();super::gate(c,&cs,&word[pivot],dirty);
  for &i in targets.iter().rev(){c.cx(&word[pivot],&word[i]);}
 }
}
fn lower(s:&Scan<'_>,c:&mut Circuit,sh:&[QReg],i:usize){
 if i>255||(i+1)%2!=s.j%2{return;}let value=(i+1)%256;let parity=((value>>1)^(s.j>>1))&1!=0;
 c.cx(&s.a[0],&s.c[0]);let mut cs=vec![(&s.c[0],parity)];cs.extend((0..4).map(|b|(&s.sm[b],value>>(b+2)&1!=0)));cs.extend((0..2).map(|b|(&sh[b],value>>(b+6)&1!=0)));
 c.x(s.g);super::super::paired_clean_mcx::toggle(c,&cs,s.mask,s.g);c.x(s.g);c.cx(&s.a[0],&s.c[0]);
}
pub(super) fn fused(s:&Scan<'_>,c:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
 assert!(s.cache.is_none());let start=c.b.ops.len();let owned=c.b.next_qubit;let n=s.support_end.min(257);assert!(n>=2);let shift=if s.j&1!=0{0}else{1};
 let word:Vec<_>=s.rank.iter().chain(std::iter::once(s.hs)).map(QReg::borrowed_alias).collect();
 let aa:Vec<_>=s.a.iter().chain(word[..2].iter()).map(QReg::borrowed_alias).collect();
 let cc:Vec<_>=s.c.iter().chain(word[2..4].iter()).map(QReg::borrowed_alias).collect();
 let mut aliases:Vec<_>=word.iter().chain(s.a).chain(s.c).chain(s.sm).chain([s.g,s.mask,s.ha,decision]).map(QReg::id).collect();aliases.sort_unstable();assert!(aliases.windows(2).all(|w|w[0]!=w[1]));
 assert!(s.dirty.iter().all(|q|!aliases.contains(&q.id())));
 s.lower(c,0);s.lower(c,1);let low=c.b.ops[start..].to_vec();
 arithmetic::add(c,s.a,s.c,None,true);chart_seed(c,s.rank,s.a,s.c,s.g,s.mask,s.ha,w1,w2,s.dirty,shift);
 let chart_start=c.b.ops.len();unpack(c,&word,s.dirty);let converter=c.b.ops[chart_start..].to_vec();arithmetic::add(c,&aa,&cc,None,false);
 let mut updates=Vec::new();let mut prefix=a7_prefix::Prefix::new(n);
 for i in 2..n{let at=c.b.ops.len();lower(s,c,&word[4..],i);let value=256-i;let cs:Vec<_>=cc.iter().enumerate().map(|(b,q)|(q,value>>b&1!=0)).collect();
  if !prefix.as_mut().is_some_and(|p|p.upper(c,&cc,&aa[7],s.g,s.mask,value)){c.x(s.g);super::super::paired_clean_mcx::toggle(c,&cs,s.mask,s.g);c.x(s.g);}updates.push(c.b.ops[at..].to_vec());s.carry(c,&w2[258-i],&w1[258-i],false);
 }
 c.cx(s.g,decision);c.ccx(s.g,s.ha,decision);
 for i in (2..n).rev(){s.carry(c,&w2[258-i],&w1[258-i],true);c.cx(s.ha,&w2[258-i]);super::gate(c,&[(s.g,true),(s.mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],s.dirty);c.cx(s.ha,&w2[258-i]);c.b.ops.extend(updates.pop().unwrap().into_iter().rev());}
 arithmetic::add(c,&aa,&cc,None,true);c.b.ops.extend(converter.into_iter().rev());
 chart_seed(c,s.rank,s.a,s.c,s.g,s.mask,s.ha,w1,w2,s.dirty,shift);s.low_update(c,w1,w2,decision,shift);arithmetic::add(c,s.a,s.c,None,false);c.b.ops.extend(low.into_iter().rev());assert_eq!(c.b.next_qubit,owned);
}
