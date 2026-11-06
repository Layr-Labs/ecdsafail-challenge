//! Exact linear QROM with bounded clean workspace and arbitrary dirty bits.
use super::*;
fn mcx(c:&mut Builder,cs:&[QubitId],out:QubitId,dirty:&[QubitId]){
 match cs.len(){0=>c.x(out),1=>c.cx(cs[0],out),2=>c.ccx(cs[0],cs[1],out),n=>{
  assert!(dirty.len()>=n-2);let d=&dirty[..n-2];
  c.ccx(cs[0],cs[1],d[0]);for i in 1..n-2{c.ccx(cs[i+1],d[i-1],d[i]);}c.ccx(cs[n-1],d[n-3],out);
  for i in(1..n-2).rev(){c.ccx(cs[i+1],d[i-1],d[i]);}c.ccx(cs[0],cs[1],d[0]);
  for i in 1..n-2{c.ccx(cs[i+1],d[i-1],d[i]);}c.ccx(cs[n-1],d[n-3],out);for i in(1..n-2).rev(){c.ccx(cs[i+1],d[i-1],d[i]);}
 }}
}
fn tree(c:&mut Builder,input:&[QubitId],depth:usize,prefix:usize,parent:QubitId,dirty:&[QubitId],body:&mut impl FnMut(&mut Builder,usize,Option<QubitId>)){
 if depth==input.len(){body(c,prefix,Some(parent));return;}
 let bit=input[depth];let borrowed=depth<dirty.len();let q=if borrowed{dirty[depth]}else{c.alloc_qubit()};
 c.ccx(parent,bit,q);tree(c,input,depth+1,prefix|(1<<depth),q,dirty,body);
 c.cx(parent,q);tree(c,input,depth+1,prefix,q,dirty,body);c.cx(parent,q);
 if borrowed{c.ccx(parent,bit,q);}else{let m=c.alloc_bit();c.walk_and_marker(q,parent,bit,m);c.hmr(q,m);c.cz_if(parent,bit,m);c.free_bit(m);c.release_clean(q);}
}
fn mcx_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
pub(super) fn plan(n:usize,room:usize)->(usize,usize){
 if n<=room+1{return((1usize<<n).saturating_sub(2),0);}
 (1..=n).map(|j|{let d=n-j;let upper=d.saturating_sub(room);let per=(1usize<<d)+(1usize<<upper)-2;(((1usize<<j)+1)*per+2*(1usize<<j)*mcx_cost(j),j)}).min().unwrap()
}
pub(super) fn visit(c:&mut Builder,input:&[QubitId],room:usize,blocked:&[QubitId],body:&mut impl FnMut(&mut Builder,usize,Option<QubitId>)){
 let(_,j)=plan(input.len(),room);if j==0{super::visit(c,input,0,0,None,body);return;}
 let d=input.len()-j;let upper=d.saturating_sub(room);let needed=1+upper+j.saturating_sub(2);
 let workspace:Vec<_>=c.walk_live().into_iter().filter(|q|!input.contains(q)&&!blocked.contains(q)).take(needed).collect();assert_eq!(workspace.len(),needed);
 let root=workspace[0];let ladder=&workspace[1..1+upper];let scratch=&workspace[1+upper..];
 // The aggregate traversal cancels every term containing an unknown initial
 // root or ladder bit. The controlled traversals leave the selected table.
 tree(c,&input[j..],0,0,root,ladder,&mut |c,lo,q|{for hi in 0..1usize<<j{body(c,hi|(lo<<j),q);}});
 for hi in 0..1usize<<j{
  for i in 0..j{if hi>>i&1==0{c.x(input[i]);}}mcx(c,&input[..j],root,scratch);for i in(0..j).rev(){if hi>>i&1==0{c.x(input[i]);}}
  tree(c,&input[j..],0,0,root,ladder,&mut |c,lo,q|body(c,hi|(lo<<j),q));
  for i in 0..j{if hi>>i&1==0{c.x(input[i]);}}mcx(c,&input[..j],root,scratch);for i in(0..j).rev(){if hi>>i&1==0{c.x(input[i]);}}
 }
}
