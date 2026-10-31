//! Exact XOR lookup using an arbitrary borrowed array and a select/swap network.
use super::*;
fn eval(tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],key:usize)->u16{
 let mut ix=0;loop{let(k,v,a,b)=tree[ix];match k{0=>return v,1=>ix=if key>>v&1==0{a}else{b}as usize,2=>{let mut z=v;for &(i,x) in &terms[a as usize..b as usize]{if key>>i&1!=0{z^=x;}}return z;},_=>unreachable!()}}
}
fn sparse_cost(tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],ix:usize,root:bool,phase:bool)->usize{
 let(k,_,a,b)=tree[ix];match k{0=>0,1=>(if root{0}else{2})+sparse_cost(tree,terms,a as usize,false,phase)+sparse_cost(tree,terms,b as usize,false,phase),2=>{
  if root||phase{return 0;}let mut basis=[0u16;16];let mut rank=0;for &(_,mut x) in &terms[a as usize..b as usize]{for j in(0..16).rev(){if x>>j&1!=0{if basis[j]==0{basis[j]=x;rank+=1;break;}x^=basis[j];}}}rank
 },_=>unreachable!()}
}
fn visit(c:&mut Builder,input:&[QubitId],depth:usize,prefix:usize,ctl:Option<QubitId>,body:&mut impl FnMut(&mut Builder,usize,Option<QubitId>)){
 if depth==input.len(){body(c,prefix,ctl);return;}let bit=input[depth];if let Some(parent)=ctl{let q=c.alloc_qubit();c.ccx(parent,bit,q);visit(c,input,depth+1,prefix|(1<<depth),Some(q),body);c.cx(parent,q);visit(c,input,depth+1,prefix,Some(q),body);c.cx(parent,q);let m=c.alloc_bit();c.walk_and_marker(q,parent,bit,m);c.hmr(q,m);c.cz_if(parent,bit,m);c.free_bit(m);c.release_clean(q);}else{visit(c,input,depth+1,1<<depth,Some(bit),body);c.x(bit);visit(c,input,depth+1,0,Some(bit),body);c.x(bit);}
}
fn copy(c:&mut Builder,low:&[QubitId],pool:&[QubitId],w:usize,out:&[QubitId],phase:bool){
 visit(c,low,0,0,None,&mut |c,j,ctl|{if j==0{return;}let q=ctl.unwrap();for bit in 0..w{if phase{c.cz(q,pool[j-1]);}else{c.ccx(q,pool[(j-1)*w+bit],out[bit]);}}});
}
fn bulk(c:&mut Builder,high:&[QubitId],pool:&[QubitId],w:usize,k:usize,table:&[u16],out:&[QubitId],ms:Option<&[crate::circuit::BitId]>,base:Option<&[u16]>){
 visit(c,high,0,0,None,&mut |c,hi,ctl|{
  let first=table[hi<<k];if let Some(base)=base{let first=base[hi<<k];if let Some(ms)=ms{for (bit,&m) in ms.iter().enumerate(){if first>>bit&1!=0{if let Some(q)=ctl{c.z_if(q,m);}else{let q=c.alloc_qubit();c.x(q);c.z_if(q,m);c.x(q);c.release_clean(q);}}}}else{for bit in 0..w{if first>>bit&1!=0{if let Some(q)=ctl{c.cx(q,out[bit]);}else{c.x(out[bit]);}}}}}
  for j in 1..1usize<<k{let value=table[(hi<<k)|j]^first;if let Some(ms)=ms{for (bit,&m) in ms.iter().enumerate(){if value>>bit&1!=0{c.push_condition(m);if let Some(q)=ctl{c.cx(q,pool[j-1]);}else{c.x(pool[j-1]);}c.pop_condition();}}}else{for bit in 0..w{if value>>bit&1!=0{if let Some(q)=ctl{c.cx(q,pool[(j-1)*w+bit]);}else{c.x(pool[(j-1)*w+bit]);}}}}}
 });
}
pub(super) fn lookup(c:&mut Builder,input:&[QubitId],out:&[QubitId],ms:Option<&[crate::circuit::BitId]>,tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)])->bool{
 let mut indices=Vec::new();for &(kind,v,a,b)in tree{if kind==1{indices.push(v as usize);}if kind==2{indices.extend(terms[a as usize..b as usize].iter().map(|x|x.0));}}indices.sort_unstable();indices.dedup();let n=indices.len();if n<2{return false;}
 let inputs:Vec<_>=indices.iter().map(|&i|input[i]).collect();let table:Vec<_>=(0..1usize<<n).map(|x|{let key=indices.iter().enumerate().fold(0,|v,(j,&i)|v|(((x>>j)&1)<<i));eval(tree,terms,key)}).collect();let value_width=(16-table.iter().copied().max().unwrap().leading_zeros())as usize;if value_width==0{return false;}assert!(value_width<=if let Some(ms)=ms{ms.len()}else{out.len()});let phase=ms.is_some();let w=if phase{1}else{value_width};
 let pool:Vec<_>=c.walk_live().into_iter().filter(|q|!input.contains(q)&&!out.contains(q)).collect();let best=(1..n).filter(|&k|((1usize<<k)-1)*w<=pool.len()).map(|k|(2*((1usize<<(n-k))-2)+2*((1usize<<k)-2)+if phase{0}else{2*((1usize<<k)-1)*w},k)).min();let Some((cost,k))=best else{return false;};if cost>=sparse_cost(tree,terms,0,true,phase){return false;}
 let pool=&pool[..((1usize<<k)-1)*w];copy(c,&inputs[..k],pool,w,out,phase);bulk(c,&inputs[k..],pool,w,k,&table,out,ms,Some(&table));copy(c,&inputs[..k],pool,w,out,phase);bulk(c,&inputs[k..],pool,w,k,&table,out,ms,None);true
}

// The borrowed array remains loaded only across arithmetic on excluded wires.
pub(super) struct Pair{inputs:Vec<QubitId>,pool:Vec<QubitId>,w:usize,k:usize,first:Vec<u16>,second:Vec<u16>}
pub(super) fn pair(c:&mut Builder,input:&[QubitId],out:&[QubitId],blocked:&[QubitId],f:(&[(u8,u16,u32,u32)],&[(usize,u16)]),g:(&[(u8,u16,u32,u32)],&[(usize,u16)]))->Option<Pair>{
 let mut indices=Vec::new();for(tree,terms)in[f,g]{for &(kind,v,a,b)in tree{if kind==1{indices.push(v as usize);}if kind==2{indices.extend(terms[a as usize..b as usize].iter().map(|x|x.0));}}}indices.sort_unstable();indices.dedup();let n=indices.len();if n<2{return None;}
 let inputs:Vec<_>=indices.iter().map(|&i|input[i]).collect();let values=|tree,terms|(0..1usize<<n).map(|x|{let key=indices.iter().enumerate().fold(0,|v,(j,&i)|v|(((x>>j)&1)<<i));eval(tree,terms,key)}).collect::<Vec<u16>>();let first=values(f.0,f.1);let second=values(g.0,g.1);let w=(16-first.iter().chain(&second).copied().max().unwrap().leading_zeros())as usize;if w==0{return None;}assert!(w<=out.len());
 let pool:Vec<_>=c.walk_live().into_iter().filter(|q|!input.contains(q)&&!out.contains(q)&&!blocked.contains(q)).collect();let best=(1..n).filter(|&k|((1usize<<k)-1)*w<=pool.len()).map(|k|(3*((1usize<<(n-k))-2)+4*((1usize<<k)-2)+4*((1usize<<k)-1)*w,k)).min();let(cost,k)=best?;
 let independent=|tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],v:&[u16]|{let bits=(16-v.iter().copied().max().unwrap().leading_zeros())as usize;if bits==0{return 0;}let dirty=(1..n).filter(|&k|((1usize<<k)-1)*bits<=pool.len()).map(|k|2*((1usize<<(n-k))-2)+2*((1usize<<k)-2)+2*((1usize<<k)-1)*bits).min().unwrap_or(usize::MAX);dirty.min(sparse_cost(tree,terms,0,true,false))};
 if cost>=independent(f.0,f.1,&first)+independent(g.0,g.1,&second){return None;}
 Some(Pair{inputs,pool:pool[..((1usize<<k)-1)*w].to_vec(),w,k,first,second})
}
impl Pair{
 pub(super) fn start(&self,c:&mut Builder,out:&[QubitId]){copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&self.first,out,None,Some(&self.first));copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);}
 pub(super) fn finish(self,c:&mut Builder,out:&[QubitId]){let delta:Vec<_>=self.first.iter().zip(&self.second).map(|(a,b)|a^b).collect();bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&delta,out,None,Some(&self.second));copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&self.second,out,None,None);copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);}
}
