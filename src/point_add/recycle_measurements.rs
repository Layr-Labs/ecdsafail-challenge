use quantum_ecc::circuit::{Op,OperationType as K,QubitId,BitId};
use std::collections::{HashMap,HashSet,BTreeSet};
use sha3::{Digest,Sha3_256};
type E=u32;
// Exact semantic keys for small classical Boolean supports. Large functions
// remain opaque symbols of their actual immutable expressions; no sampling.
#[derive(Clone,Debug,PartialEq,Eq,Hash)]struct SemTruth{atoms:Vec<u32>,table:u64}
impl SemTruth{
 fn mask(n:usize)->u64{if n==6{u64::MAX}else{(1u64<<(1usize<<n))-1}}
 fn complement(&self)->Self{Self{atoms:self.atoms.clone(),table:self.table^Self::mask(self.atoms.len())}}
 fn shrink(mut self)->Self{let mut bit=0;while bit<self.atoms.len(){let n=self.atoms.len();let step=1usize<<bit;let independent=(0..1usize<<n).filter(|r|r&step==0).all(|r|(self.table>>r)&1==(self.table>>(r|step))&1);if independent{let mut out=0u64;for row in 0..1usize<<(n-1){let old=(row&(step-1))|((row&!(step-1))<<1);out|=((self.table>>old)&1)<<row;}self.atoms.remove(bit);self.table=out;}else{bit+=1;}}self}
 fn key(&self)->(Self,u32){let neg=(self.table&1)as u32;if neg==0{(self.clone(),0)}else{(self.complement(),1)}}
}
impl Expr{
 fn semantic(&self,v:u32)->SemTruth{if v<=1{return SemTruth{atoms:vec![],table:v as u64};}let t=&self.truths[(v/2-1)as usize];if v&1==0{t.clone()}else{t.complement()}}
 fn combine_semantic(&self,k:u8,a:u32,b:u32)->Option<SemTruth>{let a=self.semantic(a);let b=self.semantic(b);let mut atoms=a.atoms.clone();atoms.extend_from_slice(&b.atoms);atoms.sort_unstable();atoms.dedup();if atoms.len()>6{return None;}let ap:Vec<_>=a.atoms.iter().map(|v|atoms.binary_search(v).unwrap()).collect();let bp:Vec<_>=b.atoms.iter().map(|v|atoms.binary_search(v).unwrap()).collect();let project=|row:usize,positions:&[usize]|positions.iter().enumerate().fold(0usize,|v,(i,&bit)|v|(((row>>bit)&1)<<i));let mut table=0;for row in 0..1usize<<atoms.len(){let av=(a.table>>project(row,&ap))&1;let bv=(b.table>>project(row,&bp))&1;table|=(if k==1{av&bv}else{av^bv})<<row;}Some(SemTruth{atoms,table}.shrink())}
 fn semantic_node(&mut self,k:u8,a:u32,b:u32)->u32{let summary=self.combine_semantic(k,a,b);if let Some(t)=&summary{if t.atoms.is_empty(){return(t.table&1)as u32;}let(key,neg)=t.key();if let Some(&v)=self.canonical.get(&key){return v^neg;}}let id=self.atom();*self.nodes.last_mut().unwrap()=(k,a,b);if let Some(t)=summary{let(key,neg)=t.key();*self.truths.last_mut().unwrap()=t;self.canonical.insert(key,id^neg);}id}
}

#[derive(Default)]struct Expr{restricting:bool,truths:Vec<SemTruth>,canonical:HashMap<SemTruth,u32>,nodes:Vec<(u8,u32,u32)>,implications:HashMap<(u32,u32),bool>,next:u32,and:HashMap<(u32,u32),u32>,xor:HashMap<(u32,u32),u32>}
impl Expr{
 fn atom(&mut self)->u32{self.next+=2;self.nodes.push((0,0,0));let t=SemTruth{atoms:vec![self.next],table:2};self.truths.push(t.clone());self.canonical.insert(t,self.next);self.next}
 fn and(&mut self,mut a:u32,mut b:u32)->u32{if a==0||b==0{return 0;}if a==1{return b;}if b==1||a==b{return a;}if a==b^1{return 0;}if a>b{std::mem::swap(&mut a,&mut b);}if let Some(&v)=self.and.get(&(a,b)){return v;}if !self.restricting{self.restricting=true;let mut result=None;if let Some(v)=self.cofactor(b,a,6){if v!=b{result=Some(self.and(a,v));}}if result.is_none(){if let Some(v)=self.cofactor(a,b,6){if v!=a{result=Some(self.and(b,v));}}}self.restricting=false;if let Some(v)=result{self.and.insert((a,b),v);return v;}}let v=self.semantic_node(1,a,b);self.and.insert((a,b),v);v}
 fn or(&mut self,a:u32,b:u32)->u32{self.and(a^1,b^1)^1}
 fn xor(&mut self,mut a:u32,mut b:u32)->u32{if a==0{return b;}if b==0{return a;}if a==1{return b^1;}if b==1{return a^1;}if a==b{return 0;}if a==b^1{return 1;}let neg=(a^b)&1;a&=!1;b&=!1;if a>b{std::mem::swap(&mut a,&mut b);}if let Some(&v)=self.xor.get(&(a,b)){return v^neg;}let v=self.semantic_node(2,a,b);self.xor.insert((a,b),v);v^neg}
 fn ite(&mut self,g:u32,new:u32,old:u32)->u32{if g==0||new==old{return old;}if g==1{return new;}if old==0{return self.and(g,new);}if new==0{return self.and(g^1,old);}if old==1{return self.or(g^1,new);}if new==1{return self.or(g,old);}if new==old^1{return self.xor(g,old);}let a=self.and(g,new);let b=self.and(g^1,old);self.or(a,b)}
}
impl Expr{
 fn quick_implies(&self,a:u32,b:u32,depth:usize)->bool{if a==0||b==1||a==b{return true;}if depth==0||a<=1||b==0{return false;}let an=self.nodes[(a/2-1)as usize];if an.0==1{if a&1==0{if self.quick_implies(an.1,b,depth-1)||self.quick_implies(an.2,b,depth-1){return true;}}else if self.quick_implies(an.1^1,b,depth-1)&&self.quick_implies(an.2^1,b,depth-1){return true;}}let bn=self.nodes[(b/2-1)as usize];if bn.0==1{if b&1==0{return self.quick_implies(a,bn.1,depth-1)&&self.quick_implies(a,bn.2,depth-1);}return self.quick_implies(a,bn.1^1,depth-1)||self.quick_implies(a,bn.2^1,depth-1);}false}
 fn implies(&mut self,a:u32,b:u32)->bool{if self.quick_implies(a,b,12){return true;}if let Some(&v)=self.implications.get(&(a,b)){return v;}let root=self.and(a,b^1);let answer=self.zero_truth_table(root);self.implications.insert((a,b),answer);answer}
 fn zero_truth_table(&self,root:u32)->bool{if root<=1{return root==0;}let mut pending=vec![root&!1];let mut visited=BTreeSet::new();let mut atoms=BTreeSet::new();while let Some(id)=pending.pop(){if id<=1||!visited.insert(id){continue;}if visited.len()>4096{return false;}let(k,a,b)=self.nodes[(id/2-1)as usize];if k==0{atoms.insert(id);if atoms.len()>10{return false;}}else{pending.push(a&!1);pending.push(b&!1);}}
  let ord:HashMap<_,_>=atoms.into_iter().enumerate().map(|(i,v)|(v,i)).collect();let cases=1usize<<ord.len();let words=cases.div_ceil(64);let mut table:HashMap<u32,Vec<u64>>=HashMap::new();let get=|lit:u32,table:&HashMap<u32,Vec<u64>>,j:usize|if lit<=1{if lit==1{u64::MAX}else{0}}else{let v=table[&(lit&!1)][j];if lit&1!=0{!v}else{v}};
  for id in visited{let(k,a,b)=self.nodes[(id/2-1)as usize];let mut row=vec![0;words];if k==0{let shift=ord[&id];for assignment in 0..cases{row[assignment/64]|=(((assignment>>shift)&1)as u64)<<(assignment%64);}}else{for j in 0..words{let x=get(a,&table,j);let y=get(b,&table,j);row[j]=if k==1{x&y}else{x^y};}}table.insert(id,row);}
  let last_mask=if cases<64{(1u64<<cases)-1}else{u64::MAX};(0..words).all(|j|get(root,&table,j)&if j+1==words{last_mask}else{u64::MAX}==0)
 }
}
impl Expr{fn cofactor(&mut self,expression:u32,assumed:u32,depth:usize)->Option<u32>{if expression==assumed{return Some(1);}if expression==assumed^1{return Some(0);}if expression<=1||depth==0{return None;}let(k,a,b)=self.nodes[(expression/2-1)as usize];if k==0{return None;}let left=self.cofactor(a,assumed,depth-1);let right=self.cofactor(b,assumed,depth-1);if left.is_none()&&right.is_none(){return None;}let a=left.unwrap_or(a);let b=right.unwrap_or(b);let value=if k==1{self.and(a,b)}else{self.xor(a,b)};Some(value^(expression&1))}}

struct Algebra{inner:Expr}
impl Algebra{fn fresh(&mut self)->E{self.inner.atom()}fn and(&mut self,a:&E,b:&E)->E{self.inner.and(*a,*b)}fn xor(&mut self,a:&E,b:&E)->E{self.inner.xor(*a,*b)}fn select(&mut self,old:&E,new:&E,cond:&E)->E{self.inner.ite(*cond,*new,*old)}}
fn initial_inputs(ops:&[Op],nq:usize,nb:usize,alg:&mut Algebra)->(Vec<E>,Vec<E>){let no=u64::MAX;let(mut q,mut c)=(vec![0;nq],vec![0;nb]);let(mut qs,mut cs)=(HashSet::new(),HashSet::new());for o in ops{if o.kind==K::AppendToRegister{if o.q_target.0!=no&&qs.insert(o.q_target.0){q[o.q_target.0 as usize]=alg.fresh();}if o.c_target.0!=no&&cs.insert(o.c_target.0){c[o.c_target.0 as usize]=alg.fresh();}}}(q,c)}
fn hash(ops:&[Op])->String {
 let mut h=Sha3_256::new();for o in ops {h.update((o.kind as u64).to_le_bytes());
 for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
 format!("{:x}",h.finalize())
}
fn make(k:K,c2:u64,c1:u64,t:u64,ct:u64,cc:u64)->Op {
 let mut o=Op::empty();o.kind=k;o.q_control2=QubitId(c2);o.q_control1=QubitId(c1);o.q_target=QubitId(t);o.c_target=BitId(ct);o.c_condition=BitId(cc);o.validate();o
}
// Convert original persistent scope snapshots to explicit classical conditions.
// Temporary scopes below enclose ONLY one classical assignment and are balanced.
struct FlatGuards{nb:u64,depth_cap:usize,stack:Vec<u64>,work:u64,assignments:usize}
fn maximum_depth(ops:&[Op])->usize{let(mut depth,mut peak)=(0usize,0usize);for o in ops{match o.kind{K::PushCondition=>{depth+=1;peak=peak.max(depth);},K::PopCondition=>{assert!(depth>0);depth-=1;},_=>{}}}assert_eq!(depth,0);peak}
impl FlatGuards{
 fn new(ops:&[Op])->Self{let nb=quantum_ecc::circuit::analyze_ops(ops.iter()).1;let depth_cap=maximum_depth(ops);Self{nb,depth_cap,stack:vec![],work:nb+depth_cap as u64,assignments:0}}
 fn assign_and(&mut self,out:&mut Vec<Op>,dst:u64,a:Option<u64>,b:Option<u64>){let n=u64::MAX;assert!(a!=Some(dst)&&b!=Some(dst));out.push(make(K::BitStore0,n,n,n,dst,n));match(a,b){(None,None)=>out.push(make(K::BitStore1,n,n,n,dst,n)),(Some(bit),None)|(None,Some(bit))=>out.push(make(K::BitStore1,n,n,n,dst,bit)),(Some(a),Some(b))=>{if a==b{out.push(make(K::BitStore1,n,n,n,dst,a));}else{out.push(make(K::PushCondition,n,n,n,n,a));out.push(make(K::BitStore1,n,n,n,dst,b));out.push(make(K::PopCondition,n,n,n,n,n));}}}self.assignments+=1;}
 fn original(&mut self,o:&Op,out:&mut Vec<Op>)->Option<Op>{let n=u64::MAX;if o.kind==K::PushCondition{assert!(self.stack.len()<self.depth_cap);assert_ne!(o.c_condition.0,n);let dst=self.nb+self.stack.len()as u64;self.assign_and(out,dst,self.stack.last().copied(),Some(o.c_condition.0));self.stack.push(dst);return None;}if o.kind==K::PopCondition{self.stack.pop().expect("balanced source");return None;}if matches!(o.kind,K::Register|K::AppendToRegister|K::DebugPrint){return Some(*o);}let parent=self.stack.last().copied();let per=(o.c_condition.0!=n).then_some(o.c_condition.0);let condition=match(parent,per){(None,None)=>n,(Some(bit),None)|(None,Some(bit))=>bit,(Some(a),Some(b))=>{self.assign_and(out,self.work,Some(a),Some(b));self.work}};let mut flat=*o;flat.c_condition=BitId(condition);flat.validate();Some(flat)}
}

fn recycle_emit(ops:&[Op],leases:&[Lease],repair:bool)->Vec<Op>{let nq=quantum_ecc::circuit::analyze_ops(ops.iter()).0;let helpers:Vec<_>=(0..leases.len()).map(|j|nq+j as u64).collect();recycle_emit_named(ops,leases,&helpers,repair)}
// Every nomination and discharge is proved again on the complete original trace.
#[derive(Clone,Debug)]struct Lease{first:usize,last:usize,reset:usize,f:E,g:E,a:usize,b:usize,z:Option<usize>,unitary:Option<(usize,bool)>}
fn recycle_plan(ops:&[Op])->Vec<Lease>{
 let no=u64::MAX;let(nq,nb,_,_)=quantum_ecc::circuit::analyze_ops(ops.iter());let mut alg=Algebra{inner:Expr::default()};let(mut q,mut c)=initial_inputs(ops,nq as usize,nb as usize,&mut alg);let(mut base,mut stack)=(1,vec![]);let mut first=HashMap::<E,usize>::new();let mut pending=Vec::<Lease>::new();let mut consumed=HashSet::new();let mut accepted=vec![];
 for(i,o)in ops.iter().enumerate(){
  if o.kind==K::PushCondition{stack.push(base);base=alg.inner.and(base,c[o.c_condition.0 as usize]);continue;}if o.kind==K::PopCondition{base=stack.pop().unwrap();continue;}
  let g=if o.c_condition.0==no{base}else{alg.inner.and(base,c[o.c_condition.0 as usize])};let(t,a,b,ct)=(o.q_target.0 as usize,o.q_control1.0 as usize,o.q_control2.0 as usize,o.c_target.0 as usize);
  let toggle=match o.kind{K::X=>Some(g),K::CX=>Some(alg.inner.and(q[a],g)),K::CCX=>{let ab=alg.inner.and(q[a],q[b]);let f=alg.inner.and(g,ab);if f>1&&!consumed.contains(&f){if let Some(&j)=first.get(&f){if !pending.iter().any(|p|p.f==f){pending.push(Lease{first:j,last:i,reset:usize::MAX,f,g,a,b,z:None,unitary:None});}}else{first.insert(f,i);}}Some(f)},_=>None};
  if matches!(o.kind,K::R|K::Hmr){if let Some(j)=pending.iter().position(|p|p.f==q[t]){let mut p=pending.remove(j);p.reset=i;p.unitary=Some((t,true));consumed.insert(p.f);accepted.push(p);}}
  if matches!(o.kind,K::R|K::Hmr)&&alg.inner.and(g,q[t])==0{
   let chosen=pending.iter().enumerate().find_map(|(j,p)|{if i-p.last>200000||alg.inner.and(p.f,g^1)!=0{return None;}let ab=alg.inner.and(q[p.a],q[p.b]);if alg.inner.and(p.g,ab)==p.f{return Some((j,None));}q.iter().position(|&v|v==p.f).map(|z|(j,Some(z)))});
   if let Some((j,z))=chosen{let mut p=pending.remove(j);p.reset=i;p.z=z;consumed.insert(p.f);accepted.push(p);}
  }
  pending.retain(|p|i-p.last<=200000);
  match o.kind{K::X|K::CX|K::CCX=>q[t]=alg.inner.xor(q[t],toggle.unwrap()),K::Swap=>{let v=alg.inner.xor(q[a],q[t]);let v=alg.inner.and(g,v);q[a]=alg.inner.xor(q[a],v);q[t]=alg.inner.xor(q[t],v);},K::R|K::Hmr=>{q[t]=alg.inner.and(q[t],g^1);if o.kind==K::Hmr{let r=alg.inner.atom();c[ct]=alg.inner.ite(g,r,c[ct]);}},K::BitInvert=>c[ct]=alg.inner.xor(c[ct],g),K::BitStore0=>c[ct]=alg.inner.and(c[ct],g^1),K::BitStore1=>c[ct]=alg.inner.or(c[ct],g),K::Neg|K::Z|K::CZ|K::CCZ|K::Register|K::AppendToRegister|K::DebugPrint=>{},_=>unreachable!()}
  if matches!(o.kind,K::X|K::CX|K::CCX|K::Swap){let wires=if o.kind==K::Swap{vec![t,a]}else{vec![t]};for wire in wires{if let Some(j)=pending.iter().position(|p|p.f==q[wire]){let mut p=pending.remove(j);p.reset=i;p.unitary=Some((wire,false));consumed.insert(p.f);accepted.push(p);}}}
  if i%1000000==0{eprintln!("RECYCLE_PLAN op={i} accepted={} pending={} nodes={}",accepted.len(),pending.len(),alg.inner.nodes.len());}
 }assert!(stack.is_empty());accepted.sort_by_key(|p|p.first);accepted
}
fn recycle_emit_named(ops:&[Op],leases:&[Lease],helpers:&[u64],repair:bool)->Vec<Op>{assert_eq!(leases.len(),helpers.len());
 if leases.is_empty(){return ops.to_vec();}let no=u64::MAX;let nq=quantum_ecc::circuit::analyze_ops(ops.iter()).0;let mut flat=FlatGuards::new(ops);let saved_base=flat.work+1;let random_bit=saved_base+leases.len()as u64;let phase_bit=random_bit+1;
 let mut events=HashMap::<usize,(usize,u8)>::new();for(j,p)in leases.iter().enumerate(){assert!(p.first<p.last&&p.last<=p.reset);for(i,k)in[(p.first,0),(p.last,1),(p.reset,2)]{if k==2&&p.reset==p.last{assert!(p.unitary.is_some());continue;}assert!(events.insert(i,(j,k)).is_none());}}
 let mut out=Vec::with_capacity(ops.len()+leases.len()*20);
 for(i,o)in ops.iter().enumerate(){let Some(mut v)=flat.original(o,&mut out)else{continue;};if let Some(&(j,kind))=events.get(&i){let p=&leases[j];let helper=helpers[j];match kind{
  0=>{assert_eq!(v.kind,K::CCX);v.q_target=QubitId(helper);v.validate();out.push(v);out.push(make(K::CX,no,helper,o.q_target.0,no,no));},
  1=>{assert_eq!(v.kind,K::CCX);let cc=(v.c_condition.0!=no).then_some(v.c_condition.0);flat.assign_and(&mut out,saved_base+j as u64,cc,None);out.push(make(K::CX,no,helper,o.q_target.0,no,no));if p.reset==i{let(wire,before)=p.unitary.unwrap();assert!(!before);if repair{out.push(make(K::CX,no,wire as u64,helper,no,no));}}},
  2=>{if let Some((wire,before))=p.unitary{if before&&repair{out.push(make(K::CX,no,wire as u64,helper,no,no));}out.push(v);if !before&&repair{out.push(make(K::CX,no,wire as u64,helper,no,no));}continue;}assert!(matches!(v.kind,K::R|K::Hmr));v.q_target=QubitId(helper);if v.kind==K::R{v.kind=K::Hmr;v.c_target=BitId(random_bit);}let r=v.c_target.0;v.validate();out.push(v);flat.assign_and(&mut out,phase_bit,Some(saved_base+j as u64),Some(r));if repair{if let Some(z)=p.z{out.push(make(K::Z,no,no,z as u64,no,r));}else{out.push(make(K::CZ,no,p.a as u64,p.b as u64,no,phase_bit));}}},_=>unreachable!()
 }}else{out.push(v);}}
 assert!(flat.stack.is_empty());out
}

#[cfg(test)]mod recycle_tests{use super::*;use quantum_ecc::sim::Simulator;use sha3::digest::XofReader;
 struct W{v:u64,at:usize}impl XofReader for W{fn read(&mut self,b:&mut[u8]){b.copy_from_slice(&self.v.rotate_left(self.at as u32%64).to_le_bytes());self.at+=1;}}
 fn fixture(hmr:bool,guarded:bool)->Vec<Op>{let n=u64::MAX;let mut out=vec![];for q in 0..4{let mut o=Op::empty();o.kind=K::AppendToRegister;o.q_target=QubitId(q);o.r_target=quantum_ecc::circuit::RegisterId(0);out.push(o);}for c in 0..2{let mut o=Op::empty();o.kind=K::AppendToRegister;o.c_target=BitId(c);o.r_target=quantum_ecc::circuit::RegisterId(1);out.push(o);}for target in[2,3]{if guarded{out.push(make(K::PushCondition,n,n,n,n,0));}out.push(make(K::CCX,0,1,target,n,n));if guarded{out.push(make(K::PopCondition,n,n,n,n,n));}}out.push(if hmr{make(K::Hmr,n,n,4,0,n)}else{make(K::R,n,n,4,n,n)});out}
 fn compare(ops:&[Op],want_lease:bool,check_fault:bool){let p=recycle_plan(ops);assert_eq!(p.len(),usize::from(want_lease));let out=recycle_emit(ops,&p,true);let bad=recycle_emit(ops,&p,false);let(nq,nb,_,_)=quantum_ecc::circuit::analyze_ops(ops.iter());let(nq2,nb2,_,_)=quantum_ecc::circuit::analyze_ops(out.iter());let mut detected=false;
 for v in[0,u64::MAX,0xa55a_dd33_ff00_1188,0x1248_69ac_bdf0_7531]{let(mut ra,mut rb,mut rc)=(W{v,at:0},W{v,at:0},W{v,at:0});let(mut a,mut b,mut c)=(Simulator::new(nq as usize,nb as usize,&mut ra),Simulator::new(nq2 as usize,nb2 as usize,&mut rb),Simulator::new(nq2 as usize,nb2 as usize,&mut rc));let registered:HashSet<_>=ops.iter().filter(|o|o.kind==K::AppendToRegister&&o.q_target.0!=u64::MAX).map(|o|o.q_target.0 as usize).collect();for lane in 0..64{for &q in &registered{a.qubits[q]|=(((lane>>q)&1)as u64)<<lane;}for bit in 0..2{a.bits[bit]|=(((lane>>(bit+4))&1)as u64)<<lane;}}for s in[&mut b,&mut c]{s.qubits[..nq as usize].copy_from_slice(&a.qubits);s.bits[..nb as usize].copy_from_slice(&a.bits);}a.apply_iter(ops.iter());b.apply_iter(out.iter());c.apply_iter(bad.iter());assert_eq!(a.qubits,b.qubits[..nq as usize]);assert!(b.qubits[nq as usize..].iter().all(|&q|q==0));assert_eq!(a.bits,b.bits[..nb as usize]);assert_eq!(a.phase,b.phase);if want_lease{assert_eq!(a.stats.toffoli_gates-b.stats.toffoli_gates,if ops.iter().any(|o|o.kind==K::PushCondition){32}else{64});}else{assert_eq!(a.stats,b.stats);}detected|=a.phase!=c.phase||c.qubits[nq as usize..].iter().any(|&v|v!=0);drop((a,b,c));assert_eq!(ra.at,rb.at);assert_eq!(ra.at,rc.at);}if check_fault{assert!(detected,"missing CZ/Z phase repair must be detected");}}
 #[test]fn original_r_recycles_same_word_for_all_basis_states_and_phase_fault_is_detected(){compare(&fixture(false,false),true,true);}
 #[test]fn original_hmr_preserves_classical_outputs_and_rng(){compare(&fixture(true,false),true,true);}
 #[test]fn sibling_scope_captured_guard_survives_mutation_and_hmr_alias(){let n=u64::MAX;let mut ops=fixture(true,true);let j=ops.len()-1;ops.insert(j,make(K::BitInvert,n,n,n,0,n));compare(&ops,true,true);}
 #[test]fn reset_condition_may_alias_its_hmr_classical_output(){let mut ops=fixture(true,true);ops.last_mut().unwrap().c_condition=BitId(0);compare(&ops,true,true);}
 #[test]fn dirty_donor_is_rejected(){let n=u64::MAX;let mut ops=fixture(false,false);let j=ops.len()-1;ops.insert(j,make(K::X,n,n,4,n,n));compare(&ops,false,false);}
 #[test]fn nonimplied_reset_guard_is_rejected(){let mut ops=fixture(true,true);ops.last_mut().unwrap().c_condition=BitId(1);compare(&ops,false,false);}
 #[test]fn changed_current_control_product_is_rejected(){let n=u64::MAX;let mut ops=fixture(false,false);let j=ops.len()-1;ops.insert(j,make(K::X,n,n,0,n,n));compare(&ops,false,false);}
 #[test]fn changed_controls_with_exact_product_invariance_are_accepted(){let n=u64::MAX;let mut ops=fixture(false,true);let j=ops.len()-1;ops.splice(j..j,[make(K::X,n,n,0,n,n),make(K::CX,n,1,0,n,n)]);compare(&ops,true,true);}
 #[test]fn exact_original_wire_phase_alias_survives_changed_last_controls(){let n=u64::MAX;let mut ops=fixture(false,false);ops.retain(|o|!(o.kind==K::AppendToRegister&&o.q_target.0==2));let j=ops.len()-1;ops.insert(j,make(K::X,n,n,0,n,n));let p=recycle_plan(&ops);assert_eq!(p.len(),1);assert_eq!(p[0].z,Some(2));compare(&ops,true,true);}

 #[test]fn zero_last_target_accepts_immediate_free_unitary_cleanup_and_fault_leaves_dirty_cache(){let mut ops=fixture(false,false);ops.retain(|o|!(o.kind==K::AppendToRegister&&o.q_target.0==3));let p=recycle_plan(&ops);assert_eq!(p.len(),1);assert_eq!(p[0].reset,p[0].last);assert_eq!(p[0].unitary,Some((3,false)));compare(&ops,true,true);}
 #[test]fn later_source_alias_allows_cleanup_before_a_nonzero_measurement(){let n=u64::MAX;let mut ops=fixture(false,false);ops.retain(|o|!(o.kind==K::AppendToRegister&&o.q_target.0==2));let j=ops.len()-1;ops[j]=make(K::R,n,n,2,n,n);let p=recycle_plan(&ops);assert_eq!(p.len(),1);assert_eq!(p[0].unitary,Some((2,true)));compare(&ops,true,true);}

}
// A fixed original wire may hold a cache only if it is proved zero at the
// first use and has NO original quantum read, write or phase touch through
// discharge. Metadata is not a quantum touch. Overlapping loans cannot alias.
fn quantum_touches(o:&Op)->Vec<usize>{match o.kind{
 K::X|K::Z|K::R|K::Hmr=>vec![o.q_target.0 as usize],
 K::CX|K::CZ|K::Swap=>vec![o.q_control1.0 as usize,o.q_target.0 as usize],
 K::CCX|K::CCZ=>vec![o.q_control2.0 as usize,o.q_control1.0 as usize,o.q_target.0 as usize],_=>vec![]}}
fn select_donor(q:&[E],touches:&[Vec<usize>],busy:&[Option<usize>],first:usize,end:usize)->Option<usize>{
 (0..q.len()).find(|&d|q[d]==0&&busy[d].map_or(true,|e|e<first)&&{let at=touches[d].partition_point(|&i|i<first);touches[d].get(at).map_or(true,|&i|i>end)})
}
fn borrowed_plan(ops:&[Op],leases:&[Lease])->(Vec<Lease>,Vec<u64>){
 let no=u64::MAX;let(nq,nb,_,_)=quantum_ecc::circuit::analyze_ops(ops.iter());let mut touches=vec![vec![];nq as usize];for(i,o)in ops.iter().enumerate(){for d in quantum_touches(o){touches[d].push(i);}}
 let mut alg=Algebra{inner:Expr::default()};let(mut q,mut c)=initial_inputs(ops,nq as usize,nb as usize,&mut alg);let(mut base,mut stack)=(1,vec![]);let mut busy=vec![None;nq as usize];let mut accepted=vec![];let mut donors=vec![];let mut next=0;
 for(i,o)in ops.iter().enumerate(){
  if next==leases.len(){break;}
  if i==leases[next].first{let p=&leases[next];if let Some(d)=select_donor(&q,&touches,&busy,p.first,p.reset){busy[d]=Some(p.reset);accepted.push(p.clone());donors.push(d as u64);}next+=1;}
  if o.kind==K::PushCondition{stack.push(base);base=alg.inner.and(base,c[o.c_condition.0 as usize]);continue;}if o.kind==K::PopCondition{base=stack.pop().unwrap();continue;}
  let g=if o.c_condition.0==no{base}else{alg.inner.and(base,c[o.c_condition.0 as usize])};let(t,a,b,ct)=(o.q_target.0 as usize,o.q_control1.0 as usize,o.q_control2.0 as usize,o.c_target.0 as usize);
  match o.kind{K::X=>q[t]=alg.inner.xor(q[t],g),K::CX=>{let v=alg.inner.and(q[a],g);q[t]=alg.inner.xor(q[t],v);},K::CCX=>{let v=alg.inner.and(q[a],q[b]);let v=alg.inner.and(v,g);q[t]=alg.inner.xor(q[t],v);},K::Swap=>{let v=alg.inner.xor(q[a],q[t]);let v=alg.inner.and(g,v);q[a]=alg.inner.xor(q[a],v);q[t]=alg.inner.xor(q[t],v);},K::R|K::Hmr=>{q[t]=alg.inner.and(q[t],g^1);if o.kind==K::Hmr{let r=alg.inner.atom();c[ct]=alg.inner.ite(g,r,c[ct]);}},K::BitInvert=>c[ct]=alg.inner.xor(c[ct],g),K::BitStore0=>c[ct]=alg.inner.and(c[ct],g^1),K::BitStore1=>c[ct]=alg.inner.or(c[ct],g),K::Neg|K::Z|K::CZ|K::CCZ|K::Register|K::AppendToRegister|K::DebugPrint=>{},_=>unreachable!()}
  if i%1000000==0{eprintln!("BORROW_ORIGINAL_ZERO op={i} leases={} candidates={} nodes={}",accepted.len(),next,alg.inner.nodes.len());}
 }assert_eq!(next,leases.len());(accepted,donors)
}

#[cfg(test)]mod borrowed_wire_tests{use super::*;use quantum_ecc::sim::Simulator;use sha3::digest::XofReader;
 struct W(u64);impl XofReader for W{fn read(&mut self,b:&mut[u8]){b.copy_from_slice(&self.0.to_le_bytes());}}
 fn fixture()->Vec<Op>{let n=u64::MAX;let mut ops=vec![];for q in 0..3{let mut o=Op::empty();o.kind=K::AppendToRegister;o.q_target=QubitId(q);o.r_target=quantum_ecc::circuit::RegisterId(0);ops.push(o);}ops.extend([make(K::CCX,0,1,2,n,n),make(K::CCX,0,1,3,n,n),make(K::R,n,n,4,n,n)]);ops}
 #[test]fn existing_zero_wire_can_hold_exact_cache_at_unchanged_width(){let ops=fixture();let raw=recycle_plan(&ops);let(p,d)=borrowed_plan(&ops,&raw);assert_eq!(d,vec![4]);assert_eq!(p.len(),1);let out=recycle_emit_named(&ops,&p,&d,true);let(nq,nb,_,_)=quantum_ecc::circuit::analyze_ops(ops.iter());let(nq2,nb2,_,_)=quantum_ecc::circuit::analyze_ops(out.iter());assert_eq!(nq,nq2);for pattern in[0,u64::MAX,0xa55a_dd33_ff00_1188]{let(mut ra,mut rb)=(W(pattern),W(pattern));let(mut a,mut b)=(Simulator::new(nq as usize,nb as usize,&mut ra),Simulator::new(nq2 as usize,nb2 as usize,&mut rb));for lane in 0..64{for q in 0..3{a.qubits[q]|=(((lane>>q)&1)as u64)<<lane;}}b.qubits.clone_from(&a.qubits);a.apply_iter(ops.iter());b.apply_iter(out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.stats.toffoli_gates-b.stats.toffoli_gates,64);}}
 #[test]fn even_a_zero_control_source_touch_inside_loan_prevents_borrowing(){let n=u64::MAX;let mut ops=fixture();ops.insert(4,make(K::CX,n,4,0,n,n));let raw=recycle_plan(&ops);assert_eq!(raw.len(),1);assert!(borrowed_plan(&ops,&raw).0.is_empty());}
 #[test]fn nonzero_original_wire_is_never_a_zero_donor(){let n=u64::MAX;let mut ops=fixture();ops.insert(3,make(K::X,n,n,4,n,n));let raw=recycle_plan(&ops);assert_eq!(raw.len(),1);assert!(borrowed_plan(&ops,&raw).0.is_empty());}
 #[test]fn donor_occupancy_and_inclusive_original_phase_touches_are_enforced(){let q=vec![0];let idle=vec![vec![]];assert_eq!(select_donor(&q,&idle,&[None],10,20),Some(0));assert_eq!(select_donor(&q,&idle,&[Some(20)],15,30),None);assert_eq!(select_donor(&q,&idle,&[Some(20)],21,30),Some(0));assert_eq!(select_donor(&q,&[vec![20]],&[None],10,20),None);let op=make(K::Z,u64::MAX,u64::MAX,0,u64::MAX,u64::MAX);assert_eq!(quantum_touches(&op),vec![0]);}
}
#[cfg(test)]mod semantic_algebra_controls{use super::*;
 #[test]fn distributivity_and_unused_support_are_exact(){let mut e=Expr::default();let a=e.atom();let b=e.atom();let ab=e.and(a,b);let anb=e.and(a,b^1);assert_eq!(e.xor(ab,anb),a);let or=e.or(a,b);assert_eq!(e.and(or,a),a);assert_ne!(or,a);}
 #[test]fn above_six_atom_cofactor_has_disabled_negative_control(){fn run(enabled:bool)->(u32,u32){let mut e=Expr::default();e.restricting=!enabled;let mut g=1;let mut old=1;for _ in 0..6{let a=e.atom();g=e.and(g,a);let b=e.atom();old=e.and(old,b);}assert_eq!(e.semantic(g).atoms.len(),6);assert_eq!(e.semantic(old).atoms.len(),6);let r=e.atom();let v=e.ite(g,r,old);let actual=e.and(g,v);let expected=e.and(g,r);(actual,expected)}let no=run(false);assert_ne!(no.0,no.1);let yes=run(true);assert_eq!(yes.0,yes.1);}
 #[test]fn complete_six_atom_expression_truths_match_original_functions(){fn get(e:&Expr,v:u32,assignment:usize,atoms:&[u32])->bool{if v<=1{return v==1;}let(k,a,b)=e.nodes[(v/2-1)as usize];let value=match k{0=>assignment>>atoms.iter().position(|&a|a==v&!1).unwrap()&1!=0,1=>get(e,a,assignment,atoms)&get(e,b,assignment,atoms),_=>get(e,a,assignment,atoms)^get(e,b,assignment,atoms)};value^(v&1!=0)}let mut e=Expr::default();let atoms:Vec<_>=(0..6).map(|_|e.atom()).collect();let mut pool=atoms.clone();let mut seed=0xa8d7135f23649b01u64;for _ in 0..500{seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);let(a,b,g)=(pool[seed as usize%pool.len()],pool[(seed>>17)as usize%pool.len()],pool[(seed>>33)as usize%pool.len()]);let kind=seed%3;let v=match kind{0=>e.and(a,b),1=>e.xor(a,b),_=>e.ite(g,a,b)};for assignment in 0..64{let(a,b,g)=(get(&e,a,assignment,&atoms),get(&e,b,assignment,&atoms),get(&e,g,assignment,&atoms));let want=match kind{0=>a&b,1=>a^b,_=>if g{a}else{b}};assert_eq!(get(&e,v,assignment,&atoms),want);}pool.push(v);if pool.len()>64{pool.remove(6);}}}
}

pub(super)const IDENTITY_NONCE:u64=142;
fn strip_identity_tail(mut ops:Vec<Op>)->Vec<Op>{let n=u64::MAX;assert!(ops.len()>=96);let end=ops.len()-96;for pair in ops[end..].chunks_exact(2){assert_eq!(pair[0],pair[1]);let o=pair[0];assert_eq!(o.kind,K::X);assert!(o.q_target.0<2);assert_eq!([o.q_control2.0,o.q_control1.0,o.c_target.0,o.c_condition.0,o.r_target.0],[n;5]);}ops.truncate(end);ops}
pub(super)fn run(ops:Vec<Op>)->Vec<Op>{assert_eq!(ops.len(),10995456);assert_eq!(hash(&ops),"373e44f24e185dd662b59a4ff683555b66a05c9995ff2684eefb6723446100cc","Exact official FFE parent binding");let nominations=recycle_plan(&ops);let(leases,donors)=borrowed_plan(&ops,&nominations);assert_eq!(donors,vec![1376,1377,1376,1384,1384,1384,1385,1384,1384,1384,1384,1385,1384]);let triples:Vec<_>=leases.iter().map(|p|(p.first,p.last,p.reset)).collect();assert_eq!(triples,vec![(5184983,5390191,5390191),(5232928,5246880,5246880),(5860757,5875383,5875383),(7392534,7394064,7394064),(7407948,7409478,7409478),(7423362,7424892,7424892),(7423366,7424901,7424901),(7438776,7440306,7440306),(7454190,7455720,7455720),(7469604,7471134,7471134),(7485018,7486548,7486548),(7485022,7486557,7486557),(7500432,7501962,7501962)]);let out=recycle_emit_named(&ops,&leases,&donors,true);assert_eq!(hash(&out),"4d22fd4af8ca8044063b8438e10b744e672557a2cbc0ff2aff354d3501881609","Complete native18/fresh48 protected qualified emitter binding");let mut out=strip_identity_tail(out);assert!(IDENTITY_NONCE<(1u64<<48));for bit in 0..48{let o=make(K::X,u64::MAX,u64::MAX,(IDENTITY_NONCE>>bit)&1,u64::MAX,u64::MAX);out.extend([o,o]);}eprintln!("EXACT_ORIGINAL_MEASUREMENT_RECYCLE leases=13 unitary_cleanup no_new_random_word nonce={IDENTITY_NONCE}");out}
#[cfg(test)]mod finished_tail_tests{use super::*;fn tail(n:u64)->Vec<Op>{let mut out=vec![];for bit in 0..48{let o=make(K::X,u64::MAX,u64::MAX,(n>>bit)&1,u64::MAX,u64::MAX);out.extend([o,o]);}out}
#[test]fn all_tail_bits_are_checked(){for n in[0,261,(1u64<<48)-1]{assert!(strip_identity_tail(tail(n)).is_empty());}}
#[test]#[should_panic]fn mismatched_pair_is_rejected(){let mut x=tail(0);x[95].q_target=QubitId(1);strip_identity_tail(x);}
#[test]#[should_panic]fn nonidentity_data_qubit_is_rejected(){let mut x=tail(0);x[94].q_target=QubitId(2);x[95].q_target=QubitId(2);strip_identity_tail(x);}}
