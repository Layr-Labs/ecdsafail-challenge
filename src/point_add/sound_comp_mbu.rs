//! Exact, conservative measurement cleanup of the frozen M3 op stream.
//! Select a CCX only after an exact Boolean proof establishes
//! target = (control_a AND control_b) XOR L, where L is zero, one or another
//! retained wire. X-basis demolition, conditioned CZ plus exact linear-phase
//! repair, and Clifford restoration of L give the same isometry without a
//! Toffoli in the repair. No arithmetic step or register width is changed.
use super::inverse::payload::point::{Micro,NONE};
use std::{collections::HashMap,fs::File,io::{Read,Write,Seek,SeekFrom,BufReader,BufWriter},path::Path};
pub const MBU_AND:u16=24;
pub const MBU_COPY:u16=25;
pub const MBU_ONE:u16=26;
#[derive(Clone,Copy,Debug)]
pub enum Restore {Zero,One,Copy(u16)}
#[derive(Clone,Copy)]
struct Node{kind:u8,a:u32,b:u32}
#[derive(Clone,Copy)]
struct EncoderCheck {step:usize,w:[u16;6]}
pub struct Proof {
    codec:Option<EncoderCheck>,pub codec_facts:u64,pub anf_facts:u64,cut:Vec<u32>,
    nodes:Vec<Node>,intern:HashMap<(u8,u32,u32),u32>,q:Vec<u32>,class:HashMap<u16,u32>,global:u16,
    live:HashMap<u32,u16>,budget:usize,pub epochs:u64,pub peak_nodes:usize,
}
impl Proof {
    pub fn new(qubits:usize,ports:usize,global:u16,budget:usize)->Self {
        let mut s=Self{codec:None,codec_facts:0,anf_facts:0,cut:vec![0;qubits],nodes:vec![Node{kind:0,a:0,b:0},Node{kind:0,a:1,b:0}],intern:HashMap::new(),q:vec![0;qubits],class:HashMap::new(),global,live:HashMap::new(),budget,epochs:0,peak_nodes:2};
        for i in 0..ports{s.q[i]=s.variable();s.live.insert(s.q[i],i as u16);}s
    }
    fn variable(&mut self)->u32{let id=self.nodes.len() as u32;self.nodes.push(Node{kind:1,a:0,b:0});id}
    fn node(&mut self,kind:u8,a:u32,b:u32)->u32 {
        let key=(kind,a.min(b),a.max(b));if let Some(&id)=self.intern.get(&key){return id;}
        let id=self.nodes.len() as u32;self.nodes.push(Node{kind,a:key.1,b:key.2});self.intern.insert(key,id);id
    }
    fn xor(&mut self,a:u32,b:u32)->u32 {
        if a==b{return 0;}if a==0{return b;}if b==0{return a;}
        let x=self.nodes[a as usize];if x.kind==2{if x.a==b{return x.b;}if x.b==b{return x.a;}}
        let x=self.nodes[b as usize];if x.kind==2{if x.a==a{return x.b;}if x.b==a{return x.a;}}
        self.node(2,a,b)
    }
    fn and(&mut self,a:u32,b:u32)->u32 {
        if a==0||b==0{return 0;}if a==1{return b;}if b==1||a==b{return a;}
        self.node(3,a,b)
    }
    fn condition(&mut self,c:u16)->u32 {
        if c==NONE||c==self.global{return 1;}
        if let Some(&id)=self.class.get(&c){return id;}let id=self.variable();self.class.insert(c,id);id
    }
    /// Retain a bounded exact DAG neighborhood; replace anything outside it by
    /// a fresh unconstrained variable. This ONLY forgets proof information:
    /// each retained relation remains exact and no physical bit/gate is dropped.
    fn forget(&mut self){
        self.peak_nodes=self.peak_nodes.max(self.nodes.len());self.epochs+=1;self.cut.fill(0);
        let old=std::mem::replace(&mut self.nodes,vec![Node{kind:0,a:0,b:0},Node{kind:0,a:1,b:0}]);
        let old_q=self.q.clone();let mut old_c:Vec<_>=self.class.iter().map(|(&c,&id)|(c,id)).collect();old_c.sort_unstable();
        self.intern.clear();self.class.clear();let mut map=HashMap::from([(0u32,0u32),(1,1)]);
        for(c,id)in old_c{let n=if let Some(&x)=map.get(&id){x}else{let x=self.variable();map.insert(id,x);x};self.class.insert(c,n);}
        fn keep(s:&mut Proof,old:&[Node],map:&mut HashMap<u32,u32>,id:u32,depth:usize)->u32 {
            if let Some(&n)=map.get(&id){return n;}
            let node=old[id as usize];let n=if depth==0||node.kind==1||s.nodes.len()>=1_000_000{s.variable()}else{
                let a=keep(s,old,map,node.a,depth-1);let b=keep(s,old,map,node.b,depth-1);
                match node.kind{2=>s.xor(a,b),3=>s.and(a,b),_=>panic!("unexpected proof node")}
            };map.insert(id,n);n
        }
        for(i,id)in old_q.into_iter().enumerate(){self.q[i]=keep(self,&old,&mut map,id,16);}
        self.live.clear();for(i,&id)in self.q.iter().enumerate(){self.live.insert(id,i as u16);}
    }
    /// Exact Boolean ANF certificate in GF(2)[x]/(x²=x). Old DAG roots are
    /// opaque independent variables. Resource limits ABORT proof, never drop terms.
    fn anf_constant(&self,root:u32,cut:u32)->Option<u32>{
      use std::collections::BTreeSet;type Poly=BTreeSet<Vec<u32>>;
      fn rec(s:&Proof,id:u32,cut:u32,memo:&mut HashMap<u32,Poly>,fuel:&mut usize,depth:usize)->Option<Poly>{
       if id==0{return Some(Poly::new());}if id==1{return Some(Poly::from([vec![]]));}
       if let Some(p)=memo.get(&id){return Some(p.clone());}
       if *fuel==0||depth>16{return None;}*fuel-=1;
       let n=s.nodes[id as usize];
       let p=if id<cut||n.kind==1{Poly::from([vec![id]])}else{
        let a=rec(s,n.a,cut,memo,fuel,depth+1)?;let b=rec(s,n.b,cut,memo,fuel,depth+1)?;
        if n.kind==2{let mut p=a;for mon in b{if !p.insert(mon.clone()){p.remove(&mon);}if p.len()>32{return None;}}p}
        else if n.kind==3{let mut p=Poly::new();for x in &a{for y in &b{let mon:Vec<_>=x.iter().chain(y.iter()).copied().collect::<BTreeSet<_>>().into_iter().collect();if mon.len()>8{return None;}if !p.insert(mon.clone()){p.remove(&mon);}if p.len()>32{return None;}}}p}else{return None;}
       };memo.insert(id,p.clone());Some(p)
      }
      let p=rec(self,root,cut,&mut HashMap::new(),&mut 64,0)?;
      if p.is_empty(){Some(0)}else if p==Poly::from([vec![]]){Some(1)}else{None}
    }
    /// Checked exact local theorem, not an empirical zero assumption.
    fn legal_pair(&self,c:u16,e:u16)->bool {
        let(c,e)=(self.q[c as usize],self.q[e as usize]);
        c==0 || e==1 || c==e || {let n=self.nodes[c as usize];n.kind==3&&(n.a==e||n.b==e)}
    }
    fn encoder_gate(&mut self,m:Micro)->Option<u16>{
        if let Some(mut k)=self.codec.take(){
            let good=if m.cond!=self.global {false}
            else if k.step==1||k.step==2 {
                let n=2*k.step;
                let fresh=m.kind==8 && !k.w[..n].contains(&m.a) && !k.w[..n].contains(&m.t) && m.a!=m.t;
                if fresh&&self.legal_pair(m.a,m.t){k.w[n]=m.t;k.w[n+1]=m.a;true}else{false}
            }else{
                let w=k.w;
                let(kind,a,b,t)=match k.step{
                    3=>(8,w[0],0,w[2]),4=>(8,w[5],0,w[3]),5=>(6,0,0,w[4]),
                    6=>(13,w[1],w[3],w[5]),7=>(8,w[1],0,w[4]),8=>(6,0,0,w[2]),
                    9=>(13,w[3],w[4],w[5]),10=>(13,w[4],w[5],w[1]),
                    11=>(13,w[2],w[5],w[0]),12=>(13,w[0],w[1],w[5]),_=>unreachable!()};
                m.kind==kind&&m.t==t&&(kind==6||m.a==a)&&(kind!=13||m.b==b)
            };
            if good {if k.step==12{return Some(k.w[5]);}k.step+=1;self.codec=Some(k);return None;}
        }
        if m.cond==self.global&&m.kind==8&&m.a!=m.t&&self.legal_pair(m.a,m.t){self.codec=Some(EncoderCheck{step:1,w:[m.t,m.a,0,0,0,0]});}
        None
    }
    /// Advance the ORIGINAL gate and return a checked zero/one/copied-linear
    /// remainder. Its MBU implementation has exactly this symbolic next state.
    pub fn advance(&mut self,m:Micro)->Option<Restore> {
        if self.nodes.len()>=self.budget{self.forget();}
        let codec_zero=self.encoder_gate(m);
        let (a,b,t)=(m.a as usize,m.b as usize,m.t as usize);let cond=self.condition(m.cond);let mut restore=None;
        match m.kind {
            6=>self.q[t]=self.xor(self.q[t],cond),
            8=>{let f=self.and(self.q[a],cond);self.q[t]=self.xor(self.q[t],f);},
            10=>{if cond==1{self.q.swap(a,t);}else{let d=self.xor(self.q[a],self.q[t]);let d=self.and(d,cond);self.q[a]=self.xor(self.q[a],d);self.q[t]=self.xor(self.q[t],d);}},
            13=>{
                assert_eq!(m.cond,self.global,"all Toffolis must use the common preserved offset-nonzero condition (or NONE for field units)");
                let before=self.q[t];
                if before==0{self.cut[t]=self.q[a].min(self.q[b]);}
                let term=self.and(self.q[a],self.q[b]);assert_eq!(cond,1);
                let mut post=self.xor(before,term);
                if before!=0&&post>1&&self.cut[t]>0{
                  if let Some(k)=self.anf_constant(post,self.cut[t]){post=k;self.anf_facts+=1;}
                }
                restore=if post==0{Some(Restore::Zero)}else if post==1{Some(Restore::One)}else if self.live.contains_key(&post){
                    let direct=self.live.get(&post).copied().filter(|&w|w as usize!=t&&self.q[w as usize]==post);
                    direct.or_else(||self.q.iter().enumerate().find_map(|(i,&x)|if i!=t&&x==post{Some(i as u16)}else{None})).map(Restore::Copy)
                }else{None};self.q[t]=post;
            },
            _=>panic!("nonpermutation quantum input to MBU proof"),
        }
        if let Some(q)=codec_zero {
            assert_eq!(q as usize,t);assert_eq!(m.kind,13);assert_ne!(self.q[t],1);
            // All27 legal patterns map this wire to zero. Preconditions were
            // proved structurally from exact DAG nodes before the13 gates.
            self.q[t]=0;self.codec_facts+=1;restore=Some(Restore::Zero);
        }
        self.live.insert(self.q[t],t as u16);if m.kind==10{self.live.insert(self.q[a],a as u16);}
        self.peak_nodes=self.peak_nodes.max(self.nodes.len());restore
    }
    pub fn step(&mut self,m:Micro)->bool {matches!(self.advance(m),Some(Restore::Zero))}
}

#[derive(Clone,Debug)]pub struct Contract{pub start:u64,pub end:u64,pub wires:Vec<u16>,pub last:Vec<u64>,pub kind:u8}
fn same(x:Micro,y:Micro)->bool{(x.kind,x.a,x.b,x.t,x.cond)==(y.kind,y.a,y.b,y.t,y.cond)}
fn gate(kind:u16,a:u16,b:u16,t:u16,c:u16)->Micro{Micro{kind,a,b,t,cond:c}}
fn targets(m:Micro)->Vec<u16>{if m.kind==10{vec![m.a,m.t]}else{vec![m.t]}}
fn touched(m:Micro)->Vec<u16>{let mut v=targets(m);if m.kind==8||m.kind==13{v.push(m.a);}if m.kind==13{v.push(m.b);}v}
fn match_add(g:&[Micro],i:usize)->Option<(usize,Vec<u16>)>{
 if i+3>=g.len(){return None;}let cond=g[i].cond;let mut j=i;let mut a=vec![];let mut b=vec![];let mut carry=0;
 while j+2<g.len(){let x=g[j];let y=g[j+1];let z=g[j+2];if z.kind!=13{break;}let(ai,bi,ci)=(z.t,z.b,z.a);
  if a.is_empty(){carry=ci;}else if ci!=*a.last().unwrap(){break;}
  if !same(x,gate(8,ai,0,bi,cond))||!same(y,gate(8,ai,0,ci,cond))||z.cond!=cond{break;}
  a.push(ai);b.push(bi);j+=3;if a.len()>512{return None;}
 }
 if a.is_empty()||j+1>=g.len(){return None;}let ci=*a.last().unwrap();let(ai,bi)=(g[j].a,g[j].t);
 if !same(g[j],gate(8,ai,0,bi,cond))||!same(g[j+1],gate(8,ci,0,bi,cond)){return None;}a.push(ai);b.push(bi);j+=2;
 let mut used=std::collections::HashSet::new();for &q in a.iter().chain(&b).chain(std::iter::once(&carry)){if !used.insert(q){return None;}}
 for k in(0..a.len()-1).rev(){let ci=if k==0{carry}else{a[k-1]};for m in [gate(13,ci,b[k],a[k],cond),gate(8,a[k],0,ci,cond),gate(8,ci,0,b[k],cond)]{if j>=g.len()||!same(g[j],m){return None;}j+=1;}}
 a.push(carry);Some((j,a))
}
fn match_gidney(g:&[Micro],i:usize)->Option<(usize,Vec<u16>)>{
 if i+6>=g.len(){return None;}let cond=g[i].cond;let mut j=i;let mut a=vec![];let mut b=vec![];let mut cs=vec![];let mut carry=0;
 while j+5<g.len(){let x=g[j];let y=g[j+1];let z=g[j+2];if x.kind!=8||y.kind!=8||z.kind!=13{break;}let(ci,ai,bi,si)=(x.a,x.t,y.t,z.t);
  if a.is_empty(){carry=ci;}else if ci!=*cs.last().unwrap(){break;}
  let want=[gate(8,ci,0,ai,cond),gate(8,ci,0,bi,cond),gate(13,ai,bi,si,cond),gate(8,ci,0,si,cond),gate(8,ci,0,bi,cond),gate(8,ci,0,ai,cond)];
  if !g[j..j+6].iter().zip(want).all(|(&x,y)|same(x,y)){break;}a.push(ai);b.push(bi);cs.push(si);j+=6;if a.len()>512{return None;}
 }
 if a.is_empty(){return None;}let mut e=NONE;
 for k in 0..=a.len(){if j+2>=g.len(){return None;}let ci=if k==0{carry}else{cs[k-1]};if k==a.len(){a.push(g[j].t);b.push(g[j+1].t);}
  if k==0{e=g[j+1].a;}
  let want=[gate(8,ci,0,a[k],cond),gate(13,e,a[k],b[k],cond),gate(8,ci,0,a[k],cond)];if !g[j..j+3].iter().zip(want).all(|(&x,y)|same(x,y)){return None;}j+=3;
 }
 let mut used=std::collections::HashSet::new();for &q in a.iter().chain(&b).chain(&cs).chain([&carry,&e]){if !used.insert(q){return None;}}
 for k in(0..cs.len()).rev(){let ci=if k==0{carry}else{cs[k-1]};let want=[gate(8,ci,0,cs[k],cond),gate(8,ci,0,a[k],cond),gate(8,ci,0,b[k],cond),gate(8,e,0,b[k],cond),gate(13,a[k],b[k],cs[k],cond),gate(8,e,0,b[k],cond),gate(8,ci,0,b[k],cond),gate(8,ci,0,a[k],cond)];if j+8>g.len()||!g[j..j+8].iter().zip(want).all(|(&x,y)|same(x,y)){return None;}j+=8;}
 a.extend(cs);a.push(carry);Some((j,a))
}
pub fn contracts(input:&Path,start:u64,end:u64)->Vec<Contract>{
 let mut f=File::open(input).unwrap();f.seek(SeekFrom::Start(start*12)).unwrap();let mut bytes=vec![0;(end-start)as usize*12];f.read_exact(&mut bytes).unwrap();let g:Vec<_>=bytes.chunks_exact(12).map(Micro::read).collect();drop(bytes);let n=g.len();let mut found=vec![];
 for reverse in [false,true]{let rev;if reverse{rev=g.iter().rev().copied().collect::<Vec<_>>();}else{rev=vec![];}let view=if reverse{&rev}else{&g};let mut i=0;
  while i<n{let m=match_gidney(view,i).map(|(j,w)|(j,w,2)).or_else(||match_add(view,i).map(|(j,w)|(j,w,1)));if let Some((j,w,kind))=m{let(lo,hi)=if reverse{(n-j,n-i)}else{(i,j)};found.push((lo,hi,w,kind));i=j;}else{i+=1;}}
 }
 // Pure compute-target-toggle-uncompute palindrome, target absent from G.
 for i in 0..n{for central in [1,2]{if i+central>n{continue;}let flag=g[i].t;let ok=if central==1{matches!(g[i].kind,6|8|13)}else{g[i+1].t==flag&&matches!((g[i].kind,g[i+1].kind),(6,8)|(8,6))};if !ok{continue;}
  let mut k=0;let mut writes=std::collections::HashSet::new();while i>k&&i+central+k<n{let a=g[i-1-k];let b=g[i+central+k];if !same(a,b)||!matches!(a.kind,6|8|10|13)||touched(a).contains(&flag){break;}for q in targets(a){writes.insert(q);}k+=1;}
  if k>=8{let mut w=writes.into_iter().collect::<Vec<_>>();w.sort_unstable();found.push((i-k,i+central+k,w,3));}
 }}
 found.sort_by_key(|x|(x.0,x.1,x.3));found.dedup_by(|a,b|a.0==b.0&&a.1==b.1&&a.2==b.2);
 let mut out=vec![];for(lo,hi,w,kind)in found{let mut map=HashMap::new();for j in lo..hi{for q in targets(g[j]){map.insert(q,start+j as u64);}}let mut wires=vec![];let mut last=vec![];for q in w{if let Some(&at)=map.get(&q){wires.push(q);last.push(at);}}if !wires.is_empty(){out.push(Contract{start:start+lo as u64,end:start+hi as u64,wires,last,kind});}}
 println!("COMPOSITIONAL_CONTRACTS add={} gidney={} bennett={} all_basis=true no_zero_entry_assumption=true",out.iter().filter(|x|x.kind==1).count(),out.iter().filter(|x|x.kind==2).count(),out.iter().filter(|x|x.kind==3).count());out
}
pub struct Runtime{cs:Vec<Contract>,values:Vec<Vec<u32>>,events:Vec<(u64,usize,usize)>,si:usize,ei:usize,pub restorations:u64}
impl Runtime{
 pub fn new(cs:Vec<Contract>)->Self{let values=cs.iter().map(|x|vec![0;x.wires.len()]).collect();let mut events=vec![];for(i,c)in cs.iter().enumerate(){for(j,&at)in c.last.iter().enumerate(){events.push((at,i,j));}}events.sort_unstable();Self{cs,values,events,si:0,ei:0,restorations:0}}
 pub fn begin(&mut self,i:u64,p:&Proof){assert_eq!(p.epochs,0,"abort: proof epoch changed while contract snapshots are live");while self.si<self.cs.len()&&self.cs[self.si].start==i{let c=&self.cs[self.si];for(j,&w)in c.wires.iter().enumerate(){self.values[self.si][j]=p.q[w as usize];}self.si+=1;}}
 pub fn finish(&mut self,i:u64,p:&mut Proof,t:u16)->bool{assert_eq!(p.epochs,0,"abort: proof epoch changed while contract snapshots are live");let mut changed=false;while self.ei<self.events.len()&&self.events[self.ei].0==i{let(_,c,j)=self.events[self.ei];let w=self.cs[c].wires[j];let value=self.values[c][j];p.q[w as usize]=value;p.live.insert(value,w);changed|=w==t;self.restorations+=1;self.ei+=1;}changed}
}
pub fn remainder(p:&Proof,t:u16)->Option<Restore>{let v=p.q[t as usize];if v==0{Some(Restore::Zero)}else if v==1{Some(Restore::One)}else{p.q.iter().enumerate().find_map(|(i,&w)|if i!=t as usize&&w==v{Some(Restore::Copy(i as u16))}else{None})}}
pub struct Optimized {pub replacements:u64,pub zeros:u64,pub copies:u64,pub ones:u64,pub epochs:u64,pub peak_nodes:usize,pub global_condition:u16,pub macros:u64}
pub fn optimize(input:&Path,output:&Path,certificate:&Path,qubits:usize,start:u64,end:u64)->Optimized {
    assert!(!output.exists(),"choose a fresh M4 artifact directory");
    let total=std::fs::metadata(input).unwrap().len()/12;
    let mut scan=File::open(input).unwrap();scan.seek(SeekFrom::Start(start*12)).unwrap();let mut global=NONE;
    for _ in start..end {let mut r=[0;12];scan.read_exact(&mut r).unwrap();let m=Micro::read(&r);if m.kind==13{global=m.cond;break;}}
    assert_ne!(global,NONE);
    let mut runtime=Runtime::new(contracts(input,start,end));
    let mut p=Proof::new(qubits,512,global,64_000_000);
    let mut rd=BufReader::with_capacity(4*1024*1024,File::open(input).unwrap());let mut wr=BufWriter::with_capacity(4*1024*1024,File::create(output).unwrap());let mut cert=BufWriter::new(File::create(certificate).unwrap());
    let mut replacements=0;let mut zeros=0;let mut copies=0;let mut ones=0;let mut next=10_000_000;
    for i in 0..total {
        let mut r=[0;12];rd.read_exact(&mut r).unwrap();let mut m=Micro::read(&r);
        if i>=start&&i<end{
            assert!(m.kind<20);
            runtime.begin(i,&p);let mut repair=p.advance(m);if runtime.finish(i,&mut p,m.t)&&m.kind==13{repair=repair.or_else(||remainder(&p,m.t));}
            if let Some(restore)=repair{
                assert_eq!(m.kind,13);match restore{Restore::Zero=>{m.kind=MBU_AND;zeros+=1;},Restore::One=>{m.kind=MBU_ONE;ones+=1;},Restore::Copy(w)=>{assert_ne!(w,m.t);m.kind=MBU_COPY;m.cond=w;copies+=1;}}replacements+=1;
                cert.write_all(&i.to_le_bytes()).unwrap();cert.write_all(&p.epochs.to_le_bytes()).unwrap();
            }
        }
        wr.write_all(&m.bytes()).unwrap();
        if i>=start&&i<end&&i-start>=next{println!("PROOF gates={} replacements={replacements} epochs={} nodes={}",i-start,p.epochs,p.nodes.len());std::io::stdout().flush().unwrap();next+=10_000_000;}
    }
    wr.flush().unwrap();cert.flush().unwrap();
    println!("COMPOSITIONAL_RESTORATIONS count={}",runtime.restorations);
    println!("EXACT_CODEC_FACTS count={}",p.codec_facts);println!("EXACT_ANF_FACTS count={}",p.anf_facts);
    Optimized{replacements,zeros,copies,ones,epochs:p.epochs,peak_nodes:p.peak_nodes,global_condition:global,macros:total}
}

#[cfg(test)]
mod tests {
    use super::*;
    fn m(kind:u16,a:u16,b:u16,t:u16)->Micro{Micro{kind,a,b,t,cond:NONE}}
    #[test]fn and_erase_truth_table_phase(){
        // Outcome-conditioned branch amplitudes are positive after repair, for
        // every a,b and X outcome; the target is zero. This includes superposed
        // inputs by linearity with identical branch probability 1/2.
        for a in [false,true]{for b in [false,true]{for measurement in [false,true]{let t=a&b;let measured_phase=measurement&t;let fix=measurement&a&b;assert!(!(measured_phase^fix));}}}
    }
    #[test]fn proof_and_forgetting_are_conservative(){
        let mut p=Proof::new(8,3,NONE,10000);
        assert!(!p.step(m(13,0,1,3)));assert!(p.step(m(13,0,1,3)));
        assert!(!p.step(m(13,0,1,2))); // arbitrary initial target: NOT an AND erase
        assert!(!p.step(m(13,0,1,2))); // toggling it back is still arbitrary
        assert!(!p.step(m(13,0,1,4)));p.forget();assert!(p.step(m(13,0,1,4))); // exact local relation survives conservative compaction
        let mut q=Proof::new(8,3,NONE,10000);q.step(m(13,0,1,3));q.step(m(6,0,0,0));assert!(!q.step(m(13,0,1,3))); // changed control
    }
    #[test]fn exact_xor_and_rules(){
        let mut p=Proof::new(8,3,NONE,10000);let a=p.q[0];let b=p.q[1];let x=p.xor(a,b);assert_eq!(p.xor(x,a),b);assert_eq!(p.xor(x,b),a);assert_eq!(p.and(a,a),a);assert_eq!(p.and(0,a),0);assert_eq!(p.and(1,a),a);
    }
    #[test]fn frequent_compaction_matches_exhaustive_boolean_truth(){
        let mut p=Proof::new(8,3,NONE,10000);let mut q=[0u8;8];q[0]=0b10101010;q[1]=0b11001100;q[2]=0b11110000;
        let mut seed=12345u64;
        for i in 0..10000 {
            seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);let kind=[6,8,10,13][(seed as usize>>5)%4];
            let a=((seed>>12)%8)as u16;let b=(a+1+((seed>>20)%7)as u16)%8;let mut t=((seed>>32)%8)as u16;while t==a||t==b{t=(t+1)%8;}
            let op=m(kind,a,b,t);let erase=p.step(op);if erase{assert_eq!(q[t as usize],q[a as usize]&q[b as usize]);}
            match kind{6=>q[t as usize]^=255,8=>q[t as usize]^=q[a as usize],10=>q.swap(a as usize,t as usize),13=>q[t as usize]^=q[a as usize]&q[b as usize],_=>panic!()}
            if i%7==0{p.forget();}
        }
    }

    #[test]fn copied_linear_part_phase_truth_table(){
        for w in [false,true]{for a in [false,true]{for b in [false,true]{for m in [false,true]{
            let old=w^(a&b);let phase=(m&old)^(m&a&b)^(m&w);assert!(!phase);let restored=w;assert_eq!(restored,old^(a&b));
        }}}}
    }
    #[test]fn generalized_proof_matches_all_eight_basis_inputs(){
        let mut p=Proof::new(8,3,NONE,10000);let mut q=[0u8;8];q[0]=0b10101010;q[1]=0b11001100;q[2]=0b11110000;let mut seed=87654321u64;
        for i in 0..20000 {seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);let kind=[6,8,10,13][(seed as usize>>5)%4];let a=((seed>>12)%8)as u16;let b=(a+1+((seed>>20)%7)as u16)%8;let mut t=((seed>>32)%8)as u16;while t==a||t==b{t=(t+1)%8;}let r=p.advance(m(kind,a,b,t));
            if let Some(r)=r{let post=q[t as usize]^(q[a as usize]&q[b as usize]);assert_eq!(post,match r{Restore::Zero=>0,Restore::One=>255,Restore::Copy(w)=>{assert_ne!(w,t);q[w as usize]}});}
            match kind{6=>q[t as usize]^=255,8=>q[t as usize]^=q[a as usize],10=>q.swap(a as usize,t as usize),13=>q[t as usize]^=q[a as usize]&q[b as usize],_=>panic!()}if i%11==0{p.forget();}
        }
    }

}

#[cfg(test)]mod codec_theorem_tests{
 use super::*;
 fn code(w:[u16;6])->Vec<Micro>{let mut v=vec![];let mut one=|kind,a,b,t|v.push(Micro{kind,a,b,t,cond:NONE});one(8,w[1],0,w[0]);one(8,w[3],0,w[2]);one(8,w[5],0,w[4]);one(8,w[0],0,w[2]);one(8,w[5],0,w[3]);one(6,0,0,w[4]);one(13,w[1],w[3],w[5]);one(8,w[1],0,w[4]);one(6,0,0,w[2]);one(13,w[3],w[4],w[5]);one(13,w[4],w[5],w[1]);one(13,w[2],w[5],w[0]);one(13,w[0],w[1],w[5]);v}
 #[test]fn codec_fact_requires_exact_legal_relations(){let mut p=Proof::new(9,6,NONE,4000000);for i in 0..3{p.advance(Micro{kind:13,a:i,b:i+3,t:i+6,cond:NONE});}let mut last=None;for m in code([0,6,1,7,2,8]){last=p.advance(m);}assert_eq!(p.codec_facts,1);assert_eq!(p.q[8],0);assert!(matches!(last,Some(Restore::Zero)));}
 #[test]fn arbitrary_pairs_or_broken_patterns_never_get_a_fact(){let mut p=Proof::new(6,6,NONE,4000000);for m in code([0,1,2,3,4,5]){p.advance(m);}assert_eq!(p.codec_facts,0);let mut p=Proof::new(9,6,NONE,4000000);for i in 0..3{p.advance(Micro{kind:13,a:i,b:i+3,t:i+6,cond:NONE});}let mut g=code([0,6,1,7,2,8]);g[5].t=0;for m in g{p.advance(m);}assert_eq!(p.codec_facts,0);}
}

#[cfg(test)]mod anf_tests{
 use super::*;
 #[test]fn exact_factored_controlled_carry_identity(){
  let mut p=Proof::new(4,4,NONE,4000000);let(a,b,c,e)=(p.q[0],p.q[1],p.q[2],p.q[3]);let cut=p.nodes.len()as u32;
  let ac=p.xor(a,c);let bc=p.xor(b,c);let t=p.and(ac,bc);let carry=p.xor(c,t);let es=p.and(e,ac);let bnew=p.xor(b,es);let v=p.xor(bnew,c);let v=p.xor(v,e);let prod=p.and(ac,v);let r=p.xor(carry,c);let r=p.xor(r,prod);assert_eq!(p.anf_constant(r,cut),Some(0));
 }
 #[test]fn proof_budget_aborts_never_truncates_terms(){
  let mut p=Proof::new(200,200,NONE,4000000);let mut r=p.q[0];for i in 1..200{r=p.xor(r,p.q[i]);}assert_eq!(p.anf_constant(r,2),None);
  let a=p.q[0];let b=p.q[1];let x=p.and(a,b);assert_eq!(p.anf_constant(x,2),None);
 }
 #[test]fn anf_constants_match_exhaustive_truth_under_many_cuts(){
  let mut p=Proof::new(4,4,NONE,4000000);let vars=p.q.clone();let mut values=vec![0u16,65535];for i in 0..4{values.push((0..16).fold(0,|x,j|x|((((j>>i)&1)as u16)<<j)));}let mut seed=987654321u64;
  for i in 0..3000{seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);let a=(seed as usize)%p.nodes.len();let b=((seed>>21)as usize)%p.nodes.len();let kind=if seed&1==0{2}else{3};let id=if kind==2{p.xor(a as u32,b as u32)}else{p.and(a as u32,b as u32)};while values.len()<p.nodes.len(){let n=p.nodes[values.len()];values.push(if n.kind==2{values[n.a as usize]^values[n.b as usize]}else{values[n.a as usize]&values[n.b as usize]});}let cut=2+((seed>>35)as usize)%(p.nodes.len()-1);if let Some(k)=p.anf_constant(id,cut as u32){assert_eq!(values[id as usize],if k==0{0}else{65535},"i={i}");}}
  assert_eq!(vars.len(),4);
 }
}

#[cfg(test)]mod compositional_tests{
 use super::*;
 fn emit(v:&mut Vec<Micro>,kind:u16,a:u16,b:u16,t:u16){v.push(gate(kind,a,b,t,NONE));}
 fn sample(n:usize,gidney:bool)->(Vec<Micro>,Vec<u16>,usize){let a:(Vec<u16>)=(0..n as u16).collect();let b:Vec<_>=(n as u16..2*n as u16).collect();let cs:Vec<_>=(2*n as u16..(3*n-1)as u16).collect();let carry=(3*n-1)as u16;let e=3*n as u16;let mut v=vec![];
  if gidney{for i in 0..n-1{let c=if i==0{carry}else{cs[i-1]};for m in [gate(8,c,0,a[i],NONE),gate(8,c,0,b[i],NONE),gate(13,a[i],b[i],cs[i],NONE),gate(8,c,0,cs[i],NONE),gate(8,c,0,b[i],NONE),gate(8,c,0,a[i],NONE)]{v.push(m);}}
   for i in 0..n{let c=if i==0{carry}else{cs[i-1]};emit(&mut v,8,c,0,a[i]);emit(&mut v,13,e,a[i],b[i]);emit(&mut v,8,c,0,a[i]);}
   for i in(0..n-1).rev(){let c=if i==0{carry}else{cs[i-1]};for m in [gate(8,c,0,cs[i],NONE),gate(8,c,0,a[i],NONE),gate(8,c,0,b[i],NONE),gate(8,e,0,b[i],NONE),gate(13,a[i],b[i],cs[i],NONE),gate(8,e,0,b[i],NONE),gate(8,c,0,b[i],NONE),gate(8,c,0,a[i],NONE)]{v.push(m);}}
  }else{for i in 0..n-1{let c=if i==0{carry}else{a[i-1]};emit(&mut v,8,a[i],0,b[i]);emit(&mut v,8,a[i],0,c);emit(&mut v,13,c,b[i],a[i]);}emit(&mut v,8,a[n-1],0,b[n-1]);emit(&mut v,8,a[n-2],0,b[n-1]);for i in(0..n-1).rev(){let c=if i==0{carry}else{a[i-1]};emit(&mut v,13,c,b[i],a[i]);emit(&mut v,8,a[i],0,c);emit(&mut v,8,c,0,b[i]);}}
  let mut w=a;if gidney{w.extend(cs);}w.push(carry);(v,w,3*n+1)
 }
 fn apply(m:Micro,q:&mut[bool]){match m.kind{6=>q[m.t as usize]^=true,8=>q[m.t as usize]^=q[m.a as usize],13=>q[m.t as usize]^=q[m.a as usize]&q[m.b as usize],10=>q.swap(m.a as usize,m.t as usize),_=>panic!()}}
 #[test]fn dirty_carry_identity_complete_boolean_certificate(){for d in[false,true]{for c in[false,true]{for a in[false,true]{for b in[false,true]{for e in[false,true]{let s=d^c^((a^c)&(b^c));let bn=b^(e&(a^c));let restored=s^c^((a^c)&(bn^c^e));assert_eq!(restored,d);}}}}}}
 #[test]fn matched_words_restore_early_on_arbitrary_dirty_basis(){for n in 2..=4{for gidney in[false,true]{let(v,w,nq)=sample(n,gidney);let(j,got)=if gidney{match_gidney(&v,0).unwrap()}else{match_add(&v,0).unwrap()};assert_eq!(j,v.len());assert_eq!(got,w);
  for reverse in[false,true]{let gates=if reverse{v.iter().rev().copied().collect::<Vec<_>>()}else{v.clone()};let last:Vec<_>=w.iter().map(|&q|gates.iter().rposition(|&m|targets(m).contains(&q))).collect();for input in 0..1usize<<nq{let mut q:(Vec<bool>)=(0..nq).map(|i|input>>i&1!=0).collect();let old=q.clone();for(i,&m)in gates.iter().enumerate(){apply(m,&mut q);for(k,&wire)in w.iter().enumerate(){if last[k]==Some(i){assert_eq!(q[wire as usize],old[wire as usize],"n={n} dirty={input} reverse={reverse} i={i}");}}}for &wire in &w{assert_eq!(q[wire as usize],old[wire as usize]);}}}
  let mut broken=v.clone();let k=broken.iter().position(|m|m.kind==13).unwrap();broken[k].t^=1;assert!(if gidney{match_gidney(&broken,0)}else{match_add(&broken,0)}.is_none());
 }}}
 #[test]fn epoch_change_aborts_instead_of_reusing_node_ids(){let mut p=Proof::new(4,4,NONE,64000000);p.epochs=1;let mut r=Runtime::new(vec![]);assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||r.begin(0,&p))).is_err());}
}
