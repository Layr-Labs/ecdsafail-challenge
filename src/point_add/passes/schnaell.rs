// schnaell.rs ("fast"): the record pass of the 637 build = schnaellstriicher's engine (q644/bw637/schnaellstriicher/schn.rs, library
// part, unchanged except: the SCHN_BREAK / SCHN_EMU / SCHN_TRACE environment switches are fixed to 0 / 0 / 0, the command line is dropped).
// The comments below are the engine's own.  fertig.rs uses it with mode 5 (cancel + sandwich; no Swap kind 10, no CCZ kind 14).
// schnaellstriicher ("fast canceller"): streaming, cascading version of batzechlemmer's abstriicher4 rule set.
// Records are u16le x 4 = [kind,a,b,c] (see BRIEF.md). Rules (all exact, same exactness conditions as abstriicher4):
//  (1) cancel   : identical self-inverse records (X, CX, CCX, Z, CZ, Swap, CCZ; same classical condition bit, same push/pop
//                 frame instance, no write to the condition bit between) with only commuting records between;
//  (2) sandwich : U w U (U unconditional X(a) / CX(a,b) / CCX) with ONE non-commuting record w between -> w x  (mode bit 1)
//  (3) swap     : CX(a,b;c) CX(b,a;c) CX(a,b;c) -> Swap(a,b;c) (kind 10)                                      (mode bit 2)
//  mode bit 4 forbids the rules that create CCZ (kind 14); without bit 2 no Swap (kind 10) is created.
// Commutation by role per qubit: 0 = diagonal (control, Z, CZ, CCZ), 1 = X-like (X, CX target, CCX target), 2 = measurement,
// 3 = Swap. Only equal roles in {0,1} commute. Measurements and classical-bit writes are barriers as in abstriicher4.
// Difference to abstriicher4: no rounds. Surviving records of a bounded window sit in per-qubit doubly linked lists; whenever a
// record is created, removed or rewritten, the following records on its qubits are put back on a worklist and re-examined at once
// (cascade), a rewrite product is itself examined at once, no one-slot-per-record limit. Records leave the window in stream order
// when it is full (they can no longer take part in a rewrite): that is the only approximation, the loss is measured.
// Library use:  let mut e=Eng::new(cap,mode,k); for each row: e.push(row,&mut |r|sink(r)); at the end: e.finish(&mut sink);
// CLI: schn <in.u16le> <skip> <count|0> <out.u16le|-> [mode=3] [window=4194304] [K=6]    (env SCHN_CHUNK=n: independent chunks of n rows)
//      env SCHN_BREAK=1..9 injects a deliberate rule violation (break controls); SCHN_NOWAKE=1 turns the cascade off.
const NQ:usize=1024;const NIL:u32=u32::MAX;const NOB:u16=65535;const GAP:u64=1<<20;
type R=[u16;4];
#[inline] fn norm(r:&R)->R{ if r[0]==6||r[0]==7{[r[0],r[1],r[2],NOB]} else if r[0]==13 && r[1]>r[2]{[13,r[2],r[1],r[3]]} else if (r[0]==9||r[0]==10) && r[1]>r[2]{[r[0],r[2],r[1],r[3]]} else if r[0]==14{let mut t=[r[1],r[2],r[3]];t.sort();[14,t[0],t[1],t[2]]} else {*r}}
#[inline] fn roles(r:&R,out:&mut [(u16,u8);3])->usize{match r[0]{6=>{out[0]=(r[1],1);1},8=>{out[0]=(r[2],1);out[1]=(r[1],0);2},13=>{out[0]=(r[3],1);out[1]=(r[1],0);out[2]=(r[2],0);3},7=>{out[0]=(r[1],0);1},9=>{out[0]=(r[1],0);out[1]=(r[2],0);2},10=>{out[0]=(r[1],3);out[1]=(r[2],3);2},14=>{out[0]=(r[1],0);out[1]=(r[2],0);out[2]=(r[3],0);3},12=>{out[0]=(r[1],2);1},_=>0}}
#[inline] fn condbit(r:&R)->u16{match r[0]{6|7=>r[2],8=>r[3],9=>r[3],10=>r[3],_=>NOB}}
#[inline] fn comm(a:u8,b:u8)->bool{a==b&&a<2}
#[inline] fn comm7(a:u8,b:u8)->bool{a<2&&b<2}
// conjugate w by U (U unconditional X or CX or CCX); returns the extra record to put after w (w itself stays)
fn conj(u:&R,w:&R)->Option<R>{
 if u[0]==8{let(a,b)=(u[1],u[2]);if u[3]!=NOB{return None;}
  match w[0]{8=>{let(x,y,c)=(w[1],w[2],w[3]);if x==b&&y!=a&&y!=b{Some([8,a,y,c])}else if y==a&&x!=b&&x!=a{Some([8,x,b,c])}else{None}}
   6=>{if w[1]==a{Some([6,b,w[2],NOB])}else{None}}
   7=>{if w[1]==b{Some([7,a,w[2],NOB])}else{None}}
   9=>{let(x,y,c)=(w[1],w[2],w[3]);if x==b||y==b{let o=if x==b{y}else{x};if o==a{Some([7,a,c,NOB])}else{Some([9,a.min(o),a.max(o),c])}}else{None}}
   _=>None}}
 else if u[0]==6{if u[2]!=NOB{return None;}let q=u[1];
  match w[0]{8=>{if w[1]==q&&w[2]!=q{Some([6,w[2],w[3],NOB])}else{None}}
   13=>{if w[1]==q{Some([8,w[2],w[3],NOB])}else if w[2]==q{Some([8,w[1],w[3],NOB])}else{None}}
   9=>{if w[1]==q{Some([7,w[2],w[3],NOB])}else if w[2]==q{Some([7,w[1],w[3],NOB])}else{None}}
   _=>None}}
 else if u[0]==13{let(a,b,t)=(u[1],u[2],u[3]);
  match w[0]{
   8=>{let(x,y,c)=(w[1],w[2],w[3]);if c!=NOB{return None;}
       if x==t&&y!=a&&y!=b&&y!=t{Some([13,a,b,y])}else if y==a&&x!=b&&x!=t&&x!=a{Some([13,x,b,t])}else if y==b&&x!=a&&x!=t&&x!=b{Some([13,a,x,t])}else{None}}
   6=>{if w[1]==a{Some([8,b,t,w[2]])}else if w[1]==b{Some([8,a,t,w[2]])}else{None}}
   7=>{if w[1]==t{Some([9,a.min(b),a.max(b),w[2]])}else{None}}
   9=>{let(x,y,c)=(w[1],w[2],w[3]);if c!=NOB{return None;}let o=if x==t{y}else if y==t{x}else{return None};if o==a||o==b{None}else{Some([14,a,b,o])}}
   _=>None}}
 else{None}}

#[derive(Default,Clone)]
pub struct Stats{pub n_in:u64,pub n_out:u64,pub cancel:[u64;32],pub sand:std::collections::BTreeMap<(u16,u16),u64>,pub swaps:u64,pub steps:u64,pub work:u64,pub depth_hist:[u64;12],pub flushed_early:u64,pub gen_hist:[u64;16],pub rep_hist:[u64;16]}
pub struct Eng{
 cap:usize,rec:Vec<R>,lab:Vec<u64>,frm:Vec<u32>,flg:Vec<u8>,gn:Vec<u32>,gp:Vec<u32>,
 qi:Vec<[u16;3]>,rl:Vec<[u8;3]>,nq:Vec<u8>,qn:Vec<[u32;3]>,qp:Vec<[u32;3]>,
 gh:u32,gt:u32,qh:Vec<u32>,qt:Vec<u32>,free:Vec<u32>,lastw:Vec<u64>,stack:Vec<u32>,nextf:u32,seq:u64,
 gen:Vec<u8>,swc:Vec<u16>,work:Vec<(u32,u8)>,pub mode:u32,pub kk:usize,pub nowake:bool,pub brk:u32,pub emu:u32,pub trace:u32,pub base:u64,pub st:Stats,pub live:usize,pub maxlive:usize}
const ALIVE:u8=1;const INQ:u8=2;
impl Eng{
 pub fn new(cap:usize,mode:u32,kk:usize)->Eng{
  let brk:u32=0;
  Eng{cap,rec:vec![[0;4];cap],lab:vec![0;cap],frm:vec![0;cap],flg:vec![0;cap],gn:vec![NIL;cap],gp:vec![NIL;cap],
   qi:vec![[NOB;3];cap],rl:vec![[0;3];cap],nq:vec![0;cap],qn:vec![[NIL;3];cap],qp:vec![[NIL;3];cap],
   gh:NIL,gt:NIL,qh:vec![NIL;NQ],qt:vec![NIL;NQ],free:(0..cap as u32).rev().collect(),lastw:vec![0;65536],stack:vec![0],nextf:1,seq:1,
   gen:vec![0;cap],swc:vec![0;cap],work:Vec::new(),mode,kk,nowake:false,emu:0,brk,base:0,trace:0,st:Stats::default(),live:0,maxlive:0}}
 #[inline] fn slot_of(&self,r:u32,q:u16)->usize{let a=&self.qi[r as usize];if a[0]==q{0}else if a[1]==q{1}else{2}}
 fn set_rec(&mut self,s:u32,r:R){let i=s as usize;self.rec[i]=r;let mut rg=[(0u16,0u8);3];let n=roles(&r,&mut rg);self.nq[i]=n as u8;self.qi[i]=[NOB;3];for j in 0..n{self.qi[i][j]=rg[j].0;self.rl[i][j]=rg[j].1;}}
 fn link_tail(&mut self,s:u32){let i=s as usize;for j in 0..self.nq[i] as usize{let q=self.qi[i][j];let p=self.qt[q as usize];self.qp[i][j]=p;self.qn[i][j]=NIL;
   if p!=NIL{let sp=self.slot_of(p,q);self.qn[p as usize][sp]=s;}else{self.qh[q as usize]=s;}self.qt[q as usize]=s;}}
 fn unlink(&mut self,s:u32){let i=s as usize;
  for j in 0..self.nq[i] as usize{let q=self.qi[i][j];let p=self.qp[i][j];let n=self.qn[i][j];
   if p!=NIL{let sp=self.slot_of(p,q);self.qn[p as usize][sp]=n;}else{self.qh[q as usize]=n;}
   if n!=NIL{let sn=self.slot_of(n,q);self.qp[n as usize][sn]=p;}else{self.qt[q as usize]=p;}}
  let (p,n)=(self.gp[i],self.gn[i]);if p!=NIL{self.gn[p as usize]=n;}else{self.gh=n;}if n!=NIL{self.gp[n as usize]=p;}else{self.gt=p;}
  self.flg[i]=0;self.free.push(s);self.live-=1;}
 fn enq(&mut self,s:u32,d:u8){if self.flg[s as usize]&INQ==0{self.flg[s as usize]|=INQ;self.work.push((s,d));}}
 // put the following records on each qubit of r back on the worklist (first K, up to the first role change)
 fn wake(&mut self,r:u32,d:u8){if self.nowake{return;}let i=r as usize;for j in 0..self.nq[i] as usize{let q=self.qi[i][j];let mut n=self.qn[i][j];let mut cnt=0;let mut r0=255u8;
   while n!=NIL&&cnt<self.kk{let s=self.slot_of(n,q);let role=self.rl[n as usize][s];if r0==255{r0=role;}self.enq(n,d);cnt+=1;if role!=r0{break;}n=self.qn[n as usize][s];}}}
 fn flush<F:FnMut(&R,u64)>(&mut self,n:usize,out:&mut F){
  for _ in 0..n{let r=self.gh;if r==NIL{break;}let i=r as usize;
   for j in 0..self.nq[i] as usize{let q=self.qi[i][j];let nn=self.qn[i][j];self.qh[q as usize]=nn;if nn!=NIL{let sn=self.slot_of(nn,q);self.qp[nn as usize][sn]=NIL;}else{self.qt[q as usize]=NIL;}}
   let ng=self.gn[i];self.gh=ng;if ng!=NIL{self.gp[ng as usize]=NIL;}else{self.gt=NIL;}
   out(&self.rec[i],self.base+(self.lab[i]>>20)-1);self.st.n_out+=1;self.flg[i]=0;self.free.push(r);self.live-=1;}}
 pub fn finish<F:FnMut(&R,u64)>(&mut self,out:&mut F){self.work.clear();let n=self.live;self.flush(n+1,out);}
 pub fn push<F:FnMut(&R,u64)>(&mut self,r:R,out:&mut F){
  if self.free.len()<64{let n=self.cap/16;self.flush(n,out);self.st.flushed_early+=1;}
  let s=self.free.pop().unwrap();let i=s as usize;self.st.n_in+=1;
  match r[0]{1|2|18|3|4|5|6|7|8|9|10|12|13|14|15|16=>{},k=>panic!("unsupported kind {}",k)}
  self.set_rec(s,r);self.gen[i]=0;self.swc[i]=0;self.lab[i]=self.seq<<20;self.seq+=1;self.flg[i]=ALIVE;self.live+=1;if self.live>self.maxlive{self.maxlive=self.live;}
  self.gp[i]=self.gt;self.gn[i]=NIL;if self.gt!=NIL{self.gn[self.gt as usize]=s;}else{self.gh=s;}self.gt=s;
  match r[0]{15=>{self.frm[i]=*self.stack.last().unwrap();self.stack.push(self.nextf);self.nextf+=1;}
   16=>{if self.stack.len()>1{self.stack.pop();}else{self.stack[0]=self.nextf;self.nextf+=1;}self.frm[i]=*self.stack.last().unwrap();}
   _=>{self.frm[i]=*self.stack.last().unwrap();}}
  match r[0]{3|4|5=>{self.lastw[r[1] as usize]=self.lab[i];}12=>{self.lastw[r[2] as usize]=self.lab[i];}_=>{}}
  self.link_tail(s);
  if matches!(r[0],6|7|8|9|10|13|14){self.enq(s,0);
   while let Some((x,d))=self.work.pop(){self.flg[x as usize]&=!INQ;if self.flg[x as usize]&ALIVE!=0{self.st.work+=1;self.process(x,d);}}}
 }
 fn process(&mut self,e:u32,depth:u8){
  let ei=e as usize;let er=self.rec[ei];let k=er[0];if !matches!(k,6|7|8|9|10|13|14){return;}
  let g=norm(&er);let mut rg=[(0u16,0u8);3];let nr=roles(&g,&mut rg);let fr=self.frm[ei];let cb=condbit(&g);let p=rg[0].0;
  let sand=(self.mode&3)!=0;let brk=self.brk;
  let mut h=self.qp[ei][self.slot_of(e,p)];let mut steps=0u32;let mut bl=NIL;let mut found=NIL;
  while h!=NIL&&steps<8192{steps+=1;let hi=h as usize;
   if (self.frm[hi]==fr||brk==2)&&norm(&self.rec[hi])==g{found=h;break;}
   let j=self.slot_of(h,p);let role=self.rl[hi][j];
   if !(if brk==7{comm7(role,rg[0].1)}else{comm(role,rg[0].1)}){ if brk==1&&role==2{h=self.qp[hi][j];continue;} if !sand||bl!=NIL||role==2{break;}bl=h;}
   h=self.qp[hi][j];}
  self.st.steps+=steps as u64;
  if found==NIL{return;}
  let fi=found as usize;let mut ok=true;
  if cb!=NOB&&brk!=3&&self.lastw[cb as usize]>self.lab[fi]{ok=false;}
  if ok{for j in 1..nr{let q=rg[j].0;let mut x=self.qp[ei][self.slot_of(e,q)];let mut st=0;
    while x!=found{if x==NIL{ok=false;break;}st+=1;if st>8192{ok=false;break;}let xi=x as usize;let jj=self.slot_of(x,q);let role=self.rl[xi][jj];
      if role==2&&brk!=1{ok=false;break;}
      if !(if brk==7{comm7(role,rg[j].1)}else{comm(role,rg[j].1)})&&brk!=4{if !sand{ok=false;break;}if bl!=x{if bl!=NIL{ok=false;break;}bl=x;}}
      x=self.qp[xi][jj];}
    self.st.steps+=1;if !ok{break;}}}
  if !ok{return;}
  if bl==NIL{ // cancel
   self.st.cancel[k as usize]+=2;{let ge=(1+self.gen[fi].max(self.gen[ei])).min(15);self.st.gen_hist[ge as usize]+=1;}self.wake(found,depth+1);self.wake(e,depth+1);self.unlink(found);self.unlink(e);return;}
  let w=bl;let wi=w as usize;
  if (self.mode&2)!=0&&k==8{let wr=self.rec[wi];
   if wr[0]==8&&wr[1]==g[2]&&wr[2]==g[1]&&(wr[3]==g[3]||brk==6)&&(self.frm[wi]==fr||brk==2){
    let sw=[10,g[1].min(g[2]),g[1].max(g[2]),g[3]];
    self.wake(found,depth+1);self.wake(e,depth+1);self.unlink(found);self.unlink(e);
    // retarget w in place to the swap (same two qubits)
    let oq=self.qi[wi];let op=self.qp[wi];let on=self.qn[wi];self.set_rec(w,sw);
    for j in 0..2{let q=self.qi[wi][j];let oj=if oq[0]==q{0}else{1};self.qp[wi][j]=op[oj];self.qn[wi][j]=on[oj];}
    {let ge=(1+self.gen[fi].max(self.gen[ei]).max(self.gen[wi])).min(15);self.st.gen_hist[ge as usize]+=1;self.gen[wi]=ge;self.swc[wi]=self.swc[wi].saturating_add(1);let c=self.swc[wi] as u32;self.st.rep_hist[(32-c.leading_zeros()) as usize]+=1;}self.wake(w,depth+1);self.enq(w,depth+1);self.st.swaps+=1;self.st.cancel[0]+=0;
    let dd=(depth as usize).min(11);self.st.depth_hist[dd]+=1;return;}}
  if (self.mode&1)!=0&&(k==6||k==8||k==13)&&(g[0]==6&&g[2]==NOB||g[0]==8&&g[3]==NOB||g[0]==13){
   if (self.emu&4)!=0&&(self.swc[wi]>0||self.gen[wi]>0){return;}
   let mut wn=norm(&self.rec[wi]);
   let x=match conj(&g,&wn){Some(x)=>x,None=>return};
   let x=if brk==5&&x[0]==8{[8,x[2],x[1],x[3]]}else if brk==8&&x[0]==8{[8,g[2],x[2],x[3]]}else{x};
   if (self.mode&4)!=0&&x[0]==14{return;}
   // feasibility of the insertion after w (before anything is changed)
   let nxt=self.gn[wi];
   let lw=self.lab[wi];let hi_l=if nxt!=NIL{self.lab[nxt as usize]}else{lw+GAP};let mid=lw+(hi_l-lw)/2;if mid<=lw||mid>=hi_l{return;}
   let mut xr=[(0u16,0u8);3];let nx=roles(&x,&mut xr);let mut preds=[NIL;3];
   for j in 0..nx{let q=xr[j].0;let mut n=self.qt[q as usize];let mut st=0;
    while n!=NIL&&(self.lab[n as usize]>mid||n==found){st+=1;if st>4096{return;}let s=self.slot_of(n,q);n=self.qp[n as usize][s];}
    preds[j]=n;}
   if self.trace>0{self.trace-=1;eprintln!("SAND h#{} {:?} w#{} {:?} e#{} {:?} -> {:?}",self.lab[fi]>>20,self.rec[fi],self.lab[wi]>>20,self.rec[wi],self.lab[ei]>>20,self.rec[ei],x);}
   let ge=(1+self.gen[fi].max(self.gen[ei]).max(self.gen[wi])).min(15);self.st.gen_hist[ge as usize]+=1;self.swc[wi]=self.swc[wi].saturating_add(1);{let c=self.swc[wi] as u32;self.st.rep_hist[(32-c.leading_zeros()) as usize]+=1;}
   self.st.sand.entry((k,self.rec[wi][0])).and_modify(|c|*c+=1).or_insert(1);
   self.wake(found,depth+1);self.wake(e,depth+1);self.unlink(found);self.unlink(e);
   let s=self.free.pop().unwrap();let si=s as usize;self.set_rec(s,x);self.lab[si]=mid;self.frm[si]=self.frm[wi];self.flg[si]=ALIVE;self.live+=1;
   self.gp[si]=w;self.gn[si]=self.gn[wi];if self.gn[wi]!=NIL{let n=self.gn[wi];self.gp[n as usize]=s;}else{self.gt=s;}self.gn[wi]=s;
   for j in 0..nx{let q=xr[j].0;let pr=preds[j];let nn=if pr!=NIL{let sp=self.slot_of(pr,q);self.qn[pr as usize][sp]}else{self.qh[q as usize]};
    self.qp[si][j]=pr;self.qn[si][j]=nn;
    if pr!=NIL{let sp=self.slot_of(pr,q);self.qn[pr as usize][sp]=s;}else{self.qh[q as usize]=s;}
    if nn!=NIL{let sn=self.slot_of(nn,q);self.qp[nn as usize][sn]=s;}else{self.qt[q as usize]=s;}}
   // slot order of x in qi follows roles(x), same as nx loop above
   self.gen[si]=ge;self.swc[si]=0;if (self.emu&2)==0{self.enq(s,depth+1);}self.wake(s,depth+1);
   let dd=(depth as usize).min(11);self.st.depth_hist[dd]+=1;wn[0]=0;let _=wn;
  }
 }
}
