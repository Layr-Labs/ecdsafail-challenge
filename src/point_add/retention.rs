// Source-bound output refinement. Original semantic expansion and Proof are untouched.
#[derive(Clone,Copy)]
struct RetentionLocation { h:usize,re:usize,end:usize,start_byte:usize,end_byte:usize,t:usize,a:usize,b:usize,c:usize }
#[derive(Clone,Copy)]
struct RetentionActive { capture:bool,q:[QubitId;3],c:BitId,cleanup_end:usize,re_start:usize,re_end:usize }
struct Retention { enabled:bool,locations:Vec<Vec<RetentionLocation>>,entries:usize,proven:usize,selected:usize,fallback:usize,removed_ops:usize,max_capture:usize }
impl Retention {
 fn new()->Self{let mut locations=vec![Vec::new();2270];for line in include_str!("retention_intervals.tsv").lines(){let v:Vec<usize>=line.split_whitespace().map(|s|s.parse().unwrap()).collect();assert_eq!(v.len(),10);locations[v[0]].push(RetentionLocation{h:v[1],re:v[2],end:v[3],start_byte:v[4],end_byte:v[5],t:v[6],a:v[7],b:v[8],c:v[9]});}Self{enabled:true,locations,entries:0,proven:0,selected:0,fallback:0,removed_ops:0,max_capture:0}}
}
fn retention_removable(v:&[Op],x:RetentionActive)->bool{
 use OperationType as K;
 if x.cleanup_end!=4||x.re_end!=x.re_start+1||x.re_start<4||x.re_end>v.len(){return false;}
 let [t,a,b]=x.q;
 let pair=|o:&Op| (o.q_control1==a&&o.q_control2==b)||(o.q_control1==b&&o.q_control2==a);
 if !(v[0].kind==K::Hmr&&v[0].q_target==t&&v[0].c_target==x.c&&v[0].c_condition==NO_BIT&&v[1].kind==K::PushCondition&&v[1].c_condition==x.c&&v[2].kind==K::CZ&&((v[2].q_control1==a&&v[2].q_target==b)||(v[2].q_control1==b&&v[2].q_target==a))&&v[3].kind==K::PopCondition){return false;}
 let r=&v[x.re_start];if !(r.kind==K::CCX&&r.q_target==t&&pair(r)&&r.c_condition==NO_BIT){return false;}
 // The emitted gap may not touch the retained physical product, modify its controls,
 // or observe the omitted outcome. This also rules out generated scratch/cleanup uses.
 for o in &v[4..x.re_start]{
  if [o.q_control1,o.q_control2,o.q_target].contains(&t)||o.c_condition==x.c||o.c_target==x.c{return false;}
  if [a,b].contains(&o.q_target)&&matches!(o.kind,K::X|K::CX|K::CCX|K::Swap|K::Hmr|K::R){return false;}
  if o.kind==K::Swap&&[a,b].contains(&o.q_control1){return false;}
 }
 // At recomputation q reconverges; the source outcome remains different until
 // a surviving unconditional HMR overwrites it. Require a syntactic kill before read.
 let mut killed=false;let mut depth=0usize;
 for o in &v[x.re_end..]{
  if o.c_condition==x.c&&!killed{return false;}
  if o.kind==K::PushCondition{depth+=1;}if o.kind==K::PopCondition{if depth==0{return false;}depth-=1;}
  if o.c_target==x.c{if o.kind!=K::Hmr||depth!=0||o.c_condition!=NO_BIT{return false;}killed=true;}
 }
 killed&&depth==0
}
impl State{
 fn retention_boundary(&mut self,node:usize,ix:usize,byte:usize,qs:usize,cs:usize,loc_ix:&mut usize,active:&mut Option<RetentionActive>){
  if !self.retention.enabled{return;}
  let Some(loc)=self.retention.locations[node].get(*loc_ix).copied()else{return;};
  if ix==loc.h{
   assert!(active.is_none());assert_eq!(byte,loc.start_byte);self.flush_raw();assert!(matches!(self.pending_hmr,PendingHmr::None));let q=[self.qmap[qs+loc.t],self.qmap[qs+loc.a],self.qmap[qs+loc.b]];let c=self.cmap[cs+loc.c];
   let valid=!q.contains(&QubitId(0))&&q[0]!=q[1]&&q[0]!=q[2]&&q[1]!=q[2]&&c!=self.measurement_bit&&c!=self.predicate_bit;
   let(proven,_)=self.proof.retention_product(q[0].0 as usize,q[1].0 as usize,q[2].0 as usize);let capture=valid&&proven;
   self.retention.entries+=1;if capture{self.retention.proven+=1;assert!(self.capture.is_none());self.capture=Some(Vec::new());}
   *active=Some(RetentionActive{capture,q,c,cleanup_end:0,re_start:0,re_end:0});
  }
  assert!(ix<=loc.h||active.is_some(),"source interval skipped by another optimizer");
  if [loc.h+4,loc.re,loc.re+1,loc.end].contains(&ix){self.flush_raw();if let Some(a)=active.as_mut(){if a.capture{let n=self.capture.as_ref().unwrap().len();if ix==loc.h+4{a.cleanup_end=n;}if ix==loc.re{a.re_start=n;}if ix==loc.re+1{a.re_end=n;}}}}
  if ix==loc.end{
   assert_eq!(byte,loc.end_byte);assert!(matches!(self.pending_hmr,PendingHmr::None));let a=active.take().unwrap();
   if a.capture{let v=self.capture.take().unwrap();self.retention.max_capture=self.retention.max_capture.max(v.len());
    if retention_removable(&v,a){
     self.retention.selected+=1;self.retention.removed_ops+=5;self.selected_delta-=5;
     self.output_ops-=v.len();for o in &v{self.output_hist[o.kind as usize]-=1;}
     for(i,o)in v.into_iter().enumerate(){if i>=4&&i!=a.re_start{self.write(o);}}
    }else{self.retention.fallback+=1;if self.retain_output{self.out.extend(v);}}
   }*loc_ix+=1;
  }
 }
}

#[cfg(test)]
include!("retention_tests.rs");
#[cfg(test)]
#[test]
fn retention_tiny(){retention_tests();}
#[cfg(test)]
#[test]
#[ignore="new combined sourcecount requires coordinated slot"]
fn retention_one_census(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.proof.balanced());let t=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered;
 println!("retention={} proven={} fallback={} expectedT={} output={} delta={} one={} skipped_one={} motif={:?} trace={:016x}{:016x} fingerprint={}",s.retention.selected,s.retention.proven,s.retention.fallback,t-512*s.predicate_blocks/2,s.output_ops,s.selected_delta,s.one_cleanups,s.skipped_one,s.selected_counts,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
 assert_eq!([s.retention.selected,s.retention.proven,s.retention.fallback],[47917,49176,1259]);assert_eq!(t,63818849);assert_eq!(t-512*s.predicate_blocks/2,63490145);assert_eq!(s.output_ops,404225240);assert_eq!(s.selected_delta,-287488);
 assert_eq!(s.input_ops,401952311);assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!(s.skipped_one,0);
 assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);assert_eq!(s.prefix_rewrites,7421);assert_eq!(s.shared_rewrites,4229758);assert_eq!(s.predicate_blocks,1284);assert_eq!(s.selected_counts,[170,340,11701]);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert!(s.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
}
