#[derive(Clone)]struct TestRec{tag:u8,conds:Vec<usize>,expected:usize,q:Vec<usize>,c:Vec<usize>,start:usize}
fn test_decode(data:&[u8])->Vec<TestRec>{let mut r=Reader{data,at:0};let mut v=Vec::new();while r.at<data.len(){let start=r.at;let tag=r.byte();let cw=r.uvar();let expected=r.uvar();let conds=(0..cw).map(|_|r.uvar()).collect();if tag==11{assert_eq!(r.uvar(),0);}let nq=r.uvar();let q=(0..nq).map(|_|r.uvar()).collect();let nc=r.uvar();let c=(0..nc).map(|_|r.uvar()).collect();v.push(TestRec{tag,conds,expected,q,c,start});}v}
fn test_emit(s:&mut State,o:&TestRec){let start=s.cmap.len();for &c in &o.conds{s.cmap.push(s.cmap[c]);}s.emit_condition(start,o.conds.len(),o.expected);let mut qs=[NO_QUBIT;3];for(j,&q)in o.q.iter().enumerate(){qs[j]=s.qmap[q];}if o.tag==11{assert_eq!(o.q.len(),2);s.emit_leaf(4,&qs,2,NO_BIT,0);}else{s.emit_leaf(o.tag,&qs,o.q.len(),o.c.first().map(|c|s.cmap[*c]).unwrap_or(NO_BIT),o.c.len());}s.unemit_condition(start,o.conds.len(),o.expected);s.cmap.truncate(start);}
fn retention_tests(){
 use crate::sim::Simulator;use sha3::digest::XofReader;use OperationType as K;
 struct Rng{v:Vec<u8>,i:usize}impl XofReader for Rng{fn read(&mut self,b:&mut[u8]){b.fill(self.v.get(self.i).copied().unwrap_or(0));self.i+=1;}}
 let fixtures:&[(&[u8],usize,usize,usize,usize,usize)]=include!("retention_fixtures.rs");let(mut cases,mut selected,mut fallback)=(0usize,0usize,0usize);
 for (shape,&(data,re,end,t,a,b))in fixtures.iter().enumerate(){let ops=test_decode(data);assert_eq!(ops.len(),end);let mut locals=vec![t,a,b];for o in &ops{for &q in &o.q{if !locals.contains(&q){locals.push(q);}}}let n=locals.len();assert!(n<64);
  for context in 0..5{
   let build=|enabled,retain|{let inputs:Vec<_>=(1..=n).filter(|q|context==3||*q!=1).collect();let mut s=State::new(n+1,2,&inputs,&[0,1],retain,0);s.retention.enabled=enabled;s.retention.locations=vec![vec![RetentionLocation{h:0,re,end,start_byte:0,end_byte:data.len(),t,a,b,c:0}]];s.qmap=vec![QubitId(0);*locals.iter().max().unwrap()+1];for(j,&q)in locals.iter().enumerate(){s.qmap[q]=QubitId((j+1)as u64);}
    if context!=3{let o=s.raw(K::CCX);o.q_control1=QubitId(2);o.q_control2=QubitId(3);o.q_target=QubitId(1);}
    if context==1||context==2{let o=s.raw(if context==1{K::BitStore1}else{K::BitStore0});o.c_target=BitId(1);s.raw(K::PushCondition).c_condition=BitId(1);}
    if context==4{s.raw(K::PushCondition).c_condition=BitId(1);}
    let mut ix=0;let mut active=None;for(j,o)in ops.iter().enumerate(){s.retention_boundary(0,j,o.start,0,0,&mut ix,&mut active);test_emit(&mut s,o);}s.retention_boundary(0,end,data.len(),0,0,&mut ix,&mut active);if context==1||context==2||context==4{s.raw(K::PopCondition);}s.flush_raw();assert!(s.proof.balanced());s};
   let got=build(true,true);let count=build(true,false);let old=build(false,true);assert_eq!(got.output_hist,count.output_hist);assert_eq!(got.input_hist,count.input_hist);assert_eq!(got.output_ops,count.output_ops);assert_eq!(got.selected_delta,count.selected_delta);assert_eq!(got.retention.selected,count.retention.selected);assert_eq!(got.proof.diagnostic_fingerprint(),count.proof.diagnostic_fingerprint());assert_eq!(got.proof.diagnostic_fingerprint(),old.proof.diagnostic_fingerprint());assert_eq!(got.input_hist,old.input_hist);assert_eq!(got.input_ops,old.input_ops);assert_eq!(got.out.len(),got.output_ops);assert!(count.out.is_empty());
   let chosen=got.retention.selected==1;if chosen{selected+=1;assert_eq!(old.output_ops-got.output_ops,5);}else{fallback+=1;assert_eq!(old.output_hist,got.output_hist);}
   // Exhaustive eight input coordinates plus deterministic assignments across remaining wires.
   // Full all-input equality is separately certified by the frozen 100-shape Boolean ANF test.
   // Each source HMR outcome is enumerated; the deleted first outcome is independently varied.
   let nh=old.out.iter().filter(|o|matches!(o.kind,K::Hmr|K::R)).count();assert!(nh<=8);
   for sample in 0..(1usize<<n.min(8)){let mask=if n<=8{sample}else{sample|((sample.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(23))&(!255usize))};if context!=3&&mask&1!=0{continue;}
    for outcomes in 0..1usize<<nh{for stale in 0..2{let rv:Vec<u8>=(0..nh).map(|j|if outcomes>>j&1!=0{255}else{0}).collect();let nv=if chosen{rv[1..].to_vec()}else{rv.clone()};let mut rr=Rng{v:rv,i:0};let mut nr=Rng{v:nv,i:0};let mut want=Simulator::new(n+1,4,&mut rr);let mut have=Simulator::new(n+1,4,&mut nr);for j in 0..n{want.qubits[j+1]=((mask>>j)&1)as u64;have.qubits[j+1]=want.qubits[j+1];}want.bits[0]=stale;have.bits[0]=stale;want.bits[1]=stale;have.bits[1]=stale;want.bits[2]=stale;have.bits[2]=stale;want.apply_iter(old.out.iter());have.apply_iter(got.out.iter());assert_eq!(want.qubits,have.qubits,"shape {shape} context {context}");assert_eq!(want.phase,have.phase,"phase shape {shape} context {context}");assert_eq!(want.bits[..2],have.bits[..2],"source bits shape {shape} context {context}");cases+=1;}}
   }
  }
 }
 retention_negative_tests();assert!(selected>0&&fallback>0);println!("ACTUAL_SIMULATOR PASS shapes={} cases={cases} selected_contexts={selected} fallback_contexts={fallback}; eight exhaustive coordinates plus deterministic full-width assignments, all independent HMR outcomes, stale source/private bits, active/inactive and dirty-entry contexts; complete histogram/count parity and original Proof fingerprint",fixtures.len());
}

fn retention_negative_tests(){
 use OperationType as K;
 let(t,a,b,c)=(QubitId(1),QubitId(2),QubitId(3),BitId(0));
 let mut v=vec![Op::empty();7];v[0].kind=K::Hmr;v[0].q_target=t;v[0].c_target=c;v[1].kind=K::PushCondition;v[1].c_condition=c;v[2].kind=K::CZ;v[2].q_control1=a;v[2].q_target=b;v[3].kind=K::PopCondition;v[4].kind=K::CX;v[4].q_control1=QubitId(4);v[4].q_target=QubitId(5);v[5].kind=K::CCX;v[5].q_control1=a;v[5].q_control2=b;v[5].q_target=t;v[6].kind=K::Hmr;v[6].q_target=QubitId(6);v[6].c_target=c;
 let x=RetentionActive{capture:true,q:[t,a,b],c,cleanup_end:4,re_start:5,re_end:6};assert!(retention_removable(&v,x));
 for change in 0..7{let mut w=v.clone();match change{0=>w[4].q_control1=t,1=>w[4].q_target=t,2=>w[4].q_target=a,3=>w[4].c_condition=c,4=>w[6].c_condition=c,5=>w[6].c_target=BitId(7),6=>w[5].q_target=QubitId(6),_=>unreachable!()}assert!(!retention_removable(&w,x),"mutation {change}");}
 println!("REJECTION_TESTS PASS retained-wire read/write, control write, omitted outcome read, conditional kill, missing kill, incorrect recomputation");
}
