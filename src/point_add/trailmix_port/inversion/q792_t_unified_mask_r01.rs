//! Unified T H-mask loan AFTER q0 pop and numeric low unpack.
//! Original rank5/A6/C6/SM4, held SMALL=(original Squarter==0), carry0
//! on g; source-head loan already holds SMALL in a separate sixth rank rail.
//! Every active A0..252 gets exactly one real zero donor. No new quantum rail.
//! Apply before rank6 chart; inverse AFTER inverse chart and BEFORE low inverse.
//! C0 is mutated only by the final C1 loan; its inverse runs first.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::metadata_arithmetic5_encoded::add;
fn high_swap(circ:&mut Circuit,rank:&[QReg],carry:&QReg,g:&QReg,bit:usize,left:&QReg,right:&QReg){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
    let controls:Vec<_>=rank.iter().chain(std::iter::once(carry)).collect();
    if super::q792_esop_r01::active(){circ.cx(right,left);circ.x(g);super::q792_esop_r01::paired(circ,&controls,truth,&[(left,true)],right,g);circ.x(g);circ.cx(right,left);return;}
    let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,6);
    for(i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    circ.cx(right,left);circ.x(g);
    // On original g1, X(g) supplies a clean scratch. Off g this is only
    // part of the arbitrary routing unitary, undone before the boundary.
    for m in terms{let mut cs=vec![(left,true)];cs.extend((0..6).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));super::paired_clean_mcx::toggle(circ,&cs,right,g);}
    circ.x(g);circ.cx(right,left);
    for(i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}

fn c1(c:&mut Circuit,r:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){for mut cs in super::q792_t10_dirtyq1_r01::ceq(r,cl,1){cs.push((g,true));super::q794_t10_quotient::gate(c,&cs,out,d);}}
fn m255(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){add(c,a,cl,None,false);let ts=super::q792_fold20_rank_r01::triples();let mut base=vec![(g,true)];base.extend(cl.iter().map(|q|(q,true)));super::q792_fold20_r01::table(c,&r.iter().collect::<Vec<_>>(),ts.iter().map(|t|t[0]+t[1]==3).collect(),&base,out,d);add(c,a,cl,None,true);}
fn normal_flag(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg],endpoints:bool){c.cx(g,out);c1(c,r,cl,g,out,d);if endpoints{m255(c,r,a,cl,g,out,d);super::q794_t10_quotient::endpoint(c,r,a,cl,&[(g,true)],out,d);}}

fn swap2(c:&mut Circuit,g:&QReg,flag:&QReg,x:&QReg,y:&QReg,d:&[QReg]){
 c.cx(y,x);super::q794_t10_quotient::gate(c,&[(g,true),(flag,true),(x,true)],y,d);c.cx(y,x);
}
fn c01(c:&mut Circuit,r:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){
 // Exact C<=1 predicate independent of the donated Cbit0.
 for mut cs in super::q792_t10_dirtyq1_r01::ceq(r,cl,1){cs.retain(|(q,_)|q.id()!=cl[0].id());cs.push((g,true));super::q794_t10_quotient::gate(c,&cs,out,d);}
}
fn a0_c01_small(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,small:&QReg,out:&QReg,d:&[QReg]){
 // SMALL implies original SH0; AH0/CH0/SH0 is rank0. Includes rawC256.
 // Does not inspect C0 or SM, which can hold borrowed passengers.
 let mut cs=vec![(g,true),(small,true)];cs.extend(r.iter().chain(a).chain(&cl[1..]).map(|q|(q,false)));super::q794_t10_quotient::gate(c,&cs,out,d);
}
fn raw_c256(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){
 let mut cs=vec![(g,true)];cs.extend(r.iter().chain(a).chain(cl).map(|q|(q,false)));super::q794_t10_quotient::gate(c,&cs,out,d);
}
fn ordinary_c1(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,small:&QReg,out:&QReg,d:&[QReg]){
 c01(c,r,cl,g,out,d);a0_c01_small(c,r,a,cl,g,small,out,d);
}
pub(super) fn emit(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,small:&QReg,mask:&QReg,carry:&QReg,w1:&[QReg],d:&[QReg],j:usize,inverse:bool){
 assert_eq!(r.len(),5);assert_eq!(a.len(),6);assert_eq!(cl.len(),6);assert_eq!(sm.len(),4);assert!(w1.len()>=256&&d.len()>=19&&j<4);
 let owned=c.b.next_qubit;let at=c.b.ops.len();let support=super::q792_t_narrow_support_r01::quotient_support(c);
 let bound=support.map(|(_,hi)|hi.saturating_mul(2).saturating_sub(7));let endpoints=bound.map_or(true,|v|v>=255);let endpoint256=bound.map_or(true,|v|v>=256);
 // 1. Ordinary C>=2,M<=254: the actual popped q0 source slot is zero.
 let route_at=c.b.ops.len();add(c,a,cl,Some(carry),false);
 let(lo,hi)=support.map_or((1,254),|(lo,hi)|(lo.max(1).min(253),hi.saturating_mul(2).saturating_sub(7).min(254)));
 let mut nodes:Vec<_>=(0..256).map(|v|if(lo..=hi).contains(&v)&&v<=254{Some(&w1[v+1])}else{None}).collect();if nodes.iter().all(Option::is_none){nodes[1]=Some(&w1[2]);}
 for b in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(z))=>{if b<6{c.cswap(&cl[b],l,z);}else{high_swap(c,r,carry,g,b-6,l,z);}Some(l)},(Some(l),None)|(None,Some(l))=>Some(l),(None,None)=>None});}nodes=next;}let root=nodes[0].unwrap();
 add(c,a,cl,Some(carry),true);let route=c.b.ops[route_at..].to_vec();normal_flag(c,r,a,cl,g,carry,d,endpoints);swap2(c,g,carry,root,mask,d);normal_flag(c,r,a,cl,g,carry,d,endpoints);c.b.ops.extend(route.into_iter().rev());
 // 2. Endpoint popped zero slots become SM zeros in even low unpack.
 // Odd low unpack is identity and all these SM rails were zero already.
 if endpoints{m255(c,r,a,cl,g,carry,d);swap2(c,g,carry,&sm[2-(j&1)],mask,d);m255(c,r,a,cl,g,carry,d);}
 if endpoint256&&j&1==0{
  super::q794_t10_quotient::endpoint(c,r,a,cl,&[(g,true)],carry,d);raw_c256(c,r,a,cl,g,carry,d);
  swap2(c,g,carry,&sm[1],mask,d);
  raw_c256(c,r,a,cl,g,carry,d);super::q794_t10_quotient::endpoint(c,r,a,cl,&[(g,true)],carry,d);
 }
 // 3. A0/C<=1/SMALL has t=1 odd: low unpack is identity and SM2=0.
 // Includes raw C256, which is deliberately removed from the prior branch.
 a0_c01_small(c,r,a,cl,g,small,carry,d);swap2(c,g,carry,&sm[2],mask,d);a0_c01_small(c,r,a,cl,g,small,carry,d);
 // 4. Remaining C<=1 is actual C1. C0=1 is a reversible zero donor;
 // the selecting predicate excludes C0 and every SM bit. Run this LAST.
 ordinary_c1(c,r,a,cl,g,small,carry,d);c.ccx(g,carry,&cl[0]);swap2(c,g,carry,&cl[0],mask,d);ordinary_c1(c,r,a,cl,g,small,carry,d);
 if inverse{c.b.ops[at..].reverse();}assert_eq!(c.b.next_qubit,owned);
}
