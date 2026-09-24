//! Quotient window follows retained q793_t10_routes_v12, credited there to
//! welttowelt public Q793 W47, commit4e6322f775db282dc8b22f700eb0c263e6e665fc.
//! Public-calendar-pruned T quotient acquisition: physical normal pop, virtual C1,
//! and separately proved packed endpoints. Mask loan belongs to source head.
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
/// Care A<=252, C>=1 (or raw A0/C0/S0 for C256). Thus C1 cannot meet M255/256.
pub(super)fn pop(c:&mut Circuit,r:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,q:&QReg,_mask:&QReg,carry:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize){
 let owned=c.b.next_qubit;
 // This is the original public calendar support, never the narrower A range
 // selected by an arithmetic branch. The proved address bound is M<=2*Ahi-7.
 // No support means the complete endpoint behavior must remain present.
 let endpoints=super::q792_t_narrow_support_r01::quotient_support(c).map_or(true,|(_,hi)|hi.saturating_mul(2).saturating_sub(7)>=255);
 if endpoints{super::q792_t_endpoint_pop_r01::pop(c,r,a,cl,sm,g,q,carry,w1,w2,d,j);}
 let at=c.b.ops.len();add(c,a,cl,Some(carry),false);let support=super::q792_t_narrow_support_r01::quotient_support(c);let(lo,hi)=support.map_or((1,254),|(lo,hi)|(lo.max(1).min(253),(2*hi).saturating_sub(7).min(254)));let mut nodes:Vec<_>=(0..256).map(|v|if (lo..=hi).contains(&v)&&v<=254{Some(&w1[v+1])}else{None}).collect();if nodes.iter().all(Option::is_none){nodes[1]=Some(&w1[2]);}
 for b in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(z))=>{if b<6{c.cswap(&cl[b],l,z);}else{high_swap(c,r,carry,g,b-6,l,z);}Some(l)},(Some(l),None)|(None,Some(l))=>Some(l),(None,None)=>None});}nodes=next;}let root=nodes[0].unwrap();
 add(c,a,cl,Some(carry),true);let route=c.b.ops[at..].to_vec();normal_flag(c,r,a,cl,g,carry,d,endpoints);c.cx(q,root);super::q794_t10_quotient::gate(c,&[(g,true),(carry,true),(root,true)],q,d);c.cx(q,root);normal_flag(c,r,a,cl,g,carry,d,endpoints);c.b.ops.extend(route.into_iter().rev());
 c1(c,r,cl,g,q,d);assert_eq!(c.b.next_qubit,owned);
}
