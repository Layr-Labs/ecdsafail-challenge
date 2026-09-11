//! Complete decoded EEA step carrying a missing phase lane's arbitrary cargo.
//! P2 is borrowed for the complete traversal; endpoints return its passenger.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q798_step as old,q797_cargo_moves as moves,length_recompute::mixed_mcx};
#[path="metadata_phase115_programs.rs"] mod programs;
type Terms<'a>=Vec<Vec<(&'a QReg,bool)>>;
fn toggle_terms(circ:&mut Circuit,terms:&Terms<'_>,target:&QReg,dirty:&[QReg]){for term in terms{mixed_mcx(circ,term,target,dirty);}}
fn ceq<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize,base:&[(&'a QReg,bool)])->Terms<'a>{
    programs::C_EQUAL[value>>6].iter().map(|&(m,v)|{let mut cs=base.to_vec();cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()
}
fn product<'a>(a:&Terms<'a>,b:&Terms<'a>)->Terms<'a>{
    let mut out=Vec::new();for x in a{for y in b{let mut z=x.clone();let mut valid=true;for &(q,v)in y{if let Some(&(_,old))=z.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{valid=false;break;}}else{z.push((q,v));}}if valid{out.push(z);}}}out
}
fn szero<'a>(rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],j:usize)->Terms<'a>{
    if j%2==1{return vec![];}
    programs::S_ZERO[0].iter().map(|&(m,v)|{let mut cs=vec![(&c[0],j==2)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()
}
fn newborn(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    circ.cx(sign,p2); // P2 is now a clean carry cache on newborn phase11.
    super::metadata_phase115_phased::prepare(circ,c,sm,sign,Some(p2),dirty,j,false);
    let start=circ.b.ops.len();let mut nodes=vec![None;512];for value in 1..=257{nodes[value]=Some(&w2[259-value]);}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{
            if level<6{circ.cswap(&c[level],left,right);}else{
                let ctrl:Vec<_>=rank.iter().chain(std::iter::once(p2)).collect();let truth:Vec<_>=(0..64).map(|r|((ts[r&31][1]+ts[r&31][2]+(r>>5))>>(level-6))&1!=0).collect();
                super::metadata_muxlease::truth_swap(circ,&ctrl,truth,left,right,dirty);
                // On a newborn S_raw0 at j0 the actual S is256, not0.
                if level==8&&j==0{let mut cs=vec![(sign,true)];cs.extend(rank.iter().chain(sm).map(|q|(q,false)));circ.cx(right,left);cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);}
            }Some(left)
        },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let right=nodes[0].unwrap();let r=circ.b.ops[start..].to_vec();let(left,l)=super::q798_handoffs::gather_a(circ,rank,a,w1,3,dirty);
    circ.cswap(sign,left,right);circ.cx(sign,left); // restore the old zero gap
    circ.b.ops.extend(l.into_iter().rev());circ.b.ops.extend(r.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,sign,Some(p2),dirty,j,true);circ.cx(sign,p2);
}
pub(super) fn step(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,block:usize){
    assert_eq!(helpers.len(),23);let start=circ.b.ops.len();let entry_j=(post_j+3)%4;
    let (rfirst,tend)=super::shared_step::SCHEDULE_SUPPORTS[block];let (lo,hi)=super::metadata_entry_head5::A_SUPPORTS[block];let previous=circ.q797_a_support.replace((lo,hi));
    // Iteration is not read until cycle exit. Borrow it, restore it, then exclude
    // it from that exit's lender list. This funds legacy max-control predicates.
    let pool:Vec<_>=helpers.iter().chain(std::iter::once(iteration)).map(QReg::borrowed_alias).collect();let sign=&pool[0];let dirty=&pool[1..];
    old::decode_birth(circ,rank,a,c,sm,p1,p2,w2,&pool,entry_j);
    old::loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    super::metadata_arithmetic5_encoded::phase10_with_support(circ,rank,a,c,p1,p2,sign,w1,w2,dirty,tend);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);circ.ccx(p1,p2,sign);old::loan(circ,rank,a,w1,sign,dirty);
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,&pool,false);
    let p01=vec![(p1,false),(p2,true)];
    super::metadata_remainder015_funded::signless(circ,rank,a,c,sm,p1,p2,w1,w2,&pool,entry_j,259-rfirst);
    // R01 never reads the coefficient head, for C0 or C>0. Keep its phase
    // passenger there for the whole R01 run rather than moving a Work2 gap.
    old::loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::metadata_remainder5_phased::phase00_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,entry_j,259-rfirst);
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,dirty,true);
    super::metadata_terminal5::emit(circ,rank,a,c,sm,dirty,post_j==0,false);
    super::metadata_phase_counter5::emit(circ,rank,a,c,sm,p1,p2,dirty,entry_j);
    let c1_t10=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    toggle_terms(circ,&c1_t10,sign,dirty);
    let tflag=vec![vec![(p1,true),(p2,false),(sign,true)]];
    moves::adjacent_a_terms_flip(circ,rank,a,w1,2,3,&tflag,dirty);
    toggle_terms(circ,&c1_t10,sign,dirty);
    super::metadata_entry_boundary5::entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,lo,hi);
    newborn(circ,rank,a,c,sm,p2,sign,w1,w2,dirty,post_j);
    // Sign is zero on both R phases. Cache a routing predicate there while
    // masking its unrelated phase11 value with P1=false at every exchange.
    let rflag=vec![vec![(p1,false),(sign,true)]];
    // Both R phases retain cargo in the coefficient head. Neither arithmetic
    // reads that head, so R00 continuation and R00->R01 need no handoff.
    let zero=szero(rank,c,sm,post_j);let mut to_t10=product(&vec![p01.clone()],&zero);
    if post_j==0{let mut peak=p01.clone();peak.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));peak.push((&w2[258],false));to_t10.push(peak);}
    let mut to_c1=Vec::new();if post_j==2{for r in [0,13,23,29]{let mut cs=p01.clone();cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(sm.iter().map(|q|(q,false)));to_c1.push(cs);}}
    let mut to_head=to_t10;to_head.extend(to_c1.clone());
    if !to_c1.is_empty(){toggle_terms(circ,&to_c1,sign,dirty);moves::adjacent_a_terms_flip(circ,rank,a,w1,0,3,&rflag,dirty);toggle_terms(circ,&to_c1,sign,dirty);}
    if !to_head.is_empty(){toggle_terms(circ,&to_head,sign,dirty);moves::adjacent_a_terms(circ,rank,a,w1,0,2,&rflag,dirty);toggle_terms(circ,&to_head,sign,dirty);}
    old::encode_birth(circ,rank,a,c,sm,p1,p2,sign,dirty,post_j);old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);
    super::q798_sign_erase::emit(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,(tend+1).min(258));old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);old::loan(circ,rank,a,w1,sign,dirty);
    if post_j==0{super::metadata_exit_boundary5::exit_phase_cargo(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi);}
    old::phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w2[258],&pool,post_j);
    let window=std::env::var("Q795_CORE_CANCEL").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(2048);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,window,8);super::shared_optimize::cancel_nct_live(&mut tail,window);circ.b.ops.extend(tail);circ.q797_a_support=previous;
}
