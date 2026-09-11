//! Own integrated two-hole modulo4 step. Unverified until native checker passes.
//! Experimental two-phase cargo step. Native and physical validation required.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q798_step as old,q794_moves as moves,length_recompute::mixed_mcx};
#[path="metadata_phase115_programs.rs"] mod programs;
type Terms<'a>=Vec<Vec<(&'a QReg,bool)>>;
thread_local!{static TRACE:std::cell::RefCell<Vec<(&'static str,usize)>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn marks()->Vec<(&'static str,usize)>{TRACE.with(|t|t.borrow().clone())}
pub(super) fn mark(circ:&Circuit,name:&'static str){
    let census=std::env::var_os("Q795_STAGE_CENSUS").is_some();
    if census||std::env::var_os("Q795_TRACE").is_some(){TRACE.with(|t|{
        let mut trace=t.borrow_mut();let first=trace.last().map(|x|x.1).unwrap_or(0);
        if census{let ops=&circ.b.ops[first..];let ccx=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();eprintln!("Q795_STAGE_RAW name={name} ops={} T={ccx}",ops.len());}
        trace.push((name,circ.b.ops.len()));
    });}
}
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
    let right=nodes[0].unwrap();let r=circ.b.ops[start..].to_vec();let(left,l)=super::q794_handoffs::gather_a(circ,rank,a,&w1[..257],3,dirty);
    super::q794_dual_extreme::newborn(circ,rank,a,sign,left,right,dirty);
    circ.b.ops.extend(l.into_iter().rev());circ.b.ops.extend(r.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,sign,Some(p2),dirty,j,true);circ.cx(sign,p2);
}
pub(super) fn step(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,block:usize){
    assert_eq!(helpers.len(),23);let start=circ.b.ops.len();let entry_j=(post_j+3)%4;
    TRACE.with(|t|t.borrow_mut().clear());
    if std::env::var_os("Q795_STAGE_CENSUS").is_some(){eprintln!("Q795_STAGE_START block={block} j={post_j}");TRACE.with(|t|t.borrow_mut().push(("start",start)));}
    let (rfirst,tend)=super::shared_step::SCHEDULE_SUPPORTS[block];let (lo,hi)=super::metadata_entry_head5::A_SUPPORTS[block];let previous=circ.q797_a_support.replace((lo,hi));
    // Iteration is not read until cycle exit. Borrow it, restore it, then exclude
    // it from that exit's lender list. This funds legacy max-control predicates.
    let pool:Vec<_>=helpers.iter().chain(std::iter::once(iteration)).map(QReg::borrowed_alias).collect();let sign=&pool[0];let dirty=&pool[1..];
    if entry_j==0{birth_cargo(circ,rank,a,c,sm,p1,p2,w1,&pool);}
    old::decode_birth(circ,rank,a,c,sm,p1,p2,w2,&pool,entry_j);
    super::q794_t10::emit(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,tend,entry_j);
    mark(circ,"T10");
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,&pool,false);
    let p01=vec![(p1,false),(p2,true)];
    super::q794_r01::signless(circ,rank,a,c,sm,p1,p2,w1,w2,&pool,entry_j,259-rfirst);
    mark(circ,"R01");
    // R01 never reads the coefficient head, for C0 or C>0. Keep its phase
    // passenger there for the whole R01 run rather than moving a Work2 gap.
    old::loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::q794_r00::phase00_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,entry_j,259-rfirst);
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,dirty,true);
    // Both R bodies now have their second cargo at A+2. Terminal R00
    // skipped the pre-rotation and must skip this normalization as well.
    let mut r00=vec![vec![(p1,false),(p2,false)]];let mut terminal=r00[0].clone();terminal.extend((0..5).map(|i|(&rank[i],29>>i&1!=0)));terminal.extend(a.iter().map(|q|(q,true)));r00.push(terminal);
    moves::adjacent_a_terms(circ,rank,a,w2,1,2,&r00,dirty);
    super::metadata_terminal5::emit(circ,rank,a,c,sm,dirty,post_j==0,false);
    super::metadata_phase_counter5::emit(circ,rank,a,c,sm,p1,p2,dirty,entry_j);
    mark(circ,"counter");
    let c1_t10=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    toggle_terms(circ,&c1_t10,sign,dirty);
    let tflag=vec![vec![(p1,true),(p2,false),(sign,true)]];
    super::q794_dual_extreme::inbound(circ,rank,a,&w1[..257],w2,2,&tflag,dirty);
    toggle_terms(circ,&c1_t10,sign,dirty);
    super::q794_dual_extreme::before_entry(circ,rank,a,c,sm,p1,p2,&w1[..257],w2,dirty);
    super::metadata_entry_boundary5::entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,lo,hi);
    newborn(circ,rank,a,c,sm,p2,sign,w1,w2,dirty,post_j);
    super::q794_dual_extreme::after_entry(circ,rank,a,sign,&w1[..257],w2,dirty);
    mark(circ,"entry");
    // Sign is zero on both R phases. Cache a routing predicate there while
    // masking its unrelated phase11 value with P1=false at every exchange.
    let rflag=vec![vec![(p1,false),(sign,true)]];
    // Both R phases retain cargo in the coefficient head. Neither arithmetic
    // reads that head, so R00 continuation and R00->R01 need no handoff.
    let zero=szero(rank,c,sm,post_j);let mut to_t10=product(&vec![p01.clone()],&zero);
    if post_j==0{let mut peak=p01.clone();peak.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));peak.push((&w2[258],false));to_t10.push(peak);}
    let mut to_c1=Vec::new();if post_j==2{for r in [0,13,23,29]{let mut cs=p01.clone();cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(sm.iter().map(|q|(q,false)));to_c1.push(cs);}}
    let mut to_head=to_t10;to_head.extend(to_c1.clone());
    if !to_c1.is_empty(){toggle_terms(circ,&to_c1,sign,dirty);super::q794_dual_extreme::inbound(circ,rank,a,&w1[..257],w2,0,&rflag,dirty);toggle_terms(circ,&to_c1,sign,dirty);}
    if !to_head.is_empty(){toggle_terms(circ,&to_head,sign,dirty);moves::adjacent_a_terms(circ,rank,a,&w1[..257],0,2,&rflag,dirty);toggle_terms(circ,&to_head,sign,dirty);}
    old::encode_birth(circ,rank,a,c,sm,p1,p2,sign,dirty,post_j);
    if post_j==0{birth_cargo(circ,rank,a,c,sm,p1,p2,w1,dirty);}
    old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);
    mark(circ,"before_sign");
    super::q794_sign::emit(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,(tend+1).min(258));old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);old::loan(circ,rank,a,w1,sign,dirty);
    mark(circ,"before_exit");
    if post_j==0{super::q794_metadata_exit::exit_phase_cargo(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi);}
    mark(circ,"after_exit");
    old::phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w2[258],&pool,post_j);
    // Route by final phase: old and newly entered T10 share the A+2 gap.
    moves::adjacent_a_terms(circ,rank,a,w2,2,1,&vec![vec![(p1,false),(p2,true)]],&pool);
    let c1=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    let mut other=vec![vec![(p1,true),(p2,false)]];other.extend(c1.clone());
    moves::adjacent_a_terms(circ,rank,a,w2,2,3,&other,&pool);
    moves::across_a_terms(circ,rank,a,w2,2,&w1[..257],2,&c1,true,&pool);
    let window=std::env::var("Q795_CORE_CANCEL").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(2048);
    mark(circ,"final");
    for op in &circ.b.ops[start..]{for h in [257usize,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"STEP touched omitted Work1[{h}]");}}
    if std::env::var_os("Q795_TRACE").is_none(){let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,window,32);super::shared_optimize::cancel_nct_live(&mut tail,window);
        if std::env::var("Q794_TFACTOR").ok().as_deref()==Some("1") {
            let removed=super::q794_tfactor::apply(&mut tail,4096);
            super::shared_optimize::cancel_nct_live(&mut tail,window);
            if std::env::var_os("Q795_STAGE_CENSUS").is_some(){eprintln!("Q794_TFACTOR block={block} j={post_j} removed_T={removed}");}
        }
        circ.b.ops.extend(tail);}circ.q797_a_support=previous;
}
fn birth_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],dirty:&[QReg]){
    // Encoded true-S256 newborn has C0. Keep its logical Work1[2]=0
    // discriminator visible across the S-zero phase update.
    let mut term=vec![(p1,true),(p2,true)];term.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));
    moves::adjacent_a_terms(circ,rank,a,&w1[..257],2,3,&vec![term],dirty);
}
pub(super) fn r01_correction(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    let terms=ceq(rank,c,0,&[(g,true)]);
    let (source,s)=super::q794_handoffs::gather_a(circ,rank,a,w2,2,dirty);
    let (target,t)=super::q794_handoffs::gather_a(circ,rank,a,&w1[..257],2,dirty);
    for mut term in terms{term.push((source,true));mixed_mcx(circ,&term,target,dirty);}
    circ.b.ops.extend(t.into_iter().rev());circ.b.ops.extend(s.into_iter().rev());
}

