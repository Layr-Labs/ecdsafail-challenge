//! Candidate three-hole modulo8 step. Full native qualification is mandatory.
//! Experimental two-phase cargo step. Native and physical validation required.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q798_step as old,q794_moves as moves,length_recompute::mixed_mcx};
#[path="metadata_phase115_programs.rs"] mod programs;
type Terms<'a>=Vec<Vec<(&'a QReg,bool)>>;
thread_local!{static TRACE:std::cell::RefCell<Vec<(&'static str,usize)>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn marks()->Vec<(&'static str,usize)>{TRACE.with(|t|t.borrow().clone())}
pub(super) fn mark(circ:&Circuit,name:&'static str){
    let census=std::env::var_os("Q795_STAGE_CENSUS").is_some();
    if census||std::env::var_os("Q795_TRACE").is_some()||super::q793_mbu::capturing(){TRACE.with(|t|{
        let mut trace=t.borrow_mut();let first=trace.last().map(|x|x.1).unwrap_or(0);
        if census{let ops=&circ.b.ops[first..];let ccx=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();eprintln!("Q795_STAGE_RAW name={name} ops={} T={ccx}",ops.len());}
        trace.push((name,circ.b.ops.len()));
    });}
}
fn mcx_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
/// Exact rank-function factoring for a bank of target-XOR product terms.
///
/// After duplicate literals are merged, terms are grouped by their identical
/// non-rank conjunction B.  The rank part is tabulated on all 32 codes, so no
/// reachable-state or disjoint-cover premise is used.  With arbitrary dirty d,
/// D_(B,d) H_d D_(B,d)^-1 H_d toggles the target by B*H and restores d.
/// The direct bank remains the fallback unless the exact dirty-ladder T model
/// proves the echo strictly cheaper.
fn toggle_terms(circ:&mut Circuit,terms:&Terms<'_>,rank:&[QReg],target:&QReg,dirty:&[QReg]){
    if !super::metadata_muxlease::active("Q793_RANK_ECHO_STEP")||dirty.len()<2{for term in terms{mixed_mcx(circ,term,target,dirty);}return;}
    let rank_pos=|q:&QReg|rank.iter().position(|r|r.id()==q.id());
    struct Group<'a>{key:Vec<(&'a QReg,bool)>,truth:Vec<bool>,direct:usize,members:Vec<usize>}
    let mut groups:Vec<Group>=Vec::new();
    for (n,term) in terms.iter().enumerate(){
        let mut unique:Vec<(&QReg,bool)>=Vec::new();let mut skip=false;
        for &(q,v) in term{assert_ne!(q.id(),target.id());if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{skip=true;break;}}else{unique.push((q,v));}}
        if skip{continue;}
        let mut key:Vec<_>=unique.iter().copied().filter(|(q,_)|rank_pos(q).is_none()).collect();key.sort_by_key(|(q,_)|q.id());
        let lits:Vec<_>=unique.iter().filter_map(|&(q,v)|rank_pos(q).map(|i|(i,v))).collect();
        let at=match groups.iter().position(|g|g.key.len()==key.len()&&g.key.iter().zip(&key).all(|(a,b)|a.0.id()==b.0.id()&&a.1==b.1)){Some(i)=>i,None=>{groups.push(Group{key,truth:vec![false;32],direct:0,members:Vec::new()});groups.len()-1}};
        for code in 0..32{if lits.iter().all(|&(i,v)|(code>>i&1!=0)==v){groups[at].truth[code]^=true;}}
        groups[at].direct+=mcx_cost(unique.len());groups[at].members.push(n);
    }
    let d=&dirty[0];let rest=&dirty[1..];
    for group in groups{
        if group.truth.iter().all(|&v|!v){continue;}
        let (polarity,monomials)=super::metadata_muxlease::swap_terms(group.truth,5);
        let rank_cost:usize=monomials.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum();
        let echo_cost=2*rank_cost+2*mcx_cost(group.key.len()+1);
        if group.direct<=echo_cost{for n in group.members{mixed_mcx(circ,&terms[n],target,dirty);}continue;}
        for &(q,_) in &group.key{assert_ne!(q.id(),d.id(),"rank echo scratch aliases shared controls");}
        let compute=|circ:&mut Circuit|{
            for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}
            for &m in &monomials{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}
            for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}
        };
        let consume=|circ:&mut Circuit|{let mut cs=vec![(d,true)];cs.extend_from_slice(&group.key);mixed_mcx(circ,&cs,target,rest);};
        consume(circ);compute(circ);consume(circ);compute(circ);
    }
}
/// Conjugate one reversible body by a rank-factored predicate while keeping
/// the rank chart live in one arbitrary borrowed wire across the body.
///
/// For F=B*H(rank), C=X_target^(B*d), and D=X_d^H, `C D C` toggles
/// target by F and leaves d^H.  Therefore `C D C U C D C` is exactly
/// F U F and restores arbitrary d.  The body receives lenders excluding d.
/// This is selected only when its native CCX cost is strictly below two
/// independently restored predicate toggles.
fn toggle_pair_around<F>(circ:&mut Circuit,terms:&Terms<'_>,rank:&[QReg],target:&QReg,dirty:&[QReg],switch:&str,body:F)
where F:FnOnce(&mut Circuit,&[QReg]){
    if !super::metadata_muxlease::active(switch)||dirty.len()<3{
        toggle_terms(circ,terms,rank,target,dirty);body(circ,dirty);toggle_terms(circ,terms,rank,target,dirty);return;
    }
    let rank_pos=|q:&QReg|rank.iter().position(|r|r.id()==q.id());
    let mut key:Option<Vec<(&QReg,bool)>>=None;let mut truth=vec![false;32];let mut direct=0usize;
    for term in terms{
        let mut unique:Vec<(&QReg,bool)>=Vec::new();let mut skip=false;
        for &(q,v) in term{assert_ne!(q.id(),target.id());if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{skip=true;break;}}else{unique.push((q,v));}}
        if skip{continue;}
        let mut base:Vec<_>=unique.iter().copied().filter(|(q,_)|rank_pos(q).is_none()).collect();base.sort_by_key(|(q,_)|q.id());
        if let Some(want)=&key{assert!(want.len()==base.len()&&want.iter().zip(&base).all(|(a,b)|a.0.id()==b.0.id()&&a.1==b.1),"held rank chart requires one shared non-rank rectangle");}else{key=Some(base);}
        let lits:Vec<_>=unique.iter().filter_map(|&(q,v)|rank_pos(q).map(|i|(i,v))).collect();
        for code in 0..32{if lits.iter().all(|&(i,v)|(code>>i&1!=0)==v){truth[code]^=true;}}
        direct+=mcx_cost(unique.len());
    }
    let key=key.unwrap_or_default();let (polarity,monomials)=super::metadata_muxlease::swap_terms(truth,5);
    let rank_cost:usize=monomials.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum();
    let consume_cost=mcx_cost(key.len()+1);let restored_pair=2*direct.min(2*rank_cost+2*consume_cost);let held=2*rank_cost+4*consume_cost;
    if held>=restored_pair{toggle_terms(circ,terms,rank,target,dirty);body(circ,dirty);toggle_terms(circ,terms,rank,target,dirty);return;}
    let d=&dirty[0];let rest=&dirty[1..];for &(q,_)in &key{assert_ne!(q.id(),d.id(),"held rank chart aliases shared controls");}
    let compute=|circ:&mut Circuit|{
        for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}
        for &m in &monomials{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}
        for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}
    };
    let consume=|circ:&mut Circuit|{let mut cs=vec![(d,true)];cs.extend_from_slice(&key);mixed_mcx(circ,&cs,target,rest);};
    consume(circ);compute(circ);consume(circ);body(circ,rest);consume(circ);compute(circ);consume(circ);
}
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
pub(super) fn newborn(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    circ.cx(sign,p2);
    super::metadata_phase115_phased::prepare(circ,c,sm,sign,Some(p2),dirty,j,false);
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for endpoint in [false,true] {
        let start=circ.b.ops.len();let mut nodes=vec![None;512];
        for value in 1..=if endpoint{4}else{257}{nodes[value]=Some(&w2[259-value]);}
        for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
            (Some(left),Some(right))=>{
                if level<6{circ.cswap(&c[level],left,right);}else{
                    let ctrl:Vec<_>=rank.iter().chain(std::iter::once(p2)).collect();let truth:Vec<_>=(0..64).map(|r|((ts[r&31][1]+ts[r&31][2]+(r>>5))>>(level-6))&1!=0).collect();
                    super::metadata_muxlease::truth_swap(circ,&ctrl,truth,left,right,dirty);
                    if level==8&&j==0&&!endpoint{let mut cs=vec![(sign,true)];cs.extend(rank.iter().chain(sm).map(|q|(q,false)));circ.cx(right,left);cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);}
                }Some(left)
            },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
        });}nodes=next;}
        let right=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
        if endpoint {
            super::q793_cargo_r02::newborn_253(circ,rank,a,sign,&w2[254],right,dirty);
        }else{
            let(left,gather)=super::q794_handoffs::gather_a(circ,rank,a,&w1[..256],3,dirty);
            super::q793_cargo_r02::newborn_regular(circ,rank,a,sign,left,right,dirty);
            circ.b.ops.extend(gather.into_iter().rev());
        }
        circ.b.ops.extend(route.into_iter().rev());
    }
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
    super::q793_t10_full_v13::emit(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,tend,entry_j);
    mark(circ,"T10");
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,&pool,false);
    let p01=vec![(p1,false),(p2,true)];
    super::q793_r01_dynamic_timefix_r01::signless(circ,rank,a,c,sm,p1,p2,w1,w2,&pool,entry_j,259-rfirst);
    mark(circ,"R01");
    // R01 never reads the coefficient head, for C0 or C>0. Keep its phase
    // passenger there for the whole R01 run rather than moving a Work2 gap.
    mark(circ,"mbu_before_loan");super::q793_loans::global_a(circ,rank,a,sign,w1,&w2[258],None,dirty);mark(circ,"mbu_after_loan");circ.ccx(p1,p2,sign);
    let mut low_seed=|cc:&mut Circuit,mask:&QReg,carry:&QReg,dd:&[QReg],clock:usize|super::q793_r00_seed_dynamic_r02::emit(cc,rank,a,w1,w2,mask,carry,dd,clock);
    super::q793_r00::phase00_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,entry_j,259-rfirst,&mut low_seed);
    mark(circ,"mbu_after_r00");
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,dirty,true);
    // Both R bodies now have their second cargo at A+2. Terminal R00
    // skipped the pre-rotation and must skip this normalization as well.
    let mut r00=vec![vec![(p1,false),(p2,false)]];let mut terminal=r00[0].clone();terminal.extend((0..5).map(|i|(&rank[i],29>>i&1!=0)));terminal.extend(a.iter().map(|q|(q,true)));r00.push(terminal);
    moves::adjacent_a_terms(circ,rank,a,w2,1,2,&r00,dirty);
    super::metadata_terminal5::emit(circ,rank,a,c,sm,dirty,post_j==0,false);
    super::metadata_phase_counter5::emit_for_block(circ,rank,a,c,sm,p1,p2,dirty,entry_j,block);
    mark(circ,"counter");
    let c1_t10=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    let tflag=vec![vec![(p1,true),(p2,false),(sign,true)]];
    toggle_pair_around(circ,&c1_t10,rank,sign,dirty,"Q793_C1_HOLD",|circ,lenders|super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,2,&tflag,lenders));
    super::q793_cargo_r02::normalize_old11(circ,rank,a,c,sm,p1,p2,w2,post_j,dirty);
    super::q793_cargo_r02::before_entry(circ,rank,a,c,sm,p1,p2,w2,dirty);
    super::metadata_entry_boundary5::entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,lo,hi);
    newborn(circ,rank,a,c,sm,p2,sign,w1,w2,dirty,post_j);
    super::q793_cargo_r02::after_entry(circ,rank,a,sign,w2,dirty);
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
    if !to_c1.is_empty(){toggle_pair_around(circ,&to_c1,rank,sign,dirty,"Q793_C1_J2_HOLD",|circ,lenders|super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,0,&rflag,lenders));}
    if !to_head.is_empty(){toggle_terms(circ,&to_head,rank,sign,dirty);super::q793_cargo_r02::head_to_two(circ,rank,a,c,w1,w2,&rflag,dirty);toggle_terms(circ,&to_head,rank,sign,dirty);}
    old::encode_birth(circ,rank,a,c,sm,p1,p2,sign,dirty,post_j);
    if post_j==0{birth_cargo(circ,rank,a,c,sm,p1,p2,w1,dirty);}
    old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);
    mark(circ,"before_sign");
    super::q793_sign_dynamic_r06::emit(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,(tend+1).min(258));old::hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);super::q793_loans::global_a(circ,rank,a,sign,w1,&w2[258],None,dirty);
    mark(circ,"before_exit");
    if post_j==0{super::q793_metadata_exit::exit_phase_cargo(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi);}
    mark(circ,"after_exit");
    old::phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w2[258],&pool,post_j);
    // Route by final phase: old and newly entered T10 share the A+2 gap.
    moves::adjacent_a_terms(circ,rank,a,w2,2,1,&vec![vec![(p1,false),(p2,true)]],&pool);
    let c1=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    let mut other=vec![vec![(p1,true),(p2,false)]];other.extend(c1.clone());
    moves::adjacent_a_terms(circ,rank,a,w2,2,3,&other,&pool);
    super::q793_cargo_r02::finish_c1(circ,rank,a,w1,w2,&c1,&pool);
    let window=std::env::var("Q795_CORE_CANCEL").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(2048);
    mark(circ,"final");
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"STEP touched omitted Work1[{h}]");}}
    if std::env::var_os("Q795_TRACE").is_none()&&!super::q793_mbu::capturing(){let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,window,8);super::shared_optimize::cancel_nct_live(&mut tail,window);
        if std::env::var("Q794_TFACTOR").ok().as_deref()==Some("1") {
            let removed=super::q794_tfactor::apply(&mut tail,64);
            super::shared_optimize::cancel_nct_live(&mut tail,window);
            if std::env::var_os("Q795_STAGE_CENSUS").is_some(){eprintln!("Q794_TFACTOR block={block} j={post_j} removed_T={removed}");}
        }
        circ.b.ops.extend(tail);}circ.q797_a_support=previous;
}
fn birth_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],dirty:&[QReg]){
    // Encoded true-S256 newborn has C0. Keep its logical Work1[2]=0
    // discriminator visible across the S-zero phase update.
    let mut term=vec![(p1,true),(p2,true)];term.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));
    moves::adjacent_a_terms(circ,rank,a,&w1[..256],2,3,&vec![term],dirty);
}

/// Passive read-only metadata templates for the own fold20 lowering.
pub(super) fn passive20_template(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,kind:usize){
    let pool:Vec<_>=helpers.iter().chain(std::iter::once(iteration)).map(QReg::borrowed_alias).collect();let sign=&pool[0];let dirty=&pool[1..];let p01=vec![(p1,false),(p2,true)];
    match kind{
    0=>{    let c1_t10=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    let tflag=vec![vec![(p1,true),(p2,false),(sign,true)]];
    toggle_pair_around(circ,&c1_t10,rank,sign,dirty,"Q793_C1_HOLD",|circ,lenders|super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,2,&tflag,lenders));
    super::q793_cargo_r02::normalize_old11(circ,rank,a,c,sm,p1,p2,w2,post_j,dirty);
    super::q793_cargo_r02::before_entry(circ,rank,a,c,sm,p1,p2,w2,dirty);
},
    1=>{    let rflag=vec![vec![(p1,false),(sign,true)]];
    // Both R phases retain cargo in the coefficient head. Neither arithmetic
    // reads that head, so R00 continuation and R00->R01 need no handoff.
    let zero=szero(rank,c,sm,post_j);let mut to_t10=product(&vec![p01.clone()],&zero);
    if post_j==0{let mut peak=p01.clone();peak.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));peak.push((&w2[258],false));to_t10.push(peak);}
    let mut to_c1=Vec::new();if post_j==2{for r in [0,13,23,29]{let mut cs=p01.clone();cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(sm.iter().map(|q|(q,false)));to_c1.push(cs);}}
    let mut to_head=to_t10;to_head.extend(to_c1.clone());
    if !to_c1.is_empty(){toggle_pair_around(circ,&to_c1,rank,sign,dirty,"Q793_C1_J2_HOLD",|circ,lenders|super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,0,&rflag,lenders));}
    if !to_head.is_empty(){toggle_terms(circ,&to_head,rank,sign,dirty);super::q793_cargo_r02::head_to_two(circ,rank,a,c,w1,w2,&rflag,dirty);toggle_terms(circ,&to_head,rank,sign,dirty);}
},
    2=>{    old::phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w2[258],&pool,post_j);
    // Route by final phase: old and newly entered T10 share the A+2 gap.
    moves::adjacent_a_terms(circ,rank,a,w2,2,1,&vec![vec![(p1,false),(p2,true)]],&pool);
    let c1=ceq(rank,c,1,&[(p1,true),(p2,false)]);
    let mut other=vec![vec![(p1,true),(p2,false)]];other.extend(c1.clone());
    moves::adjacent_a_terms(circ,rank,a,w2,2,3,&other,&pool);
    super::q793_cargo_r02::finish_c1(circ,rank,a,w1,w2,&c1,&pool);
},
    3=>{let mut r00=vec![vec![(p1,false),(p2,false)]];let mut terminal=r00[0].clone();terminal.extend((0..5).map(|i|(&rank[i],29>>i&1!=0)));terminal.extend(a.iter().map(|q|(q,true)));r00.push(terminal);moves::adjacent_a_terms(circ,rank,a,w2,1,2,&r00,dirty);},
    4=>{super::q793_cargo_r02::after_entry(circ,rank,a,sign,w2,dirty);},
    5=>{super::q793_cargo_r02::normalize_old11(circ,rank,a,c,sm,p1,p2,w2,post_j,dirty);super::q793_cargo_r02::before_entry(circ,rank,a,c,sm,p1,p2,w2,dirty);},
    6=>{old::phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w2[258],&pool,post_j);},
    _=>panic!("unknown passive20 section"),
    }
}

pub(super) fn final20_provided(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],t10:bool){
    if !t10{moves::adjacent_a_terms(circ,rank,a,w2,2,1,&vec![vec![(g,true)]],dirty);return;}
    let c1=ceq(rank,c,1,&[(g,true)]);let mut other=vec![vec![(g,true)]];other.extend(c1.clone());moves::adjacent_a_terms(circ,rank,a,w2,2,3,&other,dirty);super::q793_cargo_r02::finish_c1(circ,rank,a,w1,w2,&c1,dirty);
}

/// Both final phase transports share one unfolded metadata chart.
/// `active = P1 xor P2`; selector retains the original P2.
pub(super) fn final20_mux_provided(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],active:&QReg,selector:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    moves::adjacent_a_terms(circ,rank,a,w2,2,1,&vec![vec![(active,true),(selector,true)]],dirty);
    let base=vec![(active,true),(selector,false)];
    let c1=ceq(rank,c,1,&base);let mut other=vec![base];other.extend(c1.clone());
    moves::adjacent_a_terms(circ,rank,a,w2,2,3,&other,dirty);
    super::q793_cargo_r02::finish_c1(circ,rank,a,w1,w2,&c1,dirty);
}
