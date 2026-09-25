//! Joint retained-final-carry / overlapping low-constant fold experiment.
//! It preserves the original B comparisons, exactly erases the inserted
//! prefix boundary and final overflow, and explicitly changes the low fold.
use super::*;
thread_local! { pub(super) static GUARD:std::cell::Cell<Option<usize>>=const{std::cell::Cell::new(None)}; }

fn low_bits(guard:usize)->usize { super::super::optional_env::<usize>("PP_JOINT_LOW_BITS").unwrap_or(32+guard) }

#[derive(Debug)]
struct Plan { bounds:Vec<(usize,usize)>, prefix:usize, guard:usize, bits:usize, saving:f64, exact:bool }

fn plan(circ:&Builder,round:usize,multiply:bool,fw:usize)->Option<Plan> {
    if !multiply && env_raw("PP_PREBIAS_RETAIN_BITS").is_some() {return None;}
    let guard=super::super::optional_env::<usize>("PP_JOINT_GUARD")?;
    let low=if env_flag("PP_SPRINT_MIXED") && multiply && (364..=402).contains(&round) {29}else{low_bits(guard)};assert!((12..=fw).contains(&low) && !split_fold());

    assert!(env_flag("PP_REUSE_DIV_PARITY") && env_flag("PP_REUSE_MUL_SELECTORS"));
    let room=walk_max_qubits().saturating_sub(circ.active_qubits()as usize);
    let loans=REPLAY_SIGN_LOANS.with(|s|s.get());
    let old_bounds=composition_bounds(circ,round,multiply)?;
    let bounds=retained_rebalance(circ,&old_bounds,round,multiply);
    if bounds.len()<2 {return None;}
    let &(lo,hi)=bounds.last()?;
    let (plo,phi)=bounds[bounds.len()-2];
    let (k,seeded)=boundary_repair_spec(round,multiply,plo,phi);
    if lo<fw || phi-k-usize::from(seeded)<fw {return None;}
    let need=(low-3).max(fw-34);
    let existing=walk_max_qubits()as isize-circ.active_qubits()as isize-(hi-lo)as isize-if multiply&&env_flag("PP_JOINT_MUL_FOLD"){3}else{4};
    let missing=(need as isize-existing).max(0)as usize;
    let prefix=if missing==0 {0} else {missing+1};
    if prefix+1>=hi-lo {return None;}
    let mut fk=if multiply {flag_compare(round)+usize::from(a5_policy()=="mul-f-plus1-early200"&&(2..202).contains(&round))}
        else {flag_compare(round)+usize::from(policy_width(round)>=flag_widen_div())};
    let seeded=if multiply {policy_width(round)>=38 && matches!(a5_policy(),"mul-f-seed"|"mul-fb-seed")}else{env_flag("CMP_SEED_ALL")};
    if !multiply && seeded {fk-=1;}
    if !seeded {fk=refined_unseeded_width(fk,N,"PP_REFINE_UNSEEDED_F");}
    let saving=(fk-1)as f64/2.0-missing as f64/2.0-(low as f64-33.0);
    if saving<=0.0 {return None;}
    // Release a bounded additional carry prefix to fit the full finite fold.
    // Outer B comparisons are unchanged; the inserted midpoint uses exact cleanup.
    let limit=super::super::optional_env::<usize>("PP_RETAIN_EXACT_EXTRA_MUL").unwrap_or(0);
    let exact_missing=((fw-3) as isize-existing).max(0) as usize;
    let exact_prefix=if exact_missing==0 {0}else{exact_missing+1};
    let exact=multiply && env_flag("PP_RETAIN_EXACT_MUL") && exact_missing<=limit && exact_prefix+1<hi-lo;
    let prefix=if exact {exact_prefix}else{prefix};
    let saving=if exact {saving-(exact_missing-missing) as f64/2.0-1.0}else{saving};
    Some(Plan{bounds,prefix,guard,bits:low,saving,exact})
}

pub(super) fn try_replay(circ:&mut Builder,sign:QubitId,a:&[QubitId],b:&[QubitId],fw:usize,
    round:usize,doubled:Option<QubitId>)->bool {
    let multiply=doubled.is_some();
    let Some(p)=plan(circ,round,multiply,fw)else{return false;};
    eprintln!("JOINT_LOWFOLD r={} mul={} base={} last={} prefix={} guard={} saving={}",round,multiply as u8,
        circ.active_qubits(),p.bounds.last().unwrap().1-p.bounds.last().unwrap().0,p.prefix,p.guard,p.saving);
    if env_flag("PP_COMPOSE_TRACE"){eprintln!("COMPOSE_MUL {} {} {} {} {} {:?}",round,circ.active_qubits(),fw,p.bits,REPLAY_SIGN_LOANS.with(|s|s.get()),p.bounds);}
    if p.exact {eprintln!("EXACT_RETAINED_FOLD mul {} {}",round,fw);}
    let mut incoming=None;
    let mut previous=None;
    // EXP PP_PREBIAS_DOUBLE: bit 0 leaves the main add. z0 = s^a0 by CX, and the
    // missing carry s&a0 joins the fold's own bit-1 carry (the two are exclusive).
    let pre=multiply && env_flag("PP_PREBIAS_DOUBLE");
    if pre {circ.cx(a[0],b[0]);}
    for &(lo,hi)in &p.bounds {
        let next=circ.alloc_qubit();
        if hi==N {
            let split=lo+p.prefix;
            let mid=if p.prefix==0 {incoming}else{
                let m=circ.alloc_qubit();ripple_add(circ,&a[lo..split],&b[lo..split],incoming,Some(m));Some(m)
            };
            super::super::modular::ripple_add_consume(circ,&a[split..hi],&b[split..hi],mid,next,
                |c,o,at,st,carry|{
                    GUARD.with(|g|{assert!(g.replace(if p.exact {None}else{Some(p.bits)}).is_none());});
                    if let Some(d)=doubled {
                        if env_flag("PP_JOINT_MUL_FOLD"){fold_double_joint(c,&b[..fw],sign,a[0],d,o,pre);}else{fold_double_reused(c,&b[..fw],sign,d,o);}
                        c.cx(b[0],d);c.cx(sign,d);c.cx(a[0],d);c.cx(o,d);c.free(d);
                    }else{fold_halve_reused(c,&b[..fw],sign,o);}
                    GUARD.with(|g|g.set(None));
                    super::super::modular::erase_overflow_from_frame(c,o,at,st,carry);
                });
            if p.prefix>0 {
                let mid=mid.unwrap();
                // Exact: carry(a+b+incoming) = [sum<a]+[sum=a]*incoming.
                erase_with_compare(circ,mid,&b[lo..split],&a[lo..split],incoming);circ.free(mid);
            }
        }else{let at=if pre&&lo==0{1}else{lo};ripple_add(circ,&a[at..hi],&b[at..hi],incoming,Some(next));}
        if let Some((q,plo,phi))=previous {
            let(k,seeded)=boundary_repair_spec(round,multiply,plo,phi);
            circ.record_replay_site('B',round,phi,k);
            // A full first-chunk compare must skip bit 0, which the add no longer covers.
            let from=if pre&&plo==0&&phi==k{1}else{phi-k};
            erase_with_compare(circ,q,&b[from..phi],&a[from..phi],seeded.then(||a[phi-k-1]));circ.free(q);
        }
        incoming=Some(next);previous=Some((next,lo,hi));
    }
    true
}

pub(super) fn fold(circ:&mut Builder,acc:&[QubitId],f:U256,plus:QubitId,twice:Option<QubitId>,minus:QubitId,first:QubitId,g:usize) {
    assert_eq!(f>>32usize,U256::from(1));let low=g;assert!(low<=acc.len());
    let small=f&((U256::from(1)<<32usize)-U256::from(1));
    fold_selected_single(circ,&acc[..low],small,plus,twice,minus,first);
    let boundary=circ.alloc_qubit();
    with_selector_xor(circ,&[plus,minus],plus,|c,q|c.ccx(acc[32],q,boundary));
    fold_selected_single(circ,&acc[32..],U256::from(1),plus,twice,minus,boundary);
    with_selector_xor(circ,&[plus,minus],plus,|c,q|{
        c.cx(q,acc[32]);and_uncompute(c,boundary,acc[32],q);c.cx(q,acc[32]);
    });
}
