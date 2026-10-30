/// Move the existing known-copy terminal's X measurement before the ladder.
/// Borrow its now-zero result wire for the final carry; defer the same
/// Clifford phase repair until the terminal inputs exist, then restore the
/// result copy only after all carry wires have been erased. No new precision.
pub(crate) fn result_top_loan_enabled(acc:&[QubitId])->bool {
    acc.len()>=4 && has_top_copy(acc) && super::env_flag("I74_RESULT_TOP_LOAN")
}

pub(crate) fn ripple_add_result_top_loan(
    c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,lent:Option<QubitId>,source_loan:bool,
) {
    let n=b.len();assert_eq!(a.len(),n);assert!(n>=3+usize::from(lent.is_some())+usize::from(source_loan));
    assert!(has_top_copy(b));assert!(a.iter().all(|q|!b.contains(q)));
    if let Some(q)=lent {assert!(!a.contains(&q)&&!b.contains(&q));}
    let top=b[n-1];let phase=c.alloc_bit();c.hmr(top,phase);
    if source_loan {c.cx(a[n-2],a[n-1]);}
    let owned=n-3-usize::from(lent.is_some())-usize::from(source_loan);
    let mut carries=c.alloc_qubits(owned);carries.extend(lent);if source_loan {carries.push(a[n-1]);}carries.push(top);
    let previous=|i:usize|if i==0{cin}else{Some(carries[i-1])};
    for i in 0..carries.len(){carry_step(c,a[i],b[i],previous(i),carries[i]);}
    let i=n-2;let p=*carries.last().unwrap();
    c.cx(p,a[i]);c.cx(p,b[i]);
    // Identical terminal_top_copy phase polynomial, evaluated in the same
    // folded penultimate frame. The old top bit was measured earlier.
    if source_loan {
        // Original top source is the penultimate source before folding.
        // Its Z cancels folded-a's Z, leaving Z of the incoming carry.
        c.cz_if(a[i],b[i],phase);c.z_if(p,phase);c.z_if(b[i],phase);
    }else{c.z_if(a[n-1],phase);c.cz_if(a[i],b[i],phase);c.z_if(a[i],phase);c.z_if(b[i],phase);}
    c.free_bit(phase);
    c.cx(p,a[i]);c.cx(a[i],b[i]);
    // Keep top as the arithmetic carry until its loan has been paid back.
    for i in (0..carries.len()).rev(){
        if i<owned {unwind_carry_step(c,a[i],b[i],previous(i),carries[i]);}
        else {unwind_carry_step_lent(c,a[i],b[i],previous(i),carries[i]);}
    }
    if source_loan {c.cx(a[n-2],a[n-1]);}
    c.cx(b[n-2],top);
}
