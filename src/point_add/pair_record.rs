// R73 experimental exact public-pair record. Independent algebraic codec;
// the older WL codec in this base belongs to odinfree21857b5 and is disabled
// when this option is active. No fitted caller or score is implied.
// LFA2_PAIR=1 alone selects legacy (1,2),(3,4),... .
// LFA2_PAIR_MATCH=104523 selects partner digits on positions 0..5, repeated
// with origin zero: (0,1),(2,4),(3,5). Any fixed-point-free involution is valid.
// A pair is packed only when both endpoints are A ticks; other A ticks are raw.
// At most one e>=4 per pair, and emax<=5, are semantic requirements.
fn a2_pair() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_PAIR").is_ok_and(|v| v == "1"))
}
fn a2_pair_matching() -> Option<[usize;6]> {
    static V: OnceLock<Option<[usize;6]>> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_PAIR_MATCH").ok().map(|v| {
        let b=v.as_bytes();
        assert_eq!(b.len(),6,"LFA2_PAIR_MATCH requires six partner digits");
        let mut p=[0usize;6];
        for i in 0..6 {
            assert!((b'0'..=b'5').contains(&b[i]),"matching digit outside 0..5");
            p[i]=(b[i]-b'0') as usize;
        }
        for i in 0..6 { assert!(p[i]!=i && p[p[i]]==i,"matching must be a fixed-point-free involution"); }
        p
    }))
}
fn a2_pair_partner(t: usize) -> usize {
    if let Some(p)=a2_pair_matching() { 6*(t/6)+p[t%6] }
    else { assert!(t>=1); if t%2==0 { t-1 } else { t+1 } }
}
fn a2_pair_start(t: usize) -> usize { t.min(a2_pair_partner(t)) }
fn a2_pair_second(t: usize) -> bool {
    if t<1 || !a2_tick(t) { return false; }
    let other=a2_pair_partner(t);
    other<t && a2_tick(other)
}
thread_local! {
    // Host bookkeeping only. The three live physical record cells are the
    // first tick's field F and the two original k2 wire ids r,s.
    static A2_PAIR_PACKED: std::cell::RefCell<std::collections::BTreeSet<usize>> = const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
}
fn a2_pair_is_packed(t: usize) -> bool {
    A2_PAIR_PACKED.with(|v| v.borrow().contains(&a2_pair_start(t)))
}
fn a2_pair_spent(t: usize) -> Lin {
    if !a2_pair_second(t) { return Lin::k(false); }
    assert!(!a2_pair_is_packed(t), "pair quota read before pop / after commit");
    Lin::of(&[a2_field(a2_pair_partner(t))[0].expect("pair quota: prior raw flag")])
}
fn a2_pair_swap(c: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    c.cx(b,a); c.ccx(ctrl,a,b); c.cx(b,a);
}
fn a2_pair_commit(c: &mut Builder, t: usize, k3: QubitId) {
    assert!(a2_emax(t)<=5, "pair record requires emax<=5");
    assert_eq!(a2_field(t)[0],Some(k3), "pair decision must write its dense field slot");
    if !a2_pair_second(t) { return; }
    let first=a2_pair_partner(t);
    let f=a2_field(first)[0].expect("pair first flag");
    let r=a2_cell(first).expect("pair first k2");
    let s=a2_cell(t).expect("pair second k2");
    assert!(A2_PAIR_PACKED.with(|v| v.borrow_mut().insert(first)), "pair committed twice");
    // F=f0+f1; swap the small-bit values when the second letter is big.
    c.cx(k3,f); a2_pair_swap(c,k3,r,s); c.cx(k3,r);
    // On the exact legal pair care, f1=F*r. Clear and release f1.
    c.ccx(f,r,k3); c.release_clean(k3);
    A2_REC.with(|v| v.borrow_mut().get_mut(&t).expect("pair second field")[0]=None);
}
fn a2_pair_pop(c: &mut Builder, first: usize) {
    assert!(A2_PAIR_PACKED.with(|v| v.borrow_mut().remove(&first)), "pair is not packed");
    let second=a2_pair_partner(first);
    assert!(first<second && a2_pair_second(second), "invalid packed pair endpoints");
    let f=a2_field(first)[0].expect("pair first flag");
    let r=a2_cell(first).expect("pair first k2");
    let s=a2_cell(second).expect("pair second k2");
    let g=c.alloc_qubit(); c.ccx(f,r,g);
    c.cx(g,r); a2_pair_swap(c,g,r,s); c.cx(g,f);
    A2_REC.with(|v| v.borrow_mut().get_mut(&second).expect("pair second field")[0]=Some(g));
}
fn a2_pair_consume(c: &mut Builder, t: usize) -> QubitId {
    if a2_pair_is_packed(t) {
        assert!(a2_pair_second(t), "pair must be consumed in descending tick order");
        a2_pair_pop(c,a2_pair_partner(t));
    }
    let f=A2_REC.with(|v| v.borrow_mut().remove(&t)).expect("pair consumed field");
    assert!(f[1].is_none());
    A2_CELLS.with(|v| { v.borrow_mut().remove(&t); });
    f[0].expect("pair raw flag absent")
}
fn a2_pair_read(c: &mut Builder, t: usize) -> (QubitId,QubitId) {
    if !a2_pair_is_packed(t) {
        let f=a2_field(t)[0].expect("pair raw read flag");
        let b=a2_cell(t).expect("pair raw read k2");
        let q=c.alloc_qubit(); let u=c.alloc_qubit(); c.cx(f,q); c.cx(b,u);
        return(q,u);
    }
    let first=a2_pair_start(t);
    let f=a2_field(first)[0].expect("pair packed F");
    let r=a2_cell(first).expect("pair packed r");
    let s=a2_cell(a2_pair_partner(first)).expect("pair packed s");
    let q=and_new(c,f,r); let u=and_new(c,q,s);
    if t==first { c.cx(r,u); c.cx(q,u); c.cx(f,q); }
    else { c.cx(s,u); }
    (q,u)
}
fn a2_pair_read_erase(c: &mut Builder, t: usize, q: QubitId, u: QubitId) {
    if !a2_pair_is_packed(t) {
        let f=a2_field(t)[0].expect("pair raw erase flag");
        let b=a2_cell(t).expect("pair raw erase k2");
        c.cx(b,u); c.cx(f,q); c.release_clean(u); c.release_clean(q);
        return;
    }
    let first=a2_pair_start(t);
    let f=a2_field(first)[0].expect("pair packed erase F");
    let r=a2_cell(first).expect("pair packed erase r");
    let s=a2_cell(a2_pair_partner(first)).expect("pair packed erase s");
    if t==first { c.cx(f,q); c.cx(q,u); c.cx(r,u); }
    else { c.cx(s,u); }
    // Restore the two AND values, then retire them in dependency order.
    // Every HMR coin is local and paid by a Clifford CZ before it is freed.
    and_erase(c,u,q,s); and_erase(c,q,f,r);
}
