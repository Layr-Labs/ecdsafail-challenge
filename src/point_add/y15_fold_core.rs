// W136: retirement of a selected threshold gate before the digit tail peak.
fn w136_enabled() -> bool {
    true
}
// ======================================================================================================================
// round17 fold-core ("IPK"): the A fold with the digit held in place. Same values, same addend program and same
// ladder as [`fold_fwd_a`]; the digit's upper bits are written onto the wires of the gated digit bits (Y_3 holds
// k_3 = y_3 ^ p, Y_j holds k_j = y_j ^ t_j), so the +-1 chain t_4..t_(K-1) and r3 leave before the fields and are
// built again after the ladder (K - 3 Toffoli more). Before the ladder c4 and c3 may leave as well (c3 is no longer
// read by any form of the addend; 1 Toffoli each), with the gate wires of bypass 1.
// ======================================================================================================================
/// LFF_IPK=1: the builder's A ticks run the IPK fold (forward) in place of [`fold_fwd_a`].
pub(super) fn f_ipk_on() -> bool { std::env::var("LFF_IPK").is_ok_and(|v| v == "1") }
/// LFF_NO_C3=1: the IPK fold never sheds c3 (research knob).
fn f_c3_shed_on() -> bool { !std::env::var("LFF_NO_C3").is_ok_and(|v| v == "1") }
/// Wires the IPK fold holds beside its main ladder at its full level (fin = 0, nothing shed): [`a_fixed`] less r3 and
/// t_4..t_(K-1). At level 0 it is [`a_fixed`].
pub(super) fn f_fixed(emax: usize) -> usize { a_fixed(emax) - 1 - (emax - 1) }
/// LFF_LEV=n (research knob): the IPK fold runs at least level n (0 ..= K - 3).
/// Ids for wires that are gone but still named by records (renamed to the new wire when built again): never
/// allocated, so no rename can catch a live wire that reuses a freed id.
thread_local! { static F_GHOST: std::cell::Cell<u64> = const { std::cell::Cell::new(1 << 40) }; }
fn f_ghost() -> QubitId {
    F_GHOST.with(|g| {
        let v = g.get();
        g.set(v + 1);
        QubitId(v)
    })
}
thread_local! { static F_SH_FORCE: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) }; }
thread_local! { static F_LEV_FORCE: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) }; }
fn f_lev_min() -> usize {
    F_LEV_FORCE.with(|x| x.get()).unwrap_or_else(|| std::env::var("LFF_LEV").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}
/// Wires the IPK fold can shed by itself for its ladder (1 Toffoli each): c4, c3 (not with the top-wire shed), the gate
/// ANDs above k1 k2, and the K - 3 levels of the digit in place.
pub(super) fn f_own_sheds(emax: usize) -> usize {
    1 + usize::from(f_c3_shed_on()) + if a_gate_shed_on() { match emax { 5 => 1, 6 => 2, _ => 3 } } else { 0 } + emax + f_extra_sheds(emax)
}
/// The least ladder budget of the IPK fold's forward main ladder on `nbits` bits, dropped kept carries included.
pub(super) fn f_min_budget(nbits: usize) -> usize {
    let b0 = a_min_budget(nbits);
    if !f_drop_on() {
        return b0;
    }
    (1..b0).find(|&b| F_DROPS.iter().any(|ds| f_drop_plan(nbits, b, ds).is_some())).unwrap_or(b0)
}
fn f_fix(f: &mut Lin, w: QubitId, d: &Lin) {
    if f.w.contains(&w) {
        *f = f.x(d);
    }
}
/// A wire w now holds (old value) ^ d: every form that reads w (as its old value) gets ^ d.
fn f_fix_recs(recs: &mut [Rec], w: QubitId, d: &Lin) {
    for r in recs.iter_mut() {
        match r {
            Rec::And(_, a, b) => {
                f_fix(a, w, d);
                f_fix(b, w, d);
            }
            Rec::Maj(_, a, b, ci) => {
                f_fix(a, w, d);
                f_fix(b, w, d);
                f_fix(ci, w, d);
            }
            _ => {}
        }
    }
}
fn f_fix_vec(v: &mut [Lin], w: QubitId, d: &Lin) {
    for f in v.iter_mut() {
        f_fix(f, w, d);
    }
}
fn f_sub(f: &mut Lin, old: QubitId, new: QubitId) {
    for q in f.w.iter_mut() {
        if *q == old {
            *q = new;
        }
    }
}
fn f_pop(c: &mut Builder, r: Rec) {
    match r {
        Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
        Rec::Maj(q, a, b, ci) => {
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &a, &b);
        }
        _ => unreachable!("fold-core: the IPK fold records only ANDs"),
    }
}
/// Wires [`esh_out`] frees.
fn f_esh_count(st: &ESh) -> usize {
    3 + st.deep_c.len().saturating_sub(1) + usize::from(!st.top1) + 2 * usize::from(!st.direct && !st.top1)
}
/// The digit's state after the serial part (shared by the forward and the inverse IPK fold).
struct FDig {
    /// gates indexed by j, the AND k1 k2, gate records + r1 + r2 (`pre`, ngate gate records first)
    g: Vec<Lin>,
    tt: Lin,
    pre: Vec<Rec>,
    ngate: usize,
    // W136: g7 was already erased at its last forward digit use.
    early_g7: bool,
    r2: Lin,
    /// Y_3 .. Y_(K-1) and their erase forms (AND of; forms of y_j)
    yw: Vec<QubitId>,
    yer: Vec<(Lin, Lin)>,
    /// t_4 .. t_K (index j - 4): wires and records in current forms; None once erased
    tw: Vec<Option<QubitId>>,
    trec: Vec<Option<Rec>>,
    /// r3's record (None once erased), ks's wire
    r3v: Option<Rec>,
    ks: QubitId,
    /// the serial Q chain records, k's forms, Q's forms, the current Q carry form
    qser: Vec<Rec>,
    k: Vec<Lin>,
    qb: Vec<Lin>,
    q: Lin,
    /// level: the top `tops` of t_4..t_(K-1) are written onto their Y wires; `full`: p onto Y3 as well (r3 gone)
    tops: usize,
    full: bool,
}
fn f_fix_trec(trec: &mut [Option<Rec>], w: QubitId, d: &Lin) {
    for r in trec.iter_mut().flatten() {
        f_fix_recs(std::slice::from_mut(r), w, d);
    }
}
/// A wire was built again under a new id: every record and form of the digit reads the new one.
fn f_rename(d: &mut FDig, old: QubitId, new: QubitId) {
    for f in &mut d.g { f_sub(f, old, new); }
    y18_subst(&mut d.pre, old, new);
    y18_subst(&mut d.qser, old, new);
    for r in d.trec.iter_mut().flatten() {
        y18_subst(std::slice::from_mut(r), old, new);
    }
    for (a, b) in d.yer.iter_mut() {
        f_sub(a, old, new);
        f_sub(b, old, new);
    }
}
/// The digit of the IPK fold at level `lev` (0 ..= K - 3). Forward (`fwd`): the serial chunk [4, K) runs inside (sums
/// written, inner carries erased, its carry into bit K returned); inverse: the digit bits are read from acc (W's bits
/// in the clear). Level n writes t_j onto Y_j for the top min(n, K - 4) j < K and erases those t_j (top down); level
/// K - 3 also writes p onto Y3 and erases r3. Returns (state, kept carry, Q on [4, K) in current forms).
#[allow(clippy::too_many_arguments)]
fn f_digit(c: &mut Builder, acc: &[QubitId], nm: [QubitId; 3], k1: QubitId, k2: QubitId, k3: QubitId, emax: usize, c3: QubitId, c4: QubitId, fwd: bool, lev: usize) -> (FDig, Option<QubitId>, Vec<Lin>) {
    let kx = 3 + emax;
    let fc3 = l(c3);
    let v3 = Lin::of(&[acc[3], c3]);
    let mut pre: Vec<Rec> = Vec::new();
    let (g, tt) = a_gates(c, &mut pre, k1, k2, k3, emax);
    let ngate = pre.len();
    let r1 = r_and(c, &mut pre, l(nm[0]), l(acc[0]));
    let mut k = vec![Lin::of(&[nm[0], acc[0]]), Lin::of(&[nm[1], acc[1]]).x(&r1)];
    let r2 = r_maj(c, &mut pre, l(nm[1]), l(acc[1]), r1);
    k.push(Lin::of(&[nm[2], acc[2]]).x(&r2));
    let mut r3v: Vec<Rec> = Vec::new();
    let r3 = r_maj(c, &mut r3v, l(nm[2]), l(acc[2]), r2.clone());
    let p = r3.x(&fc3);
    let y3q = lin_and(c, &g[3], &v3);
    let mut yw = vec![y3q];
    let mut yer = vec![(g[3].clone(), v3.clone())];
    k.push(l(y3q).x(&p));
    let mut trec: Vec<Rec> = Vec::new();
    let mut t = r_and(c, &mut trec, p.clone(), l(y3q).x(&fc3));
    let mut tw = vec![t.w[0]];
    let mut qser: Vec<Rec> = Vec::new();
    let mut qb = vec![k[0].clone(), k[1].x(&k[0])];
    let mut q = r_and(c, &mut qser, k[1].clone(), k[0].clone());
    let mut cc: Vec<QubitId> = vec![c4];
    let mut add_lo: Vec<Lin> = Vec::new();
    for j in 4..kx {
        let i = j - 4;
        if i >= 2 {
            qb.push(k[i].x(&k[i - 1]).x(&q));
            q = r_maj(c, &mut qser, k[i].clone(), k[i - 1].clone(), q);
        }
        let aj = qb[i].clone();
        let yq = if fwd {
            let sum = l(acc[j]).x(&aj).x(&l(cc[i]));
            let yq = lin_and(c, &g[j], &sum);
            let cn = m_carry(c, acc[j], &aj, cc[i]);
            cc.push(cn);
            yq
        } else {
            lin_and(c, &g[j], &l(acc[j]))
        };
        yw.push(yq);
        yer.push((g[j].clone(), l(acc[j])));
        k.push(l(yq).x(&t));
        t = r_and(c, &mut trec, t, l(yq).x(&fc3));
        tw.push(t.w[0]);
        add_lo.push(aj);
    }
    let ckx = if fwd {
        for j in (4..kx).rev() {
            lin_xor_into(c, &add_lo[j - 4], acc[j]);
            c.cx(cc[j - 4], acc[j]);
            if j > 4 {
                m_carry_erase(c, cc[j - 4], acc[j - 1], &add_lo[j - 5], cc[j - 5]);
            }
        }
        Some(cc[kx - 4])
    } else {
        None
    };
    k.push(t.clone());
    let ks = lin_and(c, &t, &fc3);
    // the digit in place at level `lev`; every form that read y_j now reads Y_j ^ (p or t_j)
    let tops = lev.min(kx - 4);
    let full = lev >= kx - 3;
    if full {
        lin_xor_into(c, &p, y3q);
        f_fix_recs(&mut trec, y3q, &p);
        f_fix_recs(&mut qser, y3q, &p);
        f_fix_vec(&mut k, y3q, &p);
        f_fix_vec(&mut qb, y3q, &p);
        f_fix_vec(&mut add_lo, y3q, &p);
    }
    for j in kx - tops..kx {
        let (yq, tj) = (yw[j - 3], tw[j - 4]);
        let d = l(tj);
        c.cx(tj, yq);
        f_fix_recs(&mut trec, yq, &d);
        f_fix_recs(&mut qser, yq, &d);
        f_fix_vec(&mut k, yq, &d);
        f_fix_vec(&mut qb, yq, &d);
        f_fix_vec(&mut add_lo, yq, &d);
    }
    let mut trec: Vec<Option<Rec>> = trec.into_iter().map(Some).collect();
    let mut tw: Vec<Option<QubitId>> = tw.into_iter().map(Some).collect();
    for j in (kx - tops..kx).rev() {
        f_pop(c, trec[j - 4].take().unwrap());
        tw[j - 4] = None;
    }
    // t_K's record names t_(K-1) (gone when folded): f_restore writes it again in any case
    trec[kx - 4] = None;
    let r3r = r3v.pop().unwrap();
    let r3v = if full {
        f_pop(c, r3r);
        None
    } else {
        Some(r3r)
    };
    (FDig { g, tt, pre, ngate, early_g7: false, r2, yw, yer, tw, trec, r3v, ks, qser, k, qb, q, tops, full }, ckx, add_lo)
}
/// After the ladder: r3 (full level) and the erased t_j again, bottom up (one Toffoli each); ks leaves; t_K leaves
/// unless `keep_tk` (then its record is in `trec`); the wires Y_j hold y_j again. `extra` (forms that read k on the
/// Y wires) and the serial Q records are rewritten to y_j. On return every t_4..t_(K-1) and r3 is a wire with its
/// record in current forms. `c3` = the wire that holds c3 now (records already renamed to it).
fn f_restore(c: &mut Builder, acc: &[QubitId], nm: [QubitId; 3], emax: usize, d: &mut FDig, c3: QubitId, extra: &mut [Lin], keep_tk: bool) {
    let kx = 3 + emax;
    let fc3 = l(c3);
    if d.full {
        let mut v: Vec<Rec> = Vec::new();
        r_maj(c, &mut v, l(nm[2]), l(acc[2]), d.r2.clone());
        d.r3v = v.pop();
    }
    let r3w = match d.r3v.as_ref() {
        Some(Rec::Maj(q, _, _, _)) => *q,
        _ => unreachable!("fold-core: r3's record"),
    };
    let p = l(r3w).x(&fc3);
    let y3q = d.yw[0];
    let folded = |d: &FDig, i: usize| i >= kx - d.tops && i < kx && i >= 4;
    // y_i in current forms
    let yform = |d: &FDig, i: usize| -> Lin {
        if i == 3 {
            if d.full { l(y3q).x(&p) } else { l(y3q) }
        } else if folded(d, i) {
            l(d.yw[i - 3]).x(&l(d.tw[i - 4].unwrap()))
        } else {
            l(d.yw[i - 3])
        }
    };
    for j in kx - d.tops..kx {
        let prev = if j == 4 { p.clone() } else { l(d.tw[j - 5].unwrap()) };
        let b = yform(d, j - 1).x(&fc3);
        let q = lin_and(c, &prev, &b);
        d.trec[j - 4] = Some(Rec::And(q, prev, b));
        d.tw[j - 4] = Some(q);
    }
    let tk = d.tw[kx - 4].unwrap();
    lin_and_erase(c, d.ks, &l(tk), &fc3);
    let tkm1 = l(d.tw[kx - 5].unwrap());
    let blast = yform(d, kx - 1).x(&fc3);
    if keep_tk {
        d.trec[kx - 4] = Some(Rec::And(tk, tkm1, blast));
    } else {
        lin_and_erase(c, tk, &tkm1, &blast);
        d.trec[kx - 4] = None;
        d.tw[kx - 4] = None;
    }
    for j in (kx - d.tops..kx).rev() {
        let (yq, tj) = (d.yw[j - 3], d.tw[j - 4].unwrap());
        c.cx(tj, yq);
        let dl = l(tj);
        f_fix_trec(&mut d.trec, yq, &dl);
        f_fix_recs(&mut d.qser, yq, &dl);
        f_fix_vec(extra, yq, &dl);
    }
    if d.full {
        lin_xor_into(c, &p, y3q);
        f_fix_trec(&mut d.trec, y3q, &p);
        f_fix_recs(&mut d.qser, y3q, &p);
        f_fix_vec(extra, y3q, &p);
    }
    d.tops = 0;
    d.full = false;
}
/// The addend's fields from k (as [`fold_fwd_a`]): records into `post`; returns the forms over [0, MW).
fn f_fields(c: &mut Builder, post: &mut Vec<Rec>, d: &FDig, emax: usize, mw: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let nk = d.k.len();
    let ksign = l(d.ks);
    let kb = &d.k;
    let kbit = |i: usize| if i < nk { kb[i].clone() } else { ksign.clone() };
    let (uw, hw) = a_widths(emax);
    let mut qb = d.qb.clone();
    let mut q = d.q.clone();
    let mut i = qb.len();
    while i < 6 + uw {
        if i >= nk + 1 {
            qb.push(ksign.clone());
        } else {
            qb.push(kbit(i).x(&kbit(i - 1)).x(&q));
            if i < nk {
                q = r_maj(c, post, kbit(i), kbit(i - 1), q);
            }
        }
        i += 1;
    }
    let jb: Vec<Lin> = qb[6..6 + uw].to_vec();
    let mut u = vec![jb[0].x(&kb[0])];
    let mut b = r_and(c, post, jb[0].x(&one), kb[0].clone());
    for j in 1..uw {
        u.push(jb[j].x(&kbit(j)).x(&b));
        if j < uw - 1 {
            b = r_maj(c, post, jb[j].x(&one), kbit(j), b);
        }
    }
    let s = u[uw - 1].clone();
    let mut h = vec![kb[0].x(&s)];
    let mut z = r_and(c, post, kb[0].x(&one), s.x(&one));
    h.push(kb[1].x(&one).x(&z));
    z = r_and(c, post, kb[1].x(&one), z);
    h.push(kb[2].x(&one).x(&z));
    let zero = s.x(&ksign).x(&one);
    for j in 3..hw {
        h.push(kbit(j).x(&one).x(&zero));
    }
    (0..mw)
        .map(|bb| {
            if bb < 4 {
                Lin::k(false)
            } else if bb < 10 {
                qb[bb - 4].clone()
            } else if bb < 10 + uw {
                u[bb - 10].clone()
            } else if bb < 32 {
                s.clone()
            } else if bb < 32 + hw {
                h[bb - 32].clone()
            } else {
                h[hw - 1].clone()
            }
        })
        .collect()
}
/// ANDs [`f_fields`] will build.
fn f_nfields(d: &FDig, emax: usize) -> usize {
    let (uw, _) = a_widths(emax);
    d.k.len() - d.qb.len() + (uw - 1) + 2
}
// W110 local fixture: leave the five continued-Q carries out over the main ladder.
// At emax=7, post starts [q6..q10, B0..B9, H0,H1].  U[1+i] reads
// q[6+i] ^ B[i] (plus K), so B[i] ^= q[6+i] makes its wire the required
// combination.  The q records retain exact K/Kprev/qprev parents.
struct FPage5 {
    q_old: [QubitId; 5],
    q_ghost: [QubitId; 5],
    b: [QubitId; 5],
}
// The same source-level eligibility used by the physical page operation and
// by callers that must reserve room before entering the fold. The credit is
// only a potential five-owner release: the fold still pages only if its
// unpaged final ladder plan does not fit, then verifies the actual budget.
fn f_page5_room_credit(emax: usize) -> usize {
    if emax == 7 && std::env::var("LFF_PAGE5").ok().as_deref() == Some("1") { 5 } else { 0 }
}
fn f_page5_out(c: &mut Builder, post: &mut [Rec], add: &mut [Lin], emax: usize, tight: bool) -> Option<FPage5> {
    if !tight || f_page5_room_credit(emax) == 0 {
        return None;
    }
    assert_eq!(post.len(), 17, "W110 post shape");
    let q = std::array::from_fn(|i| match &post[i] {
        Rec::Maj(id, _, _, _) => *id,
        _ => panic!("W110 continued-Q shape"),
    });
    let b = std::array::from_fn(|i| match &post[5+i] {
        Rec::And(id, _, _) | Rec::Maj(id, _, _, _) => *id,
        _ => panic!("W110 U-borrow shape"),
    });
    // Mutate the value owners and rewrite every Lin consumer to the new basis.
    for i in 0..5 {
        assert!(add[11+i].w.contains(&q[i]) && add[11+i].w.contains(&b[i]), "W110 U output parent shape");
        c.cx(q[i], b[i]);
        f_fix_vec(add, b[i], &l(q[i]));
        assert!(!add[11+i].w.contains(&q[i]) && add[11+i].w.contains(&b[i]), "W110 in-place U basis");
    }
    for f in add.iter() { for &old in &q { assert!(!f.w.contains(&old), "W110 q still needed by value addend"); } }
    // Reverse recurrence order: q[i-1] remains live at each measurement.
    for i in (0..5).rev() {
        match &post[i] {
            Rec::Maj(id, a, bb, ci) => f_pop(c, Rec::Maj(*id, a.clone(), bb.clone(), ci.clone())),
            _ => unreachable!(),
        }
    }
    // Every old q ID is now free and may be reused by ladder carries.  Pending
    // records must use nonallocated ghosts; otherwise replay's global
    // old->new substitution can merge a new q with another old placeholder.
    let q_ghost = std::array::from_fn(|_| f_ghost());
    for i in 0..5 { y18_subst(post, q[i], q_ghost[i]); }
    Some(FPage5 { q_old: q, q_ghost, b })
}
fn f_page5_back(c: &mut Builder, post: &mut [Rec], add: &mut [Lin], p: FPage5) {
    // Rebuild q6..q10 in forward order.  y18_subst advances all future
    // parent versions and the target's own id before the canonical undo.
    for i in 0..5 {
        let (a, b, ci) = match &post[i] {
            Rec::Maj(_, a, b, ci) => (a.clone(), b.clone(), ci.clone()),
            _ => unreachable!(),
        };
        let new_q = lin_and(c, &a, &b);
        lin_xor_into(c, &ci, new_q);
        if std::env::var_os("LFF_PAGE5_TRACE").is_some() {
            eprintln!("W110_REPLAY i={i} old={:?} new={:?} collides_other_old={}",p.q_old[i],new_q,p.q_old.iter().enumerate().any(|(j,&o)|j!=i && o==new_q));
        }
        y18_subst(post, p.q_ghost[i], new_q);
        c.cx(new_q, p.b[i]);
        f_fix_vec(add, p.b[i], &l(new_q));
    }
}
// W120: an explicit, paid physical realization of the 1038-state cubic
// cleanup witness.  A correction monomial is hosted on fresh clean wires;
// each parity is restored before release.  This intentionally pays up to
// three transient owners instead of treating symbolic Lin parities as wires.
fn f_page5_phase_symbol(name: &str, d: &FDig, post: &[Rec], p: &FPage5) -> Lin {
    let retained = |i: usize| match &post[i] {
        Rec::And(id, _, _) | Rec::Maj(id, _, _, _) => l(*id),
        _ => panic!("W120 retained owner shape"),
    };
    if let Some(rest) = name.strip_prefix('k') {
        if let Ok(i) = rest.parse::<usize>() {
            assert!(i <= 10 && i < d.k.len(), "W120 K index");
            return d.k[i].clone();
        }
    }
    match name {
        "ks" => l(d.ks),
        "q5" => d.q.clone(),
        "H0" => retained(15),
        "H1" => retained(16),
        "B5" => retained(10),
        "B6" => retained(11),
        "B7" => retained(12),
        "B8" => retained(13),
        "B9" => retained(14),
        "R0" => l(p.b[0]),
        "R1" => l(p.b[1]),
        "R2" => l(p.b[2]),
        "R3" => l(p.b[3]),
        "R4" => l(p.b[4]),
        _ => panic!("W120 unknown phase symbol {name}"),
    }
}
fn f_page5_phase_term(c: &mut Builder, m: crate::circuit::BitId, factors: &[&[&str]], d: &FDig, post: &[Rec], p: &FPage5) {
    assert!(factors.len() <= 3, "W120 phase degree");
    if factors.is_empty() {
        // XZXZ = -I on any live pivot, with all four gates under m.
        c.push_condition(m);
        c.x(d.ks); c.z_if(d.ks, crate::circuit::NO_BIT); c.x(d.ks); c.z_if(d.ks, crate::circuit::NO_BIT);
        c.pop_condition();
        return;
    }
    let mut hosts = Vec::with_capacity(factors.len());
    let mut forms = Vec::with_capacity(factors.len());
    for names in factors {
        let form = names.iter().fold(Lin::k(false), |acc, name| acc.x(&f_page5_phase_symbol(name, d, post, p)));
        let h = c.alloc_qubit();
        lin_xor_into(c, &form, h);
        hosts.push(h);
        forms.push(form);
    }
    match hosts.as_slice() {
        [a] => c.z_if(*a, m),
        [a,b] => c.cz_if(*a, *b, m),
        [a,b,t] => c.ccz_if(*a, *b, *t, m),
        _ => unreachable!(),
    }
    for (h, form) in hosts.into_iter().zip(forms).rev() {
        lin_xor_into(c, &form, h);
        c.release_clean(h);
    }
}
fn f_page5_phase_erase(c: &mut Builder, target: &str, terms: &[&[&str]], cubes: &[[&[&str];3]], d: &FDig, post: &[Rec], p: &FPage5) {
    let form = f_page5_phase_symbol(target, d, post, p);
    assert!(!form.one && form.w.len() == 1, "W120 target must be a physical owner");
    let q = form.w[0];
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.release_clean(q);
    for names in terms {
        if names.is_empty() { f_page5_phase_term(c, m, &[], d, post, p); }
        else {
            let singles: Vec<&[&str]> = names.iter().map(std::slice::from_ref).collect();
            f_page5_phase_term(c, m, &singles, d, post, p);
        }
    }
    for triple in cubes { f_page5_phase_term(c, m, triple, d, post, p); }
    c.free_bit(m);
}
fn f_page5_direct_cleanup(c: &mut Builder, post: &mut Vec<Rec>, d: &FDig, p: FPage5) {
    assert_eq!(post.len(), 17, "W120 post shape");
    f_page5_phase_erase(c, "H1", &[&["H0"], &["H0", "k1"]], &[], d, post, &p);
    f_page5_phase_erase(c, "B9", &[&[], &["H0"], &["k10"], &["ks"], &["k0", "ks"]], &[], d, post, &p);
    f_page5_phase_erase(c, "H0", &[&[], &["B8"], &["k10"], &["k9"], &["B8", "k9"], &["k0", "ks"]], &[], d, post, &p);
    f_page5_phase_erase(c, "B8", &[&["k8"], &["B7"], &["ks", "k8"], &["ks", "B7"], &["k8", "B7"]], &[], d, post, &p);
    f_page5_phase_erase(c, "B7", &[&["B6"], &["k7"], &["ks"], &["B6", "k7"]], &[], d, post, &p);
    f_page5_phase_erase(c, "B6", &[&["B5"], &["k6"], &["ks"], &["B5", "k6"]], &[], d, post, &p);
    f_page5_phase_erase(c, "B5", &[&["R4"], &["k5"], &["ks"], &["R4", "k5"], &["R4", "k9"]], &[[&["k4"], &["k9"], &["R4"]]], d, post, &p);
    f_page5_phase_erase(c, "R4", &[&["R3"], &["k2"], &["k4"], &["R2", "k10"], &["R3", "k2"], &["R3", "k4"], &["R3", "k8"], &["k2", "k8"], &["k2", "k9"], &["k4", "k9"], &["k8", "k9"]], &[[&["k2", "k3"], &["k2", "k9"], &["k2", "k8", "R3"]]], d, post, &p);
    f_page5_phase_erase(c, "R3", &[&["R2"], &["k1"], &["k3"], &["R2", "k1"], &["R2", "k3"], &["R2", "k7"], &["R2", "k9"], &["k1", "k7"], &["k1", "k8"], &["k3", "k8"], &["k3", "k9"], &["k7", "k8"], &["k8", "k9"]], &[[&["k1", "k2"], &["k1", "k8"], &["k1", "k7", "R2"]]], d, post, &p);
    f_page5_phase_erase(c, "R2", &[&["R1"], &["k2"], &["R1", "k2"], &["R1", "k6"], &["R1", "k8"], &["k2", "k7"], &["k2", "k8"], &["k6", "k7"], &["k7", "k8"]], &[[&["k1"], &["k7"], &["k6", "R1"]]], d, post, &p);
    f_page5_phase_erase(c, "R1", &[&["k1"], &["R0", "k0"], &["R0", "k1"], &["R0", "k6"], &["R0", "k7"], &["k1", "k6"], &["k1", "k7"], &["k6", "k7"]], &[[&["k0"], &["k5"], &["R0"]]], d, post, &p);
    f_page5_phase_erase(c, "R0", &[&["k0"], &["k0", "k5"], &["k0", "k6"], &["k0", "q5"], &["k3", "k4"], &["k3", "q5"], &["k4", "k5"], &["k5", "k6"], &["k6", "q5"]], &[], d, post, &p);
    post.clear();
}
/// The fold's own sheds for its ladder.
#[derive(Clone, Copy, Debug)]
struct FSh {
    c4: bool,
    c3: bool,
    gsh: usize,
    lev: usize,
    klo: usize,
    qs: usize,
    /// kept carries of the main ladder dropped early (0, 1, 2; forward only)
    drops: usize,
}
/// Own sheds beyond c4, gates, levels and c3: k's low bits in place (2) and the serial Q carries (K - 6).
fn f_extra_sheds(emax: usize) -> usize {
    if f_extra_on() { 2 + (emax - 3) } else { 0 }
}
/// LFF_NO_EXTRA=1: no k-low-in-place and no serial-carry sheds (research knob).
fn f_extra_on() -> bool { !std::env::var("LFF_NO_EXTRA").is_ok_and(|v| v == "1") }
/// The own sheds the ladder needs, in menu order (1 Toffoli each): c4, the gate ANDs above k1 k2, the levels of the
/// digit in place, c3 (`c3_ok`; only at the full level, where no form of the addend reads it), k's low bits in place
/// (2), the serial Q carries (K - 6). `at_ladder` = the wires held at the ladder with none of them.
fn f_sheds(emax: usize, nbits: usize, at_ladder: usize, ngate: usize, c3_ok: bool, drops_ok: bool) -> FSh {
    let ng = if a_gate_shed_on() { ngate - 1 } else { 0 };
    let c3n = usize::from(c3_ok && f_c3_shed_on());
    let lmin = f_lev_min().min(emax);
    let nx = f_extra_sheds(emax);
    let max_own = 1 + ng + emax + c3n + nx;
    let budget = |sh: usize| cells::cap().saturating_sub(at_ladder.saturating_sub(sh));
    // the forced levels (LFF_LEV) count as taken whatever the room
    let mut sh = F_SH_FORCE.with(|x| x.get()).unwrap_or(0).min(max_own);
    while a_plan(nbits, budget(sh + lmin)).is_none() && sh + lmin < max_own {
        sh += 1;
    }
    let c4 = sh >= 1;
    let mut rest = sh.saturating_sub(1);
    let gsh = rest.min(ng);
    rest -= gsh;
    let lv = (rest + lmin).min(emax);
    rest = (rest + lmin) - lv;
    let c3 = c3n == 1 && rest >= 1;
    rest -= usize::from(c3);
    let klo = rest.min(if nx > 0 { 2 } else { 0 });
    rest -= klo;
    let qs = rest.min(nx.saturating_sub(2));
    // past the whole menu: the ladder drops kept carries (y28 card s2-1), 1 then 2
    let mut drops = 0;
    if drops_ok && f_drop_on() && a_plan(nbits, budget(sh + lmin)).is_none() {
        for (i, ds) in F_DROPS.iter().enumerate() {
            if f_drop_plan(nbits, budget(sh + lmin), ds).is_some() {
                drops = i + 1;
                break;
            }
        }
    }
    FSh { c4, c3, gsh, lev: lv, klo, qs, drops }
}
/// Gate ANDs (the top `gsh` above k1 k2, and k1 k2 itself with `tt`) built again under new ids.
fn f_gate_back_one(c: &mut Builder, d: &mut FDig, i: usize) {
    let (q, a, b) = match &d.pre[i] {
        Rec::And(q, a, b) => (*q, a.clone(), b.clone()),
        _ => unreachable!(),
    };
    let qn = lin_and(c, &a, &b);
    f_rename(d, q, qn);
}
fn f_gates_back(c: &mut Builder, d: &mut FDig, gsh: usize, tt: bool, k1: QubitId, k2: QubitId) {
    if tt {
        let tq = d.tt.w[0];
        let qn = lin_and(c, &l(k1), &l(k2));
        f_rename(d, tq, qn);
        d.tt = l(qn);
    }
    for i in d.ngate - gsh..d.ngate {
        f_gate_back_one(c, d, i);
    }
    d.early_g7 = false;
}
/// Erase the top `gsh` gate ANDs and (with `tt`) the AND k1 k2 for the ladder (nothing the ladder reads holds them);
/// their ids become ghosts in the records.
fn f_gates_out(c: &mut Builder, d: &mut FDig, gsh: usize, tt: bool, k1: QubitId, k2: QubitId) {
    for i in (d.ngate - gsh..d.ngate).rev() {
        if d.early_g7 && i == 1 { continue; }
        let q = if let Rec::And(q, a, b) = &d.pre[i] {
            lin_and_erase(c, *q, a, b);
            *q
        } else {
            unreachable!()
        };
        f_rename(d, q, f_ghost());
    }
    if tt {
        let q = d.tt.w[0];
        lin_and_erase(c, q, &l(k1), &l(k2));
        let g = f_ghost();
        f_rename(d, q, g);
        d.tt = l(g);
    }
}
/// Erase the t chain (top down, t_K first if it is still a wire) and r3.
fn f_tchain_out(c: &mut Builder, d: &mut FDig) {
    for r in d.trec.iter_mut().rev() {
        if let Some(r) = r.take() {
            f_pop(c, r);
        }
    }
    if let Some(r) = d.r3v.take() {
        f_pop(c, r);
    }
}
/// Forms that read acc[w] (as its old value) now read acc[w] ^ dl: fix every form list given.
fn f_fix_all(recs: &mut [&mut Vec<Rec>], lins: &mut [&mut Vec<Lin>], w: QubitId, dl: &Lin) {
    for r in recs.iter_mut() {
        f_fix_recs(r, w, dl);
    }
    for v in lins.iter_mut() {
        f_fix_vec(v, w, dl);
    }
}
/// k's low bits written in place on acc[0..3) (klo >= 1: k0 and k1, r1 leaves; klo = 2: k2 as well, r2 leaves first).
/// The fold's other forms of acc[0..3) (c1..c3, r3: built again or erased after [`f_klo_back`]) are not touched.
fn f_klo_out(c: &mut Builder, acc: &[QubitId], nm: [QubitId; 3], d: &mut FDig, klo: usize, recs: &mut [&mut Vec<Rec>], lins: &mut [&mut Vec<Lin>]) {
    if klo == 0 {
        return;
    }
    let ng = d.ngate;
    let (r1q, r2q) = match (&d.pre[ng], &d.pre[ng + 1]) {
        (Rec::And(a, _, _), Rec::Maj(b, _, _, _)) => (*a, *b),
        _ => unreachable!("fold-core: r1, r2 records"),
    };
    let d0 = l(nm[0]);
    let d1 = l(nm[1]).x(&l(r1q));
    let d2 = l(nm[2]).x(&l(r2q));
    lin_xor_into(c, &d0, acc[0]);
    lin_xor_into(c, &d1, acc[1]);
    if klo >= 2 {
        lin_xor_into(c, &d2, acc[2]);
    }
    for (i, dl) in [(0usize, &d0), (1, &d1), (2, &d2)] {
        if i < 2 || klo >= 2 {
            f_fix_recs(&mut d.qser, acc[i], dl);
            f_fix_vec(&mut d.k, acc[i], dl);
            f_fix_vec(&mut d.qb, acc[i], dl);
            f_fix_all(recs, lins, acc[i], dl);
        }
    }
    if klo >= 2 {
        // r2 = MAJ(nm1, acc1, r1) on the old acc1 = acc1 ^ nm1 ^ r1
        if let Rec::Maj(q, a, b, ci) = d.pre.remove(ng + 1) {
            f_pop(c, Rec::Maj(q, a, b.x(&d1), ci));
        }
    }
    if let Rec::And(q, a, b) = d.pre.remove(ng) {
        f_pop(c, Rec::And(q, a, b.x(&d0)));
        // r2's record (klo = 1) still names r1
        y18_subst(&mut d.pre, q, f_ghost());
    }
}
/// The inverse of [`f_klo_out`]: r1 (and r2) built again (one Toffoli each), acc[0..3) back to L's bits; the forms
/// fixed by [`f_klo_out`] are fixed back.
fn f_klo_back(c: &mut Builder, acc: &[QubitId], nm: [QubitId; 3], d: &mut FDig, klo: usize, recs: &mut [&mut Vec<Rec>], lins: &mut [&mut Vec<Lin>]) {
    if klo == 0 {
        return;
    }
    let ng = d.ngate;
    // r1 = AND(nm0, old acc0), old acc0 = acc0 ^ nm0
    let r1n = lin_and(c, &l(nm[0]), &l(acc[0]).x(&l(nm[0])));
    let r2q = if klo >= 2 {
        maj_wire(c, &l(nm[1]), &l(acc[1]).x(&l(nm[1])).x(&l(r1n)), &l(r1n))
    } else {
        match &d.pre[ng] {
            Rec::Maj(b, _, _, _) => *b,
            _ => unreachable!("fold-core: r2 record"),
        }
    };
    let d0 = l(nm[0]);
    let d1 = l(nm[1]).x(&l(r1n));
    let d2 = l(nm[2]).x(&l(r2q));
    if klo >= 2 {
        lin_xor_into(c, &d2, acc[2]);
    }
    lin_xor_into(c, &d1, acc[1]);
    lin_xor_into(c, &d0, acc[0]);
    // forms written on the in-place k read the old wires again; r1's old id is r1n now
    let r1_old = if klo == 1 {
        match &d.pre[ng] {
            Rec::Maj(_, _, _, ci) => ci.w[0],
            _ => unreachable!("fold-core: r2 record"),
        }
    } else {
        r1n
    };
    for (i, dl) in [(0usize, &d0), (1, &d1), (2, &d2)] {
        if i < 2 || klo >= 2 {
            f_fix_recs(&mut d.qser, acc[i], dl);
            f_fix_vec(&mut d.k, acc[i], dl);
            f_fix_vec(&mut d.qb, acc[i], dl);
            f_fix_all(recs, lins, acc[i], dl);
        }
    }
    if klo == 1 {
        y18_subst(&mut d.pre, r1_old, r1n);
    } else {
        d.pre.insert(ng, Rec::Maj(r2q, l(nm[1]).x(&l(r1n)), l(acc[1]).x(&l(r1n)), l(r1n)));
        d.r2 = l(r2q);
    }
    d.pre.insert(ng, Rec::And(r1n, l(nm[0]), l(acc[0])));
}
/// The serial Q carries q_1..q_qs (read only by the serial chunk's forms Q_2..Q_(qs+1), not by the main ladder) leave
/// top down. Returns their old wire ids.
fn f_qser_out(c: &mut Builder, d: &mut FDig, qs: usize, lins: &mut [&mut Vec<Lin>]) -> Vec<QubitId> {
    let out: Vec<Rec> = d.qser.drain(0..qs).collect();
    let ids: Vec<QubitId> = out
        .iter()
        .map(|r| match r {
            Rec::And(q, _, _) | Rec::Maj(q, _, _, _) => *q,
            _ => unreachable!(),
        })
        .collect();
    for r in out.into_iter().rev() {
        f_pop(c, r);
    }
    let ghosts: Vec<QubitId> = ids.iter().map(|_| f_ghost()).collect();
    for (o, g) in ids.iter().zip(ghosts.iter()) {
        y18_subst(&mut d.qser, *o, *g);
        for f in d.qb.iter_mut() {
            f_sub(f, *o, *g);
        }
        for v in lins.iter_mut() {
            for f in v.iter_mut() {
                f_sub(f, *o, *g);
            }
        }
    }
    ghosts
}
/// The inverse of [`f_qser_out`]: q_1..q_qs built again bottom up from k's current forms (one Toffoli each); the old
/// ids are replaced in the serial records and in the forms given.
fn f_qser_back(c: &mut Builder, d: &mut FDig, old: &[QubitId], lins: &mut [&mut Vec<Lin>]) {
    if old.is_empty() {
        return;
    }
    let mut v: Vec<Rec> = Vec::new();
    let q1 = lin_and(c, &d.k[1], &d.k[0]);
    v.push(Rec::And(q1, d.k[1].clone(), d.k[0].clone()));
    let mut q = l(q1);
    for i in 2..=old.len() {
        q = r_maj(c, &mut v, d.k[i].clone(), d.k[i - 1].clone(), q);
    }
    for (j, r) in v.iter().enumerate() {
        let nq = match r {
            Rec::And(q, _, _) | Rec::Maj(q, _, _, _) => *q,
            _ => unreachable!(),
        };
        y18_subst(&mut d.qser, old[j], nq);
        for f in lins.iter_mut() {
            for x in f.iter_mut() {
                f_sub(x, old[j], nq);
            }
        }
    }
    let rest = std::mem::take(&mut d.qser);
    d.qser = v;
    d.qser.extend(rest);
}
/// LFF_NO_DROP=1: the IPK fold's ladder never drops kept carries (research knob).
fn f_drop_on() -> bool { !std::env::var("LFF_NO_DROP").is_ok_and(|v| v == "1") }
/// Cheapest chunk plan of the main ladder on `nbits` bits for `budget` wires with the kept carries of chunks `drops`
/// dropped early ([`ladder_drop`]; y28 card s2-1). Live rule: chunk j holds j kept carries less the drops already
/// done (chunk d's leaves after chunk d + 1) plus w_j carries (final chunk w_j - 2). Cost: (w - 1)/2 per non-final
/// kept carry's compare, plus (w_d + (w_d - 1)/2)/2 per dropped chunk (its chain and compare again under the bit
/// above). `scripts/dropplan.py` is the same search (it gives main's Y28_PLAN9 / Y28_PLAN8 on 50 bits).
fn f_drop_plan(nbits: usize, budget: usize, drops: &[usize]) -> Option<Vec<usize>> {
    fn go(j: usize, done: usize, nbits: usize, budget: usize, drops: &[usize], memo: &mut std::collections::HashMap<(usize, usize), (f64, Option<Vec<usize>>)>) -> (f64, Option<Vec<usize>>) {
        if let Some(v) = memo.get(&(j, done)) {
            return v.clone();
        }
        let live = j - drops.iter().filter(|&&d| d + 2 <= j).count();
        let rem = nbits - done;
        let mut res: (f64, Option<Vec<usize>>) = (1e9, None);
        if rem >= 2 && live + rem - 2 <= budget && !drops.contains(&(j.wrapping_sub(1))) {
            res = (0.0, Some(vec![rem]));
        }
        if j + 1 < 16 && live < budget {
            for w in 1..=(budget - live).min(rem.saturating_sub(2)) {
                let mut cst = (w as f64 - 1.0) / 2.0;
                if drops.contains(&j) {
                    cst += (w as f64 + (w as f64 - 1.0) / 2.0) / 2.0;
                }
                let sub = go(j + 1, done + w, nbits, budget, drops, memo);
                let Some(sp) = sub.1 else { continue };
                if drops.contains(&j) && sp.len() < 2 {
                    continue;
                }
                if cst + sub.0 < res.0 {
                    let mut p = vec![w];
                    p.extend(sp);
                    res = (cst + sub.0, Some(p));
                }
            }
        }
        memo.insert((j, done), res.clone());
        res
    }
    let mut memo = std::collections::HashMap::new();
    go(0, 0, nbits, budget, drops, &mut memo).1
}
#[allow(clippy::too_many_arguments)]
fn f_digit_pebble(c: &mut Builder, acc: &[QubitId], nm: [QubitId; 3], k1: QubitId, k2: QubitId, k3: QubitId, emax: usize, c3: QubitId, c4: QubitId, fwd: bool, lev: usize, early_g7: bool) -> (FDig, Option<QubitId>, Vec<Lin>) {
    let kx = 3 + emax;
    let fc3 = l(c3);
    let v3 = Lin::of(&[acc[3], c3]);
    let mut pre: Vec<Rec> = Vec::new();
    let (mut g, tt) = a_gates(c, &mut pre, k1, k2, k3, emax);
    let ngate = pre.len();
    let r1 = r_and(c, &mut pre, l(nm[0]), l(acc[0]));
    let mut k = vec![Lin::of(&[nm[0], acc[0]]), Lin::of(&[nm[1], acc[1]]).x(&r1)];
    let r2 = r_maj(c, &mut pre, l(nm[1]), l(acc[1]), r1);
    k.push(Lin::of(&[nm[2], acc[2]]).x(&r2));
    let mut r3v: Vec<Rec> = Vec::new();
    let r3 = r_maj(c, &mut r3v, l(nm[2]), l(acc[2]), r2.clone());
    let p = r3.x(&fc3);
    let y3q = lin_and(c, &g[3], &v3);
    let mut yw = vec![y3q];
    let mut yer = vec![(g[3].clone(), v3.clone())];
    k.push(l(y3q).x(&p));
    let mut trec: Vec<Rec> = Vec::new();
    let mut t = r_and(c, &mut trec, p.clone(), l(y3q).x(&fc3));
    let mut tw = vec![t.w[0]];
    let mut qser: Vec<Rec> = Vec::new();
    let mut qb = vec![k[0].clone(), k[1].x(&k[0])];
    let mut q = r_and(c, &mut qser, k[1].clone(), k[0].clone());
    let mut cc: Vec<QubitId> = vec![c4];
    // Chunk endpoints retain their carry; all sums are written before that
    // endpoint can be measured. Input addend forms contain no acc[4..kx] wires.
    let mut add_lo: Vec<Lin> = Vec::new();
    let mut chunk_lo = 4usize;
    let mut chunk_ends: Vec<usize> = Vec::new();
    for j in 4..kx {
        let i = j - 4;
        if i >= 2 {
            qb.push(k[i].x(&k[i - 1]).x(&q));
            q = r_maj(c, &mut qser, k[i].clone(), k[i - 1].clone(), q);
        }
        let aj = qb[i].clone();
        let yq = if fwd {
            let sum = l(acc[j]).x(&aj).x(&l(cc[i]));
            let yq = lin_and(c, &g[j], &sum);
            if early_g7 && j == 7 {
                assert!(emax == 7 && ngate == 4 && fwd);
                let (old, a, b) = match &pre[1] {
                    Rec::And(q, a, b) => (*q, a.clone(), b.clone()),
                    _ => unreachable!("W136 g7 record"),
                };
                lin_and_erase(c, old, &a, &b);
                let ghost = f_ghost();
                // Complete renaming precedes any possible allocator reuse.
                y18_subst(&mut pre, old, ghost);
                y18_subst(&mut qser, old, ghost);
                y18_subst(&mut trec, old, ghost);
                for (a, b) in &mut yer { f_sub(a, old, ghost); f_sub(b, old, ghost); }
                for f in g.iter_mut().chain(k.iter_mut()).chain(qb.iter_mut()).chain(add_lo.iter_mut()) { f_sub(f, old, ghost); }
                f_sub(&mut q, old, ghost);
                f_sub(&mut t, old, ghost);
                assert!(!g[8].w.contains(&ghost) && !g[9].w.contains(&ghost));
            }
            let cn = m_carry(c, acc[j], &aj, cc[i]);
            cc.push(cn);
            yq
        } else {
            lin_and(c, &g[j], &l(acc[j]))
        };
        yw.push(yq);
        yer.push((g[j].clone(), l(acc[j])));
        k.push(l(yq).x(&t));
        t = r_and(c, &mut trec, t, l(yq).x(&fc3));
        tw.push(t.w[0]);
        add_lo.push(aj);
        if fwd && ((j + 1 - chunk_lo == 2) || j + 1 == kx) {
            for z in (chunk_lo..=j).rev() {
                lin_xor_into(c, &add_lo[z - 4], acc[z]);
                c.cx(cc[z - 4], acc[z]);
                if z > chunk_lo {
                    m_carry_erase(c, cc[z - 4], acc[z - 1], &add_lo[z - 5], cc[z - 5]);
                }
            }
            chunk_ends.push(j + 1);
            chunk_lo = j + 1;
        }
    }
    let ckx = if fwd {
        // Every internal carry is gone. Erase each kept boundary top down:
        // kept_erase releases its owner BEFORE its width-2 compare allocates
        // one repair wire, so phase repair does not recover the old peak.
        for idx in (0..chunk_ends.len().saturating_sub(1)).rev() {
            let lo = if idx == 0 { 4 } else { chunk_ends[idx - 1] };
            let hi = chunk_ends[idx];
            // kept_erase indexes add by absolute bit; this digit uses offset 4.
            let m = c.alloc_bit();
            c.hmr(cc[hi - 4], m);
            c.release_clean(cc[hi - 4]);
            c.push_condition(m);
            lin_lt_phase(c, &acc[lo..hi], &add_lo[lo - 4..hi - 4], cc[lo - 4]);
            c.pop_condition();
            c.free_bit(m);
        }
        Some(cc[kx - 4])
    } else {
        None
    };
    k.push(t.clone());
    let ks = lin_and(c, &t, &fc3);
    // the digit in place at level `lev`; every form that read y_j now reads Y_j ^ (p or t_j)
    let tops = lev.min(kx - 4);
    let full = lev >= kx - 3;
    if full {
        lin_xor_into(c, &p, y3q);
        f_fix_recs(&mut trec, y3q, &p);
        f_fix_recs(&mut qser, y3q, &p);
        f_fix_vec(&mut k, y3q, &p);
        f_fix_vec(&mut qb, y3q, &p);
        f_fix_vec(&mut add_lo, y3q, &p);
    }
    for j in kx - tops..kx {
        let (yq, tj) = (yw[j - 3], tw[j - 4]);
        let d = l(tj);
        c.cx(tj, yq);
        f_fix_recs(&mut trec, yq, &d);
        f_fix_recs(&mut qser, yq, &d);
        f_fix_vec(&mut k, yq, &d);
        f_fix_vec(&mut qb, yq, &d);
        f_fix_vec(&mut add_lo, yq, &d);
    }
    let mut trec: Vec<Option<Rec>> = trec.into_iter().map(Some).collect();
    let mut tw: Vec<Option<QubitId>> = tw.into_iter().map(Some).collect();
    for j in (kx - tops..kx).rev() {
        f_pop(c, trec[j - 4].take().unwrap());
        tw[j - 4] = None;
    }
    // t_K's record names t_(K-1) (gone when folded): f_restore writes it again in any case
    trec[kx - 4] = None;
    let r3r = r3v.pop().unwrap();
    let r3v = if full {
        f_pop(c, r3r);
        None
    } else {
        Some(r3r)
    };
    (FDig { g, tt, pre, ngate, early_g7, r2, yw, yer, tw, trec, r3v, ks, qser, k, qb, q, tops, full }, ckx, add_lo)
}

/// The drop sets tried (1 then 2 dropped kept carries).
const F_DROPS: [&[usize]; 2] = [&[0], &[0, 2]];
/// The final physical ladder choice, after every owner release including an
/// optional five-wire page. A pre-page shed estimate cannot select its drops.
fn f_final_plan(nbits: usize, budget: usize, drops_ok: bool) -> Option<(Vec<usize>, Vec<usize>)> {
    if let Some(p) = a_plan(nbits, budget) { return Some((p, Vec::new())); }
    if drops_ok && f_drop_on() {
        for ds in F_DROPS {
            if let Some(p) = f_drop_plan(nbits, budget, ds) { return Some((p, ds.to_vec())); }
        }
    }
    None
}
fn f_ngate(emax: usize) -> usize {
    match emax {
        5 => 2,
        6 => 3,
        _ => 4,
    }
}
/// round17 fold-core: the forward A fold with the digit held in place (IPK, levelled); values and interface as
/// [`fold_fwd_a`]. Level and own sheds are chosen for the room at the ladder (level 0 = [`fold_fwd_a`]'s wires).
#[allow(clippy::too_many_arguments)]
fn fold_fwd_f(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, k3: QubitId, emax: usize, fin: usize, mut esh: Option<&mut ESh>) -> Vec<usize> {
    LOAN_ACTIVE.with(|x| x.set(false));
    let mw = acc.len();
    let kx = 3 + emax;
    let a_in = c.active_qubits();
    assert!(fin <= 6 && (fin >= 4) == esh.is_some());
    let nbits = mw - kx;
    // with the top-wire shed, c2, c1 and the top wires leave first (as fold_fwd_a) and c3 stays
    let early = esh.is_some();
    let n_fin = usize::from(fin >= 1) + usize::from(fin >= 2) + usize::from(fin >= 3) + esh.as_deref().map_or(0, f_esh_count);
    let at_ladder = (a_in as usize + a_fixed(emax)).saturating_sub(n_fin);
    let sh = f_sheds(emax, nbits, at_ladder, f_ngate(emax), !early, true);
    let (sh_c4, sh_c3, gsh, lev) = (sh.c4, sh.c3, sh.gsh, sh.lev);
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    // c2 and c1 leave at once unless c3 leaves after the digit (its erase reads c2)
    let late12 = sh_c3 && !early;
    if !late12 {
        if fin >= 1 {
            maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
        }
        if fin >= 2 {
            lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
        }
        if let Some(st) = esh.as_deref() {
            esh_out(c, st);
        }
    }
    let pebble = PAYLOAD_AT.with(|x| x.get().is_some_and(|(rev,t)| !rev && (115..=120).contains(&t)));
    if pebble { eprintln!("W118_PEBBLE fwd emax={emax}"); }
    let ((mut d, ckx, _), pk_k) = c.r3_peak(|c| {
        if pebble {
            let early_g7 = emax == 7 && gsh == 3 && lev >= 7
                && PAYLOAD_AT.with(|x| x.get() == Some((false, 115)))
                && w136_enabled();
            f_digit_pebble(c, acc, nm, k1, k2, k3, emax, c3, c4, true, lev, early_g7)
        }
        else { f_digit(c, acc, nm, k1, k2, k3, emax, c3, c4, true, lev) }
    });
    let ckx = ckx.unwrap();
    let mut prof = vec![("in", a_in as i64), ("kpeak", pk_k as i64), ("kphase_end", c.active_qubits() as i64)];
    if sh_c4 {
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    let c3g = f_ghost();
    if sh_c3 {
        maj_wire_erase(c, c3, &l(acc[2]), &l(e[2]), &l(c2));
        f_rename(&mut d, c3, c3g);
    }
    let dbg = std::env::var("LFF_DBG").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(0);
    let c3 = if sh_c3 && dbg == 1 { maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2)) } else { c3 };
    if dbg == 1 && sh_c3 {
        eprintln!("DBG c3 rebuilt at once: id {:?}", c3);
    }
    if late12 {
        if fin >= 1 {
            maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
        }
        if fin >= 2 {
            lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
        }
    }
    f_gates_out(c, &mut d, gsh, fin >= 3, k1, k2);
    f_klo_out(c, acc, nm, &mut d, sh.klo, &mut [], &mut []);
    let qold = f_qser_out(c, &mut d, sh.qs, &mut []);
    prof.push(("shed", c.active_qubits() as i64));
    let mut post: Vec<Rec> = Vec::new();
    let (w110_a0,w110_t0)=(c.active_qubits(),c.expected_total());
    let mut add = f_fields(c, &mut post, &d, emax, mw);
    let (w110_af,w110_tf)=(c.active_qubits(),c.expected_total());
    if dbg == 2 {
        for (b, f) in add.iter().enumerate() {
            if f.w.contains(&c3) { eprintln!("DBG add[{b}] reads c3"); }
        }
        for (i, f) in d.k.iter().enumerate() { if f.w.contains(&c3) { eprintln!("DBG k[{i}] reads c3"); } }
        for r in post.iter() { if let Rec::And(q, a, b) | Rec::Maj(q, a, b, _) = r { if a.w.contains(&c3) || b.w.contains(&c3) { eprintln!("DBG post {:?} reads c3", q); } } }
        for r in d.qser.iter() { if let Rec::And(q, a, b) | Rec::Maj(q, a, b, _) = r { if a.w.contains(&c3) || b.w.contains(&c3) { eprintln!("DBG qser {:?} reads c3", q); } } }
    }
    prof.push(("fields", c.active_qubits() as i64));
    if room_trace() {
        eprintln!("F_FOLD fwd emax={emax} held={} fixed={} fin={fin} lev={lev} sheds {sh:?}", c.active_qubits() as isize - a_in as isize, a_fixed(emax));
    }
    let unpaged_budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let unpaged_plan = f_final_plan(nbits, unpaged_budget, true);
    // W118-v2: pay five page replays only if neither existing plan fits.
    // Select the final chunk plan after those five owners are actually free.
    let page5 = f_page5_out(c, &mut post, &mut add, emax, unpaged_plan.is_none());
    if page5.is_some() { eprintln!("W118_PAGE fwd budget={unpaged_budget} min={} emax={emax}", a_min_budget(nbits)); }
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let (plan, drops) = f_final_plan(nbits, budget, true).unwrap_or_else(|| panic!("fold-core: the IPK fold's ladder does not fit: budget {budget}, need {}, active {}, cap {}, emax {emax}, lev {lev}, {sh:?}", f_min_budget(nbits), c.active_qubits(), cells::cap()));
    if !drops.is_empty() { eprintln!("W118_FINAL_DROP fwd budget={budget} drops={drops:?} plan={plan:?}"); }
    if room_trace() && !drops.is_empty() {
        eprintln!("F_FOLD fwd drops {:?} plan {:?}", drops, plan);
    }
    let (w110_ap,w110_tp)=(c.active_qubits(),c.expected_total());
    let ((), pk_l) = c.r3_peak(|c| ladder_d(c, acc, &add, kx, ckx, &plan, &drops));
    let (w110_al,w110_tl)=(c.active_qubits(),c.expected_total());
    prof.push(("ladder_peak", pk_l as i64));
    let ((), page_cleanup_peak) = c.r3_peak(|c| { if let Some(page5) = page5 {
        if std::env::var_os("LFF_CUBIC_CLEANUP").is_some() {
            f_page5_direct_cleanup(c, &mut post, &d, page5);
        } else {
            f_page5_back(c, &mut post, &mut add, page5);
            while let Some(r) = post.pop() { f_pop(c, r); }
        }
    } else {
        while let Some(r) = post.pop() { f_pop(c, r); }
    }});
    if std::env::var_os("LFF_PAGE5_TRACE").is_some() { eprintln!("W120_CLEANUP fwd peak={page_cleanup_peak} end={} cubic={}", c.active_qubits(), std::env::var_os("LFF_CUBIC_CLEANUP").is_some()); }
    if std::env::var_os("LFF_PAGE5_TRACE").is_some() { eprintln!("W110_STAGE fwd emax={emax} fields_q={} fields_T={:.1} page_q={} page_T={:.1} ladder_peak={pk_l} ladder_end_q={w110_al} ladder_T={:.1} back_q={} back_T={:.1}", w110_af as isize-w110_a0 as isize,w110_tf-w110_t0,w110_ap as isize-w110_af as isize,w110_tp-w110_tf,w110_tl-w110_tp,c.active_qubits() as isize-w110_al as isize,c.expected_total()-w110_tl); }
    f_qser_back(c, &mut d, &qold, &mut [&mut add]);
    f_klo_back(c, acc, nm, &mut d, sh.klo, &mut [], &mut [&mut add]);
    // c3 again where it left (no top-wire shed then): c1 and c2 first
    let (c1, c2) = if sh_c3 {
        let c1 = if fin >= 2 { lin_and(c, &l(acc[0]), &l(e[0])) } else { c1 };
        let c2 = if fin >= 1 { maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1)) } else { c2 };
        (c1, c2)
    } else {
        (c1, c2)
    };
    let c3n = if sh_c3 && dbg != 1 { maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2)) } else { c3 };
    if sh_c3 && dbg != 1 {
        f_rename(&mut d, c3g, c3n);
    }
    let c4 = if sh_c4 { lin_and(c, &l(acc[3]), &l(c3n)) } else { c4 };
    prof.push(("rebuilt", c.active_qubits() as i64));
    // the serial chunk's kept carry, by its compare (acc[4..K) holds W's bits)
    kept_erase(c, acc, &add, 4, kx, c4, ckx);
    while let Some(r) = d.qser.pop() {
        f_pop(c, r);
    }
    f_restore(c, acc, nm, emax, &mut d, c3n, &mut [], false);
    prof.push(("restored", c.active_qubits() as i64));
    f_tchain_out(c, &mut d);
    f_gates_back(c, &mut d, gsh, fin >= 3, k1, k2);
    for j in (0..d.yw.len()).rev() {
        let (a, b) = d.yer[j].clone();
        lin_and_erase(c, d.yw[j], &a, &b);
    }
    while let Some(r) = d.pre.pop() {
        f_pop(c, r);
    }
    // the top wires, then c1, c2 again (as fold_fwd_a, once the helper wires are gone)
    let e = match esh.as_deref_mut() {
        Some(st) => {
            esh_in(c, st);
            [st.x256, st.x257, st.x258]
        }
        None => e,
    };
    let (c1, c2) = if sh_c3 {
        (c1, c2)
    } else {
        let c1 = if fin >= 2 { lin_and(c, &l(acc[0]), &l(e[0])) } else { c1 };
        let c2 = if fin >= 1 { maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1)) } else { c2 };
        (c1, c2)
    };
    fold_undo_low_c(c, acc, e, [c1, c2, c3n, c4], None);
    if room_trace() {
        eprintln!("F_PROF fwd cap={} lev={lev} {:?}", cells::cap(), prof);
    }
    assert_eq!(c.active_qubits(), a_in, "fold-core: the IPK fold left a wire");
    plan
}
/// round17 fold-core: the exact inverse of [`fold_fwd_f`] (fin <= 2, no top-wire shed), as [`fold_inv_a`] with the
/// digit held in place through the ladder at the level the room asks for.
fn f_inv_phase<R>(c: &mut Builder, label: &str, body: impl FnOnce(&mut Builder) -> R) -> R {
    let start = c.active_qubits();
    let (result, peak) = c.r3_peak(body);
    if std::env::var("W118_FINE_TRACE").ok().as_deref() == Some("1") {
        eprintln!("F_INV_PHASE stage={label} start={start} peak={peak} end={}", c.active_qubits());
    }
    result
}
#[allow(clippy::too_many_arguments)]
fn fold_inv_f(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, k3: QubitId, emax: usize, fin: usize) -> Vec<usize> {
    // round17 a2-build: fin 3 also sheds the AND k1 k2 for the ladder (as the forward's fin 3)
    assert!(fin <= 3, "fold-core: the inverse IPK fold sheds at most c2, c1 and k1 k2");
    let mw = acc.len();
    let kx = 3 + emax;
    let a_in = c.active_qubits();
    let nbits = mw - kx;
    let n_fin = usize::from(fin >= 1) + usize::from(fin >= 2) + usize::from(fin >= 3);
    let at_ladder = (a_in as usize + a_fixed(emax)).saturating_sub(n_fin);
    let sh = f_sheds(emax, nbits, at_ladder, f_ngate(emax), true, false);
    let (sh_c4, sh_c3, gsh, lev) = (sh.c4, sh.c3, sh.gsh, sh.lev);
    let (c1, c2, c3, c4) = f_inv_phase(c, "entry_setup", |c| {
    c.cx(e[0], acc[0]);
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    c.cx(c1, acc[1]);
    c.cx(e[1], acc[1]);
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    c.cx(c2, acc[2]);
    c.cx(e[2], acc[2]);
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    c.cx(c3, acc[3]);
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    if !sh_c3 {
        if fin >= 1 {
            maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
        }
        if fin >= 2 {
            lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
        }
    }
    (c1, c2, c3, c4)
    });
    let (mut d, _, mut add_lo) = f_inv_phase(c, "digit", |c| f_digit(c, acc, nm, k1, k2, k3, emax, c3, c4, false, lev));
    // the serial chunk's kept carry, built exactly from W's bits [4, K) (its addend = Q's forms on [4, K))
    let ckx = f_inv_phase(c, "kept_seed", |c| a_lt_value(c, &acc[4..kx], &d.qb[0..kx - 4], c4));
    if sh_c4 {
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    let c3g = f_ghost();
    if sh_c3 {
        maj_wire_erase(c, c3, &l(acc[2]), &l(e[2]), &l(c2));
        f_rename(&mut d, c3, c3g);
        for f in add_lo.iter_mut() {
            f_sub(f, c3, c3g);
        }
        if fin >= 1 {
            maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
        }
        if fin >= 2 {
            lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
        }
    }
    f_inv_phase(c, "pre_fields_sheds", |c| {
        f_gates_out(c, &mut d, gsh, fin >= 3, k1, k2);
        f_klo_out(c, acc, nm, &mut d, sh.klo, &mut [], &mut [&mut add_lo]);
    });
    let qold = f_inv_phase(c, "qser_out", |c| f_qser_out(c, &mut d, sh.qs, &mut [&mut add_lo]));
    let mut post: Vec<Rec> = Vec::new();
    let (w110_a0,w110_t0)=(c.active_qubits(),c.expected_total());
    let mut add = f_inv_phase(c, "fields", |c| f_fields(c, &mut post, &d, emax, mw));
    let (w110_af,w110_tf)=(c.active_qubits(),c.expected_total());
    let unpaged_budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let page5 = f_inv_phase(c, "page_out", |c| f_page5_out(c, &mut post, &mut add, emax, f_final_plan(nbits, unpaged_budget, false).is_none()));
    if page5.is_some() { eprintln!("W118_PAGE inv budget={unpaged_budget} min={} emax={emax}", a_min_budget(nbits)); }
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let (plan, _) = f_final_plan(nbits, budget, false).unwrap_or_else(|| panic!("fold-core: the inverse IPK fold's ladder does not fit: budget {budget}, need {}, active {}, cap {}, lev {lev}", a_min_budget(nbits), c.active_qubits(), cells::cap()));
    let (w110_ap,w110_tp)=(c.active_qubits(),c.expected_total());
    f_inv_phase(c, "ladder_all", |c| a_ladder_inv(c, acc, &add, kx, ckx, &plan));
    let (w110_al,w110_tl)=(c.active_qubits(),c.expected_total());
    let ((), page_cleanup_peak) = c.r3_peak(|c| { if let Some(page5) = page5 {
        if std::env::var_os("LFF_CUBIC_CLEANUP").is_some() {
            f_page5_direct_cleanup(c, &mut post, &d, page5);
        } else {
            f_page5_back(c, &mut post, &mut add, page5);
            while let Some(r) = post.pop() { f_pop(c, r); }
        }
    } else {
        while let Some(r) = post.pop() { f_pop(c, r); }
    }});
    if std::env::var_os("LFF_PAGE5_TRACE").is_some() { eprintln!("W120_CLEANUP inv peak={page_cleanup_peak} end={} cubic={}", c.active_qubits(), std::env::var_os("LFF_CUBIC_CLEANUP").is_some()); }
    if std::env::var_os("LFF_PAGE5_TRACE").is_some() { eprintln!("W110_STAGE inv emax={emax} fields_q={} fields_T={:.1} page_q={} page_T={:.1} ladder_end_q={w110_al} ladder_T={:.1} back_q={} back_T={:.1}", w110_af as isize-w110_a0 as isize,w110_tf-w110_t0,w110_ap as isize-w110_af as isize,w110_tp-w110_tf,w110_tl-w110_tp,c.active_qubits() as isize-w110_al as isize,c.expected_total()-w110_tl); }
    f_inv_phase(c, "qser_back", |c| f_qser_back(c, &mut d, &qold, &mut [&mut add, &mut add_lo]));
    f_inv_phase(c, "klo_back", |c| f_klo_back(c, acc, nm, &mut d, sh.klo, &mut [], &mut [&mut add, &mut add_lo]));
    let (c1, c2, c3n, c4) = f_inv_phase(c, "low_parent_rebuild", |c| {
    let c1 = if fin >= 2 { lin_and(c, &l(acc[0]), &l(e[0])) } else { c1 };
    let c2 = if fin >= 1 { maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1)) } else { c2 };
    let c3n = if sh_c3 { maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2)) } else { c3 };
    let c4 = if sh_c4 { lin_and(c, &l(acc[3]), &l(c3n)) } else { c4 };
    if sh_c3 {
        f_rename(&mut d, c3g, c3n);
        for f in add.iter_mut().chain(add_lo.iter_mut()) {
            f_sub(f, c3g, c3n);
        }
    }
    (c1, c2, c3n, c4)
    });
    f_inv_phase(c, "digit_restore", |c| f_restore(c, acc, nm, emax, &mut d, c3n, &mut add_lo, true));
    // At emax=7, the three shed gate ANDs only reappear in the serial Y erase
    // forms. Rebuild each after the matching carry has been returned, rather
    // than holding all three across the serial carry build.
    // W135 fixture selector: fin3 additionally owns a shed tt=k1*k2. Its
    // rebuild is paid only after the first serial carry has been returned.
    let fin3_lazy = fin == 3; // W135 baked on
    let lazy_gates = std::env::var("W123_LAZY_GATES").ok().as_deref() == Some("1")
        && emax == 7 && gsh == 3 && (fin < 3 || fin3_lazy);
    if lazy_gates {
        assert_eq!(d.ngate, 4);
        eprintln!("W123_LAZY_GATES inv emax={emax} gsh={gsh} fin={fin}");
    } else {
        f_inv_phase(c, "gates_back", |c| f_gates_back(c, &mut d, gsh, fin >= 3, k1, k2));
    }
    // the serial chunk: its sums taken back bottom up, its carries built again
    let mut cc: Vec<QubitId> = vec![c4];
    f_inv_phase(c, "serial_carry_build", |c| {
    for j in 4..kx {
        if j > 4 {
            let t = m_carry(c, acc[j - 1], &add_lo[j - 5], cc[j - 5]);
            cc.push(t);
        }
        c.cx(cc[j - 4], acc[j]);
        lin_xor_into(c, &add_lo[j - 4], acc[j]);
    }
    });
    cc.push(ckx);
    // ... and the serial sweep's carries, digit bits and chain measured away top down
    f_inv_phase(c, "serial_carry_return", |c| {
    for j in (4..kx).rev() {
        f_pop(c, d.trec[j - 3].take().unwrap());
        m_carry_erase(c, cc[j - 3], acc[j], &add_lo[j - 4], cc[j - 4]);
        if lazy_gates && j >= kx - gsh {
            if fin3_lazy && j == kx - 1 {
                // g9 is the first remaining client of tt. trec and this
                // chunk's carry are already erased, paying for tt and g9.
                f_gates_back(c, &mut d, 0, true, k1, k2);
                eprintln!("W135_TT_BACK after_carry_j={j} active={}", c.active_qubits());
            }
            let gi = d.ngate + j - kx;
            f_gate_back_one(c, &mut d, gi);
        }
        let sum = l(acc[j]).x(&add_lo[j - 4]).x(&l(cc[j - 4]));
        let gj = d.yer[j - 3].0.clone();
        lin_and_erase(c, d.yw[j - 3], &gj, &sum);
        if j >= 6 {
            f_pop(c, d.qser.pop().unwrap());
        }
    }
    });
    f_inv_phase(c, "residual_return", |c| {
    f_pop(c, d.qser.pop().unwrap());
    f_pop(c, d.trec[0].take().unwrap());
    let (a, b) = d.yer[0].clone();
    lin_and_erase(c, d.yw[0], &a, &b);
    f_pop(c, d.r3v.take().unwrap());
    while let Some(r) = d.pre.pop() {
        f_pop(c, r);
    }
    lin_and_erase(c, c4, &l(acc[3]), &l(c3n));
    maj_wire_erase(c, c3n, &l(acc[2]), &l(e[2]), &l(c2));
    maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    });
    assert!(d.trec.iter().all(|r| r.is_none()) && d.qser.is_empty());
    assert_eq!(c.active_qubits(), a_in, "fold-core: the inverse IPK fold left a wire");
    plan
}
#[cfg(test)]
mod f_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    #[test]
    fn w118_final_drop_budget8() {
        // Exact t115 post-page layout: 47 high bits, eight free owners.
        assert_eq!(a_min_budget(47), 9);
        assert!(f_drop_plan(47, 8, &[0]).is_none());
        assert_eq!(f_final_plan(47, 8, false), None);
        let (plan, drops) = f_final_plan(47, 8, true).expect("two kept-carry drops fit");
        assert_eq!(drops, vec![0, 2]);
        assert_eq!(plan, vec![4, 7, 7, 6, 6, 5, 4, 3, 2, 3]);
        let (_, no_drops) = f_final_plan(47, 9, true).expect("ordinary plan fits at nine");
        assert!(no_drops.is_empty());
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }
    /// W = L + E - (Nm + m - E)(f - 1) mod 2^mw with m = W mod 2^K (m = (L + E - (Nm - E)(f - 1)) / f mod 2^K).
    fn f_expect(lv: u64, ev: u64, nmv: u64, kk: usize, mw: usize) -> u64 {
        let f1: i128 = (1i128 << 32) + 976;
        let md: i128 = 1i128 << mw;
        let mk: i128 = 1i128 << kk;
        let base = lv as i128 + ev as i128 - (nmv as i128 - ev as i128) * f1;
        // f = f1 + 1 is odd: m = base * f^-1 mod 2^K
        let finv = {
            let f = (f1 + 1).rem_euclid(1i128 << 16);
            let mut x: i128 = 1;
            for _ in 0..5 {
                x = (x * (2 - f * x)).rem_euclid(1i128 << 16);
            }
            x
        };
        let m = (base.rem_euclid(mk) * finv.rem_euclid(mk)).rem_euclid(mk);
        let w = (base - m * f1).rem_euclid(md);
        assert_eq!(w & (mk - 1), m);
        w as u64
    }
    /// Inputs: `exh` = exhaustive over (L mod 2^lowb, E, Nm, e <= emax) with random high bits, else random shots.
    fn inputs(emax: usize, mw: usize, batches: usize, exh: Option<usize>, seed: u64) -> Vec<(u64, u64, u64, usize)> {
        let mut rng = Rng(seed);
        let mut v = Vec::new();
        if let Some(lowb) = exh {
            for lo in 0..(1u64 << lowb) {
                for ev in 0..8u64 {
                    for nmv in 0..8u64 {
                        for ee in 0..=emax {
                            let hi = (rng.next() << lowb) & ((1u64 << mw) - 1);
                            v.push((hi | lo, ev, nmv, ee));
                        }
                    }
                }
            }
        } else {
            for _ in 0..batches * 64 {
                let lv = rng.next() & ((1u64 << mw) - 1);
                let ev = rng.next() % 8;
                let nmv = rng.next() % 8;
                let ee = loop {
                    let x = (rng.next() % 8) as usize;
                    if x <= emax {
                        break x;
                    }
                };
                v.push((lv, ev, nmv, ee));
            }
        }
        while v.len() % 64 != 0 {
            let x = v[v.len() % 7];
            v.push(x);
        }
        v
    }
    /// Exact check of [`fold_fwd_f`] (fwd) or [`fold_inv_f`] at a cap that gives the ladder `room` wires beside the
    /// fixed part: values, clean ancillas, letters unchanged, no phase. Returns expected Toffoli.
    fn check_f(fwd: bool, emax: usize, mw: usize, room: isize, fin: usize, inp: &[(u64, u64, u64, usize)]) -> f64 {
        let mut c = Builder::new();
        let acc = c.alloc_qubits(mw);
        let e = c.alloc_qubits(3);
        let nm = c.alloc_qubits(3);
        let k = c.alloc_qubits(3);
        let base = c.active_qubits() as usize;
        let cap = ((base + a_fixed(emax) - fin.min(2)) as isize + room) as usize;
        let e0 = c.expected_total();
        let plan = super::super::super::pingpong::with_phase_cap(Some(cap), || {
            if fwd {
                fold_fwd_f(&mut c, &acc, [e[0], e[1], e[2]], [nm[0], nm[1], nm[2]], k[0], k[1], k[2], emax, fin, None)
            } else {
                fold_inv_f(&mut c, &acc, [e[0], e[1], e[2]], [nm[0], nm[1], nm[2]], k[0], k[1], k[2], emax, fin)
            }
        });
        let cost = c.expected_total() - e0;
        let peak = c.peak_total() as usize;
        let (nq, nbits) = c.i13_dims();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(if fwd { b"fold-core-fwd" } else { b"fold-core-inv" });
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let mut bad = 0usize;
        for chunk in inp.chunks(64) {
            sim.clear_for_shot();
            for (shot, &(lv, ev, nmv, ee)) in chunk.iter().enumerate() {
                let wv = f_expect(lv, ev, nmv, 3 + ee, mw);
                let x = if fwd { lv } else { wv };
                for i in 0..mw {
                    if x >> i & 1 == 1 {
                        *sim.qubit_mut(acc[i]) |= 1 << shot;
                    }
                }
                for i in 0..3 {
                    if ev >> i & 1 == 1 {
                        *sim.qubit_mut(e[i]) |= 1 << shot;
                    }
                    if nmv >> i & 1 == 1 {
                        *sim.qubit_mut(nm[i]) |= 1 << shot;
                    }
                    if ee >> i & 1 == 1 {
                        *sim.qubit_mut(k[i]) |= 1 << shot;
                    }
                }
            }
            sim.apply_iter(ops.iter());
            for (shot, &(lv, ev, nmv, ee)) in chunk.iter().enumerate() {
                let want = if fwd { f_expect(lv, ev, nmv, 3 + ee, mw) } else { lv };
                let mut got = 0u64;
                for i in 0..mw {
                    got |= ((sim.qubit(acc[i]) >> shot) & 1) << i;
                }
                let mut ok = got == want && (sim.phase >> shot) & 1 == 0;
                for i in 0..3 {
                    ok &= ((sim.qubit(e[i]) >> shot) & 1) == (ev >> i & 1);
                    ok &= ((sim.qubit(nm[i]) >> shot) & 1) == (nmv >> i & 1);
                    ok &= ((sim.qubit(k[i]) >> shot) & 1) == (ee as u64 >> i & 1);
                }
                let mut dirty = Vec::new();
                for q in base..nq {
                    if (sim.qubits[q] >> shot) & 1 != 0 {
                        dirty.push(q);
                    }
                }
                ok &= dirty.is_empty();
                if !ok {
                    if bad < 3 && std::env::var("LFF_T").is_ok() {
                        eprintln!("BAD shot: value_ok={} phase={} dirty={:?} got^want={:x} e={ev} nm={nmv} ee={ee}", got == want, (sim.phase >> shot) & 1, dirty, got ^ want);
                    }
                    bad += 1;
                }
            }
        }
        eprintln!("F_FOLD_CHECK {} emax={emax} mw={mw} room={room} fin={fin} lev>={} fixed={} plan={plan:?} expected_T={cost:.1} peak_over_base={} shots={} bad={bad}", if fwd { "fwd" } else { "inv" }, f_lev_min(), a_fixed(emax), peak - base, inp.len());
        assert_eq!(bad, 0, "fold-core: the IPK fold ({}) is wrong on {bad} shots", if fwd { "fwd" } else { "inv" });
        cost
    }
    fn own_max(emax: usize) -> usize { 1 + (emax - 4).min(3) + emax + 1 + f_extra_sheds(emax) }
    /// W110 bounded paired local ABI test.  `check_f(false)` initializes W
    /// independently, not by applying the matching forward circuit.
    #[test]
    fn f_page5_local() {
        std::env::set_var("LFF_PAGE5_TRACE", "1");
        std::env::set_var("LFF_T", "1");
        let inp = inputs(7, 57, 4, None, 0x9e37_79b9_f0c0_a660);
        for fwd in [true, false] {
            std::env::remove_var("LFF_PAGE5");
            let base = check_f(fwd, 7, 57, 14, 0, &inp);
            std::env::set_var("LFF_PAGE5", "1");
            let page = check_f(fwd, 7, 57, 14, 0, &inp);
            eprintln!("W110_PAIR dir={} baseline_T={base:.1} page_T={page:.1} delta_T={:.1}", if fwd { "fwd" } else { "inv" }, page-base);
            std::env::remove_var("LFF_PAGE5");
        }
        std::env::remove_var("LFF_PAGE5_TRACE");
        std::env::remove_var("LFF_T");
    }
    #[test]
    fn f_fold_random() {
        for emax in [5usize, 6, 7] {
            let mb = a_min_budget(57 - 3 - emax) as isize;
            let mut rooms = vec![(60isize, 0usize), (20, 0), (14, 0), (12, 1)];
            for r in ((mb - own_max(emax) as isize)..=11).rev() {
                rooms.push((r, 2));
            }
            for (room, fin) in rooms {
                if room + own_max(emax) as isize >= mb {
                    let inp = inputs(emax, 57, 40, None, 0x9e37_79b9_7f4a_7c15 ^ (emax as u64 * 1000 + (room + 100) as u64));
                    check_f(true, emax, 57, room, fin, &inp);
                    check_f(false, emax, 57, room, fin, &inp);
                }
            }
        }
    }
    /// Every level forced, at an ample room and at the least room.
    #[test]
    fn f_fold_levels() {
        for emax in [5usize, 6, 7] {
            for lev in 0..=emax {
                F_LEV_FORCE.with(|x| x.set(Some(lev)));
                let inp = inputs(emax, 57, 40, None, 0x1234_5678 ^ (emax as u64 * 100 + lev as u64));
                check_f(true, emax, 57, 60, 0, &inp);
                check_f(false, emax, 57, 60, 0, &inp);
            }
            F_LEV_FORCE.with(|x| x.set(None));
        }
    }
    /// LFF_EXH=lowbits (default 8): exhaustive over L mod 2^lowbits x E x Nm x e for emax 5 and 7: full level at an
    /// ample room, and the least room (every own shed).
    #[test]
    fn f_fold_exhaustive() {
        let lowb: usize = std::env::var("LFF_EXH").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
        for emax in [5usize, 7] {
            let inp = inputs(emax, 57, 0, Some(lowb), 0x2545_f491_4f6c_dd1d ^ emax as u64);
            let least = a_min_budget(57 - 3 - emax) as isize - own_max(emax) as isize;
            F_LEV_FORCE.with(|x| x.set(Some(emax)));
            check_f(true, emax, 57, 60, 0, &inp);
            check_f(false, emax, 57, 60, 0, &inp);
            F_LEV_FORCE.with(|x| x.set(None));
            check_f(true, emax, 57, least, 2, &inp);
            check_f(false, emax, 57, least, 2, &inp);
        }
    }
    /// The forward fold past the whole own-shed menu: 1 and 2 dropped kept carries (exhaustive low bits, LFF_EXH).
    #[test]
    fn f_fold_drops() {
        let lowb: usize = std::env::var("LFF_EXH").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
        for mw in [57usize, 56] {
            for emax in [5usize, 6, 7] {
                let inp = inputs(emax, mw, 0, Some(lowb), 0x5eed ^ emax as u64 ^ (mw as u64) << 8);
                let least = a_min_budget(mw - 3 - emax) as isize - own_max(emax) as isize;
                let (nb, mb) = (mw - 3 - emax, a_min_budget(mw - 3 - emax));
                for extra in 0..=2usize {
                    if extra == 0 || F_DROPS.iter().any(|ds| f_drop_plan(nb, mb - extra, ds).is_some()) {
                        check_f(true, emax, mw, least - extra as isize, 2, &inp);
                    }
                }
            }
        }
    }
    /// LFF_T="emax,room,fin[,sh]": one configuration (debug), sh = forced least number of own sheds.
    #[test]
    fn f_fold_one() {
        let Ok(v) = std::env::var("LFF_T") else { return };
        let x: Vec<isize> = v.split(',').map(|t| t.parse().unwrap()).collect();
        let (emax, room, fin) = (x[0] as usize, x[1], x[2] as usize);
        if x.len() > 3 {
            F_SH_FORCE.with(|f| f.set(Some(x[3] as usize)));
        }
        let inp = inputs(emax, 57, 40, None, 77);
        check_f(true, emax, 57, room, fin, &inp);
        check_f(false, emax, 57, room, fin, &inp);
    }
}
