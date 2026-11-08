thread_local! {static FRAME_FWD_K3:std::cell::Cell<Option<QubitId>>=const{std::cell::Cell::new(None)};}
pub(super)fn frame_fwd_take()->QubitId{FRAME_FWD_K3.with(|v|v.take().expect("delayed k3 missing"))}
// ======================================================================================================================
// round17 a2-build (lever A end to end on fold-core's IPK fold). Piece M2: the 8-way payload rotation, the round6 B1
// parity-split network (axes 0, -4, -2, -6, -7; 508 Fredkins on n = 256), every half-stage controlled by a linear form
// of (k1, k2, k3) (CX onto a host letter wire, Clifford). out[i] = in[(i + e) mod n], e = k1 + 2 k2 + 4 k3.
// ======================================================================================================================
/// The network's units in stage order: (axis x, parity (0: even i, 1: odd i, 2: every i), control mask over
/// (k1 = 1, k2 = 2, k3 = 4)). A reflection pairs i with (x - i) mod n; half-stages of one stage act on disjoint pairs.
const ROT8_UNITS: [(isize, u8, u8); 9] = [(0, 0, 4), (0, 1, 2), (-4, 0, 6), (-4, 1, 0), (-2, 0, 0), (-2, 1, 6), (-6, 0, 3), (-6, 1, 5), (-7, 2, 1)];

/// The active units of the 8-way rotation on n wires: (Fredkin pairs, control mask).
pub(super) fn rot8_units(n: usize) -> Vec<(Vec<(usize, usize)>, u8)> {
    assert!(n % 2 == 0 && n >= 16, "rot8: the parity split needs an even register");
    ROT8_UNITS
        .iter()
        .filter(|u| u.2 != 0)
        .map(|&(x, par, mask)| {
            let pairs = (0..n)
                .filter(|&i| par == 2 || i % 2 == par as usize)
                .filter_map(|i| {
                    let j = (x - i as isize).rem_euclid(n as isize) as usize;
                    (i < j).then_some((i, j))
                })
                .collect();
            (pairs, mask)
        })
        .collect()
}

/// The permutation of [`rot8`] for shift e (arr[i] = the input index that lands on i).
pub(super) fn rot8_map(n: usize, e: usize) -> Vec<usize> {
    let mut arr: Vec<usize> = (0..n).collect();
    for (pairs, mask) in rot8_units(n) {
        if (mask as usize & e).count_ones() % 2 == 1 {
            for &(a, b) in &pairs {
                arr.swap(a, b);
            }
        }
    }
    arr
}

/// Host wire and the other letters XORed onto it for a control mask.
fn rot8_host(k: [QubitId; 3], mask: u8) -> (QubitId, Vec<QubitId>) {
    let idx: Vec<usize> = (0..3).filter(|i| mask >> i & 1 == 1).collect();
    (k[idx[0]], idx[1..].iter().map(|&i| k[i]).collect())
}

/// The 8-way rotation of `t` by e = k1 + 2 k2 + 4 k3 (inverse: by -e). 508 Fredkins on 256 wires.
pub(super) fn rot8(c: &mut Builder, k: [QubitId; 3], t: &[QubitId], inverse: bool) {
    let mut units = rot8_units(t.len());
    if inverse {
        units.reverse();
    }
    for (pairs, mask) in units {
        let (h, others) = rot8_host(k, mask);
        for &o in &others {
            c.cx(o, h);
        }
        for &(a, b) in &pairs {
            fredkin(c, h, t[a], t[b]);
        }
        for &o in others.iter().rev() {
            c.cx(o, h);
        }
    }
}

/// Phase (-1)^(sum_i m_i rot8_e(v)_i) on the unrotated `v` (the 8-way [`rot4_phase`]; `inv`: rot8_e^-1); frees the
/// bits. Monomials of [e == val] in (k1, k2, k3): every mask m containing val; 4 AND wires (k1k2, k1k3, k2k3, k1k2k3).
pub(super) fn rot8_phase(c: &mut Builder, k: [QubitId; 3], v: &[QubitId], bits: Vec<crate::circuit::BitId>, inv: bool) {
    let n = v.len();
    let maps: Vec<Vec<usize>> = (0..8).map(|e| rot8_map(n, e)).collect();
    let mut acc: std::collections::BTreeMap<(usize, usize), Vec<usize>> = std::collections::BTreeMap::new();
    for i in 0..bits.len() {
        for val in 0..8usize {
            let (j, bi) = if inv { (i, maps[val][i]) } else { (maps[val][i], i) };
            for mono in (0..8usize).filter(|m| m & val == val) {
                let l = acc.entry((j, mono)).or_default();
                if let Some(p) = l.iter().position(|&x| x == bi) {
                    l.remove(p);
                } else {
                    l.push(bi);
                }
            }
        }
    }
    let t12 = and_new(c, k[0], k[1]);
    let t13 = and_new(c, k[0], k[2]);
    let t23 = and_new(c, k[1], k[2]);
    let t123 = and_new(c, t12, k[2]);
    for (&(j, mono), l) in acc.iter() {
        for &i in l {
            match mono {
                0 => c.z_if(v[j], bits[i]),
                1 => c.cz_if(k[0], v[j], bits[i]),
                2 => c.cz_if(k[1], v[j], bits[i]),
                4 => c.cz_if(k[2], v[j], bits[i]),
                3 => c.cz_if(t12, v[j], bits[i]),
                5 => c.cz_if(t13, v[j], bits[i]),
                6 => c.cz_if(t23, v[j], bits[i]),
                _ => c.cz_if(t123, v[j], bits[i]),
            }
        }
    }
    and_erase(c, t123, t12, k[2]);
    and_erase(c, t23, k[1], k[2]);
    and_erase(c, t13, k[0], k[2]);
    and_erase(c, t12, k[0], k[1]);
    for b in bits {
        c.free_bit(b);
    }
}

// ======================================================================================================================
// The A payload tick with a real third shift letter (forward: main's body + IPK fold + rot8; reverse, M6: the exact
// inverse tick, fold^-1 before the subtractions).
// ======================================================================================================================
/// LFA2_EXT: extra window bits of the reverse tick's value compares over the forward's erase compares (default 2 = v3w).
fn a2_ext(t:usize,kind:usize) -> usize {compare_window_knob("EXT",true,t,kind,a_env("LFA2_EXT").unwrap_or(2))}
/// LFA2_TICK=1: the builder's forward A ticks (LFA_FOLD=1) run [`a2_fwd_tick`] (rot8 and the IPK fold).
pub(super) fn a2_tick_test() -> bool { std::env::var("LFA2_TICK").is_ok_and(|v| v == "1") }
/// LFA2_REV=1: the builder's reverse one-fold ticks t in [1, LFA_TO) run [`a2_rev_tick`] (M6).
pub(super) fn a2_rev_test() -> bool { std::env::var("LFA2_REV").is_ok_and(|v| v == "1") }
/// The forward A payload tick: `tgt <- (tgt + sum_i (-1)^s_i 2^i src) 2^-(3 + e) (mod p)`, e = k1 + 2 k2 + 4 k3 <= emax:
/// main's one-fold body with the A fold (IPK under LFF_IPK=1), then the rotation down by 3 + e.
pub(super) fn a2_fwd_tick(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, p: &mut [Vec<QubitId>; 2]) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (_, proxy) = proxy_fold(w, false);
    let (tg, b) = (p[ti].clone(), p[si].clone());
    let shift = cmp_shift_at(t);
    let frame_delayed=k[2]==crate::circuit::NO_QUBIT;
    a_set(Some((k[2], emax)));
    cells::with_tie(None, || cells::with_cmp_shift((shift.0 + Y15_CMP_EXTRA + super::n2_cmpx(), shift.1), || cells::with_bridge(proxy, false, || body_capped(c, t, s, k[0], k[1], &b, &tg, proxy, false))));
    let actual_k3=a_tick().expect("A tick context").0;
    let k=[k[0],k[1],actual_k3];
    if frame_delayed{FRAME_FWD_K3.with(|v|{assert!(v.get().is_none());v.set(Some(actual_k3));});}
    a_set(None);
    for _ in 0..3 {
        rot1(c, &tg, true);
    }
    if !SKIP_ROT4.with(|x| x.get()) {
        rot8(c, k, &tg, false);
    }
}
/// The reverse A payload tick, the exact inverse of [`a2_fwd_tick`]: rotation up by 3 + e, then [`body_inv`].
pub(super) fn a2_rev_tick(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, p: &mut [Vec<QubitId>; 2]) {
    a2_rev_tick_k3_owner(c, t, s, k, emax, p, false);
}
/// Payload-only consumer owns a freshly decoded record k3. Retire it at its
/// last fold use; borrowed/fused callers continue through a2_rev_tick unchanged.
pub(super) fn a2_rev_tick_owned_k3(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, p: &mut [Vec<QubitId>; 2]) {
    let owned=!(t==120&&std::env::var("RAIL_OPT_ALIAS").as_deref()==Ok("1"));
    a2_rev_tick_k3_owner(c,t,s,k,emax,p,owned);
}
fn a2_rev_tick_k3_owner(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, p: &mut [Vec<QubitId>; 2], owns_k3: bool) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (_, proxy) = proxy_fold(w, true);
    let (tg, b) = (p[ti].clone(), p[si].clone());
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    rot8(c, k, &tg, true);
    for _ in 0..3 {
        rot1(c, &tg, false);
    }
    let shift = cmp_shift_at(t);
    cells::with_tie(None, || cells::with_cmp_shift((shift.0 + Y15_CMP_EXTRA, shift.1), || cells::with_bridge(proxy, true, || {
        let ((), peak) = c.r3_peak(|c| body_inv(c, t, s, k, emax, &b, &tg, proxy, owns_k3));
        if room_trace() {
            eprintln!("A2_PEAK rev t={t} peak={peak} cap={}", cells::cap());
        }
        if std::env::var("W118_DIAG_PEAK").ok().as_deref() == Some("1") {
            eprintln!("W118_DIAG_PEAK reverse_A2 t={t} actual={peak} plan_cap={}", cells::cap());
        } else {
            assert!(peak as usize <= cells::cap(), "a2: the reverse A tick t={t} peaks at {peak}, over the walk cap {}", cells::cap());
        }
    })));
    if room_trace() {
        eprintln!("A2_TICK rev t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
}

/// target ^= [u < v + borrow_in] (u, v wires; the value form of [`super::super::compare::cmp_lt_phase`], same ladder,
/// same predicate): the carries of ~u + v + borrow_in, the top one as a MAJ onto `target` (one Toffoli), the chain
/// measured away. n Toffoli for n bits (n - 1 for the ladder, 1 for the top).
fn a2_lt_into(c: &mut Builder, u: &[QubitId], v: &[QubitId], borrow_in: Option<QubitId>, target: QubitId) {
    let n = u.len();
    assert_eq!(v.len(), n);
    assert!(n > 1);
    if borrow_in == Some(v[0]) {
        assert!(n >= 3, "a2: an aliased low seed needs two more compare bits");
        return a2_lt_into(c, &u[1..], &v[1..], borrow_in, target);
    }
    let operand_seed = borrow_in.is_some_and(|q| v[1..].contains(&q));
    assert!(!borrow_in.is_some_and(|q| u.contains(&q)), "a2: the seed cannot alias the accumulator");
    let last = n - 1;
    let carries = c.alloc_qubits(last);
    c.x_all(u);
    c.cx(u[0], v[0]);
    let first_ctrl = borrow_in.map_or(u[0], |p| {
        c.cx(u[0], p);
        p
    });
    c.ccx(first_ctrl, v[0], carries[0]);
    if operand_seed {
        c.cx(u[0], borrow_in.unwrap());
    }
    c.cx(carries[0], u[0]);
    for i in 1..last {
        c.cx(u[i], v[i]);
        c.cx(u[i], u[i - 1]);
        c.ccx(u[i - 1], v[i], carries[i]);
        c.cx(carries[i], u[i]);
    }
    // the top carry MAJ(u_l, v_l, u_(l-1)) as a value: (a ^ c)(b ^ c) ^ c
    c.cx(u[last - 1], u[last]);
    c.cx(u[last - 1], v[last]);
    c.ccx(u[last], v[last], target);
    c.cx(u[last - 1], target);
    c.cx(u[last - 1], v[last]);
    c.cx(u[last - 1], u[last]);
    for i in (1..last).rev() {
        c.cx(carries[i], u[i]);
        let m = c.alloc_bit();
        c.hmr(carries[i], m);
        c.cz_if(u[i - 1], v[i], m);
        c.free_bit(m);
        c.cx(u[i], u[i - 1]);
        c.cx(u[i], v[i]);
    }
    c.cx(carries[0], u[0]);
    let m0 = c.alloc_bit();
    c.hmr(carries[0], m0);
    match borrow_in {
        Some(p) => {
            if operand_seed {
                c.cx(u[0], p);
            }
            c.cz_if(p, v[0], m0);
            c.cx(u[0], p);
        }
        None => c.cz_if(u[0], v[0], m0),
    }
    c.free_bit(m0);
    c.cx(u[0], v[0]);
    c.free_vec(&carries);
    c.x_all(u);
}

/// acc (n + 1 wires, the top one a held carry) -= addend (n wires) as ~(~acc + addend) on n + 1 bits: the caller
/// guarantees acc >= addend, so the carry out is always 0 (released) and the top wire ends 0 (the caller releases it).
fn a2_sub_top(c: &mut Builder, addend: &[QubitId], acc: &[QubitId], proxy: usize) {
    assert_eq!(acc.len(), addend.len() + 1);
    if A2_SUB_PADTOP && A2_SUB_NOCOUT && A2_SUB_KNOWN_TOP {
        // v2: no zero wire for the addend's top bit (one wire of room more for every chunk of the subtraction)
        c.x_all(acc);
        cells::chunked_add_nocout_padtop(c, addend, acc, proxy, true, Some(true));
        c.x_all(acc);
        return;
    }
    let z = c.alloc_qubit();
    let mut add = addend.to_vec();
    add.push(z);
    c.x_all(acc);
    if A2_SUB_NOCOUT {
        // the top bit of ~acc + addend is 1 (the result's top bit is 0)
        cells::chunked_add_nocout(c, &add, acc, proxy, true, A2_SUB_KNOWN_TOP.then_some(true));
    } else {
        let cout = cells::chunked_add(c, &add, acc, proxy, true);
        c.release_clean(cout);
    }
    c.release_clean(z);
    c.x_all(acc);
}
/// The subtraction's carry-out (0 whenever acc >= addend, which the caller guarantees) is not computed: one Toffoli
/// less per subtraction, three per reverse tick. false = the parent's gate list.
const A2_SUB_NOCOUT: bool = true;
/// The subtraction's top wire (the held carry, cleared by the carry into it) is erased by an X measurement while the
/// last chunk's carries are live (its value is their terminal carry: Clifford repair) in place of the terminal
/// Toffoli that wrote that carry onto it (needs A2_SUB_NOCOUT).
const A2_SUB_KNOWN_TOP: bool = true;
/// v2 PADTOP: the subtraction allocates no zero wire for its addend's top bit; false = the parent's gate list.
const A2_SUB_PADTOP: bool = true;

/// The reverse A tick's body (M6): the exact inverse of the forward one-fold body in its A configuration (direct cuts,
/// add 1 to the top, add 2's top ripple open, no closed ripple, no deep shed) with [`fold_inv_f`] in place of the fold.
/// On entry tg = W rotated up (bits [0, MW) the fold's output, the rest X's bits), b = the source. Steps, each the
/// inverse of a forward step in reverse order:
///   I9  m2 (the carry into add 2's index sp2) by its compare as a value; add 2's top ripple opened again (sums taken
///       back, carries built);
///   I8  m0 = g0 ^ h1 (add 1's chain on its window + g0's compare, as values), m1 = x257 by the G6' top-column
///       identity, m0 ^= S'1[255] (= X1[256]);
///   I7  the three top carries; I6 the two lower top wires to their sums; I5 fold^-1; I4 the tops back to X1;
///   I3' the top ripple measured away; I3/I2/I1 the subtractions (n + 1 bits, the held carry as the top) that leave
///       m2, m1 and m0 clear.
/// Its value compares read `a2_ext` more bits than the forward's erase compares (a wrong value is a wrong result, not
/// a phase), so sp2 sits that much lower. Sheds: a block of the open ripple (1 Toffoli each) and fin <= 2 of the fold.
#[allow(clippy::too_many_arguments)]
/// L2-M2M0 switch (lane 2): shed m2 at m0's step when the open-ripple pool alone is short.
const L2_M2_AT_M0: bool = true;
/// L2-HB switch (lane 2): erase the m0 chain's top AND before m0's compare.
const L2_HB_EARLY: bool = true;
/// L2-S1 / L2-CR switches (lane 2): m0's step without the 2 unused slack wires; chain release before m2 shed.
const L2_S1_TIGHT: bool = true;
const L2_CHAIN_RELEASE: bool = true;
fn body_inv(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, b: &[QubitId], tg: &[QubitId], proxy: usize, owns_k3: bool) {
    if t==48&&false{c.z_if(tg[0],NO_BIT);}

    let (e_start, a_start) = (c.expected_total(), c.active_qubits());
    let rev = true;
    let ext = a2_ext(t,0); let ext2 = a2_ext(t,2);
    let (k0, seed0) = cells::y15_split_spec(proxy, rev, N);
    let (kk1, _) = cells::y15_split_spec(proxy, rev, N - 1);
    let k0x = k0 + ext;
    let seed0x = seed0.map(|_| N - k0x - 1);
    let kwin = k0x.max(kk1);
    let sp2 = N - 2 - kwin;
    let (kk2, seed2) = cells::y15_split_spec(proxy, rev, sp2);
    let kk2x = kk2 + ext2;
    let seed2x = seed2.map(|_| sp2 - kk2x - 1);
    let mw = fold_window(t, true);
    assert!(mw + 8 < sp2 - kk2x, "a2: the reverse tick's windows overlap the fold");
    let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
    let s0f = |i: usize| Lin::of(&[b[i], s[2], s[0]]);
    // I10 (b <- S'2) and I9
    c.cx_all(s[2], b);
    let acc2: Vec<QubitId> = tg[2..].to_vec(); // acc2[i] = bit i + 2 (the two top entries come later)
    let m2 = c.alloc_qubit();
    {
        let blo = seed2x.map_or(sp2 - kk2x, |sd| sd.min(sp2 - kk2x));
        assert!(blo >= mw);
        a2_lt_into(c, &acc2[sp2 - kk2x..sp2], &b[sp2 - kk2x..sp2], seed2x.map(|sd| b[sd]), m2);
    }
    let e_m2 = c.expected_total();
    let mut cc: Vec<QubitId> = vec![m2]; // cc[i - sp2] = the carry into index i of add 2
    for i in sp2..N - 2 {
        if i > sp2 {
            let q = m_carry(c, acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
            cc.push(q);
        }
        c.cx(cc[i - sp2], acc2[i]);
        c.cx(b[i], acc2[i]);
    }
    let e_open = c.expected_total();
    // room, m0's step: its chain and compare (2 k0x wires) with s1 carries of the open ripple shed (cq(sp2) = m2 stays;
    // cq(N - 3) and the rest are built again before I7, 1 Toffoli each)
    let frame_host=std::env::var("RAIL_OPT_M0").as_deref()==Ok("1");
    let room_m = cells::cap().saturating_sub(c.active_qubits() as usize + 2);
    // L2-HB: the chain's top AND (h1) leaves right after it is copied into m0, so the compare runs beside k0x - 1
    // chain wires.
    let need_m=k0x+(k0x-1)+if frame_host{0}else{1-usize::from(L2_HB_EARLY)};
    let s1 = need_m.saturating_sub(room_m + if L2_S1_TIGHT { 2 } else { 0 }).max(a_env("LFA2_FS1").unwrap_or(0)).min(N - 3 - sp2);
    assert!(s1 <= N - 3 - sp2, "a2: the reverse tick t={t} does not fit m0's step: short {s1}, pool {}", N - 3 - sp2);
    for i in ((N - 2 - s1)..=(N - 3)).rev() {
        m_carry_erase(c, cc[i - sp2], acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
    }
    // L2-M2M0 (exact): when m0's step is short by more than the whole ripple pool, m2 (= cc[0], the carry into sp2)
    // leaves as well, erased by its own window compare (the fold's m2-shed path), and is built again by the same
    // value compare once m0 and m1 are done, before the shed ripple carries are rebuilt.
    let m2_win_m = (sp2 - kk2x, seed2x);
    // room_m keeps 2 wires of slack (m0, m1): m0's step really overflows only when short by more than pool + 2.
    // L2-CR: wires still missing after the ripple pool are first taken from the chain (k0x - 3 at most).
    let cr_need = need_m.saturating_sub(s1 + room_m + 2);
    let cr_max = if L2_CHAIN_RELEASE { k0x - 3 } else { 0 };
    let cr = cr_need.min(cr_max);
    let m2_shed_m = L2_M2_AT_M0 && cr_need > cr_max;
    if m2_shed_m {
        let (w0, sd) = m2_win_m;
        cells::y15_erase_cmp(c, cc[0], &acc2[w0..sp2], &b[w0..sp2], sd.map(|i| b[i]));
        c.free(cc[0]);
        if room_trace() { eprintln!("L2_M2M0 shed t={t} need={need_m} room={room_m} pool={}", N - 3 - sp2); }
    }
    // I8: m0 = g0 ^ h1, then m1 = x257, then m0 = X1[256]
    let lo = N - k0x;
    let i0 = lo - 1;
    assert!(sp2 + 2 <= i0 + 1 && i0 >= 1);
    let frame_old_m0=(!frame_host).then(||c.alloc_qubit());
    let m0={
        let mut r: Vec<Lin> = vec![s1f(i0 - 1)];
        let mut rr: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
        for i in i0..N - 1 {
            let ci = r[i - i0].clone();
            let (fa, fb) = (s1f(i).x(&ci), l(tg[i + 1]).x(&s1f(i)));
            let q = lin_and(c, &fa, &fb);
            lin_xor_into(c, &ci, q);
            rr.push((q, fa, fb, ci));
            r.push(l(q));
        }
        let hb = rr.last().expect("a2: the chain is not empty").0; // C1[N - 1] = h1
        let m0=frame_old_m0.unwrap_or(hb);
        if !frame_host{c.cx(hb,m0);}
        if frame_host&&std::env::var("FRAME_M0_FAULT").as_deref()==Ok("1"){c.x(m0);}
        if L2_HB_EARLY&&!frame_host {
            // L2-HB (exact): h1 is read only by m0 (the chain's XOR into tg stops at r[N - 2 - i0]); its erase forms
            // (ci, s1f(N - 2), tg[N - 1]) are untouched until here, so the existing erase moves ahead of the compare.
            let (q, fa, fb, ci) = rr.pop().expect("a2: the chain is not empty");
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fb);
        }
        for j in lo..N {
            lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
        }
        // L2-CR (exact): tg[i + 1] now holds tg[i + 1] ^ s1f(i) ^ ci, so the AND's second form is tg[i + 1] ^ ci; the top
        // `cr` chain ANDs leave (measured, top down, each above a live ci) and are built again after the compare.
        let nrr=rr.len()-usize::from(frame_host);
        assert!(cr < nrr, "a2: chain release larger than the chain");
        for idx in (nrr - cr..nrr).rev() {
            let (q, fa, _fb, ci) = rr[idx].clone();
            let fbn = l(tg[i0 + idx + 1]).x(&ci);
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fbn);
        }
        if cr > 0 && room_trace() { eprintln!("L2_CR t={t} cr={cr} need={need_m} room={room_m} s1={s1}"); }
        let blo = seed0x.map_or(lo, |sd| sd.min(lo));
        for i in blo..N {
            c.cx(s[2], b[i]);
            c.cx(s[0], b[i]);
        }
        a2_lt_into(c, &tg[lo..N], &b[lo..N], seed0x.map(|sd| b[sd]), m0);
        for i in blo..N {
            c.cx(s[0], b[i]);
            c.cx(s[2], b[i]);
        }
        for idx in nrr - cr..nrr {
            let i = i0 + idx;
            let ci = r[idx].clone();
            let fa = s1f(i).x(&ci);
            let q = lin_and(c, &fa, &l(tg[i + 1]).x(&ci));
            lin_xor_into(c, &ci, q);
            rr[idx] = (q, fa, l(tg[i + 1]).x(&s1f(i)), ci);
            r[idx + 1] = l(q);
        }
        for j in (lo..N).rev() {
            lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
        }
        while let Some((q, fa, fb, ci)) = rr.pop() {
            if frame_host&&q==m0{continue;}
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fb);
        }
        m0
    };
    let m1 = c.alloc_qubit();
    {
        // G6' identity: x257 = q ^ u (q ^ S'1[255]), q = MAJ(S'0[255], S'1[254], ~X1[255]), u = m0
        let (fx, fy) = (s0f(N - 1), s1f(N - 2));
        let fc = l(tg[N - 1]).x(&Lin::k(true));
        let q = maj_wire(c, &fx, &fy, &fc);
        lin_and_into(c, m1, &l(m0), &l(q).x(&s1f(N - 1)));
        c.cx(q, m1);
        maj_wire_erase(c, q, &fx, &fy, &fc);
    }
    lin_xor_into(c, &s1f(N - 1), m0);
    let e_m01 = c.expected_total();
    if m2_shed_m {
        let (w0, sd) = m2_win_m;
        let q = c.alloc_qubit();
        a2_lt_into(c, &acc2[w0..sp2], &b[w0..sp2], sd.map(|i| b[i]), q);
        cc[0] = q;
    }

    for i in (N - 2 - s1)..=(N - 3) {
        cc[i - sp2] = m_carry(c, acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
    }
    // I7: cq(N - 2), cq(N - 1) and x258 = cq(N); acc2's two top entries are m0 (X1[256]) and m1 (X1[257])
    let cq2 = m_carry(c, tg[N - 1], &l(b[N - 3]), cc[N - 3 - sp2]);
    cc.push(cq2);
    let cq1 = m_carry(c, m0, &l(b[N - 2]), cq2);
    cc.push(cq1);
    let x258 = m_carry(c, m1, &l(b[N - 1]), cq1);
    cc.push(x258);
    // I6: the two lower top wires hold X's bits 256, 257 while fold^-1 reads them
    c.cx(b[N - 2], m0);
    c.cx(cq2, m0);
    c.cx(b[N - 1], m1);
    c.cx(cq1, m1);
    let e_tops = c.expected_total();
    // room, the fold: fin <= 2, then s2 carries cq(N - 1), cq(N - 2), cq(N - 3), ... shed top down (built again after
    // fold^-1, 1 Toffoli each); x258, m0, m1 (its inputs) and m2 stay. cq(N - 1)'s forms: X1[256] = m0 ^ S'2[254] ^ cq2.
    let nbits = mw - 3 - emax;
    // W110 may retire five continued-Q owners inside an emax=7 fold before
    // its final ladder plan. The outer reverse shed must use the same
    // eligibility when deciding whether fin/ripple/m2 have enough capacity;
    // fold_inv_f still checks the actual post-page physical budget.
    let fold_need = a_fixed(emax) - f_own_sheds(emax) + a_min_budget(nbits) - f_page5_room_credit(emax);
    let short_f0 = fold_need.saturating_sub(cells::cap().saturating_sub(c.active_qubits() as usize));
    // fin <= 3 (c2, c1, the AND k1 k2), then the open ripple (s2 <= N - 1 - sp2), then m2 itself (erased by its
    // compare under the outcome, built again by its value compare after fold^-1: about k2x + k2x/2 Toffoli)
    // (fin 3 only once fin 2 + the whole ripple pool is short: the cap-1242 stream stays the measured v3's)
    let pool = N - 1 - sp2;
    let fin = (if short_f0 > 2 + pool { short_f0.min(3) } else { short_f0.min(2) }).max(a_env("LFA2_FFIN").unwrap_or(0));
    let s2 = (short_f0 - short_f0.min(fin)).max(a_env("LFA2_FS2").unwrap_or(0)).min(pool);
    let m2_shed = short_f0 > fin + pool || a_env("LFA2_FM2").is_some_and(|v| v == 1);
    assert!(short_f0 <= fin + pool + usize::from(m2_shed), "a2: the reverse tick t={t} does not fit fold^-1: short {short_f0}, fin 3 + pool {pool} + m2");
    assert!(s2 <= N - 1 - sp2, "a2: the reverse tick t={t} does not fit fold^-1: short {short_f0} (fin {fin}), pool {}", N - 1 - sp2);
    let cq1_forms = (Lin::of(&[m0, b[N - 2]]), Lin::of(&[b[N - 2], cq2]));
    for j in 1..=s2 {
        let i = N - j;
        if i == N - 1 {
            c.cx(cq2, cq1);
            lin_and_erase(c, cq1, &cq1_forms.0, &cq1_forms.1);
        } else if i == N - 2 {
            m_carry_erase(c, cq2, tg[N - 1], &l(b[N - 3]), cc[N - 3 - sp2]);
        } else {
            m_carry_erase(c, cc[i - sp2], acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
        }
    }
    let m2_win = (sp2 - kk2x, seed2x);
    if m2_shed {
        let (w0, sd) = m2_win;
        cells::y15_erase_cmp(c, cc[0], &acc2[w0..sp2], &b[w0..sp2], sd.map(|i| b[i]));
        c.free(cc[0]);
    }
    let a_fold = c.active_qubits();
    // I5
    if std::env::var("W118_FINE_TRACE").ok().as_deref() == Some("1") {
        eprintln!("A2_FOLD_START rev t={t} active={a_fold}");
    }
    let (plan, fold_peak) = c.r3_peak(|c| fold_inv_f(c, &tg[..mw], [m0, m1, x258], s, k[0], k[1], k[2], emax, fin));
    if std::env::var("W118_FINE_TRACE").ok().as_deref() == Some("1") {
        eprintln!("A2_FOLD_END rev t={t} peak={fold_peak} active={}", c.active_qubits());
    }
    if room_trace() { eprintln!("A2_FOLD_PEAK rev t={t} peak={fold_peak} cap={}", cells::cap()); }
    let e_fold = c.expected_total();
    if m2_shed {
        let (w0, sd) = m2_win;
        let q = c.alloc_qubit();
        a2_lt_into(c, &acc2[w0..sp2], &b[w0..sp2], sd.map(|i| b[i]), q);
        cc[0] = q;
    }
    for j in (1..=s2).rev() {
        let i = N - j;
        if i == N - 1 {
            let q = lin_and(c, &cq1_forms.0, &Lin::of(&[b[N - 2], cc[N - 2 - sp2]]));
            c.cx(cc[N - 2 - sp2], q);
            cc[N - 1 - sp2] = q;
        } else if i == N - 2 {
            cc[N - 2 - sp2] = m_carry(c, tg[N - 1], &l(b[N - 3]), cc[N - 3 - sp2]);
        } else {
            cc[i - sp2] = m_carry(c, acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
        }
    }
    let (cq2, cq1) = (cc[N - 2 - sp2], cc[N - 1 - sp2]);
    // The fold and its restore were the final k3 reads. Payload-only k3 is
    // decoded from an external immutable record: move its existing HMR/phase,
    // without a rebuild, ahead of the subtraction scratch frontier.
    if owns_k3 {
        let before_k3 = c.active_qubits();
        super::a2_k3_erase_rec(c, t, k[2]);
        assert_eq!(c.active_qubits() + 1, before_k3, "a2: owned k3 retires exactly one owner");
        eprintln!("W133_OWNED_K3 t={t} before={before_k3} after={}", c.active_qubits());
    }
    // I4
    c.cx(cq1, m1);
    c.cx(b[N - 1], m1);
    c.cx(cq2, m0);
    c.cx(b[N - 2], m0);
    // I3': add 2's top ripple measured away, top down (acc2[N - 2] = m0, acc2[N - 1] = m1)
    let a2at = |i: usize| if i == N - 2 { m0 } else if i == N - 1 { m1 } else { acc2[i] };
    for i in (sp2..N).rev() {
        m_carry_erase(c, cc[i - sp2 + 1], a2at(i), &l(b[i]), cc[i - sp2]);
    }
    let e_ripple = c.expected_total();
    // I3: (m2, tg[2..2 + sp2)) -= S'2[0..sp2)
    let m2 = cc[0];
    let mut acc: Vec<QubitId> = tg[2..2 + sp2].to_vec();
    acc.push(m2);
    a2_sub_top(c, &b[..sp2], &acc, proxy);
    c.release_clean(m2);
    c.cx_all(s[2], b);
    let e_sub2 = c.expected_total();
    // I2: (m1, m0, tg[1..256)) -= S'1
    c.cx_all(s[1], b);
    let mut acc: Vec<QubitId> = tg[1..].to_vec();
    acc.push(m0);
    acc.push(m1);
    a2_sub_top(c, b, &acc, proxy);
    c.release_clean(m1);
    c.cx_all(s[1], b);
    let e_sub1 = c.expected_total();
    // I1: (m0, tg) -= S'0
    c.cx_all(s[0], b);
    let mut acc: Vec<QubitId> = tg.to_vec();
    acc.push(m0);
    a2_sub_top(c, b, &acc, proxy);
    c.release_clean(m0);
    c.cx_all(s[0], b);
    let e_end = c.expected_total();
    assert_eq!(c.active_qubits(), a_start - u32::from(owns_k3), "a2: the reverse A tick violated its k3 ownership return");
    if room_trace() {
        eprintln!(
            "A2_INV t={t} active={a_start} room={} at_fold={a_fold} sp2={sp2} k0x={k0x} kk2x={kk2x} s1={s1} s2={s2} fin={fin} m2shed={} plan={plan:?} m2={:.1} open={:.1} m01={:.1} tops={:.1} fold={:.1} ripple={:.1} sub2={:.1} sub1={:.1} sub0={:.1} body={:.1}",
            cells::cap().saturating_sub(a_start as usize),
            u8::from(m2_shed),
            e_m2 - e_start,
            e_open - e_m2,
            e_m01 - e_open,
            e_tops - e_m01,
            e_fold - e_tops,
            e_ripple - e_fold,
            e_sub2 - e_ripple,
            e_sub1 - e_sub2,
            e_end - e_sub1,
            e_end - e_start
        );
    }
}

// ======================================================================================================================
// M4: the 8-way rail barrel (round14 fold/rail8.py): arithmetic shift right by e = k1 + 2 k2 + 4 k3 of a rail
// t[0..w) (sign S = t[w-1]) holding 2^e * odd. Four controlled reflections (axes 1, 0, -2, -6; controls k1, k1^k2,
// k2^k3, k3 on host letter wires) with stage 3's pairs (w-5, w-1), (w-4, w-2) removed; sign fills S * phi(e)
// (phi in {1, k1, k2, k3}; S k_i one AND each) and constant fills (1, k1, k2, k3: Clifford) at stage boundaries from an
// exact GF(2) solve over every e <= min(7, w - 2); drop0 (forward, LF_LOWREL) replaces the last Fredkin that writes
// wire 0 by CNOTs and a measured wire (main's trick). 2w - 3 Toffoli forward at even w (2w - 4 odd), reverse one more.
// ======================================================================================================================
#[derive(Clone, Debug)]
pub(super) struct Rail8 {
    stages: Vec<(Vec<(usize, usize)>, u8)>,
    /// (boundary b in 0..=4, wire q, fill: 0 = S, 1..3 = S k_i, 4 = const 1, 5..7 = const k_(i-4))
    fills: Vec<(usize, usize, u8)>,
    /// the S k_i products used (bit i-1)
    prods: u8,
    /// the stage and pair of the drop0 Fredkin, if legal
    drop: Option<(usize, (usize, usize))>,
}
fn r8_ctrl(mask: u8, e: usize) -> bool { (mask as usize & e).count_ones() % 2 == 1 }
fn r8_phi(f: u8, e: usize) -> bool {
    match f { 0 | 4 => true, 1 | 5 => e & 1 == 1, 2 | 6 => e & 2 == 2, _ => e & 4 == 4 }
}
/// pos[b][q] = final position of the content at wire q at boundary b, for shift e.
fn r8_positions(w: usize, stages: &[(Vec<(usize, usize)>, u8)], e: usize) -> Vec<Vec<usize>> {
    let ns = stages.len();
    let mut pos = vec![Vec::new(); ns + 1];
    pos[ns] = (0..w).collect();
    for s in (0..ns).rev() {
        let mut p: Vec<usize> = (0..w).collect();
        if r8_ctrl(stages[s].1, e) {
            for &(a, b) in &stages[s].0 {
                p.swap(a, b);
            }
        }
        pos[s] = (0..w).map(|q| pos[s + 1][p[q]]).collect();
    }
    pos
}
fn r8_data_ok(w: usize, stages: &[(Vec<(usize, usize)>, u8)], emax: usize) -> bool {
    (0..=emax).all(|e| {
        let pos = &r8_positions(w, stages, e)[0];
        (e + 1..w - 1).all(|j| pos[j] == j - e)
    })
}
/// GF(2) solve for the fills of kinds `kinds` (sign fills: target = the e sign copies on top, the original sign wire's
/// content removed; constant fills: the lowest set bit's 1 moved to position 0), over wires near either end.
fn r8_solve(w: usize, stages: &[(Vec<(usize, usize)>, u8)], emax: usize, kinds: &[u8], konst: bool, no0_after: Option<usize>) -> Option<Vec<(usize, usize, u8)>> {
    let ns = stages.len();
    // odd widths need fills spread over the register (the k1-only sign fill); even widths stay near the ends
    let nr = a_env("LFA2_R8NEAR").unwrap_or(if true { w } else if w % 2 == 1 { w } else { 24 });
    let near: Vec<usize> = (0..w).filter(|&q| q < nr || q + nr >= w || (q + 12 >= w / 2 && q < w / 2 + 12)).collect();
    let vars: Vec<(usize, usize, u8)> = (0..=ns)
        .flat_map(|b| near.iter().flat_map(move |&q| kinds.iter().map(move |&f| (b, q, f))))
        .filter(|&(b, q, _)| !(q == 0 && no0_after.is_some_and(|s| b > s)))
        .collect();
    let nw = (vars.len() + 64) / 64;
    let tb = vars.len(); // the target bit index
    let mut rows: Vec<Vec<u64>> = Vec::new();
    for e in 0..=emax {
        let pos = r8_positions(w, stages, e);
        let from = if konst { pos[0][e] } else { pos[0][w - 1] };
        for p in 0..w {
            let tgt = if konst { (p == 0) ^ (p == from) } else { (p + 1 + e >= w) ^ (p == from) };
            let mut row = vec![0u64; nw + 1];
            for (i, &(b, q, f)) in vars.iter().enumerate() {
                if pos[b][q] == p && r8_phi(f, e) {
                    row[i / 64] |= 1 << (i % 64);
                }
            }
            if tgt {
                row[tb / 64] |= 1 << (tb % 64);
            }
            if row.iter().any(|&x| x != 0) {
                rows.push(row);
            }
        }
    }
    // Gaussian elimination (pivot = lowest variable bit), then back substitution with the free variables 0
    let mut piv: Vec<Option<Vec<u64>>> = vec![None; tb];
    for mut r in rows {
        loop {
            let lead = (0..nw).find_map(|wi| {
                let m = if wi == tb / 64 { r[wi] & ((1u64 << (tb % 64)) - 1) } else if wi > tb / 64 { 0 } else { r[wi] };
                (m != 0).then(|| wi * 64 + m.trailing_zeros() as usize)
            });
            match lead {
                Some(h) => match &piv[h] {
                    Some(pr) => { for i in 0..r.len() { r[i] ^= pr[i]; } }
                    None => { piv[h] = Some(r); break; }
                },
                None => {
                    if r[tb / 64] >> (tb % 64) & 1 == 1 { return None; }
                    break;
                }
            }
        }
    }
    let mut sol = vec![false; tb];
    for h in (0..tb).rev() {
        if let Some(r) = &piv[h] {
            let mut v = r[tb / 64] >> (tb % 64) & 1 == 1;
            for j in h + 1..tb {
                if sol[j] && r[j / 64] >> (j % 64) & 1 == 1 { v = !v; }
            }
            sol[h] = v;
        }
    }
    Some((0..tb).filter(|&i| sol[i]).map(|i| vars[i]).collect())
}
/// Classical check of a plan on every value of the 2^e-odd promise class at small w, or random values: forward (with
/// drop0's semantics when `drop0`) and reverse. Returns (ok, drop0 legal).
fn r8_check(w: usize, pl: &Rail8, emax: usize, drop0: bool) -> (bool, bool) {
    let mut seed = 0x2545_f491_4f6c_dd1du64 ^ w as u64;
    let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut legal = true;
    for trial in 0..(64 * (emax + 1)) {
        let e = trial % (emax + 1);
        let sv = rnd() & 1 == 1;
        let mut x = vec![false; w];
        x[e] = true;
        for j in e + 1..w - 1 { x[j] = rnd() & 1 == 1; }
        x[w - 1] = sv;
        let want: Vec<bool> = (0..w).map(|p| if p + e < w { x[p + e] } else { sv }).collect();
        let fills_at = |t: &mut Vec<bool>, b: usize| {
            for &(fb, q, f) in &pl.fills {
                if fb == b && r8_phi(f, e) { t[q] ^= if f >= 4 { true } else { sv }; }
            }
        };
        let mut t = x.clone();
        for (si, (pairs, mask)) in pl.stages.iter().enumerate() {
            fills_at(&mut t, si);
            let cv = r8_ctrl(*mask, e);
            for &(a, b) in pairs {
                if drop0 && pl.drop == Some((si, (a, b))) {
                    let pr = if a == 0 { b } else { a };
                    if cv && !t[pr] { legal = false; }
                    if !cv && !t[0] { legal = false; }
                    t[pr] = t[0] ^ t[pr] ^ true;
                    t[0] = true;
                    continue;
                }
                if cv { t.swap(a, b); }
            }
        }
        fills_at(&mut t, pl.stages.len());
        if t != want { return (false, legal); }
        let mut t = want.clone();
        fills_at(&mut t, pl.stages.len());
        for si in (0..pl.stages.len()).rev() {
            let (pairs, mask) = &pl.stages[si];
            if r8_ctrl(*mask, e) {
                for &(a, b) in pairs.iter().rev() { t.swap(a, b); }
            }
            fills_at(&mut t, si);
        }
        if t != x { return (false, legal); }
    }
    (true, legal)
}
/// The 8-way barrel's network for width w (cached).
pub(super) fn rail8_plan(w: usize) -> Rail8 {
    thread_local! { static C: std::cell::RefCell<std::collections::HashMap<usize, Rail8>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    if let Some(p) = C.with(|c| c.borrow().get(&w).cloned()) {
        return p;
    }
    assert!(w >= 3, "a2: an 8-way rail barrel needs 3 wires");
    let emax = 7.min(w - 2);
    let frame_narrow=[6,8].contains(&w)&&std::env::var("RAIL_OPT_NARROW").as_deref()==Ok("1");
    let parked = w>=9||frame_narrow;
    let domain = if parked { w - 1 } else { w };
    let masks: [u8; 4] = [1, 3, 6, 4];
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..domain).filter_map(|i| { let j = (x - i as isize).rem_euclid(domain as isize) as usize; (i < j).then_some((i, j)) }).collect()
    };
    let frame_shift=std::env::var("FRAME_SHIFT").as_deref()==Ok("1") && parked && w%2==0;
    let ax0 = if frame_narrow||frame_shift {[3,2,0,-4]} else if parked && w%2==1 {[2,1,-1,-5]} else {[1,0,-2,-6]};
    let mut cands: Vec<[isize; 4]> = vec![ax0];
    for a in -8..=8 { for b in -8..=8 { for c in -8..=8 { for d in -8..=8 { cands.push([a, b, c, d]); } } } }
    let mut best: Option<Rail8> = None;
    for ax in cands {
        let base: Vec<(Vec<(usize, usize)>, u8)> = ax.iter().zip(masks).map(|(&x, m)| (refl(x), m)).collect();
        if !r8_data_ok(w, &base, emax) { continue; }
        // stage 3 without (w-5, w-1), (w-4, w-2) where that still routes (round14's greedy removal at every width)
        let mut trial = base.clone();
        if (parked || w >= 10) && ax == ax0 {
            if parked { if w % 2 == 0 { if frame_narrow||frame_shift {trial[3].0.retain(|&p|p!=(0,w-5)&&p!=(w-4,w-2));}else{trial[3].0.retain(|&p|p!=(w-5,w-3));} } else { trial[3].0.retain(|&p| p != (w - 4, w - 3) && p != (w - 5, w - 2)); } } else { trial[3].0.retain(|&p| p != (w - 5, w - 1) && p != (w - 4, w - 2)); }
            if !r8_data_ok(w, &trial, emax) { trial = base.clone(); }
        }
        for (st, no0) in [(trial.clone(), true), (trial, false), (base.clone(), true), (base, false)] {
            // the last stage with a pair on wire 0: no fill may touch wire 0 after it if drop0 is to be legal
            let s0 = (0..st.len()).rev().find(|&si| st[si].0.iter().any(|p| p.0 == 0 || p.1 == 0));
            let no0_after = if no0 { s0 } else { None };
            let Some(cf) = r8_solve(w, &st, emax, &[4, 5, 6, 7], true, no0_after) else { continue };
            let subsets: [&[u8]; 8] = [&[0], &[0, 1], &[0, 2], &[0, 3], &[0, 1, 2], &[0, 1, 3], &[0, 2, 3], &[0, 1, 2, 3]];
            for kinds in subsets {
                let Some(sf) = r8_solve(w, &st, emax, kinds, false, no0_after) else { continue };
                let prods = kinds.iter().filter(|&&f| f > 0).fold(0u8, |m, &f| m | 1 << (f - 1));
                let mut fills = sf;
                fills.extend(cf.iter().copied());
                // drop0: the last stage pair that writes wire 0, if no later fill touches wire 0
                let mut drop = None;
                'd: for si in (0..st.len()).rev() {
                    for &pr in st[si].0.iter().rev() {
                        if pr.0 == 0 || pr.1 == 0 { drop = Some((si, pr)); break 'd; }
                    }
                }
                if let Some((si, _)) = drop {
                    if fills.iter().any(|&(b, q, _)| q == 0 && b > si) { drop = None; }
                }
                let mut pl = Rail8 { stages: st.clone(), fills, prods, drop };
                let (ok, legal) = r8_check(w, &pl, emax, pl.drop.is_some());
                let (ok, legal) = if ok && legal { (true, true) } else { (r8_check(w, &pl, emax, false).0, false) };
                if !ok { continue; }
                if !legal { pl.drop = None; }
                let cost = |p: &Rail8| p.stages.iter().map(|s| s.0.len()).sum::<usize>() + p.prods.count_ones() as usize - usize::from(p.drop.is_some());
                if best.as_ref().is_none_or(|b| cost(&pl) < cost(b)) { best = Some(pl); }
                break;
            }
        }
        if best.is_some() { break; }
    }
    let pl = best.unwrap_or_else(|| panic!("a2: no 8-way rail barrel network at w = {w}"));
    C.with(|c| c.borrow_mut().insert(w, pl.clone()));
    pl
}

/// The 8-way rail barrel on `t` (sign t[w-1]; promise: t = 2^e * odd, e = k1 + 2 k2 + 4 k3 <= min(7, w - 2)):
/// forward = arithmetic shift right by e, inverse = shift left. `drop0` (forward only): wire 0 ends as the constant 1
/// and is released inside (returns true; the caller forgets it).

thread_local! { pub(super) static RAIL_OPT_DROP_KEEP: std::cell::Cell<usize> = const {std::cell::Cell::new(usize::MAX)}; }
fn rail_opt_on(k:&str)->bool {std::env::var(k).ok().as_deref()==Some("1")}
// Replace a Fredkin with its known-output instrument. K is the value of d
// after this Fredkin; all subsequent fills into d must be XORed into K.
fn rail_opt_drop_fredkin(c:&mut Builder,h:QubitId,others:&[QubitId],d:QubitId,p:QubitId,known:&Lin){
    assert!(!known.w.contains(&d) && !known.w.contains(&p));
    c.cx(d,p);
    for &o in others.iter().rev(){c.cx(o,h);}
    lin_xor_into(c,known,d);
    for &o in others{c.cx(o,h);}
    let m=c.alloc_bit();c.hmr(d,m);
    if !false{c.cz_if(h,p,m);}
    for &o in others.iter().rev(){c.cx(o,h);}
    lin_xor_into(c,known,d);
    for &o in others{c.cx(o,h);}
    c.free_bit(m);c.cx(d,p);
}

pub(super) fn rail8_barrel(c: &mut Builder, k: [QubitId; 3], t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    let w = t.len();
    let pl = rail8_plan(w);
    let drop0 = drop0 && !inverse && pl.drop.is_some() && !std::env::var("LF_BARREL_DROP0").is_ok_and(|v| v == "0");
    let sg = t[w - 1];
    let scopy = pl.fills.iter().any(|f| f.2 == 0).then(|| {
        let q = c.alloc_qubit();
        c.cx(sg, q);
        q
    });
    let prod: Vec<Option<QubitId>> = (0..3).map(|i| (pl.prods >> i & 1 == 1).then(|| and_new(c, k[i], sg))).collect();
    let fill = |c: &mut Builder, b: usize| {
        for &(fb, q, f) in pl.fills.iter().filter(|x| x.0 == b) {
            let _ = fb;
            match f {
                0 => c.cx(scopy.unwrap(), t[q]),
                1..=3 => c.cx(prod[f as usize - 1].unwrap(), t[q]),
                4 => c.x(t[q]),
                _ => c.cx(k[f as usize - 5], t[q]),
            }
        }
    };
    let mut dropped = false;
    let mut stage = |c: &mut Builder, si: usize| {
        let (pairs, mask) = &pl.stages[si];
        let (h, others) = rot8_host(k, *mask);
        for &o in &others { c.cx(o, h); }
        for &(a, b) in pairs {
            if drop0 && pl.drop == Some((si, (a, b))) {
                let pr = if a == 0 { b } else { a };
                c.cx(t[0], t[pr]);
                c.x(t[pr]);
                c.x(t[0]); // t0 = h & !t[pr]
                let m = c.alloc_bit();
                c.hmr(t[0], m);
                let phase_fault=false&&w>=9&&w%2==0;
                if !phase_fault{c.x(t[pr]);}
                if !([6,8].contains(&w)&&std::env::var("RAIL_OPT_NARROW").as_deref()==Ok("1")&&false){c.cz_if(h,t[pr],m);}
                if !phase_fault{c.x(t[pr]);}
                c.free_bit(m);
                c.release_clean(t[0]);
                dropped = true;
            } else if !inverse && [a,b].iter().any(|&d| d>=RAIL_OPT_DROP_KEEP.with(|x|x.get()) && d<w-1 && !(si+1..pl.stages.len()).any(|j|pl.stages[j].0.iter().any(|p|p.0==d||p.1==d))) {
                let d=if a>=RAIL_OPT_DROP_KEEP.with(|x|x.get()) && a<w-1 {a}else{b};
                let p=if d==a {b}else{a};
                let mut known=l(sg);
                for &(_,q,f) in pl.fills.iter().filter(|x|x.1==d && x.0>si){let _=q;known=known.x(&match f {0=>l(scopy.unwrap()),1..=3=>l(prod[f as usize-1].unwrap()),4=>Lin::k(true),_=>l(k[f as usize-5])});}
                rail_opt_drop_fredkin(c,h,&others,t[d],t[p],&known);
            } else {
                if !(w>=9&&w%2==0&&std::env::var("FRAME_SHIFT").as_deref()==Ok("1")&&false&&si==0&&pairs.first()==Some(&(a,b))){fredkin(c,h,t[a],t[b]);}
            }
        }
        for &o in others.iter().rev() { c.cx(o, h); }
    };
    let ns = pl.stages.len();
    if !inverse {
        for si in 0..ns { fill(c, si); stage(c, si); }
        fill(c, ns);
    } else {
        fill(c, ns);
        for si in (0..ns).rev() { stage(c, si); fill(c, si); }
    }
    for i in (0..3).rev() {
        if let Some(q) = prod[i] { and_erase(c, q, k[i], t[w - 1]); }
    }
    if let Some(q) = scopy {
        c.cx(t[w - 1], q);
        c.release_clean(q);
    }
    dropped
}

#[cfg(test)]
mod a2_rot_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }
    /// Exact check of [`rot8`] (and its inverse) on n wires for every e: values, letters, clean, no phase; Fredkin count.
    fn check_rot8(n: usize, inverse: bool) -> usize {
        let mut c = Builder::new();
        let t = c.alloc_qubits(n);
        let k = c.alloc_qubits(3);
        let e0 = c.expected_total();
        rot8(&mut c, [k[0], k[1], k[2]], &t, inverse);
        let cost = (c.expected_total() - e0).round() as usize;
        let (nq, nbits) = c.i13_dims();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(b"a2-rot8");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ n as u64);
        let mut bad = 0;
        for _batch in 0..4 {
            sim.clear_for_shot();
            let mut inp = vec![vec![false; n]; 64];
            for shot in 0..64 {
                let e = shot % 8;
                for i in 0..n {
                    inp[shot][i] = rng.next() & 1 == 1;
                    if inp[shot][i] {
                        *sim.qubit_mut(t[i]) |= 1 << shot;
                    }
                }
                for i in 0..3 {
                    if e >> i & 1 == 1 {
                        *sim.qubit_mut(k[i]) |= 1 << shot;
                    }
                }
            }
            sim.apply_iter(ops.iter());
            for shot in 0..64 {
                let e = shot % 8;
                let mut ok = (sim.phase >> shot) & 1 == 0;
                for i in 0..n {
                    let src = if inverse { (i + n - e) % n } else { (i + e) % n };
                    ok &= ((sim.qubit(t[i]) >> shot) & 1 == 1) == inp[shot][src];
                }
                for i in 0..3 {
                    ok &= ((sim.qubit(k[i]) >> shot) & 1) as usize == (e >> i & 1);
                }
                bad += usize::from(!ok);
            }
        }
        eprintln!("A2_ROT8_CHECK n={n} inverse={inverse} fredkins={cost} shots=256 bad={bad}");
        assert_eq!(bad, 0, "a2: rot8 is wrong");
        // the permutation helper agrees with the circuit's map
        for e in 0..8 {
            let m = rot8_map(n, e);
            assert!((0..n).all(|i| m[i] == (i + e) % n), "a2: rot8_map");
        }
        cost
    }
    #[test]
    fn a2_rot8_exact() {
        for n in [16usize, 64, 256, 258] {
            let f = check_rot8(n, false);
            let r = check_rot8(n, true);
            assert_eq!(f, r);
            if n == 256 {
                assert_eq!(f, 508, "a2: the parity split has 508 Fredkins on 256 wires");
            }
        }
    }
}

#[cfg(test)]
mod a2_tick_tests {
    use super::*;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn u256(&mut self) -> U256 {
            let mut v = U256::ZERO;
            for i in 0..4 {
                v |= U256::from(self.next()) << (64 * i);
            }
            v
        }
    }
    fn p() -> U256 { super::super::super::SECP256K1_P }
    /// The forward A tick's exact integer map (fold-core's f_expect on the window, X's bits above it): Some(R), or None
    /// where a carry would leave the fold window (a window failure, not modelled).
    pub(super) fn model_fwd(tv: U256, sv: U256, s: [bool; 3], e: usize, mw: usize) -> Option<U256> {
        let sp = |b: bool| if b { U256::MAX - sv } else { sv };
        let (mut lo, mut top) = (tv, 0u64);
        for (i, &si) in s.iter().enumerate() {
            let v = sp(si);
            let (a, cy) = lo.overflowing_add(v << i);
            lo = a;
            top += u64::from(cy) + if i > 0 { (v >> (256 - i)).to::<u64>() } else { 0 };
        }
        let ev = top as i128;
        let nmv = (s[0] as i128) + 2 * (s[1] as i128) + 4 * (s[2] as i128);
        let kk = 3 + e;
        let f1: i128 = (1i128 << 32) + 976;
        let lw = (lo & ((U256::from(1u8) << mw) - U256::from(1u8))).to::<u128>() as i128;
        let base = lw + ev - (nmv - ev) * f1;
        let mk = 1i128 << kk;
        let mut finv: i128 = 1;
        for _ in 0..6 {
            finv = (finv * (2 - (f1 + 1) * finv)).rem_euclid(1i128 << 20);
        }
        let m = (base.rem_euclid(mk) * finv.rem_euclid(mk)).rem_euclid(mk);
        let wtrue = base - m * f1;
        if wtrue < 0 || wtrue >= (1i128 << mw) {
            return None;
        }
        let w = ((lo >> mw) << mw) | U256::from(wtrue as u128);
        assert_eq!((w & U256::from((1u64 << kk) - 1)).to::<u64>() as i128, m);
        Some((w >> kk) | (w << (256 - kk)))
    }
    /// (T + sum (-1)^s_i 2^i S) 2^-(3 + e) mod p.
    fn model_modp(tv: U256, sv: U256, s: [bool; 3], e: usize) -> U256 {
        let mut x = tv % p();
        for (i, &si) in s.iter().enumerate() {
            let term = (sv % p()).mul_mod(U256::from(1u64 << i), p());
            x = if si { x.add_mod(p() - term, p()) } else { x.add_mod(term, p()) };
        }
        let inv2k = U256::from(1u64 << (3 + e)).pow_mod(p() - U256::from(2u8), p());
        x.mul_mod(inv2k, p())
    }
    fn setup_env() {
        super::super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        super::super::install_recipe();
        std::env::set_var("LFF_IPK", "1");
    }
    /// One A tick (fwd: [`a2_fwd_tick`]; rev: [`a2_rev_tick`]; both: forward then reverse) at tick t with `room` wires
    /// over the tick's live set, on random (T, S, s, e <= emax): values against the exact model (and mod p), source and
    /// letters unchanged, ancillas clean, no phase. Returns (expected Toffoli, bad shots).
    fn check_tick(dir: &str, t: usize, emax: usize, room: usize, batches: usize, seed: u64) -> (f64, usize) {
        setup_env();
        let mut c = Builder::new();
        let pr = [c.alloc_qubits(N), c.alloc_qubits(N)];
        let lt = c.alloc_qubits(6);
        let (s, k) = ([lt[0], lt[1], lt[2]], [lt[3], lt[4], lt[5]]);
        let base = c.active_qubits() as usize;
        let cap = base + room;
        let mut pay = pr.clone();
        let (ti, si) = (t % 2, 1 - t % 2);
        let e0 = c.expected_total();
        super::super::super::pingpong::with_phase_cap(Some(cap), || {
            if dir != "rev" {
                a2_fwd_tick(&mut c, t, s, k, emax, &mut pay);
            }
            if dir != "fwd" {
                a2_rev_tick(&mut c, t, s, k, emax, &mut pay);
            }
        });
        let cost = c.expected_total() - e0;
        let peak = c.peak_total() as usize;
        let (nq, nbits) = c.i13_dims();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(b"a2-tick");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let mw_f = fold_window(t, false);
        let mut rng = Rng(seed);
        let (mut bad, mut skipped) = (0usize, 0usize);
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut ins = Vec::new();
            for shot in 0..64 {
                let (tv, sv) = (rng.u256() % p(), rng.u256() % p());
                let sb = [rng.next() & 1 == 1, rng.next() & 1 == 1, rng.next() & 1 == 1];
                let e = (rng.next() % (emax as u64 + 1)) as usize;
                let rv = model_fwd(tv, sv, sb, e, mw_f);
                let inp = if dir == "rev" { rv.unwrap_or(U256::ZERO) } else { tv };
                for i in 0..N {
                    if inp.bit(i) {
                        *sim.qubit_mut(pr[ti][i]) |= 1 << shot;
                    }
                    if sv.bit(i) {
                        *sim.qubit_mut(pr[si][i]) |= 1 << shot;
                    }
                }
                for i in 0..3 {
                    if sb[i] {
                        *sim.qubit_mut(s[i]) |= 1 << shot;
                    }
                    if e >> i & 1 == 1 {
                        *sim.qubit_mut(k[i]) |= 1 << shot;
                    }
                }
                ins.push((tv, sv, sb, e, rv));
            }
            sim.apply_iter(ops.iter());
            for (shot, &(tv, sv, sb, e, rv)) in ins.iter().enumerate() {
                let Some(rv) = rv else { skipped += 1; continue };
                if dir == "fwd" {
                    assert_eq!(rv % p(), model_modp(tv, sv, sb, e), "a2: the model disagrees with the tick's semantics");
                }
                let want = if dir == "fwd" { rv } else { tv };
                let (mut gt, mut gs) = (U256::ZERO, U256::ZERO);
                for i in 0..N {
                    if (sim.qubit(pr[ti][i]) >> shot) & 1 == 1 { gt |= U256::from(1u8) << i; }
                    if (sim.qubit(pr[si][i]) >> shot) & 1 == 1 { gs |= U256::from(1u8) << i; }
                }
                let mut ok = gt == want && gs == sv && (sim.phase >> shot) & 1 == 0;
                for i in 0..3 {
                    ok &= ((sim.qubit(s[i]) >> shot) & 1 == 1) == sb[i];
                    ok &= ((sim.qubit(k[i]) >> shot) & 1) as usize == (e >> i & 1);
                }
                let dirty: Vec<usize> = (base..nq).filter(|&q| (sim.qubits[q] >> shot) & 1 != 0).collect();
                ok &= dirty.is_empty();
                if !ok {
                    if bad < 4 {
                        eprintln!("A2 BAD {dir} t={t} e={e} s={sb:?} value_ok={} src_ok={} phase={} dirty={:?}", gt == want, gs == sv, (sim.phase >> shot) & 1, &dirty[..dirty.len().min(8)]);
                    }
                    bad += 1;
                }
            }
        }
        eprintln!("A2_TICK_CHECK {dir} t={t} emax={emax} room={room} expected_T={cost:.1} peak_over_base={} shots={} skipped={skipped} bad={bad}", peak - base, batches * 64);
        (cost, bad)
    }
    #[test]
    fn a2_tick_one() {
        let v = std::env::var("LFA2_T").unwrap_or_else(|_| "fwd,50,7,200,4".into());
        let f: Vec<&str> = v.split(',').collect();
        let (dir, t, emax, room, nb) = (f[0], f[1].parse().unwrap(), f[2].parse().unwrap(), f[3].parse().unwrap(), f[4].parse().unwrap());
        let (_, bad) = check_tick(dir, t, emax, room, nb, 0x1234_5678_9abc_def1);
        assert_eq!(bad, 0);
    }
}

#[cfg(test)]
mod a2_rail8_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    /// [`rail8_barrel`] on width w: forward (with drop0: wire 0 released, the constant 1) and inverse on random
    /// 2^e * odd rails, every e <= min(7, w - 2); values, letters, clean, no phase. Returns (fwd T, rev T).
    fn check_rail8(w: usize, drop0: bool) -> (usize, usize) {
        let mut out = (0, 0);
        for inverse in [false, true] {
            let mut c = Builder::new();
            let t = c.alloc_qubits(w);
            let k = c.alloc_qubits(3);
            let e0 = c.expected_total();
            let dropped = rail8_barrel(&mut c, [k[0], k[1], k[2]], &t, inverse, drop0);
            let cost = (c.expected_total() - e0).round() as usize;
            if inverse { out.1 = cost } else { out.0 = cost }
            let (nq, nbits) = c.i13_dims();
            let ops = c.take_ops();
            let mut h = sha3::Shake256::default();
            h.update(b"a2-rail8");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
            let emax = 7.min(w - 2);
            let mut seed = 0x9e37_79b9_7f4a_7c15u64 ^ w as u64;
            let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
            let mut bad = 0;
            for _ in 0..8 {
                sim.clear_for_shot();
                let mut ins = Vec::new();
                for shot in 0..64 {
                    let e = shot % (emax + 1);
                    let sv = rnd() & 1 == 1;
                    let mut x = vec![false; w];
                    x[e] = true;
                    for j in e + 1..w - 1 { x[j] = rnd() & 1 == 1; }
                    x[w - 1] = sv;
                    let y: Vec<bool> = (0..w).map(|p| if p + e < w { x[p + e] } else { sv }).collect();
                    let inp = if inverse { y.clone() } else { x.clone() };
                    for i in 0..w { if inp[i] { *sim.qubit_mut(t[i]) |= 1 << shot; } }
                    for i in 0..3 { if e >> i & 1 == 1 { *sim.qubit_mut(k[i]) |= 1 << shot; } }
                    ins.push((e, if inverse { x } else { y }));
                }
                sim.apply_iter(ops.iter());
                for (shot, (e, want)) in ins.iter().enumerate() {
                    let mut ok = (sim.phase >> shot) & 1 == 0;
                    for i in 0..w {
                        if dropped && i == 0 { continue; }
                        ok &= ((sim.qubit(t[i]) >> shot) & 1 == 1) == want[i];
                    }
                    for i in 0..3 { ok &= ((sim.qubit(k[i]) >> shot) & 1) as usize == (e >> i & 1); }
                    let lo = w + 3;
                    ok &= (lo..nq).all(|q| (sim.qubits[q] >> shot) & 1 == 0);
                    if dropped { ok &= (sim.qubits[t[0].0 as usize] >> shot) & 1 == 0; }
                    bad += usize::from(!ok);
                }
            }
            eprintln!("A2_RAIL8_CHECK w={w} inverse={inverse} drop0={dropped} T={cost} bad={bad}");
            assert_eq!(bad, 0, "a2: the 8-way rail barrel is wrong at w = {w}");
        }
        out
    }
    #[test]
    fn a2_rail8_exact() {
        let mut ws: Vec<usize> = (3..=40).collect();
        ws.extend([41, 43, 51, 63, 64, 65, 101, 128, 255, 256, 257, 258]);
        if let Ok(v) = std::env::var("LFA2_R8W") { ws = v.split(',').map(|x| x.parse().unwrap()).collect(); }
        for w in ws {
            let (f, r) = check_rail8(w, true);
            let pl = rail8_plan(w);
            if std::env::var("LFA2_R8FILLS").is_ok() { eprintln!("A2_FILLS w={w} {:?}", pl.fills); }
            eprintln!("A2_RAIL8 w={w} fwd={f} rev={r} 2w={} swaps={} prods={:03b} drop={:?} nfills={}", 2 * w, pl.stages.iter().map(|s| s.0.len()).sum::<usize>(), pl.prods, pl.drop, pl.fills.len());
        }
    }
}
include!("y15_a2r1.rs");

fn compare_window_knob(name:&str,rev:bool,t:usize,kind:usize,default:usize)->usize {
 let spec=match name {"EXT"=>EXT_WINDOWS,"FOLD"=>"",_=>unreachable!()};let mut out=default;
 for row in spec.split(',').filter(|s|!s.is_empty()) {
  let a:Vec<&str>=row.split(':').collect();assert_eq!(a.len(),4);
  if (a[0]=="*"||a[0]==if rev{"R"}else{"F"})&&(a[1]=="*"||a[1].parse::<usize>().unwrap()==t)&&(a[2]=="*"||a[2].parse::<usize>().unwrap()==kind){out=a[3].parse().unwrap();}
 }assert!(out<=128);out
}
const EXT_WINDOWS:&str="R:120:0:0,R:119:0:0,R:118:0:0,R:117:0:0,R:116:0:0,R:115:0:0,R:114:0:0,R:113:0:0,R:68:0:0,R:67:0:0,R:66:0:0,R:65:0:0,R:64:0:0,R:63:0:0,R:62:0:0,R:61:0:0,R:60:0:0,R:59:0:0,R:58:0:0,R:57:0:0,R:56:0:0,R:55:0:0,R:54:0:0,R:53:0:0,R:52:0:0,R:51:0:0,R:50:0:0,R:49:0:0,R:48:0:0,R:47:0:0,R:46:0:0,R:45:0:0,R:44:0:0,R:43:0:0,R:42:0:0,R:41:0:0,R:40:0:0,R:39:0:0,R:38:0:0,R:37:0:0,R:36:0:0,R:35:0:0,R:34:0:0,R:33:0:0,R:32:0:0,R:31:0:0,R:30:0:0,R:29:0:0,R:28:0:0,R:27:0:0,R:26:0:0,R:25:0:0,R:24:0:0,R:23:0:0,R:22:0:0,R:21:0:0,R:20:0:0,R:19:0:0,R:18:0:0,R:17:0:0,R:16:0:0,R:15:0:0,R:14:0:0,R:13:0:0,R:12:0:0,R:11:0:0,R:10:0:0,R:9:0:0,R:8:0:0,R:7:0:0,R:6:0:0,R:5:0:0,R:4:0:0,R:3:0:0,R:2:0:0,R:1:0:0,R:105:0:0,R:104:0:0,R:103:0:0,R:102:0:0,R:101:0:0,R:100:0:0,R:99:0:0,R:98:0:0,R:97:0:0,R:96:0:0,R:95:0:0,R:94:0:0,R:93:0:0,R:92:0:0,R:91:0:0,R:90:0:0,R:89:0:0,R:88:0:0,R:87:0:0,R:86:0:0,R:85:0:0,R:84:0:0,R:83:0:0,R:82:0:0,R:81:0:0,R:80:0:0,R:79:0:0,R:78:0:0,R:77:0:0,R:76:0:0,R:75:0:0,R:74:0:0,R:73:0:0,R:72:0:0,R:71:0:0,R:70:0:0,R:69:0:0,R:120:2:1,R:119:2:1,R:118:2:1,R:117:2:1,R:116:2:1,R:115:2:1,R:114:2:1,R:113:2:1,R:68:2:0,R:67:2:0,R:66:2:0,R:65:2:0,R:64:2:0,R:63:2:0,R:62:2:0,R:61:2:0,R:60:2:0,R:59:2:0,R:58:2:0,R:57:2:0,R:56:2:0,R:55:2:0,R:54:2:0,R:53:2:0,R:52:2:0,R:51:2:0,R:50:2:0,R:49:2:0,R:48:2:0,R:47:2:0,R:46:2:0,R:45:2:0,R:44:2:0,R:43:2:0,R:42:2:0,R:41:2:0,R:40:2:0,R:39:2:0,R:38:2:0,R:37:2:0,R:36:2:0,R:35:2:0,R:34:2:0,R:33:2:0,R:32:2:0,R:31:2:0,R:30:2:0,R:29:2:0,R:28:2:0,R:27:2:0,R:26:2:0,R:25:2:0,R:24:2:0,R:23:2:0,R:22:2:0,R:21:2:0,R:20:2:0,R:19:2:0,R:18:2:0,R:17:2:0,R:16:2:0,R:15:2:0,R:14:2:0,R:13:2:0,R:12:2:0,R:11:2:0,R:10:2:0,R:9:2:0,R:8:2:0,R:7:2:0,R:6:2:0,R:5:2:0,R:4:2:0,R:3:2:0,R:2:2:0,R:1:2:0,R:105:2:0,R:104:2:0,R:103:2:0,R:102:2:0,R:101:2:0,R:100:2:0,R:99:2:0,R:98:2:0,R:97:2:0,R:96:2:0,R:95:2:0,R:94:2:0,R:93:2:0,R:92:2:0,R:91:2:0,R:90:2:0,R:89:2:0,R:88:2:0,R:87:2:0,R:86:2:0,R:85:2:0,R:84:2:0,R:83:2:0,R:82:2:0,R:81:2:0,R:80:2:0,R:79:2:0,R:78:2:0,R:77:2:0,R:76:2:0,R:75:2:0,R:74:2:0,R:73:2:0,R:72:2:0,R:71:2:0,R:70:2:0,R:69:2:0";

