// ======================================================================================================================
// R135 w2asym: the native reverse A tick (multiply walk). Rotate up by 3 + e, the same three adds as the forward tick
// with the letters flipped (their carries for free, the held carries erased by measurement as the forward erases them),
// and a reverse fold for the A digit (K = 3 + e <= 8): T = low(X_r) + E + n (f - 1), n = E - Nm + m, m = W mod 2^K.
// Arithmetic checked exhaustively in round135-last800/w2asym/tools/foldrev_a_model.py (32,256 cases, 0 bad).
// ======================================================================================================================
thread_local! {
    /// Some(k3) while a native reverse A tick's body runs (the adds keep their low carries [7, 6, 5], the fold is fold_rev_a)
    static W2_NATIVE: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
/// Multiply reverse A ticks in [W2_NAT_FROM, W2_NAT_TO) run the native tick; the rest keep the A2 inverse.
const W2_NAT_FROM: usize = 41;
const W2_NAT_TO: usize = 62;
/// The adds' kept low carries on a native reverse A tick (add 0 into positions 1..=7, add 1 1..=6, add 2 1..=5).
const W2_KEEP: [usize; 3] = [7, 6, 5];
pub(super) fn w2_native_on(t: usize) -> bool { (W2_NAT_FROM..W2_NAT_TO).contains(&t) }

fn w2_native_a_rev_tick(c: &mut Builder, t: usize, s: [QubitId; 3], k: [QubitId; 3], emax: usize, p: &mut [Vec<QubitId>; 2], owns_k3: bool) {
    assert!(emax <= 5, "w2: the native reverse A tick needs emax <= 5 (k3 = 1 only with k2 = 0)");
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (_, proxy) = proxy_fold(w, true);
    let (tg, b) = (p[ti].clone(), p[si].clone());
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    pay_rot(c, k, &tg, true);
    for _ in 0..3 {
        rot1(c, &tg, false);
    }
    for q in s {
        c.x(q);
    }
    W2_NATIVE.with(|x| x.set(Some(k[2])));
    let shift = cmp_shift_at(t);
    cells::with_tie(None, || cells::with_cmp_shift((shift.0 + Y15_CMP_EXTRA, shift.1), || cells::with_bridge(proxy, true, || body_capped(c, t, s, k[0], k[1], &b, &tg, proxy, true))));
    W2_NATIVE.with(|x| x.set(None));
    for q in s {
        c.x(q);
    }
    if owns_k3 {
        if super::a2_code() {
            super::a2_code_read_erase(c, t, k[2], k[1]);
        } else {
            super::a2_k3_erase_rec(c, t, k[2]);
        }
    }
    if room_trace() {
        eprintln!("W2_NAT_TICK rev t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
}

/// Forms of W's bits 0..=top, W = low(X_r) - 4 S'2 - 2 S'1 - S'0 (three borrow chains on acc; ANDs onto `recs`).
fn w2_wbits(c: &mut Builder, recs: &mut Vec<Rec>, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], top: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let mut w: Vec<Lin> = (0..=top).map(|i| l(acc[i])).collect();
    for sh in [2usize, 1, 0] {
        if sh > top {
            continue;
        }
        let mut bo: Option<Lin> = None;
        let mut nw = w.clone();
        for i in sh..=top {
            let a = sb(i - sh, sh);
            match bo.clone() {
                None => {
                    nw[i] = w[i].x(&a);
                    if i < top {
                        bo = Some(r_and(c, recs, w[i].x(&one), a));
                    }
                }
                Some(bb) => {
                    nw[i] = w[i].x(&a).x(&bb);
                    if i < top {
                        bo = Some(r_maj(c, recs, w[i].x(&one), a, bb));
                    }
                }
            }
        }
        w = nw;
    }
    w
}

/// [`w2_wbits`] with every borrow taken from the adds' kept carries (no AND; [`borrow_first`] / [`borrow_next`] record
/// their measured erase): the records of borrows into bits <= `split` go to `ra`, the rest to `rb`.
#[allow(clippy::too_many_arguments)]
fn w2_wbits_kept(c: &mut Builder, ra: &mut Vec<Rec>, rb: &mut Vec<Rec>, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], kept: &[Vec<QubitId>; 3], top: usize, split: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let mut w: Vec<Lin> = (0..=top).map(|i| l(acc[i])).collect();
    for sh in [2usize, 1, 0] {
        let mut bo: Option<Lin> = None;
        let mut nw = w.clone();
        for i in sh..=top {
            let a = sb(i - sh, sh);
            match bo.clone() {
                None => {
                    nw[i] = w[i].x(&a);
                    if i < top {
                        assert!(kept[sh].len() > i - sh, "w2: kept carry missing (chain {sh}, bit {i})");
                        let recs = if i + 1 <= split { &mut *ra } else { &mut *rb };
                        bo = Some(borrow_first(c, recs, kept, sh, i, w[i].x(&one), a));
                    }
                }
                Some(bb) => {
                    nw[i] = w[i].x(&a).x(&bb);
                    if i < top {
                        assert!(kept[sh].len() > i - sh, "w2: kept carry missing (chain {sh}, bit {i})");
                        let recs = if i + 1 <= split { &mut *ra } else { &mut *rb };
                        bo = Some(borrow_next(c, recs, kept, sh, i, w[i].x(&one), a, bb));
                    }
                }
            }
        }
        w = nw;
    }
    w
}

/// Clear the copies of W's bits 4..=top (wc[i - 4] holds bit i) by measurement, top bit first (as [`clear_copies`]).
fn w2_clear_copies(c: &mut Builder, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], wc: &[QubitId], top: usize) {
    let m = c.alloc_bit();
    c.hmr(wc[top - 4], m);
    c.push_condition(m);
    {
        let mut r2: Vec<Rec> = Vec::new();
        let w = w2_wbits(c, &mut r2, acc, src, nm, top);
        lin_cz(c, &Lin::k(true), &w[top]);
        for i in 4..top {
            lin_xor_into(c, &w[i], wc[i - 4]);
        }
        pop_chain(c, &mut r2);
    }
    c.pop_condition();
    if top > 4 {
        let not_m = c.alloc_bit();
        c.bit_store1(not_m);
        c.bit_xor_into(not_m, m);
        c.push_condition(not_m);
        w2_clear_copies(c, acc, src, nm, wc, top - 1);
        c.pop_condition();
        c.free_bit(not_m);
    }
    c.free_bit(m);
}

/// The native reverse fold of an A tick. acc = bits [0, mw) of low(X_r); e = E (three top wires); nm = the flipped
/// letters; src = the source's low 8 bits (not complemented); wc = copies of W's bits 4..7. Low section [0, 8): E on
/// bits 0..2, Q0..Q3 = n0, n1, n2 ^ n0, n3 ^ n1 ^ d3 on bits 4..7; ladder on [8, mw). W's bits 0..3 come from borrow
/// chains on acc[0..4) (held to the low section's undo), bits 4..7 from the copies (cleared after the ladder while
/// acc[0..8) still holds low(X_r)). Fields of (f - 1) n for n in [-7, 262]: Q = n - 4n, J = Q >> 6, U = n + J,
/// s = n9, H = n - s.
#[allow(clippy::too_many_arguments)]
fn fold_rev_a(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, k3: QubitId, src: &[QubitId], kept: &[Vec<QubitId>; 3]) -> Vec<usize> {
    let mw = acc.len();
    assert!(src.len() >= 8 && mw >= 48, "w2: fold_rev_a inputs");
    let one = Lin::k(true);
    let nn = |i: usize| l(nm[i]).x(&one);
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    // held to the low section's undo
    let mut ra: Vec<Rec> = Vec::new();
    // above the low section: the borrows into bits 4..7, the gate wires of W's bits 4..7, the rest of n, the fields
    let mut rb: Vec<Rec> = Vec::new();
    let w = w2_wbits_kept(c, &mut ra, &mut rb, acc, src, nm, kept, 7, 3);
    // the gates [K > j]: e = k1 + 2 k2 + 4 k3 <= 5, so k2 k3 = 0
    let tt = r_and(c, &mut ra, l(k1), l(k2));
    let t13 = r_and(c, &mut ra, l(k1), l(k3));
    let g3 = Lin::of(&[k1, k2, k3]).x(&tt).x(&t13);
    let y3 = r_and(c, &mut ra, g3, w[3].clone());
    let sg: Vec<Lin> = (0..3).map(|i| l(e[i]).x(&nn(i)).x(&w[i])).collect();
    let kp1 = r_maj(c, &mut ra, l(e[0]), nn(0), w[0].clone());
    let kp2 = r_maj(c, &mut ra, l(e[1]), nn(1), w[1].clone());
    let kp3 = r_maj(c, &mut ra, l(e[2]), nn(2), w[2].clone());
    let n0 = sg[0].x(&one);
    let n1 = sg[1].x(&kp1).x(&sg[0]);
    let mut r = r_maj(c, &mut ra, sg[1].clone(), kp1.clone(), sg[0].clone());
    let n2 = sg[2].x(&kp2).x(&r);
    r = r_maj(c, &mut ra, sg[2].clone(), kp2.clone(), r);
    let n3 = y3.x(&one).x(&kp3).x(&r);
    let d3 = r_and(c, &mut ra, n2.x(&one), n0.clone());
    let q2 = n2.x(&n0);
    let q3 = n3.x(&n1).x(&d3);
    let c5 = maj_wire(c, &l(acc[4]), &n0, &l(c4));
    let c6 = maj_wire(c, &l(acc[5]), &n1, &l(c5));
    let c7 = maj_wire(c, &l(acc[6]), &q2, &l(c6));
    let c8 = maj_wire(c, &l(acc[7]), &q3, &l(c7));
    let y4 = r_and(c, &mut rb, Lin::of(&[k2, k3]), w[4].clone());
    let y5 = r_and(c, &mut rb, tt.x(&l(k3)), w[5].clone());
    let y6 = r_and(c, &mut rb, l(k3), w[6].clone());
    let y7 = r_and(c, &mut rb, t13.clone(), w[7].clone());
    let ys = [y3.clone(), y4, y5, y6, y7];
    let mut n = vec![n0.clone(), n1.clone(), n2.clone(), n3.clone()];
    r = r_maj(c, &mut rb, ys[0].x(&one), kp3.clone(), r);
    for j in 4..8 {
        n.push(ys[j - 3].x(&one).x(&ys[j - 4]).x(&r));
        r = r_maj(c, &mut rb, ys[j - 3].x(&one), ys[j - 4].clone(), r);
    }
    n.push(ys[4].x(&r).x(&one));
    let n9 = r_and(c, &mut rb, ys[4].x(&one), r.x(&one));
    n.push(n9);
    let nb = |i: usize| if i < 10 { n[i].clone() } else { n[9].clone() };
    let mut q = vec![nb(0), nb(1), q2.clone(), q3.clone()];
    let mut dd = r_maj(c, &mut rb, nb(3).x(&one), nb(1), d3.clone());
    for i in 4..11 {
        q.push(nb(i).x(&nb(i - 2)).x(&dd));
        if i < 10 {
            dd = r_maj(c, &mut rb, nb(i).x(&one), nb(i - 2), dd);
        }
    }
    let jb = |i: usize| if i < 5 { q[6 + i].clone() } else { q[10].clone() };
    let mut u = vec![nb(0).x(&jb(0))];
    let mut ec = r_and(c, &mut rb, nb(0), jb(0));
    for i in 1..9 {
        u.push(nb(i).x(&jb(i)).x(&ec));
        if i < 8 {
            ec = r_maj(c, &mut rb, nb(i), jb(i), ec);
        }
    }
    let s = nb(9);
    let mut h = vec![nb(0).x(&s)];
    let mut z = r_and(c, &mut rb, nb(0).x(&one), s.clone());
    h.push(nb(1).x(&z));
    z = r_and(c, &mut rb, nb(1).x(&one), z);
    h.push(nb(2).x(&z));
    for i in 3..9 {
        h.push(nb(i));
    }
    let add: Vec<Lin> = (0..mw)
        .map(|bb| match bb {
            0..=3 => Lin::k(false),
            4..=9 => q[bb - 4].clone(),
            10..=18 => u[bb - 10].clone(),
            19..=31 => s.clone(),
            32..=40 => h[bb - 32].clone(),
            _ => s.clone(),
        })
        .collect();
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let (plan, _) = fold_plan_0(c, mw - 2, "w2 native reverse", budget, false);
    ladder_d(c, acc, &add, 8, c8, &plan, &[]);
    // acc[0..8) still holds low(X_r): the gate wires, the fields and the kept carries into bits 4..7 leave
    pop_chain(c, &mut rb);
    // the low section, top down: bits 7..4 (their forms read ra), then ra, then bits 3..0
    maj_wire_erase(c, c8, &l(acc[7]), &q3, &l(c7));
    lin_xor_into(c, &q3, acc[7]);
    c.cx(c7, acc[7]);
    maj_wire_erase(c, c7, &l(acc[6]), &q2, &l(c6));
    lin_xor_into(c, &q2, acc[6]);
    c.cx(c6, acc[6]);
    maj_wire_erase(c, c6, &l(acc[5]), &n1, &l(c5));
    lin_xor_into(c, &n1, acc[5]);
    c.cx(c5, acc[5]);
    maj_wire_erase(c, c5, &l(acc[4]), &n0, &l(c4));
    lin_xor_into(c, &n0, acc[4]);
    c.cx(c4, acc[4]);
    pop_chain(c, &mut ra);
    fold_undo_low(c, acc, e, [c1, c2, c3, c4]);
    plan
}
