// q631 / i4e copy of i4dwalkplan.rs (i4d: block labels, the two real = 0 fixes; i4e: guard options of plan_relay, plan_revrelay)
// ---------------------------------------------------------------- plan 1: nasqret's graded relay over D2Canonical (inner walk)
// (included by walkgen.rs)
fn set_port(ports: &mut Vec<Option<i32>>, i: usize, v: i32) {
    while ports.len() <= i {
        ports.push(None);
    }
    ports[i] = Some(v);
}
/// norm() of the relay plan: the hosting table is updated between the base rotation and the per-bit blocks
fn norm_relay(p: &mut Pl, tg: &[i32], w: &Wr, controls: &Wr, base: usize, dual: bool, kind: usize) {
    if base > 0 {
        let (w, c) = (w.clone(), controls.clone());
        p.one(Box::new(move |g| g.rot(&c, &w, base as i64)));
    }
    for j in 2..=kind {
        set_port(&mut p.ports, j - 1, w[j]);
    }
    for j in (0..tg.len()).rev() {
        let s = 1usize << j;
        if s >= w.len() {
            continue;
        }
        let (w, c, t) = (w.clone(), controls.clone(), tg[j]);
        p.one(Box::new(move |g| {
            g.zer(&c, &w[w.len() - s..], t);
            if dual {
                g.rot(&cat1(&c, t), &w[base..], s as i64)
            } else {
                g.rot(&cat1(&c, t), &w, s as i64)
            }
        }));
    }
}
fn eq_tag(g: &mut W, c: &[i32], i: usize, base: usize, hi: usize) {
    if i >= base && i <= hi {
        let tst = g.tst;
        g.multag(c, i - base, &[], tst);
    }
}

/// returns the blocks of the rows (the three preludes, the closing X(sign) and the class tail are not part of the inner walk)
fn plan_relay(w: &W, real: usize, guard: u8) -> Vec<Block> {
    // i4e guard options (0 = nasqret's relay as in walkplan.rs): 1 = reduced select (tst = [r != 0]), 2 = r != 0 guard on the
    // end-of-sector fire uncompute, 4 = pre-block tst uncompute controlled by fire (the SectorReduced forms of these blocks)
    let (red, nong, fl) = (guard & 1 != 0, guard & 2 != 0, guard & 4 != 0);
    let full = w.tag.clone();
    let n = w.n;
    let (l, r_all) = (w.l.clone(), w.r.clone());
    let (tst, fire, sign, cin) = (w.tst, w.fire, w.sign, w.cin);
    let c: Wr = Rc::new(vec![fire]);
    let roles: V = full[real..full.len() - 1].iter().rev().cloned().collect();
    let mut p = Pl::new(true);
    p.tagv = full.clone();
    let dirty_qa = real == 0;
    for k in 0..n {
        let (t, m) = (k + 1, n - k);
        let a: Wr = rc(&l[..m]);
        let r: Wr = rc(&r_all[..m]);
        let u: Wr = Rc::new(co(&l, n, t));
        let v: Wr = Rc::new(co(&r_all, n, t));
        p.top = Some(r_all[m]);
        p.sector_none = true;
        p.ports = Vec::new();
        p.tagv = full.clone();
        if k > 0 && k < n - 1 {
            let cp: Wr = Rc::new(vec![tst]);
            {
                let (a, r) = (a.clone(), r.clone());
                p.lab = lab(1, k, 0, 0, 0, 0);
                p.one(Box::new(move |g| select(g, &a, &r, fire, &[], red)));
            }
            {
                p.lab = lab(2, k, 0, 0, 0, 0);
                let (a, r, u, v) = (a.clone(), r.clone(), u.clone(), v.clone());
                p.one(Box::new(move |g| {
                    let qa = g.tag[0];
                    let qcond = |g: &mut W| {
                        g.op(&[r[m - 1]], qa);
                        g.x(r[m - 1]);
                        g.lt(&[r[m - 1]], &r[..m - 1], &a[1..], qa);
                        g.x(r[m - 1]);
                    };
                    let consumer = |g: &mut W| {
                        g.op(&[fire, qa], tst);
                        g.xs(&u);
                        g.lt(&[fire, qa], &v, &u, tst);
                        g.xs(&u);
                    };
                    qcond(g);
                    consumer(g);
                    g.reverse(|g| qcond(g));
                    // i4d fix 1: with real = 0 the run driver hosts qa (= full[0], a relay role) on the last loan d, a DIRTY lane:
                    // the consumer above toggles tst by fire*(d^c)*h; a second consumer with qa = d (qcond undone) adds fire*d*h,
                    // so tst ^= fire*c*h exactly as with a clean qa (d, v, u, fire unchanged by the consumer)
                    if dirty_qa { consumer(g); }
                }));
            }
            {
                let (a, r, u, v, cp) = (a.clone(), r.clone(), u.clone(), v.clone(), cp.clone());
                p.lab = lab(3, k, 0, 0, 0, 0);
                p.one(Box::new(move |g| {
                    g.reverse(|g| g.add(&cp, &r, &a, None));
                    for j in 0..m {
                        g.swap(&cp, a[j], r[j]);
                    }
                    g.add(&cp, &v, &u, None);
                    for j in 0..t {
                        g.swap(&cp, u[j], v[j]);
                    }
                    g.op(&cp, sign);
                }));
            }
            let lnk = l[n - k];
            p.lab = lab(4, k, 0, 0, 0, 0);
            p.one(Box::new(move |g| if fl { g.op(&[fire, lnk], tst) } else { g.op(&[lnk], tst) }));
            {
                let (a, r) = (a.clone(), r.clone());
                p.lab = lab(5, k, 0, 0, 0, 0);
                p.one(Box::new(move |g| select(g, &a, &r, fire, &[], red)));
            }
        }
        let depth = roles.len();
        let low = 1usize << (real + 1);
        let wide = 1usize << full.len();
        let mut sectors: Vec<(usize, usize, usize)> = vec![(0, low, 0)];
        for j in 1..depth {
            let base = 1usize << (real + j);
            if base < m {
                sectors.push((base, base, j));
            }
        }
        if depth > 0 {
            let mut base = 1usize << (real + depth);
            while base < m {
                sectors.push((base, wide, depth));
                base += wide;
            }
        }
        sectors.reverse();
        for (sec, (base, width, kind)) in sectors.into_iter().enumerate() {
            let hi = (m - 1).min(base + width - 1);
            let dual = kind >= 2;
            let relay = kind > 0;
            let mut tagv: V = full[..real].to_vec();
            tagv.extend_from_slice(&full[full.len() - 1 - kind..]);
            p.tagv = tagv.clone();
            p.ports = if relay { vec![Some(tst)] } else { Vec::new() };
            p.sector_none = false;
            let tg0 = tagv[0];
            if let Some(j) = roles.iter().position(|&q| q == tg0) {
                set_port(&mut p.ports, j, r_all[m]);
            }
            // match(ct, w, z)
            let matchf = move |g: &mut W, ct: &[i32], wd: &[i32], z: i32| {
                if base + width < m {
                    g.zero_pair(ct, &wd[m - base..], &wd[m - base - width..], z);
                } else {
                    g.zer(ct, &wd[m - base..], z);
                }
            };
            let whole = base == 0 && hi == m - 1;
            p.lab = lab(10, k, base, kind, 0, sec);
            if whole {
                let (a, r) = (a.clone(), r.clone());
                p.one(Box::new(move |g| select(g, &a, &r, fire, &[], red)));
            } else {
                let (a, r) = (a.clone(), r.clone());
                // i4d fix 2: with real = 0, tg0 (the top tag or a relay role) is hosted on R[m] (the run driver's top port / the
                // port set above), a lane whose value x at the sector start is NOT always 0 or 1 (MEASURED: R[m] = 0 at 773 of 777
                // sector starts on some valid shot).  The select's comparison lt([tst, guard], a, r, fire) is linear in the guard:
                // run it once with guard = x (before the matching) and once with guard = x ^ match (after it): fire ^= tst*cmp*match,
                // exactly the stock select with a clean tg0, for every x (the matching restores R[m] = x).  The zero test of a[1..]
                // into tst commutes with the matching (disjoint lanes), so it brackets both comparisons.
                let dbl = real == 0;
                p.one(Box::new(move |g| {
                    if dbl {
                        let tst = g.tst;
                        let word: V = if red { r.to_vec() } else { a[1..].to_vec() };
                        g.zer(&[], &word, tst);
                        g.x(tst);
                        g.lt(&[tst, tg0], &a, &r, fire);
                        matchf(g, &[], &r, tg0);
                        g.lt(&[tst, tg0], &a, &r, fire);
                        matchf(g, &[], &r, tg0);
                        g.reverse(|g| {
                            g.zer(&[], &word, tst);
                            g.x(tst);
                        });
                    } else {
                        matchf(g, &[], &r, tg0);
                        select(g, &a, &r, fire, &[tg0], red);
                        matchf(g, &[], &r, tg0);
                    }
                }));
            }
            p.ports = if relay { vec![Some(tst)] } else { Vec::new() };
            p.lab = lab(11, k, base, kind, 0, sec);
            let rm = r_all[m];
            {
                let c = c.clone();
                p.one(Box::new(move |g| g.op(&c, rm)));
            }
            p.lab = lab(12, k, base, kind, 0, sec);
            norm_relay(&mut p, &tagv, &r, &c, base, dual, kind);
            {
                let (a, r, c) = (a.clone(), r.clone(), c.clone());
                p.lab = lab(13, k, base, kind, 0, sec);
                p.one(Box::new(move |g| {
                    let h = if relay { r[0] } else { tst };
                    g.op(&c, r[m - 1]);
                    g.x(h);
                    let lo = if relay { base } else { 0 };
                    let aa = cat1(&r[lo..m - 1], h);
                    let y0 = g.y[0];
                    g.dirty_digit(&aa, &a[lo..], r[m - 1], fire, y0);
                    g.x(h);
                }));
            }
            if relay {
                let (r1, c) = (r[1], c.clone());
                p.one(Box::new(move |g| g.swap(&c, tst, r1)));
                set_port(&mut p.ports, 0, r1);
            }
            {
                let c = c.clone();
                p.one(Box::new(move |g| g.op(&c, tst)));
            }
            p.lab = lab(14, k, base, kind, 0, sec);
            for i in 0..hi {
                p.lab = lab(16, k, base, kind, i, sec);
                if i >= 1 && i <= kind {
                    let (ri, rim, c) = (r[i], r[i - 1], c.clone());
                    p.one(Box::new(move |g| g.swap(&c, ri, rim)));
                    set_port(&mut p.ports, i - 1, rim);
                }
                let (a, r, c) = (a.clone(), r.clone(), c.clone());
                p.one(Box::new(move |g| {
                    eq_tag(g, &c, i, base, hi);
                    let en = [tst];
                    let rh = &r[i + 1..];
                    let ah = &a[i + 1..];
                    let carry = r[i];
                    for &z in &a[i..] {
                        g.swap(&en, carry, z);
                    }
                    let lo = if relay { (base as i64 - i as i64 - 1).max(0) as usize } else { 0 };
                    let head: &[i32] = if lo < rh.len() { &rh[lo..rh.len() - 1] } else { &[] };
                    let aa = cat1(head, fire);
                    let y0 = g.y[0];
                    g.dirty_digit(&aa, &ah[lo.min(ah.len())..], carry, tst, y0);
                    g.op(&cat1(&en, carry), a[i]);
                    g.op(&cat1(&en, a[i]), carry);
                }));
            }
            {
                let c = c.clone();
                p.one(Box::new(move |g| eq_tag(g, &c, hi, base, hi)));
            }
            for i in (0..hi).rev() {
                p.lab = lab(19, k, base, kind, i, sec);
                let (a, u, v, c) = (a.clone(), u.clone(), v.clone(), c.clone());
                let rk = r[kind];
                p.one(Box::new(move |g| {
                    eq_tag(g, &c, i + 1, base, hi);
                    let en = [tst];
                    let h = rk;
                    g.x(h);
                    let aa = cat1(&v[..t - 1], h);
                    g.reverse(|g| g.restore(&en, &aa, &u, a[i]));
                    g.x(h);
                    for j in (0..t).rev() {
                        g.swap(&en, a[i], u[j]);
                    }
                }));
            }
            {
                let c = c.clone();
                p.lab = lab(20, k, base, kind, 0, sec);
                p.one(Box::new(move |g| {
                    g.op(&c, tst);
                    eq_tag(g, &c, 0, base, hi);
                }));
            }
            {
                let (r, u, v, c) = (r.clone(), u.clone(), v.clone(), c.clone());
                p.lab = lab(21, k, base, kind, 0, sec);
                let lm = l[m];
                p.one(Box::new(move |g| {
                    let carry = r[m - 1];
                    g.x(tst);
                    let aa = cat1(&v[..t - 1], tst);
                    g.reverse(|g| g.restore(&c, &aa, &u, carry));
                    g.x(tst);
                    for j in (0..t).rev() {
                        g.swap(&c, carry, u[j]);
                    }
                    g.swap(&c, carry, lm);
                    g.op(&c, carry);
                }));
            }
            if relay {
                let (r, c) = (r.clone(), c.clone());
                p.lab = lab(22, k, base, kind, 0, sec);
                p.one(Box::new(move |g| g.swap(&c, r[0], tst)));
                set_port(&mut p.ports, 0, tst);
            }
            for j in (2..=kind).rev() {
                let (rjm, rj, c) = (r[j - 1], r[j], c.clone());
                p.one(Box::new(move |g| g.swap(&c, rjm, rj)));
                set_port(&mut p.ports, j - 1, rj);
            }
            {
                let (c, lw) = (c.clone(), rc(&l[m..=n]));
                p.lab = lab(24, k, base, kind, 0, sec);
                p.one(Box::new(move |g| g.rot(&c, &lw, -1)));
            }
            p.lab = lab(25, k, base, kind, 0, sec);
            rot_blocks(&mut p, &tagv, &rc(&l[..=n]), &c, -1, base);
            p.lab = lab(26, k, base, kind, 0, sec);
            let saved = std::mem::take(&mut p.blocks);
            norm_relay(&mut p, &tagv, &r, &c, base, dual, kind);
            let un = std::mem::replace(&mut p.blocks, saved);
            cat_inv(&mut p, un);
            p.ports = Vec::new();
            {
                let c = c.clone();
                p.lab = lab(27, k, base, kind, 0, sec);
                let (lw, lnk) = (rc(&l[..m]), l[n - k]);
                let l2 = l.clone();
                p.one(Box::new(move |g| {
                    g.op(&c, rm);
                    for j in 0..=n {
                        g.swap(&c, l2[j], r_all_at(g, j));
                    }
                    g.op(&c, sign);
                    if nong {
                        // i4e: the SectorReduced end block: the uncompute of fire is guarded by r != 0 (R[0..=m] after the swap)
                        let rr: V = (0..=m).map(|j| r_all_at(g, j)).collect();
                        let non = |g: &mut W| {
                            g.zer(&[], &rr, tst);
                            g.x(tst);
                        };
                        non(g);
                        if whole {
                            g.op(&[tst, lnk], fire);
                        } else {
                            matchf(g, &[tst, lnk], &lw, fire);
                        }
                        g.reverse(|g| non(g));
                    } else {
                        let guard = [lnk];
                        if whole {
                            g.op(&guard, fire);
                        } else {
                            matchf(g, &guard, &lw, fire);
                        }
                    }
                }));
            }
        }
    }
    let _ = cin;
    p.blocks
}
fn r_all_at(g: &W, j: usize) -> i32 {
    g.r[j]
}

// ---------------------------------------------------------------- plans 2 and 3: UnitWalk plan (D2ReducedImpl + select/pair, SectorReduced)
fn plan_unit(w: &W, aux_variant: bool) -> Vec<Block> {
    let n = w.n;
    let (l, r_all) = (w.l.clone(), w.r.clone());
    let (tst, fire, sign, cin, aux) = (w.tst, w.fire, w.sign, w.cin, w.aux);
    let tagv = w.tag.clone();
    let stride = 1usize << tagv.len();
    let c: Wr = Rc::new(vec![fire]);
    let mut p = Pl::new(false);
    p.tagv = tagv.clone();
    prelude(&mut p, &l, &r_all, n);
    for k in 0..n {
        let (t, m) = (k + 1, n - k);
        let a: Wr = rc(&l[..m]);
        let r: Wr = rc(&r_all[..m]);
        let u: Wr = Rc::new(co(&l, n, t));
        let v: Wr = Rc::new(co(&r_all, n, t));
        p.top = Some(r_all[m]);
        let sel = move |g: &mut W, a: &[i32], r: &[i32], z: i32, guard: &[i32]| select(g, a, r, z, guard, true);
        if k > 0 && k < n - 1 {
            let cp: Wr = Rc::new(vec![tst]);
            {
                let (a, r) = (a.clone(), r.clone());
                p.one(Box::new(move |g| sel(g, &a, &r, fire, &[])));
            }
            {
                let (a, r, u, v) = (a.clone(), r.clone(), u.clone(), v.clone());
                p.one(Box::new(move |g| {
                    let qa = if aux_variant { aux } else { g.tag[0] };
                    let qcond = |g: &mut W| {
                        g.op(&[r[m - 1]], qa);
                        g.x(r[m - 1]);
                        g.lt(&[r[m - 1]], &r[..m - 1], &a[1..], qa);
                        g.x(r[m - 1]);
                    };
                    qcond(g);
                    g.op(&[fire, qa], tst);
                    g.xs(&u);
                    g.lt(&[fire, qa], &v, &u, tst);
                    g.xs(&u);
                    g.reverse(|g| qcond(g));
                }));
            }
            {
                let (a, r, u, v, cp) = (a.clone(), r.clone(), u.clone(), v.clone(), cp.clone());
                p.one(Box::new(move |g| {
                    g.reverse(|g| g.add(&cp, &r, &a, None));
                    for j in 0..m {
                        g.swap(&cp, a[j], r[j]);
                    }
                    g.add(&cp, &v, &u, None);
                    for j in 0..t {
                        g.swap(&cp, u[j], v[j]);
                    }
                    g.op(&cp, sign);
                }));
            }
            let lnk = l[n - k];
            p.one(Box::new(move |g| g.op(&[fire, lnk], tst)));
            {
                let (a, r) = (a.clone(), r.clone());
                p.one(Box::new(move |g| sel(g, &a, &r, fire, &[])));
            }
        }
        let mut base = ((m - 1) / stride) * stride;
        loop {
            let hi = (m - 1).min(base + stride - 1);
            let aux_variant = aux_variant;
            let tg0 = tagv[0];
            // match: select-and-pair edits only exist in the non-aux class
            let matchf = move |g: &mut W, ct: &[i32], wd: &[i32], z: i32| {
                if !aux_variant && base + stride < m {
                    g.zero_pair(ct, &wd[m - base..], &wd[m - base - stride..], z);
                } else {
                    g.zer(ct, &wd[m - base..], z);
                    if base + stride < m {
                        g.zer(ct, &wd[m - base - stride..], z);
                    }
                }
            };
            let whole = base == 0 && hi == m - 1;
            if whole {
                let (a, r) = (a.clone(), r.clone());
                p.one(Box::new(move |g| sel(g, &a, &r, fire, &[])));
            } else if aux_variant {
                let (a, r, c) = (a.clone(), r.clone(), c.clone());
                p.one(Box::new(move |g| {
                    sel(g, &a, &r, fire, &[]);
                    matchf(g, &c, &r, aux);
                    sel(g, &a, &r, fire, &[]);
                    g.op(&[aux], fire);
                    g.op(&c, aux);
                }));
            } else {
                let (a, r) = (a.clone(), r.clone());
                p.one(Box::new(move |g| {
                    matchf(g, &[], &r, tg0);
                    sel(g, &a, &r, fire, &[tg0]);
                    matchf(g, &[], &r, tg0);
                }));
            }
            let rm = r_all[m];
            {
                let c = c.clone();
                p.one(Box::new(move |g| g.op(&c, rm)));
            }
            norm_blocks(&mut p, &tagv, &r, &c, base, false);
            {
                let (a, r, c) = (a.clone(), r.clone(), c.clone());
                p.one(Box::new(move |g| {
                    g.op(&c, r[m - 1]);
                    if aux_variant {
                        g.x(aux);
                        let aa = cat1(&r[..m - 1], aux);
                        g.digit(&aa, &a, r[m - 1], fire, tst);
                        g.x(aux);
                    } else {
                        g.x(tst);
                        let aa = cat1(&r[..m - 1], tst);
                        let y0 = g.y[0];
                        g.dirty_digit(&aa, &a, r[m - 1], fire, y0);
                        g.x(tst);
                    }
                }));
            }
            {
                let c = c.clone();
                p.one(Box::new(move |g| g.op(&c, tst)));
            }
            for i in 0..hi {
                let (a, r, c) = (a.clone(), r.clone(), c.clone());
                p.one(Box::new(move |g| {
                    eq_tag(g, &c, i, base, hi);
                    let en = [tst];
                    let rh = &r[i + 1..];
                    let ah = &a[i + 1..];
                    if aux_variant {
                        for &z in &a[i..] {
                            g.swap(&en, aux, z);
                        }
                        g.x(r[0]);
                        let aa = cat1(&rh[..rh.len() - 1], r[0]);
                        g.restore(&en, &aa, ah, aux);
                        g.x(r[0]);
                        g.op(&cat1(&en, aux), a[i]);
                        g.op(&cat1(&en, a[i]), aux);
                    } else {
                        let carry = r[i];
                        for &z in &a[i..] {
                            g.swap(&en, carry, z);
                        }
                        let aa = cat1(&rh[..rh.len() - 1], fire);
                        let y0 = g.y[0];
                        g.dirty_digit(&aa, ah, carry, tst, y0);
                        g.op(&cat1(&en, carry), a[i]);
                        g.op(&cat1(&en, a[i]), carry);
                    }
                }));
            }
            {
                let c = c.clone();
                p.one(Box::new(move |g| eq_tag(g, &c, hi, base, hi)));
            }
            for i in (0..hi).rev() {
                let (a, r, u, v, c) = (a.clone(), r.clone(), u.clone(), v.clone(), c.clone());
                p.one(Box::new(move |g| {
                    eq_tag(g, &c, i + 1, base, hi);
                    let en = [tst];
                    g.x(r[0]);
                    let aa = cat1(&v[..t - 1], r[0]);
                    g.reverse(|g| g.restore(&en, &aa, &u, a[i]));
                    g.x(r[0]);
                    for j in (0..t).rev() {
                        g.swap(&en, a[i], u[j]);
                    }
                }));
            }
            {
                let c = c.clone();
                p.one(Box::new(move |g| {
                    g.op(&c, tst);
                    eq_tag(g, &c, 0, base, hi);
                }));
            }
            {
                let (r, u, v, c) = (r.clone(), u.clone(), v.clone(), c.clone());
                let lm = l[m];
                p.one(Box::new(move |g| {
                    let carry = r[m - 1];
                    g.x(tst);
                    let aa = cat1(&v[..t - 1], tst);
                    g.reverse(|g| g.restore(&c, &aa, &u, carry));
                    g.x(tst);
                    for j in (0..t).rev() {
                        g.swap(&c, carry, u[j]);
                    }
                    g.swap(&c, carry, lm);
                    g.op(&c, carry);
                }));
            }
            rot_blocks(&mut p, &tagv, &r, &c, -1, base);
            {
                let (c, lw) = (c.clone(), rc(&l[m..=n]));
                p.one(Box::new(move |g| g.rot(&c, &lw, -1)));
            }
            rot_blocks(&mut p, &tagv, &rc(&l[..=n]), &c, -1, base);
            // cat(all, val(r, c, 0, base), true)
            let saved = std::mem::take(&mut p.blocks);
            norm_blocks(&mut p, &tagv, &r, &c, base, false);
            rot_blocks(&mut p, &tagv, &r, &c, -1, base);
            {
                let c = c.clone();
                p.one(Box::new(move |g| g.bias(&c, 0)));
            }
            let val = std::mem::replace(&mut p.blocks, saved);
            cat_inv(&mut p, val);
            {
                let (c, lw) = (c.clone(), rc(&l[..m]));
                let l2 = l.clone();
                let lnk = l[n - k];
                p.one(Box::new(move |g| {
                    g.op(&c, rm);
                    for j in 0..=n {
                        g.swap(&c, l2[j], r_all_at(g, j));
                    }
                    g.op(&c, sign);
                    let rr: V = (0..=m).map(|j| r_all_at(g, j)).collect();
                    let non = |g: &mut W| {
                        g.zer(&[], &rr, tst);
                        g.x(tst);
                    };
                    non(g);
                    if whole {
                        g.op(&[tst, lnk], fire);
                    } else {
                        matchf(g, &[tst, lnk], &lw, fire);
                    }
                    g.reverse(|g| non(g));
                }));
            }
            if base == 0 {
                break;
            }
            base -= stride;
        }
    }
    p.sector_none = false;
    p.one(Box::new(move |g| g.x(sign)));
    // class tail (D2ReducedImpl / SectorReduced): blocks without a top port
    p.top = None;
    for bits in 1..=n {
        let gap = n + 1 - bits;
        let rr = rc(&r_all[1..n - bits + 1]);
        let rk = r_all[n - bits + 1];
        let mark = move |g: &mut W| {
            g.zer(&[rk], &rr, fire);
        };
        let mark2 = mark.clone();
        p.one(Box::new(move |g| mark(g)));
        {
            let (l2, c) = (l.clone(), c.clone());
            p.one(Box::new(move |g| {
                for j in (gap..=n).rev() {
                    g.swap(&c, l2[j], l2[j + 1]);
                }
            }));
        }
        p.one(Box::new(move |g| mark2(g)));
    }
    {
        let r2 = r_all.clone();
        p.one(Box::new(move |g| {
            for j in (1..=n).rev() {
                g.swap(&[], r2[j], r2[j + 1]);
            }
        }));
    }
    let _ = cin;
    p.blocks
}

// ---------------------------------------------------------------- i4e: outer walk reverse from the relay class
/// [SectorReduced prelude] + plan_relay steps (real, guard) + [X(sign)] + [SectorReduced class tail]: the forward walk whose gate
/// inverse (run() reverses the block list and every block) is Kind::RevRelay.  The prelude and the tail are plan_unit's blocks
/// verbatim (they use no tag and no role); only the steps differ from plan_unit (relay steps instead of the SectorReduced steps).
fn plan_revrelay(w: &W, real: usize, guard: u8) -> Vec<Block> {
    let n = w.n;
    let (l, r_all) = (w.l.clone(), w.r.clone());
    let (fire, sign) = (w.fire, w.sign);
    let c: Wr = Rc::new(vec![fire]);
    let mut p = Pl::new(true);
    p.tagv = w.tag.clone();
    p.lab = lab(40, 0, 0, 0, 0, 0);
    prelude(&mut p, &l, &r_all, n);
    let steps = plan_relay(w, real, guard);
    p.blocks.extend(steps);
    p.top = None;
    p.sector_none = false;
    p.ports = Vec::new();
    p.tagv = w.tag.clone();
    p.lab = lab(41, 0, 0, 0, 0, 0);
    p.one(Box::new(move |g| g.x(sign)));
    // class tail (verbatim from plan_unit)
    p.lab = lab(42, 0, 0, 0, 0, 0);
    for bits in 1..=n {
        let gap = n + 1 - bits;
        let rr = rc(&r_all[1..n - bits + 1]);
        let rk = r_all[n - bits + 1];
        let mark = move |g: &mut W| {
            g.zer(&[rk], &rr, fire);
        };
        let mark2 = mark.clone();
        p.one(Box::new(move |g| mark(g)));
        {
            let (l2, c) = (l.clone(), c.clone());
            p.one(Box::new(move |g| {
                for j in (gap..=n).rev() {
                    g.swap(&c, l2[j], l2[j + 1]);
                }
            }));
        }
        p.one(Box::new(move |g| mark2(g)));
    }
    {
        let r2 = r_all.clone();
        p.one(Box::new(move |g| {
            for j in (1..=n).rev() {
                g.swap(&[], r2[j], r2[j + 1]);
            }
        }));
    }
    p.blocks
}

// ---------------------------------------------------------------- driver
fn physical(ports: &[Option<i32>], top: i32, blk_top: Option<i32>, x: u32) -> Result<u32, String> {
    if x == 1023 {
        return Ok(x);
    }
    let mut q = x as i32;
    if q == top {
        q = blk_top.ok_or_else(|| "height outside row".to_string())?;
    }
    match ports.get(q as usize).copied().flatten() {
        Some(v) if v >= 0 => Ok(v as u32),
        _ => Err(format!("unbound walk port {}", q)),
    }
}

pub fn run(cfg: &Cfg, sink: &mut dyn FnMut([u16; 4])) -> Result<usize, String> {
    let n = cfg.n;
    let mut w;
    let mut blocks: Vec<Block>;
    let mut relay: Option<(V, V)> = None; // (roles, full)
    let back;
    match cfg.kind {
        Kind::Inner { real } => {
            w = W::new(n, cfg.tags);
            w.canon_op = true;
            w.rot2 = true;
            let bits = 7usize;
            let avail: V = w.tag[..real].to_vec();
            let top = *w.tag.last().unwrap();
            let mut nt = avail.clone();
            for i in 0..(bits - real - 1) {
                nt.push(900 + i as i32);
            }
            nt.push(top);
            w.tag = nt;
            blocks = plan_relay(&w, real, 0);
            let full = w.tag.clone();
            let roles: V = full[real..full.len() - 1].iter().rev().cloned().collect();
            relay = Some((roles, full));
            back = false;
        }
        Kind::RevRelay { real, guard } => {
            // i4e: the relay set-up of Kind::Inner, the plan wrapped by plan_revrelay, emitted backwards
            w = W::new(n, cfg.tags);
            w.canon_op = true;
            w.rot2 = true;
            let bits = 7usize;
            let avail: V = w.tag[..real].to_vec();
            let top = *w.tag.last().unwrap();
            let mut nt = avail.clone();
            for i in 0..(bits - real - 1) {
                nt.push(900 + i as i32);
            }
            nt.push(top);
            w.tag = nt;
            blocks = plan_revrelay(&w, real, guard);
            blocks.reverse();
            let full = w.tag.clone();
            let roles: V = full[real..full.len() - 1].iter().rev().cloned().collect();
            relay = Some((roles, full));
            back = true;
        }
        Kind::RevImpl | Kind::RevSector => {
            w = W::new(n, 5);
            w.rot2 = true;
            w.canon_op = cfg.kind == Kind::RevImpl;
            w.aux_restore = cfg.kind == Kind::RevSector;
            w.tag.truncate(cfg.tags);
            blocks = plan_unit(&w, cfg.kind == Kind::RevSector);
            blocks.reverse();
            back = true;
        }
    }
    // port table
    let mut ports: Vec<Option<i32>> = vec![None; 1024];
    let bind = |ports: &mut Vec<Option<i32>>, a: &[i32], b: &[i32]| {
        for i in 0..a.len() {
            ports[a[i] as usize] = b.get(i).copied();
        }
    };
    bind(&mut ports, &w.l, &cfg.l);
    bind(&mut ports, &w.r, &cfg.r);
    bind(&mut ports, &w.y, &cfg.loan);
    let wt = w.tag.clone();
    bind(&mut ports, &wt, &cfg.ws_tag[..wt.len().min(cfg.ws_tag.len())]);
    ports[w.sign as usize] = Some(cfg.sign);
    ports[w.fire as usize] = Some(cfg.fire);
    ports[w.tst as usize] = Some(cfg.tst);
    ports[w.aux as usize] = Some(cfg.aux);
    let top = *w.tag.last().unwrap();
    let mut total = 0usize;
    for blk in blocks.iter() {
        let t_start = total;
        w.g.clear();
        let old_y = w.y.clone();
        if let Some(tg) = &blk.tag {
            w.tag = tg.clone();
        }
        if relay.is_some() && blk.pre {
            let l = w.y.len();
            w.y.truncate(l - 1);
        }
        (blk.f)(&mut w);
        w.y = old_y.clone();
        if let Some((roles, full)) = &relay {
            for j in 0..w.g.len() {
                let x = w.g[j];
                let mp = |q: u32| -> Result<u32, String> {
                    if q == 1023 {
                        return Ok(q);
                    }
                    if let Some(jj) = roles.iter().position(|&z| z == q as i32) {
                        if blk.pre && q as i32 == full[0] {
                            return Ok(*old_y.last().unwrap() as u32);
                        }
                        return match blk.ports.get(jj).copied().flatten() {
                            Some(v) => Ok(v as u32),
                            None => Err(format!("unhosted D22 relay {}", jj)),
                        };
                    }
                    Ok(q)
                };
                let (a, b, z) = (mp(x >> 20 & 1023)?, mp(x >> 10 & 1023)?, mp(x & 1023)?);
                if a == z || b == z || (a == b && a != 1023) {
                    return Err("dual alias".into());
                }
                w.g[j] = (a << 20) | (b << 10) | z;
            }
        }
        if blk.rev != back {
            w.g.reverse();
        }
        for &x in &w.g {
            let a = physical(&ports, top, blk.top, x >> 20 & 1023)?;
            let b = physical(&ports, top, blk.top, x >> 10 & 1023)?;
            let t = physical(&ports, top, blk.top, x & 1023)?;
            if a == t || b == t || (a != 1023 && a == b) {
                return Err("physical walk alias".into());
            }
            total += 1;
            if a == 1023 && b == 1023 {
                sink([6, t as u16, NONE16, NONE16]);
            } else if b == 1023 {
                sink([8, a as u16, t as u16, NONE16]);
            } else {
                sink([13, a as u16, b as u16, t as u16]);
            }
        }
        LOG.with(|l| if let Some(v) = l.borrow_mut().as_mut() { v.push((t_start, total, blk.lab)); });
    }
    Ok(total)
}
