// ======================================================================================================================
// round17 a2-build v4: R1 (round11 rail-strip, the fused rail-tile carry) on the 8-way rail barrel. The choice add's
// lean ladder with carry[1] := the target's complemented bit 0 leaves X^ = X - 2 L [e >= 1] (L = b1 ^ s3, both live):
// wires 1 ..= e hold X ^ L (wire 0 untouched). The barrel absorbs it with fills of L (CNOTs from b1 and s3, free) and,
// where needed, products; the network, the constant fills and the drop0 Fredkin are the plain plan's. An exact GF(2)
// solve over every e <= min(7, w - 2) on the sign (S) and garbage (L) rows jointly.
// ======================================================================================================================
#[derive(Clone, Debug)]
pub(super) struct Rail8G {
    base: Rail8,
    /// (boundary, wire, phi 0..3 = 1 / k1 / k2 / k3, sym 1 = S, 2 = L, 3 = S ^ L): these replace the base's sign fills
    sl: Vec<(usize, usize, u8, u8)>,
    /// the products (phi >= 1, sym) used, one AND each
    prods: Vec<(u8, u8)>,
    /// the base's drop0 Fredkin is still legal on X^
    drop_ok: bool,
}
impl Rail8G {
    /// Toffoli count forward (with drop0 if legal) and the base plan's.
    pub(super) fn costs(&self) -> (usize, usize) {
        let sw: usize = self.base.stages.iter().map(|s| s.0.len()).sum();
        let bd = usize::from(self.base.drop.is_some());
        (sw + self.prods.len() - usize::from(self.base.drop.is_some() && self.drop_ok), sw + self.base.prods.count_ones() as usize - bd)
    }
}
fn r8_phi4(phi: u8, e: usize) -> bool { phi == 0 || e >> (phi - 1) & 1 == 1 }
/// GF(2) elimination (pivot = lowest variable bit), back substitution with the free variables 0; `tb` = target bit.
fn r8_gf2(rows: Vec<Vec<u64>>, tb: usize, nw: usize) -> Option<Vec<bool>> {
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
    Some(sol)
}
/// Joint S / L fill solve on the plan's network: S rows = the sign target (as [`r8_solve`]), L rows = the garbage
/// (the final positions of the input wires 1 ..= e, e >= 1). `kinds` = (phi, sym) fill kinds allowed.
fn r8_solve_sl(w: usize, stages: &[(Vec<(usize, usize)>, u8)], emax: usize, kinds: &[(u8, u8)], no0_after: Option<usize>) -> Option<Vec<(usize, usize, u8, u8)>> {
    let ns = stages.len();
    let nr = a_env("LFA2_R8NEAR").unwrap_or(if w % 2 == 1 { w } else { 24 });
    let near: Vec<usize> = (0..w).filter(|&q| q < nr || q + nr >= w || (q + 12 >= w / 2 && q < w / 2 + 12)).collect();
    let vars: Vec<(usize, usize, u8, u8)> = (0..=ns)
        .flat_map(|b| near.iter().flat_map(move |&q| kinds.iter().map(move |&(f, s)| (b, q, f, s))))
        .filter(|&(b, q, _, _)| !(q == 0 && no0_after.is_some_and(|s| b > s)))
        .collect();
    let tb = vars.len();
    let nw = (tb + 64) / 64;
    let mut rows: Vec<Vec<u64>> = Vec::new();
    for e in 0..=emax {
        let pos = r8_positions(w, stages, e);
        let from = pos[0][w - 1];
        let gpos: Vec<usize> = (1..=e).map(|q| pos[0][q]).collect();
        for p in 0..w {
            for sym in [1u8, 2] {
                let tgt = if sym == 1 { (p + 1 + e >= w) ^ (p == from) } else { gpos.contains(&p) };
                let mut row = vec![0u64; nw + 1];
                for (i, &(b, q, f, s)) in vars.iter().enumerate() {
                    if s & sym != 0 && pos[b][q] == p && r8_phi4(f, e) {
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
    }
    let sol = r8_gf2(rows, tb, nw)?;
    Some((0..tb).filter(|&i| sol[i]).map(|i| vars[i]).collect())
}
/// Classical check of a garbage plan on random 2^e-odd rails with random S and L: forward from X^ (drop0's semantics
/// when `drop0`) to the shifted rail, and the inverse back to X^. Returns (ok, drop0 legal).
fn r8_check_g(w: usize, pl: &Rail8G, emax: usize, drop0: bool) -> (bool, bool) {
    let mut seed = 0x51f1_5e3a_77c2_9b4du64 ^ w as u64;
    let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let consts: Vec<(usize, usize, u8)> = pl.base.fills.iter().filter(|f| f.2 >= 4).copied().collect();
    let mut legal = true;
    for trial in 0..(128 * (emax + 1)) {
        let e = trial % (emax + 1);
        let (sv, lv) = (rnd() & 1 == 1, rnd() & 1 == 1);
        let mut x = vec![false; w];
        x[e] = true;
        for j in e + 1..w - 1 { x[j] = rnd() & 1 == 1; }
        x[w - 1] = sv;
        let want: Vec<bool> = (0..w).map(|p| if p + e < w { x[p + e] } else { sv }).collect();
        let mut xg = x.clone();
        for q in 1..=e { xg[q] ^= lv; }
        let fills_at = |t: &mut Vec<bool>, b: usize| {
            for &(fb, q, f) in &consts {
                if fb == b && r8_phi(f, e) { t[q] ^= true; }
            }
            for &(fb, q, f, s) in &pl.sl {
                if fb == b && r8_phi4(f, e) { t[q] ^= (s & 1 != 0 && sv) ^ (s & 2 != 0 && lv); }
            }
        };
        let mut t = xg.clone();
        for (si, (pairs, mask)) in pl.base.stages.iter().enumerate() {
            fills_at(&mut t, si);
            let cv = r8_ctrl(*mask, e);
            for &(a, b) in pairs {
                if drop0 && pl.base.drop == Some((si, (a, b))) {
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
        fills_at(&mut t, pl.base.stages.len());
        if t != want { return (false, legal); }
        let mut t = want.clone();
        fills_at(&mut t, pl.base.stages.len());
        for si in (0..pl.base.stages.len()).rev() {
            let (pairs, mask) = &pl.base.stages[si];
            if r8_ctrl(*mask, e) {
                for &(a, b) in pairs.iter().rev() { t.swap(a, b); }
            }
            fills_at(&mut t, si);
        }
        if t != xg { return (false, legal); }
    }
    (true, legal)
}
/// Fast path: the base's sign fills with their products read as `sym` (1 = S k_i, 3 = (S ^ L) k_i), and free L fills
/// solved for the residual garbage (L rows only).
fn r8_fast_g(w: usize, base: &Rail8, emax: usize, sym: u8) -> Option<Vec<(usize, usize, u8, u8)>> {
    let stages = &base.stages;
    let ns = stages.len();
    let sl0: Vec<(usize, usize, u8, u8)> = base.fills.iter().filter(|f| f.2 < 4).map(|&(b, q, f)| (b, q, f, if f > 0 { sym } else { 1 })).collect();
    let no0 = base.drop.map(|d| d.0);
    let nr = a_env("LFA2_R8NEAR").unwrap_or(if w % 2 == 1 { w } else { 24 });
    let near: Vec<usize> = (0..w).filter(|&q| q < nr || q + nr >= w || (q + 12 >= w / 2 && q < w / 2 + 12)).collect();
    let vars: Vec<(usize, usize)> = (0..=ns).flat_map(|b| near.iter().map(move |&q| (b, q))).filter(|&(b, q)| !(q == 0 && no0.is_some_and(|s| b > s))).collect();
    let tb = vars.len();
    let nw = (tb + 64) / 64;
    let mut rows: Vec<Vec<u64>> = Vec::new();
    for e in 0..=emax {
        let pos = r8_positions(w, stages, e);
        let mut tgt = vec![false; w];
        for q in 1..=e { tgt[pos[0][q]] ^= true; }
        for &(b, q, f, s) in &sl0 {
            if s & 2 != 0 && r8_phi4(f, e) { tgt[pos[b][q]] ^= true; }
        }
        let mut by_p: Vec<Vec<u64>> = (0..w).map(|_| vec![0u64; nw + 1]).collect();
        for (i, &(b, q)) in vars.iter().enumerate() {
            by_p[pos[b][q]][i / 64] |= 1 << (i % 64);
        }
        for (p, mut row) in by_p.into_iter().enumerate() {
            if tgt[p] { row[tb / 64] |= 1 << (tb % 64); }
            if row.iter().any(|&x| x != 0) { rows.push(row); }
        }
    }
    let sol = r8_gf2(rows, tb, nw)?;
    let mut sl = sl0;
    sl.extend((0..tb).filter(|&i| sol[i]).map(|i| (vars[i].0, vars[i].1, 0u8, 2u8)));
    Some(sl)
}
/// The garbage plan for width w (cached; None if no plan within one product of the base's).
pub(super) fn rail8_plan_g(w: usize) -> Option<Rail8G> {
    thread_local! { static C: std::cell::RefCell<std::collections::HashMap<usize, Option<Rail8G>>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    if let Some(p) = C.with(|c| c.borrow().get(&w).cloned()) {
        return p;
    }
    let base = rail8_plan(w);
    let emax = 7.min(w.saturating_sub(2));
    let bp: Vec<u8> = (1..=3u8).filter(|&i| base.prods >> (i - 1) & 1 == 1).collect();
    // candidates (cost, kinds, keep drop0): the base's products as S or S ^ L, then one extra product
    let mut cands: Vec<(usize, Vec<(u8, u8)>, bool)> = Vec::new();
    for m in 0..(1u32 << bp.len()) {
        let mut ks: Vec<(u8, u8)> = vec![(0, 1), (0, 2)];
        for (j, &i) in bp.iter().enumerate() { ks.push((i, if m >> j & 1 == 1 { 3 } else { 1 })); }
        for keep in [true, false] {
            let extra_drop = usize::from(!keep && base.drop.is_some());
            cands.push((bp.len() + extra_drop, ks.clone(), keep));
            for phi in 1..=3u8 {
                for sym in 1..=3u8 {
                    if ks.iter().any(|&(f, _)| f == phi) { continue; }
                    let mut k2 = ks.clone();
                    k2.push((phi, sym));
                    cands.push((bp.len() + 1 + extra_drop, k2, keep));
                }
            }
        }
    }
    cands.sort_by_key(|c| c.0);
    let maxc = bp.len() + 1;
    let mut found = None;
    for sym in [3u8, 1] {
        if emax == 0 { break; }
        let Some(sl) = r8_fast_g(w, &base, emax, sym) else { continue };
        let prods: Vec<(u8, u8)> = bp.iter().map(|&i| (i, sym)).filter(|k| sl.iter().any(|f| (f.2, f.3) == *k)).collect();
        let want_drop = base.drop.is_some();
        let mut pl = Rail8G { base: base.clone(), sl, prods, drop_ok: false };
        let (ok, legal) = r8_check_g(w, &pl, emax, want_drop);
        if !ok || (want_drop && !legal) { continue; }
        pl.drop_ok = want_drop;
        found = Some(pl);
        break;
    }
    if found.is_some() { cands.clear(); }
    for (cost, kinds, keep) in cands {
        if cost > maxc || emax == 0 { break; }
        let no0 = if keep { base.drop.map(|d| d.0) } else { None };
        let Some(sl) = r8_solve_sl(w, &base.stages, emax, &kinds, no0) else { continue };
        let prods: Vec<(u8, u8)> = kinds.iter().filter(|k| k.0 > 0 && sl.iter().any(|f| (f.2, f.3) == **k)).copied().collect();
        let mut pl = Rail8G { base: base.clone(), sl, prods, drop_ok: false };
        let want_drop = base.drop.is_some() && keep;
        let (ok, legal) = r8_check_g(w, &pl, emax, want_drop);
        if !ok || (want_drop && !legal) { continue; }
        pl.drop_ok = want_drop;
        found = Some(pl);
        break;
    }
    C.with(|c| c.borrow_mut().insert(w, found.clone()));
    found
}
/// [`rail8_barrel`] on X^ (R1 garbage L = l[0] ^ l[1] on wires 1 ..= e): forward to the shifted rail (drop0: wire 0
/// released, returns true), inverse from the shifted rail back to X^.
pub(super) fn rail8_barrel_g(c: &mut Builder, k: [QubitId; 3], t: &[QubitId], l: [QubitId; 2], inverse: bool, drop0: bool) -> bool {
    let w = t.len();
    let pl = rail8_plan_g(w).unwrap_or_else(|| panic!("a2: no R1 rail8 plan at w = {w}"));
    let drop0 = drop0 && !inverse && pl.drop_ok && !std::env::var("LF_BARREL_DROP0").is_ok_and(|v| v == "0");
    let sg = t[w - 1];
    let consts: Vec<(usize, usize, u8)> = pl.base.fills.iter().filter(|f| f.2 >= 4).copied().collect();
    let scopy = pl.sl.iter().any(|f| f.2 == 0 && f.3 & 1 != 0).then(|| {
        let q = c.alloc_qubit();
        c.cx(sg, q);
        q
    });
    let lq = pl.prods.iter().any(|p| p.1 == 2).then(|| {
        let q = c.alloc_qubit();
        c.cx(l[0], q);
        c.cx(l[1], q);
        q
    });
    let slq = pl.prods.iter().any(|p| p.1 == 3).then(|| {
        let q = c.alloc_qubit();
        c.cx(sg, q);
        c.cx(l[0], q);
        c.cx(l[1], q);
        q
    });
    let prod: Vec<((u8, u8), QubitId)> = pl
        .prods
        .iter()
        .map(|&(f, s)| {
            let opd = match s { 1 => sg, 2 => lq.unwrap(), _ => slq.unwrap() };
            ((f, s), and_new(c, k[f as usize - 1], opd))
        })
        .collect();
    let fill = |c: &mut Builder, b: usize| {
        for &(_, q, f) in consts.iter().filter(|x| x.0 == b) {
            if f == 4 { c.x(t[q]) } else { c.cx(k[f as usize - 5], t[q]) }
        }
        for &(_, q, f, s) in pl.sl.iter().filter(|x| x.0 == b) {
            if f == 0 {
                if s & 1 != 0 { c.cx(scopy.unwrap(), t[q]); }
                if s & 2 != 0 { c.cx(l[0], t[q]); c.cx(l[1], t[q]); }
            } else {
                let pq = prod.iter().find(|p| p.0 == (f, s)).unwrap().1;
                c.cx(pq, t[q]);
            }
        }
    };
    let mut dropped = false;
    let mut stage = |c: &mut Builder, si: usize| {
        let (pairs, mask) = &pl.base.stages[si];
        let (h, others) = rot8_host(k, *mask);
        for &o in &others { c.cx(o, h); }
        for &(a, b) in pairs {
            if drop0 && pl.base.drop == Some((si, (a, b))) {
                let pr = if a == 0 { b } else { a };
                c.cx(t[0], t[pr]);
                c.x(t[pr]);
                c.x(t[0]);
                let m = c.alloc_bit();
                c.hmr(t[0], m);
                c.x(t[pr]);
                c.cz_if(h, t[pr], m);
                c.x(t[pr]);
                c.free_bit(m);
                c.release_clean(t[0]);
                dropped = true;
            } else {
                fredkin(c, h, t[a], t[b]);
            }
        }
        for &o in others.iter().rev() { c.cx(o, h); }
    };
    let ns = pl.base.stages.len();
    if !inverse {
        for si in 0..ns { fill(c, si); stage(c, si); }
        fill(c, ns);
    } else {
        fill(c, ns);
        for si in (0..ns).rev() { stage(c, si); fill(c, si); }
    }
    for &((f, s), q) in prod.iter().rev() {
        let opd = match s { 1 => t[w - 1], 2 => lq.unwrap(), _ => slq.unwrap() };
        and_erase(c, q, k[f as usize - 1], opd);
    }
    if let Some(q) = slq {
        c.cx(l[1], q);
        c.cx(l[0], q);
        c.cx(t[w - 1], q);
        c.release_clean(q);
    }
    if let Some(q) = lq {
        c.cx(l[1], q);
        c.cx(l[0], q);
        c.release_clean(q);
    }
    if let Some(q) = scopy {
        c.cx(t[w - 1], q);
        c.release_clean(q);
    }
    dropped
}

#[cfg(test)]
mod a2_r1_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    /// [`rail8_barrel_g`] on width w: forward from X^ (random L, drop0) to the shifted rail and inverse back to X^,
    /// every e <= min(7, w - 2); values, letters, L wires, clean, no phase. Returns (fwd T, rev T).
    fn check_rail8_g(w: usize) -> (usize, usize) {
        let mut out = (0, 0);
        for inverse in [false, true] {
            let mut c = Builder::new();
            let t = c.alloc_qubits(w);
            let k = c.alloc_qubits(3);
            let l = c.alloc_qubits(2);
            let e0 = c.expected_total();
            let dropped = rail8_barrel_g(&mut c, [k[0], k[1], k[2]], &t, [l[0], l[1]], inverse, true);
            let cost = (c.expected_total() - e0).round() as usize;
            if inverse { out.1 = cost } else { out.0 = cost }
            let (nq, nbits) = c.i13_dims();
            let ops = c.take_ops();
            let mut h = sha3::Shake256::default();
            h.update(b"a2-rail8-r1");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
            let emax = 7.min(w - 2);
            let mut seed = 0x7f4a_7c15_9e37_79b9u64 ^ w as u64;
            let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
            let mut bad = 0;
            for _ in 0..8 {
                sim.clear_for_shot();
                let mut ins = Vec::new();
                for shot in 0..64 {
                    let e = shot % (emax + 1);
                    let (sv, l0, l1) = (rnd() & 1 == 1, rnd() & 1 == 1, rnd() & 1 == 1);
                    let mut x = vec![false; w];
                    x[e] = true;
                    for j in e + 1..w - 1 { x[j] = rnd() & 1 == 1; }
                    x[w - 1] = sv;
                    let y: Vec<bool> = (0..w).map(|p| if p + e < w { x[p + e] } else { sv }).collect();
                    for q in 1..=e { x[q] ^= l0 ^ l1; }
                    let inp = if inverse { y.clone() } else { x.clone() };
                    for i in 0..w { if inp[i] { *sim.qubit_mut(t[i]) |= 1 << shot; } }
                    for i in 0..3 { if e >> i & 1 == 1 { *sim.qubit_mut(k[i]) |= 1 << shot; } }
                    if l0 { *sim.qubit_mut(l[0]) |= 1 << shot; }
                    if l1 { *sim.qubit_mut(l[1]) |= 1 << shot; }
                    ins.push((e, l0, l1, if inverse { x } else { y }));
                }
                sim.apply_iter(ops.iter());
                for (shot, (e, l0, l1, want)) in ins.iter().enumerate() {
                    let mut ok = (sim.phase >> shot) & 1 == 0;
                    for i in 0..w {
                        if dropped && i == 0 { continue; }
                        ok &= ((sim.qubit(t[i]) >> shot) & 1 == 1) == want[i];
                    }
                    for i in 0..3 { ok &= ((sim.qubit(k[i]) >> shot) & 1) as usize == (e >> i & 1); }
                    ok &= ((sim.qubit(l[0]) >> shot) & 1 == 1) == *l0 && ((sim.qubit(l[1]) >> shot) & 1 == 1) == *l1;
                    ok &= (w + 5..nq).all(|q| (sim.qubits[q] >> shot) & 1 == 0);
                    if dropped { ok &= (sim.qubits[t[0].0 as usize] >> shot) & 1 == 0; }
                    bad += usize::from(!ok);
                }
            }
            eprintln!("A2_R1_CHECK w={w} inverse={inverse} drop0={dropped} T={cost} bad={bad}");
            assert_eq!(bad, 0, "a2: the R1 8-way rail barrel is wrong at w = {w}");
        }
        out
    }
    #[test]
    fn a2_r1_rail8_exact() {
        let mut ws: Vec<usize> = (3..=40).collect();
        ws.extend([41, 43, 51, 63, 64, 65, 101, 128, 255, 256, 257, 258]);
        if let Ok(v) = std::env::var("LFA2_R8W") { ws = v.split(',').map(|x| x.parse().unwrap()).collect(); }
        for w in ws {
            let Some(pl) = rail8_plan_g(w) else { eprintln!("A2_R1 w={w} none"); continue };
            let (f, r) = check_rail8_g(w);
            let (gc, bc) = pl.costs();
            eprintln!("A2_R1 w={w} fwd={f} rev={r} plan={gc} base={bc} prods={:?} drop_ok={} nsl={}", pl.prods, pl.drop_ok, pl.sl.len());
        }
    }
}
