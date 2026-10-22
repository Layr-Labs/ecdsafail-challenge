//! Original payload arithmetic with five or six ordinary owners and one shared
//! high-size word, called inside the raw outer wrapper's encode/decode pair.
//!
//! sc.sa is raw Zlow5; sc.sb is raw Ylow5 followed by the shared high3.
//! ph.rv/ph.tv are physical raw-size views assembled by the caller. `view`
//! establishes Y (false) or Z (true) using the exact high-word involution;
//! it borrows returned g/c0 (and optional tmp) only at a view boundary.
//! In five-owner mode only arithmetic borrows a conditional zero carry:
//! X(PH) on HT, or X(act) on HR after its guard is retained on fa. Original
//! c0 then supplies a globally clean AND temp; the view callback still uses
//! returned original c0/g and never runs while either borrowed lane is changed.
//! Each complete ripple, decoder walk and fused ADD/compare keeps one view.
//! The module enters and exits in Y view, and never changes view while Zlow5
//! contains the temporary S-226 code. The caller supplies the inherited
//! adjacent/top zero shuttles and source padding; no extra Q127 loan is used.
//! For the column-zero SZ=256 endpoint the caller also supplies the existing
//! ninth raw-Z size lane; the three shared high bits alone encode SZ mod256.

use super::{B, DigScr, Ph, QubitId, NP, KE, Mask, Cut, Dec, mc_xor,
    read_lane_gated, ripple, ripple_true_carry, bank_of, wl, ht_mask_shift,
    erase_ripple, D2_DIGIT_TARGET, PCNT};
use super::super::builder::G;

// Only literal IR is priced here. An opaque row/deferred operation makes
// prices() return None, preserving the original complete record. Both
// playback directions must improve or stay equal; no macro is discounted.
fn play_nonincreasing(b: &mut B, old: &[G], candidate: &[G]) {
    let take = match (super::read_lane_tree::prices(old), super::read_lane_tree::prices(candidate)) {
        (Some((of, oi)), Some((nf, ni))) => nf <= of && ni <= oi && (nf < of || ni < oi),
        _ => false,
    };
    b.play(if take { candidate } else { old }, false);
}

/// Exact selected swap: gather one defined leaf, swap it with the flight,
/// then undo the gather. An explicit address/extra predicate excludes every
/// hole and invalid raw address; no active-domain shortcut is needed.
#[allow(clippy::too_many_arguments)]
fn swap_selected(b: &mut B, reg: &[QubitId], lo: usize, hi: usize,
    lane: &dyn Fn(usize) -> Option<QubitId>, flight: QubitId,
    extra: &[(QubitId, bool)], pre: &[QubitId], temps: &[QubitId],
    dirty: &[QubitId], flag: QubitId, clean: &[QubitId]) {
    let old = super::super::frogdrop_col::rec(b, |b|
        super::super::mid2::dec_swap(b, reg, lo, hi, lane, flight, extra, pre, temps, dirty));
    if reg.is_empty() || reg.len() >= usize::BITS as usize {
        b.play(&old, false); return;
    }
    let end = 1usize << reg.len();
    let leaves: Vec<_> = (lo..=hi.min(end - 1)).filter_map(|v| lane(v).map(|q| (v, q))).collect();
    if leaves.is_empty() { b.play(&old, false); return; }
    let mut occupied = std::collections::BTreeSet::new();
    if !reg.iter().chain(leaves.iter().map(|(_, q)| q))
        .chain(extra.iter().map(|(q, _)| q)).chain([&flight, &flag])
        .chain(clean.iter()).all(|q| occupied.insert(q.0)) {
        b.play(&old, false); return;
    }
    // Every donor is restored before gather/ungather. Exclude all current
    // ports, including the whole leaf set, even when the compact MCX uses
    // its direct dirty route rather than a known-prefix implementation.
    let mut seen = std::collections::BTreeSet::new();
    let donors: Vec<_> = dirty.iter().copied()
        .filter(|q| !occupied.contains(&q.0) && seen.insert(q.0)).collect();
    if donors.len() < reg.len() + extra.len() {
        b.play(&old, false); return;
    }
    let predicate = super::super::frogdrop_col::rec(b, |b| {
        let mut mask = Mask::new(reg, end - 1, true, extra.to_vec(), flag, clean, &donors);
        let mut first = 0;
        while first < leaves.len() {
            let mut last = first;
            while last + 1 < leaves.len() && leaves[last + 1].0 == leaves[last].0 + 1 { last += 1; }
            mask.toggle_range(b, leaves[first].0, leaves[last].0);
            first = last + 1;
        }
    });
    let mut swaps = Vec::with_capacity(leaves.len() - 1);
    let root = super::read_lane_tree::collect_tree(reg, &leaves, reg.len(), &mut swaps);
    let candidate = super::super::frogdrop_col::rec(b, |b| {
        b.play(&predicate, false);
        for &(control, left, right) in &swaps { b.cswap(control, left, right); }
        b.cswap(flag, root, flight);
        for &(control, left, right) in swaps.iter().rev() { b.cswap(control, left, right); }
        b.play(&predicate, true);
    });
    play_nonincreasing(b, &old, &candidate);
}

fn with_view<R>(b: &mut B, view: &mut dyn FnMut(&mut B, bool), z: bool,
                body: impl FnOnce(&mut B) -> R) -> R {
    view(b, z);
    body(b)
}

/// Establish the raw view using only globally clean owners, then borrow a
/// phase/enable lane as zero carry on the acted sector. With extra=0 and e=0
/// the full MAJ/down body is identity for arbitrary carry. Every caller
/// returns that carry before this closing X; no view callback runs inside.
fn with_arithmetic<R>(b: &mut B, view: &mut dyn FnMut(&mut B, bool), z: bool,
    loan: Option<QubitId>, body: impl FnOnce(&mut B) -> R) -> R {
    view(b, z);
    if let Some(q) = loan { b.x(q); }
    let out = body(b);
    if let Some(q) = loan { b.x(q); }
    out
}

/// HR's enable itself is the conditional carry, so no arithmetic query may
/// read it. A nonconstant gate already lives on fa; materialize a constant
/// gate there too, and erase the copy only after the carry is restored.
fn retain_gate(b: &mut B, sc: &DigScr, act: QubitId, fa: QubitId,
    made: bool, borrow_act: bool) -> (QubitId, bool) {
    let copied = borrow_act && !made;
    if copied {
        assert_eq!(fa, act);
        b.cx(act, sc.fa);
        (sc.fa, true)
    } else { (fa, false) }
}

/// On S=Z+Y in [226,257], (Zlow+Ylow-2) mod32 is S-226.
/// It uses no shared high bit, so it is the same code in either raw view.
/// The entire transformation is undone before a view callback or arithmetic.
fn sum_code_record(b: &mut B, sc: &DigScr) -> Vec<G> {
    let roles: Vec<_> = sc.e.iter().copied().chain([sc.sv, sc.fa, sc.g, sc.c0])
        .chain(sc.tmp.iter().copied()).collect();
    let dirty: Vec<_> = sc.dirty.iter().copied()
        .filter(|q| !sc.sa.contains(q) && !sc.sb.contains(q) && !roles.contains(q)).collect();
    super::super::frogdrop_col::rec(b, |b| {
        super::super::arith::ttk_add(b, &sc.sb[..5], &sc.sa, None, None);
        let bias = super::super::frogdrop_col::rec(b, |b|
            super::super::frogdrop::add_const_dirty_exact(b, &sc.sa, 2, &dirty));
        b.play(&bias, true);
    })
}

fn guard_compare(b: &mut B, sc: &DigScr, lim: isize, cl: QubitId, chain: &[QubitId]) {
    let k = lim + 1 - 226;
    if super::super::mask::ge_const_need(sc.sa.len(), k) <= chain.len() {
        super::super::mask::ge_const(b, &sc.sa, k, cl, chain);
    } else {
        super::super::frogdrop_col::ge_const_compact(b, &sc.sa, k, cl, chain, &sc.dirty);
    }
}

// Same public pruning, fa construction, returned comparator and inverse as
// original gate_le. Only the size-code epoch is local and five bits wide.
fn gate_le(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize,
           extra: &[QubitId]) -> Option<(QubitId, bool)> {
    if (sr.0 as isize) > lim { return None; }
    if (sr.1 as isize) <= lim { return Some((act, false)); }
    let (cl, chain) = super::gate_lanes(sc, extra);
    let code = sum_code_record(b, sc);
    b.play(&code, false);
    guard_compare(b, sc, lim, cl, &chain);
    b.x(cl); b.and_c(act, cl, sc.fa); b.x(cl);
    guard_compare(b, sc, lim, cl, &chain);
    b.play(&code, true);
    Some((sc.fa, true))
}

fn gate_le_undo(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId]) {
    let (cl, chain) = super::gate_lanes(sc, extra);
    let code = sum_code_record(b, sc);
    b.play(&code, false);
    guard_compare(b, sc, lim, cl, &chain);
    b.x(cl); b.and_u(act, cl, sc.fa); b.x(cl);
    guard_compare(b, sc, lim, cl, &chain);
    b.play(&code, true);
}

pub(super) fn digit(b: &mut B, p: &[QubitId], ph: &Ph, act: QubitId, phase: QubitId, sc: &DigScr,
    dirty: &[QubitId], view: &mut dyn FnMut(&mut B, bool)) {
    assert_eq!(sc.sa.len(), 5, "raw Z low word");
    assert_eq!(sc.sb.len(), 8, "Y low word plus shared high word");
    assert!((1..=8).contains(&sc.e.len()) && sc.e.len() < KE);
    let five = sc.tmp.is_empty();
    assert!(!five || super::super::frogdrop_col::c665_pool4());
    assert!(sc.tmp.len() <= 1);
    assert!(sc.pre1.is_empty() && sc.pre2.is_empty() && sc.zeros.is_empty());
    let roles: Vec<_> = sc.e.iter().copied().chain([sc.sv, sc.fa, sc.g, sc.c0])
        .chain(sc.tmp.iter().copied()).collect();
    for (i, q) in roles.iter().enumerate() {
        assert!(!roles[..i].contains(q) && *q != act
            && !sc.sa.contains(q) && !sc.sb.contains(q));
    }
    assert!(sc.sa.iter().all(|q| !sc.sb.contains(q)));
    assert!(!sc.sa.contains(&act) && !sc.sb.contains(&act));
    assert!(sc.dirty.iter().all(|q| !roles.contains(q) && *q != act
        && !sc.sa.contains(q) && !sc.sb.contains(q)));
    assert!(dirty.iter().all(|q| !roles.contains(q) && *q != act
        && !sc.sa.contains(q) && !sc.sb.contains(q)));
    let (zview, yview) = if ph.ht { (&ph.tv, &ph.rv) } else { (&ph.rv, &ph.tv) };
    assert!((8..=9).contains(&zview.len()) && yview == &sc.sb);
    assert_eq!(&zview[..5], &sc.sa[..]);
    assert_eq!(&zview[5..8], &sc.sb[5..8]);
    // A wider-ring HR mask reads the other size during the down pass.
    // The shared-size path accepts only the official N257 contract.
    if ph.ht {
        assert_eq!(ph.src_t.len(), 257);
        assert!(ph.virt_m1);
    } else {
        assert_eq!(ph.src_r.len(), 257);
        assert!(ph.sz_mask);
    }
    // The callback changes only the shared high word and returns its clean
    // temporary before any arithmetic/query epoch starts.
    view(b, false);
    let (rlo, rhi) = ph.rr;
    let (tlo, thi) = ph.tr;
    let mtmp = &sc.tmp[..];
    // PH=1 on acted HT and is not the HT adjacent save. On HR the physical
    // PH may hold that save, so borrow act itself after retaining every query
    // guard on fa. Both loans are used only inside complete ripple epochs.
    let borrow_act = five && !ph.ht;
    let carry_loan = five.then_some(if ph.ht { phase } else { act });
    let carry = carry_loan.unwrap_or(sc.c0);
    let carry_temp = [sc.c0];
    let arithmetic_temps = if five { &carry_temp[..] } else { mtmp };
    let arithmetic_one_tmp = &arithmetic_temps[..arithmetic_temps.len().min(1)];
    if let Some(q) = carry_loan {
        assert!(!roles.contains(&q) && !sc.sa.contains(&q) && !sc.sb.contains(&q));
        assert!(!p.contains(&q) && !ph.src_r.contains(&q) && !ph.src_t.contains(&q));
        assert!(!dirty.contains(&q) && !sc.dirty.contains(&q));
        assert!(!ph.ht || phase != act);
    }
    // The caller's encoder already requires this whole post-stage-2 domain,
    // including idle/inactive classes. Intersect the public phase envelope;
    // this removes guards proved constant without restricting any input.
    let srange = ((rlo + tlo).max(226), (rhi + thi).min(257));
    let pt0 = b.tof;
    let mut ptk = [0u64; 6];
    // in-place digit (sc.e = [c, bank (8)] shorter than KE): e_k leaves the division at d-index bl(r) + k (zero
    // once d < 2^k r); one reflection of [bl(r), 257 - bl(t)] moves it to W-index bl(t) + 1 + k, above everything
    // the D^-1 writes up to bit k (W < 2^(bl(t) + k + 2), s + bl(e) <= 258); c holds the bit being processed
    let ip = sc.e.len() < KE;
    let ecl = |k: usize| if ip { sc.e[0] } else { sc.e[k] };
    let clean_e = |k: usize| -> Vec<QubitId> { if ip { sc.e[1..].to_vec() } else { sc.e[0..k].to_vec() } };
    let ipb: Vec<QubitId> = if ip { sc.e[1..sc.e.len().min(8)].to_vec() } else { vec![] };
    // No omitted raw-size high lane is a prefix owner. The six ordinary
    // roles retain the original fa/g/tmp arithmetic. Any e[1..] owners are
    // returned clean decoder prefixes, never additional quotient storage.
    let safe_bank = |bank: Vec<QubitId>| -> Vec<QubitId> { bank };
    // ---- long division: e_k = [d >= 2^k r_j] with d < 2^(k+1) r_j; window positions [k, k + bl(r) + 1)
    for k in (0..KE).rev() {
        // clean at this step: e[0..k] (not yet written) and sv (formed after the division)
        let mut lde = vec![sc.sv];
        lde.extend(clean_e(k));
        let Some((fa, made)) = gate_le(b, sc, act, srange, 257 - k as isize, &lde) else { continue };
        let (fa, copied) = retain_gate(b, sc, act, fa, made, borrow_act);
        let top = (k + rhi + 1).min(NP);
        let t: Vec<QubitId> = (k..top).map(|i| p[i]).collect();
        let s: Vec<QubitId> = ph.src_r[..top - k].to_vec();
        let ek = ecl(k);
        let rv = ph.rv.clone();
        let src = s.clone();
        // e[0..k] are still clean: from k = 8 on they are the decoder bank (below: topped up with sv, g and e[0..k];
        // g is the HR mask flag, clean until the down pass)
        let mut ldb = vec![sc.sv, sc.g];
        ldb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
        // (in place: sv tops the bank up, clean until the division's sign read)
        let bank0 = if ip { bank_of(&ipb, &[sc.sv]) } else if k >= 8 { sc.e[0..8].to_vec() }
                                else { bank_of(&sc.pre1, &ldb) };
        let bank = safe_bank(bank0);
        let mut mid = |b: &mut B| {
            let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
            read_lane_gated(b, &rv, rlo, rhi, &lane, true, &[(fa, false)], ek, &bank, arithmetic_temps, dirty);
        };
        if ph.ht {
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
            with_arithmetic(b, view, !ph.ht, carry_loan, |b|
                ripple(b, &t, &s, carry, true, &mut mid, &mut gate));
        } else {
            // HR: ring-sourced divisor; the coarse boundary follows physical
            // ring length (N280 has one fewer guaranteed zero lane than N281).
            // agent_lowq_quot: with granule g = 2^gsh the guard G must satisfy 256 <= G (a live step's Z lanes pass:
            // k + i <= 256 - bl(t)) and G <= N - g (Y's lanes, ring index >= N - bl(t), are masked): G = N - 16 needs
            // ring >= 272; below it the 8-lane granule (G = N - 8, ring >= 264)
            // (agent_lowq_lane: 4-lane granule at ring 263, G = N - 4 >= 256)
            let gsh: usize = if ph.src_r.len() >= 256 + 16 { 4 } else if ph.src_r.len() >= 256 + 8 { 3 }
                              else if ph.src_r.len() >= 260 { 2 } else if ph.src_r.len() >= 258 { 1 } else { 0 };
            let bits = &ph.tv[gsh..];
            let hr_guard = ph.src_r.len() as isize - (1 << gsh);
            let mpre_hr: Vec<QubitId> = if ip { safe_bank(ipb.clone()) } else { vec![] };
            let mut mk = if ph.sz_mask {
                Mask::new(&ph.rv, rhi, false, vec![(ek, false)], sc.g, arithmetic_one_tmp, dirty)
                    .with_lo(rlo).with_pre(&mpre_hr)
            } else {
                Mask::new(bits, thi >> gsh, true, vec![(ek, false)], sc.g, arithmetic_one_tmp, dirty)
                    .with_lo(tlo >> gsh).with_pre(&mpre_hr)
            };
            // The two-gather query returns sv before the down sweep.
            // Keep the legacy route's witness untouched through its sweep.
            // For n8 and at least8 address values, caching one high prefix
            // saves2 CCX per singleton transition, pays at most4 prefix
            // changes per direction, and retains the old compact clear.
            // Require an untruncated initial boundary: a clipped payload
            // starts with a wide interval where one-hot expansion can cost more.
            let sv_pre=[sc.sv];
            let loan=ipb.is_empty() && ph.sz_mask && ph.rv.len()==8 && rhi>=rlo+7 && top==k+rhi+1;
            let mut funded=Mask::new(&ph.rv,rhi,false,vec![(ek,false)],sc.g,arithmetic_one_tmp,dirty)
                .with_lo(rlo).with_pre(&sv_pre);
            let mut gate = |b: &mut B, i: Option<usize>, pair: bool| {
                let use_prefix=loan && pair;
                let mask=if use_prefix { &mut funded } else { &mut mk };
                match i {
                    Some(i) => {
                        let pos=(k+i) as isize;
                        mask.goto(b,Some(if ph.sz_mask { i as isize }
                            else { (hr_guard-pos).div_euclid(1<<gsh)+1 }));
                        Some(sc.g)
                    }
                    None => {
                        if use_prefix { mask.clear_compact(b); } else { mask.goto(b,None); }
                        None
                    }
                }
            };
            with_arithmetic(b, view, !ph.ht, carry_loan, |b| {
                if ph.src_r.len()<=258 {
                    super::ripple_true_carry_select(b,&t,&s,carry,&rv,rlo,rhi,&[(fa,false)],ek,sc.sv,&bank,arithmetic_temps,dirty,&mut gate);
                } else {
                    let mut old_gate=|b:&mut B,i|gate(b,i,false);
                    ripple(b,&t,&s,carry,true,&mut mid,&mut old_gate);
                }
            });
        }
        if ip {
            // e_k to d-index bl(r) + k
            let lane = |v: usize| if v + k < NP { Some(p[v + k]) } else { None };
            let swap_clean: Vec<_> = ipb.iter().copied().chain([sc.sv, sc.c0])
                .chain(mtmp.iter().copied()).collect();
            with_view(b, view, !ph.ht, |b|
                swap_selected(b, &ph.rv, rlo, rhi, &lane, ek, &[(fa, false)],
                    &safe_bank(bank_of(&ipb, &[sc.sv])), mtmp, dirty, sc.g, &swap_clean));
        }
        if copied { b.cx(act, sc.fa); }
        if made {
            gate_le_undo(b, sc, act, 257 - k as isize, &lde);
        }
    }
    #[cfg(test)] super::super::frogdrop_col::mark(b, 30000 + 1000 * usize::from(ph.ht));
    ptk[0] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("divide")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        view(b, false);
        return;
    }
    // ---- sv = sign of W (lane of bit bl(t))
    {
        let lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
        let more: Vec<QubitId> = [sc.fa, sc.g, sc.c0].into_iter().chain(sc.zeros.iter().copied()).collect();
        let bank = if ip { bank_of(&ipb, &more) } else { bank_of(&sc.pre1, &more) };
        with_view(b, view, ph.ht, |b| {
            if five && ip {
                // Every e_k has moved to P, so e[0] joins the already
                // returned fa/g/c0 bank. Keep three prefixes, and spend
                // c0 as an actual clean AND cell only during this read.
                let old = super::super::frogdrop_col::rec(b, |b|
                    read_lane_gated(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv,
                        &safe_bank(bank), mtmp, dirty));
                let pre = safe_bank(bank_of(&ipb, &[sc.e[0], sc.fa, sc.g]));
                let candidate = super::super::frogdrop_col::rec(b, |b|
                    read_lane_gated(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv,
                        &pre, &[sc.c0], dirty));
                play_nonincreasing(b, &old, &candidate);
            } else {
                read_lane_gated(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv,
                    &safe_bank(bank), mtmp, dirty);
            }
        });
    }
    if ip {
        // e: d-index bl(r) + k -> W-index bl(t) + 1 + k, the segment [bl(r), 257 - bl(t)] reversed on act shots (in
        // the payload frame down by bl(r) it is [0, 258 - s))
        // S>=226 gives reflection length 258-S<=32. Preserve every
        // physical cell in that segment, including its final cell31.
        let dest: std::collections::BTreeSet<usize> = (0..32).collect();
        let rot = super::super::frogdrop_col::rec(b, |b| {
            super::super::frogdrop::rot_by_range_care(b, p, &ph.rv, rlo, rhi, true, dirty, &dest)
        });
        with_view(b, view, !ph.ht, |b| b.play(&rot, false));
        let code = sum_code_record(b, sc);
        b.play(&code, false);
        let (slo, shi) = (srange.0.max(226), srange.1.min(257));
        let size_bits = &sc.sa[..];
        let reflect = |b: &mut B, rb: &[QubitId], temps: &[QubitId]| {
            let mut dec = Dec::new(size_bits, rb);
            for sv_ in slo..=shi {
                let l = 258 - sv_;
                if l < 2 { continue; }
                let mut ct = dec.ctrls(b, sv_ - 226);
                ct.push((act, false));
                for i in 0..l / 2 {
                    super::super::mid2::mc_swap(b, &ct, p[i], p[l - 1 - i], temps, dirty);
                }
            }
            dec.clear(b);
        };
        let rb = bank_of(&ipb, &[sc.c0, sc.fa]);
        if five {
            // sv is held; e/fa/g/c0 are all returned. The entire decoder
            // is cleared before the sum code or high-size view changes.
            let old = super::super::frogdrop_col::rec(b, |b| reflect(b, &rb, mtmp));
            let pre = bank_of(&ipb, &[sc.fa, sc.g, sc.c0]);
            let candidate = super::super::frogdrop_col::rec(b, |b| reflect(b, &pre, &[sc.e[0]]));
            play_nonincreasing(b, &old, &candidate);
        } else { reflect(b, &rb, mtmp); }
        b.play(&code, true);
        with_view(b, view, !ph.ht, |b| b.play(&rot, true));
    }
    #[cfg(test)] super::super::frogdrop_col::mark(b, 30001 + 1000 * usize::from(ph.ht));
    ptk[1] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("relocate")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        view(b, false);
        return;
    }
    // ---- D^-1: W += e_k 2^k |t|; e_k ^= act & !sv & [s <= 258 - k] & [W >= 2^k |t|]
    for k in 0..KE {
        #[cfg(test)] super::super::frogdrop_col::mark(b, 30200 + 1000 * usize::from(ph.ht) + k);
        let top = (k + thi + 1).min(NP);
        if top <= k {
            break;
        }
        let t: Vec<QubitId> = (k..top).map(|pos| wl(p, pos)).collect();
        let s: Vec<QubitId> = ph.src_t[..top - k].to_vec();
        let ek = ecl(k);
        if ip {
            // e_k from W-index bl(t) + 1 + k on shots with s <= 257 - k (elsewhere that lane is d's or W's)
            let cle = if five { vec![sc.g] } else { clean_e(k) };
            let Some((fr, mr)) = gate_le(b, sc, act, srange, 257 - k as isize, &cle) else { continue };
            let lane = |v: usize| if v + 1 + k < NP { Some(wl(p, v + 1 + k)) } else { None };
            let swap_clean: Vec<_> = ipb.iter().copied().chain([sc.c0])
                .chain(mtmp.iter().copied()).collect();
            with_view(b, view, ph.ht, |b|
                swap_selected(b, &ph.tv, tlo, thi, &lane, ek, &[(fr, false)],
                    &if ph.ht { safe_bank(bank_of(&ipb, &[sc.c0, sc.g])) }
                     else { bank_of(&ipb, &[sc.c0, sc.g]) }, mtmp, dirty, sc.g, &swap_clean));
            if mr { gate_le_undo(b, sc, act, 257 - k as isize, &cle); }
        }
        // Fuse only the exact ADD;compare pair. A missing size guard retains
        // the old ADD-before-continue behavior. The returned size query runs
        // before either arithmetic only when fa cannot alias their data/pads.
        let cle = if five { vec![sc.g] } else { clean_e(k) };
        let mut deb = vec![sc.g];
        deb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
        let pair_bank0 = if ip { if ph.ht { bank_of(&ipb, &[sc.g]) } else { ipb.clone() } }
                        else if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &deb) };
        let pair_bank = if ph.ht { safe_bank(pair_bank0) } else { pair_bank0 };
        let lim = 258 - k as isize;
        let pair_fa = if !borrow_act && (srange.1 as isize) <= lim { act } else { sc.fa };
        let pair_extra = [(pair_fa, false), (sc.sv, true)];
        let ht_margin = if ph.virt_m1 { 1 } else { ph.src_t.len() as isize - 257 };
        // agent_lowq_quot: the 16-lane granule needs a ring margin n - 257 >= 16 (ring 273); below it the granule is
        // 8 lanes (margin >= 8, ring >= 265); agent_lowq_lane: 4 lanes at ring 264 (margin 7)
        // N260 has only three guard lanes. A four-lane prefix can admit a
        // write past that margin, so use a two-lane granule there.
        let gsh = if ph.ht { ht_mask_shift(ht_margin) } else { 1 };
        let mask_pre = if ph.ht { safe_bank(ipb.clone()) } else { ipb.clone() };
        let pair_mask = if ph.ht { Some(erase_ripple::PrefixMask {
            bits: &ph.tv[gsh..], amax: thi >> gsh, flag: sc.g, margin: ht_margin, shift: gsh,
            lo: tlo >> gsh, pre: &mask_pre,
        }) } else { None };
        let pair_eligible = (srange.0 as isize) <= lim && erase_ripple::geometry(&t, &s, carry, ek,
            &ph.tv, &pair_extra, &pair_bank, arithmetic_temps, dirty, pair_mask);
        let margin1_fused = ph.ht && (ph.src_t.len() == 258 || ph.virt_m1)
            && std::env::var("R9_DIGIT_FUSED").as_deref() == Ok("1");
        if pair_eligible && (!ph.ht || ph.src_t.len() > 258 || margin1_fused) {
            let f1 = b.tof;
            let (fa, made) = gate_le(b, sc, act, srange, lim, &cle).expect("public eligible size gate");
            let (fa, copied) = retain_gate(b, sc, act, fa, made, borrow_act);
            assert_eq!(fa, pair_fa);
            let selected = if margin1_fused {
                // fa => acted public sizes and R+T <= 258-k. Since R>=1,
                // T <= 257-k <= last=min(thi,258-k); also T>=tlo.
                // fa,sv and the size word are unchanged by this ripple.
                // Hence extra already implies the complete query interval.
                erase_ripple::fused_record_margin1_gated(b, &t, &s, carry, ek, &ph.tv,
                    tlo, thi, &pair_extra, &pair_bank, arithmetic_temps, dirty, pair_mask)
                    .expect("eligible N258 fused geometry")
            } else {
                erase_ripple::choose_record(b, &t, &s, carry, ek, &ph.tv,
                    tlo, thi, &pair_extra, &pair_bank, arithmetic_temps, dirty, pair_mask)
            };
            #[cfg(test)] let diag=std::env::var("Q675_DIGIT_FINE").is_ok();
            #[cfg(not(test))] let diag=false;
            #[cfg(test)] if diag {
                with_arithmetic(b, view, ph.ht, carry_loan, |b|
                    erase_ripple::diagnostic_reference_play(b,&t,&s,carry,ek,&ph.tv,tlo,thi,&pair_extra,&pair_bank,arithmetic_temps,dirty,pair_mask,40000+1000*usize::from(ph.ht)+10*k));
            }
            if !diag {
                with_arithmetic(b, view, ph.ht, carry_loan,
                              |b| b.play(&selected, false));
            }
            if copied { b.cx(act, sc.fa); }
            if made { gate_le_undo(b, sc, act, lim, &cle); }
            super::super::f1_profile("digit.inverse_fused", f1, b.tof);
            continue;
        }
        super::super::f1_profile(if (srange.0 as isize) > lim { "digit.inverse_missing_guard" } else { "digit.inverse_geometry_fallback" }, 0, 0);
        let f1 = b.tof;
        // Fallback add: HT ring-source writes stop before the physical
        // headroom margin plus 16 (bl(t) >> 4), preventing overlap with Z.
        {
            let mut mid = |_b: &mut B| {};
            if ph.ht {
                let bits = &ph.tv[gsh..];
                let mpre_ht: Vec<QubitId> = if ip { safe_bank(ipb.clone()) } else if k >= 8 { safe_bank(sc.e[0..8].to_vec()) } else { vec![] };
                let mut mk = Mask::new(bits, thi >> gsh, false, vec![(ek, false)], sc.g, arithmetic_one_tmp, dirty)
                    .with_lo(tlo >> gsh).with_pre(&mpre_ht);
                let mut gate = |b: &mut B, i: Option<usize>| match i {
                    Some(i) => {
                        let pos = (k + i) as isize;
                        let x = pos - k as isize - ht_margin;
                        mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(1 << gsh) + 1 }));
                        Some(sc.g)
                    }
                    None => {
                        mk.goto(b, None);
                        None
                    }
                };
                with_arithmetic(b, view, ph.ht, carry_loan,
                              |b| ripple(b, &t, &s, carry, false, &mut mid, &mut gate));
            } else {
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
                with_arithmetic(b, view, ph.ht, carry_loan, |b|
                    ripple(b, &t, &s, carry, false, &mut mid, &mut gate));
            }
        }
        // compare-erase
        let cle = if five { vec![sc.g] } else { clean_e(k) };
        let Some((fa, made)) = gate_le(b, sc, act, srange, 258 - k as isize, &cle) else {
            super::super::f1_profile("digit.inverse_fallback", f1, b.tof);
            continue
        };
        let (fa, copied) = retain_gate(b, sc, act, fa, made, borrow_act);
        {
            let tv = ph.tv.clone();
            let src = s.clone();
            // e[0..k] are erased already: from k = 8 on they are the decoder bank (below: topped up with g and
            // e[0..k])
            let mut deb = vec![sc.g];
            deb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
            // (in place, HT: g tops the bank up; HR's padded source holds g)
            let bank0 = if ip { if ph.ht { bank_of(&ipb, &[sc.g]) } else { ipb.clone() } }
                                    else if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &deb) };
            let bank = if ph.ht { safe_bank(bank0) } else { bank0 };
            let mut mid = |b: &mut B| {
                let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
                read_lane_gated(b, &tv, tlo, thi, &lane, true, &[(fa, false), (sc.sv, true)], ek, &bank, arithmetic_temps, dirty);
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            with_arithmetic(b, view, ph.ht, carry_loan, |b| {
                if ph.ht && ph.src_t.len()<=258 {
                    ripple_true_carry(b,&t,&s,carry,&tv,tlo,thi,&[(fa,false),(sc.sv,true)],ek,sc.g,&bank,arithmetic_temps,dirty,&mut gate);
                } else { ripple(b, &t, &s, carry, true, &mut mid, &mut gate); }
            });
        }
        if copied { b.cx(act, sc.fa); }
        if made {
            gate_le_undo(b, sc, act, 258 - k as isize, &cle);
        }
        super::super::f1_profile("digit.inverse_fallback", f1, b.tof);
    }
    #[cfg(test)] super::super::frogdrop_col::mark(b, 30002 + 1000 * usize::from(ph.ht));
    ptk[2] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("inverse")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        view(b, false);
        return;
    }
    // ---- widen: on act, R+T<=257 gives [l>=R && l<258-T]
    // = [l<R] XOR [l<258-T]. sv is zero off-act. Complete and return
    // each flag walk before changing the shared high-size view.
    // D^-1 returned e, g and c0 on every shot. In particular, no Q-source
    // ripple is live now, so g's earlier virtual padding role has ended.
    // These three ordinary owners may hold decoder prefixes until each
    // complete walk returns; fa remains the walk flag. In five-role mode,
    // e becomes the AND temp and g/c0 are the two decoder prefixes.
    let tail_pre: Vec<_> = if five { vec![sc.g, sc.c0] }
        else { vec![sc.e[0], sc.g, sc.c0] };
    let tail_tmp = if five { sc.e[0] } else { mtmp[0] };
    assert!(tail_pre.iter().all(|q| !p.contains(q)));
    {
        let lo = rlo;
        let hi = (NP - 1).saturating_sub(tlo);
        let c1 = Cut { v: ph.rv.clone(), a: 0, neg: false };
        let c2 = Cut { v: ph.tv.clone(), a: (NP - 1) as isize, neg: true };
        with_view(b, view, !ph.ht, |b| {
            super::super::frogdrop::walk_cutf_capped(b, &c1, lo, hi,
                sc.fa, &tail_pre, tail_tmp, dirty, |b, l, f| b.ccx(sc.sv, f, p[l]));
        });
        with_view(b, view, ph.ht, |b| {
            super::super::frogdrop::walk_cutf_capped(b, &c2, lo, hi,
                sc.fa, &tail_pre, tail_tmp, dirty, |b, l, f| b.ccx(sc.sv, f, p[l]));
        });
    }
    #[cfg(test)] super::super::frogdrop_col::mark(b, 30003 + 1000 * usize::from(ph.ht));
    ptk[3] = b.tof - pt0;
    // ---- erase sv: sv = lane bl(r) (sign-extended W, not complemented)
    let erase_sign = |b: &mut B, view: &mut dyn FnMut(&mut B, bool)| {
        let lane = |v: usize| if v < NP { Some(p[v]) } else { None };
        // Both complete walks have returned fa and the prefix bank.
        let sign_pre = [sc.e[0], sc.fa, sc.g, sc.c0];
        assert!(!p.contains(&sc.fa));
        with_view(b, view, !ph.ht, |b|
            read_lane_gated(b, &ph.rv, rlo, rhi, &lane, false, &[(act, false)], sc.sv,
                            &sign_pre, mtmp, dirty));
        #[cfg(test)] super::super::frogdrop_col::mark(b, 30005 + 1000 * usize::from(ph.ht));
    };
    // E reads P[R], whereas C changes only P[l] for l>R. Thus E and C
    // commute on arbitrary payload data, with the same act and raw R.
    // Moving the entire read (including its inverse gather) frees sv for
    // the complete complement decoder, without a live prefix/view overlap.
    let early_sign_t = if five {
        let start = b.tof;
        erase_sign(b, view);
        b.tof - start
    } else { 0 };
    // ---- complement lanes (bl(r), NP) on active shots
    let complement_start = b.tof;
    let complement = |b: &mut B, pre: &[QubitId]| {
        for l in (rhi + 1)..NP {
            b.cx(act, p[l]);
        }
        let cut = Cut { v: ph.rv.clone(), a: 1, neg: false }; // f = [l < bl(r) + 1] = [l <= bl(r)]
        let lo = rlo + 1;
        let hi = rhi + 1;
        if lo < hi {
            super::super::frogdrop::walk_cutf_capped(b, &cut, lo, hi, sc.fa, pre, tail_tmp, dirty, |b, l, f| {
                b.x(f);
                b.ccx(f, act, p[l]);
                b.x(f);
            });
        }
    };
    if five {
        with_view(b, view, !ph.ht, |b| {
            let old = super::super::frogdrop_col::rec(b, |b| complement(b, &tail_pre));
            let pre = bank_of(&ipb, &[sc.sv, sc.g, sc.c0]);
            let candidate = super::super::frogdrop_col::rec(b, |b| complement(b, &pre));
            play_nonincreasing(b, &old, &candidate);
        });
    } else {
        // Preserve the inherited six-role ordering, including the view
        // callback after the unconditional high-payload complements.
        for l in (rhi + 1)..NP { b.cx(act, p[l]); }
        let cut = Cut { v: ph.rv.clone(), a: 1, neg: false };
        let (lo, hi) = (rlo + 1, rhi + 1);
        if lo < hi {
            with_view(b, view, !ph.ht, |b| {
                super::super::frogdrop::walk_cutf_capped(b, &cut, lo, hi,
                    sc.fa, &tail_pre, tail_tmp, dirty, |b, l, f| {
                        b.x(f); b.ccx(f, act, p[l]); b.x(f);
                    });
            });
        }
    }
    #[cfg(test)] super::super::frogdrop_col::mark(b, 30004 + 1000 * usize::from(ph.ht));
    // Keep the named profile buckets semantic, rather than charging the
    // early sign read to complement. Debug tags likewise stay attached to
    // their completed operation (five-role order is now 30005,30004).
    ptk[4] = ptk[3] + (b.tof - complement_start);
    let sign_t = if five { early_sign_t } else {
        let start = b.tof;
        erase_sign(b, view);
        b.tof - start
    };
    ptk[5] = ptk[4] + sign_t;
    let names = ["digit.divide", "digit.sign_relocate", "digit.inverse", "digit.widen", "digit.complement", "digit.erase_sign"];
    for i in 0..6 {
        super::super::f1_profile(names[i], 0, ptk[i] - if i == 0 { 0 } else { ptk[i - 1] });
    }
    if std::env::var("FROGDROP_PROF2").is_ok() { let pc = PCNT.with(|c| { let v = *c.borrow(); *c.borrow_mut() = [0; 4]; v }); eprintln!("digprof ht {} rr {:?} tr {:?} cum {:?} readlane/mask/gate {:?}", ph.ht, ph.rr, ph.tr, ptk, pc); }
    view(b, false);
}

