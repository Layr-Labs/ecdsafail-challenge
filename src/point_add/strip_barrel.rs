// ---- round11/rail-strip: strip barrel (R2) and its R1-garbage variant ----
// Rotation of wires 0..w-2 by e = k1 + 2 k2 (the sign wire w-1 never moves) as three letter-controlled reflections
// rho_1[k1], rho_0[k1^k2], rho_(w-3)[k2] of Z_(w-1); pair (0,1) of rho_1 is dropped (both ends hold known content
// on k1 branches) and, forward, pair (0,w-3) of rho_(w-3) too. The sign fill is done by unconditional block CNOTs,
// which commute with the controlled swaps and telescope across them, plus 1 (even w) / 2 (odd w) ANDs: 1.5w - 4
// (even) / (3w - 7)/2 (odd) Toffoli forward against lin_rail_barrel's 1.5w - 3 / (3w - 5)/2. Patterns: tables
// below, each checked gate by gate on all inputs for widths 10..26 (scripts/gen3.py). `sp = Some((b1, s3))`: the
// input is the R1 target X^ = X - 2 L [e >= 1] with L = b1 ^ s3 (source bit 1 and the sign letter, both live).
#[derive(Clone, Copy, PartialEq, Debug)]
enum SbF { One, K1, K2, S, L, W0, A(u8) }
#[derive(Clone, Copy, Debug)]
enum SbE { Lo(i16), Mid(i16), Hi(i16) }
#[derive(Clone, Copy, Debug)]
enum SbT { One(i16), Blk(SbE, SbE) }
struct SbPat {
    ands: &'static [(&'static [SbF], &'static [SbF])],
    ops: &'static [(u8, SbT, &'static [SbF])],
    phase: &'static [(&'static [SbF], &'static [SbF])],
}

/// Smallest width the strip patterns were checked at (and whose low / middle / high regions do not overlap).
const SB_MIN_W: usize = 12;

fn strip_on() -> bool {
    !std::env::var("LF_STRIP").is_ok_and(|v| v == "0")
}

/// Is there a checked strip for this width / direction / input (general w >= 12, or a per-width table)?
fn sb_avail(w: usize, inverse: bool, garbage: bool) -> bool {
    w >= SB_MIN_W || sb_small(w, inverse, garbage).is_some()
}

fn sb_pat(inverse: bool, garbage: bool, w: usize) -> &'static SbPat {
    if w < SB_MIN_W {
        return sb_small(w, inverse, garbage).expect("strip: no table for this width");
    }
    match (inverse, garbage, w % 2 == 0) {
        (false, false, true) => &SB_FWD_EVEN,
        (false, false, false) => &SB_FWD_ODD,
        (false, true, true) => &SB_FWDG_EVEN,
        (false, true, false) => &SB_FWDG_ODD,
        (true, false, true) => &SB_REV_EVEN,
        (true, false, false) => &SB_REV_ODD,
        (true, true, true) => &SB_REVG_EVEN,
        (true, true, false) => &SB_REVG_ODD,
    }
}

fn sb_lin(fs: &[SbF], k1: QubitId, k2: QubitId, s: QubitId, l: &Lin, anc: &[QubitId]) -> Lin {
    let mut out = Lin::default();
    for f in fs {
        let term = match *f {
            SbF::One => Lin::k(true),
            SbF::K1 => Lin::of(&[k1]),
            SbF::K2 => Lin::of(&[k2]),
            SbF::S => Lin::of(&[s]),
            SbF::L => {
                assert!(!l.w.is_empty(), "strip: L term without the R1 garbage");
                l.clone()
            }
            SbF::A(i) => Lin::of(&[anc[i as usize]]),
            SbF::W0 => panic!("strip: W0 inside a form"),
        };
        out = out.x(&term);
    }
    out
}

/// Strip barrel. Forward (`inverse = false`): X (or X^) on `t` -> Y, wire 0 measured away (returns true).
/// Inverse: `t[0]` holds 1 (lr_restore) and Y on the rest -> X (or X^ when `sp` is given); returns false.
fn strip_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool, sp: Option<(QubitId, QubitId)>) -> bool {
    let w = t.len();
    let pat = sb_pat(inverse, sp.is_some(), w);
    let s = t[w - 1];
    let l = sp.map(|(b, s3)| Lin::of(&[b, s3])).unwrap_or_default();
    let mut anc: Vec<QubitId> = Vec::new();
    let mut recs: Vec<(QubitId, Lin, Lin)> = Vec::new();
    for (fa, fb) in pat.ands {
        let (a, b) = (sb_lin(fa, k1, k2, s, &l, &anc), sb_lin(fb, k1, k2, s, &l, &anc));
        let q = lin_and(c, &a, &b);
        anc.push(q);
        recs.push((q, a, b));
    }
    let m = w - 1;
    let pos = |e: SbE| -> usize {
        (match e { SbE::Lo(i) => i as i64, SbE::Mid(i) => (w / 2) as i64 + i as i64, SbE::Hi(i) => w as i64 + i as i64 }) as usize
    };
    let xs = [1usize, 0, w - 3];
    let removed = |st: usize, a: usize, b: usize| (st == 0 && (a, b) == (0, 1)) || (!inverse && st == 2 && (a, b) == (0, w - 3));
    let fill = |c: &mut Builder, bd: u8, anc: &[QubitId]| {
        let mut list: Vec<(usize, &'static [SbF])> = Vec::new();
        for &(b, tg, fs) in pat.ops.iter().filter(|o| o.0 == bd) {
            let _ = b;
            match tg {
                SbT::One(p) => list.push((if p < 0 { (w as i64 + p as i64) as usize } else { p as usize }, fs)),
                SbT::Blk(lo, hi) => (pos(lo)..=pos(hi)).for_each(|p| list.push((p, fs))),
            }
        }
        // forward: the CNOTs from wire 0 (w0 = [e = 0]) run first; inverse: the exact reverse of the forward order
        // (a per-width table may XOR into the sign wire at a boundary whose other fills read S)
        list.sort_by_key(|(_, fs)| fs[0] != SbF::W0);
        if inverse {
            list.reverse();
        }
        for (p, fs) in list {
            if fs[0] == SbF::W0 {
                assert!(p != 0);
                c.cx(t[0], t[p]);
            } else {
                lin_xor_into(c, &sb_lin(fs, k1, k2, s, &l, anc), t[p]);
            }
        }
    };
    let stage = |c: &mut Builder, st: usize| {
        let pairs: Vec<(usize, usize)> = (0..m).filter_map(|i| { let j = (xs[st] + m - i % m) % m; (i < j).then_some((i, j)) }).collect();
        if st == 1 {
            c.cx(k1, k2);
        }
        let ctrl = if st == 0 { k1 } else { k2 };
        for (a, b) in pairs {
            if !removed(st, a, b) {
                fredkin(c, ctrl, t[a], t[b]);
            }
        }
        if st == 1 {
            c.cx(k1, k2);
        }
    };
    if !inverse {
        for bd in 0..4u8 {
            fill(c, bd, &anc);
            if bd < 3 {
                stage(c, bd as usize);
            }
        }
        let mb = c.alloc_bit();
        c.hmr(t[0], mb);
        for (fa, fb) in pat.phase {
            let (a, b) = (sb_lin(fa, k1, k2, s, &l, &anc), sb_lin(fb, k1, k2, s, &l, &anc));
            if b.w.is_empty() && !b.one {
                let h = a.w[0];
                lin_on(c, &a, h);
                c.z_if(h, mb);
                lin_off(c, &a, h);
            } else {
                let (ha, hb) = lin_pair_on(c, &a, &b);
                c.cz_if(ha, hb, mb);
                lin_pair_off(c, &a, &b);
            }
        }
        c.free_bit(mb);
        c.release_clean(t[0]);
    } else {
        c.x(t[0]); // lr_restore left 1; the forward circuit ends with the preparable content below
        for (fa, _) in pat.phase {
            lin_xor_into(c, &sb_lin(fa, k1, k2, s, &l, &anc), t[0]);
        }
        for bd in (0..4u8).rev() {
            if bd < 3 {
                stage(c, bd as usize);
            }
            fill(c, bd, &anc);
        }
    }
    for (q, a, b) in recs.into_iter().rev() {
        lin_and_erase(c, q, &a, &b);
    }
    !inverse
}

// generated by round11/rail-strip/scripts/codegen.py from the exhaustively checked runs/pattern_*.json
static SB_FWD_EVEN: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::S], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(0), &[SbF::S]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::W0]),
        (0, SbT::One(2), &[SbF::One]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::K1]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::A(0)]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::S]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::A(0)]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-2)), &[SbF::S]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::S]),
        (3, SbT::Blk(SbE::Lo(1), SbE::Mid(-2)), &[SbF::S]),
    ],
    phase: &[(&[SbF::K1], &[SbF::K2])],
};

static SB_FWD_ODD: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::S], &[SbF::One, SbF::K2]), (&[SbF::One, SbF::S], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::S]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::K2]),
        (0, SbT::One(2), &[SbF::S]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::S]),
        (0, SbT::One(3), &[SbF::A(1)]),
        (2, SbT::One(1), &[SbF::A(0)]),
        (2, SbT::One(2), &[SbF::A(0)]),
    ],
    phase: &[(&[SbF::K1], &[SbF::K2])],
};

static SB_FWDG_EVEN: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::K1], &[SbF::One, SbF::K1, SbF::S, SbF::L])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(0), &[SbF::S, SbF::L]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::W0]),
        (0, SbT::One(2), &[SbF::One]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::K1]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::A(0)]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::S, SbF::L]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::A(0)]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-2)), &[SbF::S, SbF::L]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::S, SbF::L]),
        (3, SbT::Blk(SbE::Lo(1), SbE::Mid(-2)), &[SbF::S, SbF::L]),
    ],
    phase: &[(&[SbF::K1], &[SbF::K2])],
};

static SB_FWDG_ODD: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::K2], &[SbF::One, SbF::K2, SbF::S, SbF::L]), (&[SbF::One, SbF::K1], &[SbF::One, SbF::K1, SbF::S, SbF::L])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::S, SbF::L]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::K2]),
        (0, SbT::One(2), &[SbF::S, SbF::L]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::S, SbF::L]),
        (0, SbT::One(3), &[SbF::A(1)]),
        (2, SbT::One(1), &[SbF::A(0)]),
        (2, SbT::One(2), &[SbF::A(0)]),
    ],
    phase: &[(&[SbF::K1], &[SbF::K2])],
};

static SB_REV_EVEN: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::S], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(0), &[SbF::S]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::W0]),
        (0, SbT::One(2), &[SbF::A(0)]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::S]),
        (0, SbT::One(3), &[SbF::A(0)]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::One(-3), &[SbF::One]),
        (0, SbT::One(-3), &[SbF::K1]),
        (0, SbT::One(-3), &[SbF::A(0)]),
        (0, SbT::One(-2), &[SbF::K1]),
        (0, SbT::One(-2), &[SbF::K2]),
        (0, SbT::One(-2), &[SbF::S]),
        (0, SbT::One(-2), &[SbF::A(0)]),
        (0, SbT::One(-2), &[SbF::W0]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::A(0)]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::One]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::K1]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::S]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::A(0)]),
        (2, SbT::One(2), &[SbF::S]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-2)), &[SbF::S]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::S]),
        (3, SbT::One(-3), &[SbF::K1]),
        (3, SbT::One(-3), &[SbF::S]),
        (3, SbT::Blk(SbE::Lo(1), SbE::Mid(-2)), &[SbF::S]),
    ],
    phase: &[],
};

static SB_REV_ODD: SbPat = SbPat {
    ands: &[(&[SbF::One, SbF::S], &[SbF::One, SbF::K2]), (&[SbF::One, SbF::S], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::S]),
        (0, SbT::One(0), &[SbF::A(0)]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::S]),
        (0, SbT::One(2), &[SbF::One]),
        (0, SbT::One(2), &[SbF::K2]),
        (0, SbT::One(2), &[SbF::S]),
        (0, SbT::One(2), &[SbF::A(1)]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::K1]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::One(-2), &[SbF::One]),
        (0, SbT::One(-2), &[SbF::K2]),
        (0, SbT::One(-2), &[SbF::W0]),
        (2, SbT::One(1), &[SbF::A(0)]),
        (3, SbT::One(-3), &[SbF::K1]),
    ],
    phase: &[],
};

static SB_REVG_EVEN: SbPat = SbPat {
    ands: &[(&[SbF::S, SbF::L], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(0), &[SbF::L]),
        (0, SbT::One(0), &[SbF::S]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::W0]),
        (0, SbT::One(2), &[SbF::One]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::A(0)]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::K1]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::S]),
        (0, SbT::One(3), &[SbF::A(0)]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::One(-3), &[SbF::L]),
        (0, SbT::One(-3), &[SbF::A(0)]),
        (0, SbT::One(-2), &[SbF::One]),
        (0, SbT::One(-2), &[SbF::K2]),
        (0, SbT::One(-2), &[SbF::L]),
        (0, SbT::One(-2), &[SbF::S]),
        (0, SbT::One(-2), &[SbF::A(0)]),
        (0, SbT::One(-2), &[SbF::W0]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::A(0)]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::L]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::S]),
        (0, SbT::Blk(SbE::Lo(0), SbE::Mid(0)), &[SbF::A(0)]),
        (1, SbT::One(2), &[SbF::L]),
        (1, SbT::One(3), &[SbF::L]),
        (2, SbT::One(2), &[SbF::S]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-2)), &[SbF::L]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-2)), &[SbF::S]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::L]),
        (2, SbT::Blk(SbE::Lo(0), SbE::Mid(-1)), &[SbF::S]),
        (3, SbT::One(-3), &[SbF::K1]),
        (3, SbT::One(-3), &[SbF::S]),
        (3, SbT::Blk(SbE::Lo(1), SbE::Mid(-2)), &[SbF::L]),
        (3, SbT::Blk(SbE::Lo(1), SbE::Mid(-2)), &[SbF::S]),
    ],
    phase: &[],
};

static SB_REVG_ODD: SbPat = SbPat {
    ands: &[(&[SbF::S, SbF::L], &[SbF::One, SbF::K2]), (&[SbF::S, SbF::L], &[SbF::One, SbF::K1])],
    ops: &[
        (0, SbT::One(0), &[SbF::One]),
        (0, SbT::One(0), &[SbF::K1]),
        (0, SbT::One(0), &[SbF::K2]),
        (0, SbT::One(0), &[SbF::L]),
        (0, SbT::One(0), &[SbF::S]),
        (0, SbT::One(0), &[SbF::A(0)]),
        (0, SbT::One(1), &[SbF::One]),
        (0, SbT::One(1), &[SbF::K2]),
        (0, SbT::One(1), &[SbF::L]),
        (0, SbT::One(1), &[SbF::S]),
        (0, SbT::One(1), &[SbF::W0]),
        (0, SbT::One(2), &[SbF::One]),
        (0, SbT::One(2), &[SbF::K1]),
        (0, SbT::One(2), &[SbF::L]),
        (0, SbT::One(2), &[SbF::S]),
        (0, SbT::One(2), &[SbF::A(1)]),
        (0, SbT::One(2), &[SbF::W0]),
        (0, SbT::One(3), &[SbF::One]),
        (0, SbT::One(3), &[SbF::K1]),
        (0, SbT::One(3), &[SbF::K2]),
        (0, SbT::One(3), &[SbF::L]),
        (0, SbT::One(3), &[SbF::W0]),
        (0, SbT::One(-3), &[SbF::L]),
        (0, SbT::One(-2), &[SbF::One]),
        (0, SbT::One(-2), &[SbF::K2]),
        (0, SbT::One(-2), &[SbF::W0]),
        (1, SbT::One(2), &[SbF::L]),
        (1, SbT::One(3), &[SbF::L]),
        (2, SbT::One(1), &[SbF::A(0)]),
        (2, SbT::One(2), &[SbF::L]),
        (3, SbT::One(-3), &[SbF::K1]),
        (3, SbT::One(-3), &[SbF::L]),
    ],
    phase: &[],
};

