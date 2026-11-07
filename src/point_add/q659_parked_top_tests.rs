//! Test child of point_add::normalized_cross_arithmetic.
//! Executes the pinned two-register frame and the pinned private Top(j)
//! witness against a compact 129-lane Q / 257-lane ring frame. A compact
//! entry needs a valid leading-marker pair wherever the witness can act.
use super::super::{
    cross_four::Roles, frogdrop, frogdrop_sched, normalized_cross_frame, pointadd_frogdrop,
    sum_size::SumSize,
};
use super::{bank, witness, Cross, Gate, QubitId, B, G};
include!("q659_cross_word_tests.rs");

fn packed_frame(b: &mut B, low: &[QubitId; 6], q: &[QubitId], ring: &[QubitId]) -> Vec<G> {
    assert_eq!((q.len(), ring.len()), (129, 257));
    b.begin();
    for (k, &bit) in low.iter().enumerate() {
        let shift = 1 << k;
        b.x(bit);
        frogdrop::crot_up(b, bit, q, shift);
        frogdrop::crot_up(b, bit, ring, 257 - shift);
        b.x(bit);
    }
    // gcd(129,64)=1. Delete 127 from the single 129-cycle. Its predecessor
    // 63 is 1 on a short input, whereas its successor must receive the old
    // zero from 127. Flipping 62 corrects that one displaced value.
    let half_cycle: Vec<_> = (0..129)
        .map(|i| (i * 64) % 129)
        .filter(|&i| i != 127)
        .collect();
    let high = q[127];
    b.x(high);
    for pair in half_cycle.windows(2).rev() {
        b.cswap(high, q[pair[1]], q[pair[0]]);
    }
    b.cx(high, q[62]);
    frogdrop::crot_up(b, high, ring, 257 - 64);
    b.x(high);
    b.end()
}

struct Circuit {
    low: [QubitId; 6],
    sum: [QubitId; 5],
    q: Vec<QubitId>,
    ring: Vec<QubitId>,
    a: QubitId,
    e: QubitId,
    high: Option<QubitId>,
    width: usize,
    frame: Vec<G>,
    guards: Vec<Vec<G>>,
}

fn circuit(parent: bool) -> Circuit {
    let mut b = B::new();
    let low: [QubitId; 6] = b.alloc_n(6).try_into().unwrap();
    let sum: [QubitId; 5] = b.alloc_n(5).try_into().unwrap();
    let q = b.alloc_n(129);
    let ring = b.alloc_n(257);
    let a = b.alloc();
    let e = b.alloc();
    let mask = b.alloc();
    let phase = b.alloc();
    let high = parent.then(|| b.alloc());
    let length_msb = high.unwrap_or(q[127]);
    let size = SumSize {
        y: [low[0], low[1], low[2], low[3], low[4], low[5], length_msb],
        sum,
    };
    let schedule = frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let col = &schedule.cols[97];
    assert!(col.ht && col.sy.0 <= 63 && col.sy.1 >= 127 && col.sz.0 <= 128 && col.sz.1 >= 192);
    let bounds = (col.sy.0.max(1), col.sy.1.min(128));
    assert_eq!(bounds, (1, 128));
    let ctx = Cross {
        size: &size,
        ring: &ring,
        q: &q[..128],
        phase,
        roles: Roles {
            activity: a,
            flight: e,
            mask,
            x128: q[128],
        },
        dirty: &[],
        y_bounds: bounds,
        qb: 30,
        clean_external: &[],
    };
    let frame = if parent {
        normalized_cross_frame::record(&mut b, &ctx)
    } else {
        packed_frame(&mut b, &low, &q, &ring)
    };
    // Only witness and bank read this view. Other Cross kernels still require
    // separate E6 and q127 owners; their existing nonalias checks stay intact.
    let dirty = bank(&ctx);
    let guards = (0..15)
        .map(|j| witness(&mut b, &ctx, Gate::Top(j), &dirty))
        .collect();
    Circuit {
        low,
        sum,
        q,
        ring,
        a,
        e,
        high,
        width: b.width() as usize,
        frame,
        guards,
    }
}

fn apply(gates: &[G], state: &mut [u64], inverse: bool) {
    let mut gate = |g: &G| match *g {
        G::X(t) => state[t.0 as usize] ^= u64::MAX,
        G::Cx(c, t) => state[t.0 as usize] ^= state[c.0 as usize],
        G::Ccx(a, c, t) => state[t.0 as usize] ^= state[a.0 as usize] & state[c.0 as usize],
        G::Swap(a, c) => state.swap(a.0 as usize, c.0 as usize),
        _ => panic!("non-NCT gate in crossing fixture: {g:?}"),
    };
    if inverse {
        for g in gates.iter().rev() {
            gate(g);
        }
    } else {
        for g in gates {
            gate(g);
        }
    }
}

fn put(w: &mut [u64], wire: QubitId, lane: usize, b: bool) {
    let mask = 1u64 << lane;
    let word = &mut w[wire.0 as usize];
    *word = (*word & !mask) | if b { mask } else { 0 };
}
fn bit(w: &[u64], wire: QubitId, lane: usize) -> bool {
    (w[wire.0 as usize] >> lane) & 1 != 0
}
fn random(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}
fn numbers(c: &Circuit, w: &mut [u64], lane: usize, y: usize, s: usize) {
    for (k, &q) in c.low.iter().enumerate() {
        put(w, q, lane, (y - 1) >> k & 1 != 0);
    }
    for (k, &q) in c.sum.iter().enumerate() {
        put(w, q, lane, s >> k & 1 != 0);
    }
    put(w, c.high.unwrap(), lane, y >= 65);
}
fn ccx(tape: &[G]) -> usize {
    tape.iter().filter(|g| matches!(g, G::Ccx(..))).count()
}

#[test]
fn q659_parked_crossing_top_guards() {
    let old = circuit(true);
    let new = circuit(false);
    assert_eq!(old.width, new.width + 1);
    assert_eq!(old.high.unwrap().0 as usize, new.width);
    assert_eq!((ccx(&old.frame), ccx(&new.frame)), (2688, 2687));
    let mut seed = 0xd1d204ab6d97e81bu64;
    let mut total_states = 0usize;
    let mut dirty_disabled = 0usize;
    let mut skipped = 0usize;
    let mut complete_closed = 0usize;
    let mut arbitrary_disabled_frame_differences = 0u32;
    for mode in 0..3 {
        // Every Y=1..128 and S=0..31 occurs once per mode.
        for batch in 0..64 {
            let mut source: Vec<u64> = (0..old.width).map(|_| random(&mut seed)).collect();
            let mut ys = [0usize; 64];
            let mut ss = [0usize; 64];
            let mut valid = 0u64;
            for lane in 0..64 {
                let key = 64 * batch + lane;
                let y = key / 32 + 1;
                let s = key % 32;
                ys[lane] = y;
                ss[lane] = s;
                numbers(&old, &mut source, lane, y, s);
                let active = mode == 0 || (mode == 1 && (batch + lane) % 3 != 0);
                put(&mut source, old.a, lane, active);
                // Mode 1 additionally checks all four abstract inputs to the
                // witness when markers are available. Only e=0 is promised
                // for a fresh active body. Mode 2 has off-A arbitrary raw Q.
                let flight = mode == 1 && (batch + lane) % 2 == 1;
                put(&mut source, old.e, lane, flight);
                if mode != 2 {
                    valid |= 1u64 << lane;
                    put(&mut source, old.q[y - 1], lane, true);
                    // q0..q14 may occupy their in-place lanes, including
                    // x128. Values above the legal park band must be zero.
                    for i in y.saturating_add(15)..129 {
                        put(&mut source, old.q[i], lane, false);
                    }
                } else {
                    dirty_disabled += 1;
                }
            }
            let mut of = source.clone();
            let mut nf = source[..new.width].to_vec();
            apply(&old.frame, &mut of, false);
            apply(&new.frame, &mut nf, false);
            for (wire, (&x, &y)) in of.iter().zip(nf.iter()).enumerate() {
                if wire == old.q[127].0 as usize {
                    assert_eq!(x & valid, valid);
                    assert_eq!(y & valid, source[old.high.unwrap().0 as usize] & valid);
                } else {
                    assert_eq!((x ^ y) & valid, 0, "frame wire {wire} mode {mode}");
                }
            }
            if mode == 2 {
                for &r in &old.ring {
                    arbitrary_disabled_frame_differences +=
                        (of[r.0 as usize] ^ nf[r.0 as usize]).count_ones();
                }
            }
            for j in 0..15 {
                assert_eq!(ccx(&old.guards[j]), ccx(&new.guards[j]));
                let mut og = of.clone();
                let mut ng = nf.clone();
                apply(&old.guards[j], &mut og, false);
                apply(&new.guards[j], &mut ng, false);
                let mut want_a = 0u64;
                let mut want_e = 0u64;
                for lane in 0..64 {
                    let pass = ys[lane] + j <= 128 && ss[lane] + j <= 31;
                    let a = bit(&source, old.a, lane);
                    let e = bit(&source, old.e, lane);
                    // The source's two-CX sandwich for a failed gate sends
                    // (A,e) to (e,e xor A), including e=1 algebraic cases.
                    let (a1, e1) = if pass { (a, e) } else { (e, e ^ a) };
                    want_a |= u64::from(a1) << lane;
                    want_e |= u64::from(e1) << lane;
                    if !pass && a && !e {
                        skipped += 1;
                    }
                }
                for (guarded, opened) in [(&og, &of), (&ng, &nf)] {
                    for w in 0..opened.len() {
                        let want = if w == old.a.0 as usize {
                            want_a
                        } else if w == old.e.0 as usize {
                            want_e
                        } else {
                            opened[w]
                        };
                        assert_eq!(
                            guarded[w], want,
                            "Top({j}) mode={mode} batch={batch} wire={w}"
                        );
                    }
                }
                if j == 2 {
                    let mut oc = og.clone();
                    let mut nc = ng.clone();
                    apply(&old.frame, &mut oc, true);
                    apply(&new.frame, &mut nc, true);
                    assert_eq!(&oc[..new.width], nc.as_slice(), "closed frame");
                    assert_eq!(
                        oc[old.high.unwrap().0 as usize],
                        source[old.high.unwrap().0 as usize]
                    );
                    for (w, &x) in nc.iter().enumerate() {
                        if w != old.a.0 as usize && w != old.e.0 as usize {
                            assert_eq!(x, source[w]);
                        }
                    }
                    complete_closed += 64;
                }
                // Literal image inverse, including skipped (A=0,e=1) rows.
                apply(&old.guards[j], &mut og, true);
                apply(&new.guards[j], &mut ng, true);
                assert_eq!(of, og);
                assert_eq!(nf, ng);
                total_states += 64;
            }
            apply(&old.frame, &mut of, true);
            apply(&new.frame, &mut nf, true);
            assert_eq!(of, source);
            assert_eq!(nf.as_slice(), &source[..new.width]);
        }
    }
    assert!(arbitrary_disabled_frame_differences > 0 && skipped > 0);
    println!("q659-cross129 Top(j) guarded_rows={total_states} complete_closed={complete_closed} dirty_disabled={dirty_disabled} skipped={skipped} raw_frame_ccx=2688/2687 widths={}/{} arbitrary_disabled_frame_differences={arbitrary_disabled_frame_differences}",old.width,new.width);
}

#[test]
fn q659_crossing_column97_alias_and_invalid_skip() {
    let old = circuit(true);
    let new = circuit(false);
    let mut raw = vec![0u64; old.width];
    // Compare the published column-97 interface pair, not full initialized
    // trajectories. Raw ring is arbitrary in this component experiment.
    for (lane, y, s, bits) in [
        (0usize, 63usize, 29usize, &[0usize, 62, 65][..]),
        (1usize, 127usize, 29usize, &[0usize, 64, 126][..]),
    ] {
        numbers(&old, &mut raw, lane, y, s);
        put(&mut raw, old.a, lane, true);
        for &i in bits {
            put(&mut raw, old.q[i], lane, true);
        }
    }
    // Deliberately outside inverse-image care: actual E says long but no
    // marker at e+64. Top(2) would be disabled by parent E. A=0,e=1 is
    // supplied as a synthetic inverse input with an incorrect Q encoding.
    numbers(&old, &mut raw, 2, 127, 29);
    put(&mut raw, old.e, 2, true);
    let mut a = raw.clone();
    let mut c = raw[..new.width].to_vec();
    apply(&old.frame, &mut a, false);
    apply(&new.frame, &mut c, false);
    for (i, &q) in old.q.iter().enumerate() {
        let ones = [1, 65, 127].contains(&i);
        assert_eq!(bit(&a, q, 0), ones);
        assert_eq!(bit(&a, q, 1), ones);
        assert_eq!(bit(&c, q, 0), ones && i != 127);
        assert_eq!(bit(&c, q, 1), ones);
    }
    let (mut wa, mut wc) = (a.clone(), c.clone());
    apply(&old.guards[2], &mut wa, false);
    apply(&new.guards[2], &mut wc, false);
    for st in [&wa, &wc] {
        assert!(bit(st, old.a, 0) && !bit(st, old.e, 0));
        assert!(!bit(st, old.a, 1) && bit(st, old.e, 1));
    }
    apply(&old.guards[2], &mut a, true);
    apply(&new.guards[2], &mut c, true);
    assert!(bit(&a, old.a, 2) && !bit(&a, old.e, 2));
    assert!(!bit(&c, old.a, 2) && bit(&c, old.e, 2));
    println!("q659-cross129 column=97 Y=63/127 S=29 Top(2)=pass/skip invalid_skip_detected=true");
}
