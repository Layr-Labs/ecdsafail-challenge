use super::*;
use super::super::frogdrop_col::rec;
use super::super::frogdrop_sched::N;
use super::super::tests_frogdrop::{run, Rng};

#[derive(Clone)]
struct Ports {
    p: Vec<QubitId>, ring: Vec<QubitId>, sz: Vec<QubitId>, sy: Vec<QubitId>,
    act: QubitId, top: QubitId, adj: QubitId, free: Vec<QubitId>, dirty: Vec<QubitId>,
    e: Vec<QubitId>, forward: usize,
}

fn bit(v: N, i: usize) -> bool { ((v >> i) & N::from(1u64)) != N::ZERO }
fn set(ws: &mut [u64], lane: QubitId, shot: usize, value: bool) {
    if value { ws[lane.0 as usize] |= 1u64 << shot; }
}
fn put(ws: &mut [u64], lanes: &[QubitId], shot: usize, value: N) {
    for (i, &lane) in lanes.iter().enumerate() { set(ws, lane, shot, bit(value, i)); }
}

/// Lower the actual `digit()` twice, with the N257 saved dirty gap and with
/// the N258 clean-gap source. A test-only stop isolates long division before
/// the payload's later phase transition, which needs a full Euclid state.
fn build(n: usize, szv: usize, syv: usize, saved: bool) -> (B, Ports) {
    let mut b = B::new();
    let p = b.alloc_n(NP);
    let ring = b.alloc_n(n);
    let sz = b.alloc_n(9);
    let sy = b.alloc_n(8);
    let act = b.alloc();
    let top = b.alloc();
    let adj = b.alloc();
    let free = b.alloc_n(40);
    let dirty = b.alloc_n(24);
    let ds = dig_scr_z(&free, &sz, &sy, &dirty, false);
    let ph = Ph { ht: false, sz_mask: saved, virt_m1: false,
        rv: sz.clone(), rr: (szv, szv), tv: sy.clone(), tr: (syv, syv),
        src_r: ring.clone(), src_t: vec![] };
    let body = rec(&mut b, |b| {
        if saved {
            // The constant-size specialization of top_record: top=1 and
            // save=not q_g, followed by the offset-0 upper swap.
            b.x(top); b.cx(ring[szv - 1], top); b.cx(top, ring[szv - 1]);
            b.cswap(act, ring[szv], adj);
        }
        digit(b, &p, &ph, act, &ds, &dirty);
        if saved {
            b.cswap(act, ring[szv], adj);
            b.cx(top, ring[szv - 1]); b.cx(ring[szv - 1], top); b.x(top);
        }
    });
    b.play(&body, false);
    let forward = b.ops.len();
    b.play(&body, true);
    (b, Ports { p, ring, sz, sy, act, top, adj, free, dirty, e: ds.e, forward })
}

#[test]
fn c42_n257_relocated_hr_digit_all_wire() {
    std::env::set_var("D2_DIGIT_STOP", "divide");
    D2_DIGIT_TARGET.with(|t| t.set(true));
    let mut rng = Rng::new(0xc48d_1917);
    let mut cases: Vec<(usize, usize)> = (0..=22).map(|g| (g, 1 + (g * 17 % 128))).collect();
    cases.extend([(0, 128), (22, 128), (13, 21)]);
    for (g, syv) in cases {
        let szv = 257 - g - syv;
        let (candidate, cp) = build(257, szv, syv, true);
        let (reference, rp) = build(258, szv, syv, false);
        let mut cand_init = vec![0u64; candidate.width() as usize];
        let mut ref_init = vec![0u64; reference.width() as usize];
        let mut quotients = vec![N::ZERO; 64];
        let mut remainders = vec![N::ZERO; 64];
        let mut acts = vec![false; 64];
        for shot in 0..64 {
            let r = rng.below(szv - 1) | (N::from(1u64) << (szv - 1));
            let d = rng.below(szv + g);
            let q = d / r;
            quotients[shot] = q;
            remainders[shot] = d % r;
            acts[shot] = shot % 8 != 0;
            for (init, port) in [(&mut cand_init, &cp), (&mut ref_init, &rp)] {
                put(init, &port.p, shot, d);
                put(init, &port.sz, shot, N::from(szv));
                put(init, &port.sy, shot, N::from(syv));
                set(init, port.act, shot, acts[shot]);
                for &wire in &port.dirty { set(init, wire, shot, rng.next() & 1 != 0); }
            }
            put(&mut ref_init, &rp.ring, shot, r);
            // Q occupies Z's flipped top and the gap; a bounded remainder
            // supplies dirty upper passengers, including live adjacent bits.
            for i in 0..szv - 1 { set(&mut cand_init, cp.ring[i], shot, bit(r, i)); }
            set(&mut cand_init, cp.ring[szv - 1], shot, bit(q, g));
            for kk in 0..g { set(&mut cand_init, cp.ring[szv - 1 + g - kk], shot, bit(q, kk)); }
            let rem_bits = syv.min(256 - szv);
            let upper = rng.below(rem_bits);
            for i in 0..rem_bits {
                let pos = szv + g + i;
                if pos < 257 { set(&mut cand_init, cp.ring[pos], shot, bit(upper, i)); }
            }
        }
        let cf = run(&candidate.ops[..cp.forward], candidate.width() as usize,
            &|ws| ws[..cand_init.len()].copy_from_slice(&cand_init));
        let rf = run(&reference.ops[..rp.forward], reference.width() as usize,
            &|ws| ws[..ref_init.len()].copy_from_slice(&ref_init));
        assert_eq!(cf.phase, 0, "candidate phase g={g} sy={syv}");
        assert_eq!(rf.phase, 0, "reference phase g={g} sy={syv}");
        for (port, initial, got) in [(&cp, &cand_init, &cf.q), (&rp, &ref_init, &rf.q)] {
            for &wire in port.ring.iter().chain(&port.sz).chain(&port.sy).chain(&port.dirty)
                .chain([&port.act, &port.top, &port.adj]) {
                assert_eq!(got[wire.0 as usize], initial[wire.0 as usize],
                    "passenger wire {:?} g={g} sy={syv}", wire);
            }
            for &wire in port.free.iter().filter(|q| !port.e.contains(q)) {
                assert_eq!(got[wire.0 as usize], 0, "scratch {:?} g={g} sy={syv}", wire);
            }
        }
        for i in 0..NP {
            assert_eq!(cf.q[cp.p[i].0 as usize], rf.q[rp.p[i].0 as usize],
                "payload lane {i} g={g} sy={syv}");
        }
        for shot in 0..64 {
            for k in 0..KE {
                let expected = acts[shot] && bit(quotients[shot], k);
                assert_eq!((cf.q[cp.e[k].0 as usize] >> shot) & 1 != 0, expected,
                    "quotient bit {k} shot {shot} g={g} sy={syv}");
            }
            if acts[shot] {
                for i in 0..szv {
                    assert_eq!((cf.q[cp.p[i].0 as usize] >> shot) & 1 != 0,
                        bit(remainders[shot], i), "remainder bit {i} g={g} sy={syv}");
                }
            }
        }
        let ci = run(&candidate.ops, candidate.width() as usize,
            &|ws| ws[..cand_init.len()].copy_from_slice(&cand_init));
        let ri = run(&reference.ops, reference.width() as usize,
            &|ws| ws[..ref_init.len()].copy_from_slice(&ref_init));
        assert_eq!(ci.phase, 0, "candidate inverse phase g={g} sy={syv}");
        assert_eq!(ri.phase, 0, "reference inverse phase g={g} sy={syv}");
        assert_eq!(&ci.q[..cand_init.len()], cand_init, "candidate inverse wires g={g} sy={syv}");
        assert_eq!(&ri.q[..ref_init.len()], ref_init, "reference inverse wires g={g} sy={syv}");
    }
    D2_DIGIT_TARGET.with(|t| t.set(false));
    std::env::remove_var("D2_DIGIT_STOP");
}
