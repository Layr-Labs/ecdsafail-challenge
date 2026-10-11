use super::builder::B;
use super::frogdrop::crot_up;
use super::frogtail::{
    finish_digits2_test, finish_page_inverse_test, fwd_tick, init, Page, Sched, Scr, Walk, JB, QP,
    ccrot_up_test,
};
use super::pointadd_frogtail::SCHED_FROGTAIL;
use crate::circuit::QubitId;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}

/// The audited q907 owner ledger is 884 qubits without Q.  Replacing Q23 by
/// one standing page16 is exactly the requested q900 geometry.
#[test]
fn page16_owner_geometry() {
    let base = 308 + 308 + 256 + 5 + 1 + 6;
    assert_eq!(base, 884);
    assert_eq!(base + 16, 900);
}

/// Phase-safe ghost cleanup pattern required by every discarded page bit.
/// Exercise forced all-zero, all-one and alternating HMR outcomes across 64
/// independent source values.  The source and output scratch are restored.
#[test]
fn page16_forced_measurement_receipt_pattern() {
    for byte in [0u8, 255, 170, 85] {
        let mut b = B::new();
        let source = b.alloc();
        let q = b.alloc();
        let m = b.fresh_bits(1)[0];
        b.cx(source, q);
        b.hmr_to(q, m);
        b.cx(source, q);
        b.z_if(q, m);
        b.cx(source, q);
        let mut xof = Fixed(byte);
        let mut sim = Simulator::new(b.width() as usize, 10_002, &mut xof);
        sim.qubits[source.0 as usize] = 0x9e37_79b9_7f4a_7c15;
        let before = sim.qubits[source.0 as usize];
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.qubits[source.0 as usize], before);
        assert_eq!(sim.qubits[q.0 as usize], 0);
        assert_eq!(sim.phase, 0, "forced HMR byte={byte}");
    }
}

/// Exact whole-step value identity, accumulated in <=16-bit low-to-high pages.
/// This proves the arithmetic reorder only; it does not supply the missing
/// phase oracle after the source state changes.
#[test]
fn page16_whole_step_integer_identity() {
    let mut cases = 0usize;
    for m in 2usize..=23 {
        for seed in 1i128..=4096 {
            let bv = 2 * seed + 1;
            let av0 = (seed * 7919 + 17) | 1;
            let ac0 = (seed * 13 + 5) | 1;
            let bc0 = seed * 101 - 7000;
            let (mut av, mut ac, mut bc) = (av0, ac0, bc0);
            let mut digits = vec![];
            for i in 0..m {
                let a = av & 1;
                digits.push(a);
                if a != 0 {
                    if i + 1 == m {
                        av -= bv;
                        bc += ac;
                    } else {
                        av += bv;
                        bc -= ac;
                    }
                }
                assert_eq!(av & 1, 0);
                av >>= 1;
                ac <<= 1;
            }
            let mut paged_q = 0i128;
            for lo in (0..m).step_by(16) {
                for i in lo..(lo + 16).min(m) {
                    let term = digits[i] << i;
                    if i + 1 == m {
                        paged_q -= term;
                    } else {
                        paged_q += term;
                    }
                }
            }
            assert_eq!((av << m) - bv * paged_q, av0);
            assert_eq!(bc + (ac >> m) * paged_q, bc0);
            cases += 1;
        }
    }
    eprintln!("PAGE16_INTEGER cases={cases}");
}

/// A destructive odd-division column cannot be ghosted and forgotten without
/// another oracle: q=u0, u'=(u+q*b)/2 has collisions after q is removed.
#[test]
fn page16_column_needs_recomputation_oracle() {
    for n in 2usize..=12 {
        let lim = 1usize << n;
        let mut collisions = 0usize;
        for b in (1..lim).step_by(2) {
            let mut seen = std::collections::HashMap::<usize, (usize, usize)>::new();
            for u in 0..lim {
                let q = u & 1;
                let up = (u + q * b) >> 1;
                if let Some((old_u, old_q)) = seen.insert(up, (u, q)) {
                    if old_u != u && old_q != q {
                        collisions += 1;
                    }
                }
            }
        }
        assert!(collisions > 0, "n={n}");
        eprintln!("PAGE16_COLUMN n={n} collisions={collisions}");
    }
}

fn put_u64(words: &mut [u64], qs: &[QubitId], shot: usize, value: u64) {
    for (i, q) in qs.iter().enumerate() {
        words[q.0 as usize] |= ((value >> i) & 1) << shot;
    }
}

fn get_u64(words: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter()
        .enumerate()
        .map(|(i, q)| ((words[q.0 as usize] >> shot) & 1) << i)
        .fold(0, |a, b| a | b)
}

/// Source-bound core of the asynchronous-frame ABI.  A value batch-inverted
/// at global frame t can be physically pre-rotated by its quantum countdown g
/// so that the unchanged compiler view at frame t-g decodes the same value.
/// This test uses a superposition of all g=0..3 across packed shots.
#[test]
fn page16_quantum_frame_precompensation() {
    const N: usize = 16;
    const T: usize = 11;
    let mut b = B::new();
    let ring = b.alloc_n(N);
    let g = b.alloc_n(2);
    for k in 0..2 {
        crot_up(&mut b, g[k], &ring, N - (1 << k));
    }
    let mut xof = Fixed(0);
    let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
    let mut expected = [0u64; 64];
    for shot in 0..64 {
        let gap = shot & 3;
        let value = ((shot as u64 * 0x9e37) ^ 0xa55a) & 0xffff;
        expected[shot] = value;
        let start_frame: Vec<QubitId> = (0..N).map(|f| ring[(f + T - 1) % N]).collect();
        put_u64(&mut sim.qubits, &start_frame, shot, value);
        put_u64(&mut sim.qubits, &g, shot, gap as u64);
    }
    sim.apply_iter(b.ops.iter());
    for shot in 0..64 {
        let gap = shot & 3;
        let join_t = T - gap;
        let join_frame: Vec<QubitId> = (0..N).map(|f| ring[(f + join_t - 1) % N]).collect();
        assert_eq!(get_u64(&sim.qubits, &join_frame, shot), expected[shot], "shot={shot} gap={gap}");
    }
    assert_eq!(sim.phase, 0);
}

#[test]
fn page16_full_ring_precompensation_price() {
    const N: usize = 308;
    let mut b = B::new();
    let ring = b.alloc_n(N);
    let g = b.alloc_n(5);
    for k in 0..5 {
        crot_up(&mut b, g[k], &ring, N - (1 << k));
    }
    eprintln!("PAGE16_FRAME_PRICE n={N} emitted_t={} ops={}", b.tof, b.ops.len());
    assert!(b.tof > 0);
}

/// Page21 keeps the raw gap in five page lanes.  At the step-start boundary
/// the existing half-counter encodes h=(g-(t mod2))/2, so the page gap clears
/// with Clifford gates only; no quotient/support narrowing is involved.
#[test]
fn page21_gap_clears_from_half_counter() {
    for parity in 0usize..=1 {
        let mut b = B::new();
        let h = b.alloc_n(5);
        let pg = b.alloc_n(5);
        if parity == 1 {
            b.x(pg[0]);
        }
        for k in 1..5 {
            b.cx(h[k - 1], pg[k]);
        }
        let mut xof = Fixed(0);
        let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
        let mut shot = 0usize;
        for g in 0usize..=22 {
            if g & 1 != parity {
                continue;
            }
            let hh = (g - parity) / 2;
            put_u64(&mut sim.qubits, &h, shot, hh as u64);
            put_u64(&mut sim.qubits, &pg, shot, g as u64);
            shot += 1;
        }
        sim.apply_iter(b.ops.iter());
        for k in 0..shot {
            assert_eq!(get_u64(&sim.qubits, &pg, k), 0, "parity={parity} shot={k}");
        }
        assert_eq!(sim.phase, 0);
    }
}

/// At a page boundary the remaining quotient is again the unique odd word
/// -L/b modulo 2^r.  Exhaust all b,L words through r=8 and verify that a
/// refill followed by the defining relation is exact.
#[test]
fn page21_tail_refill_integer_identity() {
    let mut cases = 0usize;
    for r in 1usize..=8 {
        let modulus = 1usize << r;
        for b in (1..modulus).step_by(2) {
            let inv = (1..modulus).step_by(2).find(|u| (u * b) % modulus == 1).unwrap();
            for l in 0..modulus {
                let q = (modulus - (l * inv) % modulus) % modulus;
                assert_eq!((q * b + l) % modulus, 0);
                cases += 1;
            }
        }
    }
    eprintln!("PAGE21_TAIL cases={cases} max_r=8");
}

struct FinishFixture {
    b: B,
    x: Vec<QubitId>,
    a: Vec<QubitId>,
    bb: Vec<QubitId>,
    j: Vec<QubitId>,
    par: QubitId,
    q: Vec<QubitId>,
}

fn build_finish_fixture(tick: usize, paged: bool) -> FinishFixture {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let mut bb = x.clone();
    bb.extend(b.alloc_n(sch.wb - x.len()));
    let mut w = Walk {
        a: b.alloc_n(sch.wa),
        bb,
        q: vec![],
        j: b.alloc_n(JB),
        par: b.alloc(),
    };
    let dirty = b.alloc_n(64);
    let scf = Scr::alloc_fwd(&mut b, &dirty, 0);
    init(&mut b, &w);
    for t in 1..=tick {
        let m = b.fresh_bits(1)[0];
        fwd_tick(&mut b, &w, t, &sch, &scf, m);
    }
    scf.release(&mut b);
    let sci = Scr::alloc(&mut b, &dirty);
    let q = if paged {
        let page = Page { q: b.alloc_n(QP), low1: b.alloc() };
        let bs = b.fresh_bits(2);
        finish_page_inverse_test(&mut b, &w, &page, tick, &sch, &sci, [bs[0], bs[1]]);
        page.qfr(tick)
    } else {
        w.q = b.alloc_n(23);
        b.begin();
        finish_digits2_test(&mut b, &w, tick, &sch, &sci);
        let r = b.end();
        b.play(&r, true);
        w.qfr(tick)[2..].to_vec()
    };
    FinishFixture {
        b,
        x,
        a: w.a,
        bb: w.bb,
        j: w.j,
        par: w.par,
        q,
    }
}

fn put_word256(words: &mut [u64], qs: &[QubitId], shot: usize, limbs: [u64; 4]) {
    for (i, q) in qs.iter().enumerate() {
        words[q.0 as usize] |= ((limbs[i / 64] >> (i % 64)) & 1) << shot;
    }
}

/// Compare the new first-page construction against the inherited full-Q
/// eraser at one actual even tick before attempting another whole E2E run.
#[test]
fn page21_first_selected_step_matches_full_q() {
    let tick = 300usize;
    let full = build_finish_fixture(tick, false);
    let page = build_finish_fixture(tick, true);
    let mut xf = Fixed(0);
    let mut xp = Fixed(0);
    let mut sf = Simulator::new(full.b.width() as usize, 20_000, &mut xf);
    let mut sp = Simulator::new(page.b.width() as usize, 20_000, &mut xp);
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    for shot in 0..64 {
        let mut limbs = [0u64; 4];
        for x in &mut limbs {
            s ^= s << 7;
            s ^= s >> 9;
            s ^= s << 8;
            *x = s;
        }
        limbs[0] |= 1;
        put_word256(&mut sf.qubits, &full.x, shot, limbs);
        put_word256(&mut sp.qubits, &page.x, shot, limbs);
    }
    sf.apply_iter(full.b.ops.iter());
    sp.apply_iter(page.b.ops.iter());
    let mut selected = 0usize;
    for shot in 0..64 {
        let fq = get_u64(&sf.qubits, &full.q, shot);
        let pq = get_u64(&sp.qubits, &page.q, shot);
        if fq != 0 {
            selected += 1;
            assert_eq!(pq, fq, "tick={tick} shot={shot} full={fq:#x} page={pq:#x}");
        } else {
            assert_eq!(pq, 0, "off-branch page write shot={shot}");
        }
        for (ix, (fa, pa)) in full.a.iter().zip(&page.a).enumerate() {
            assert_eq!((sf.qubits[fa.0 as usize] >> shot) & 1, (sp.qubits[pa.0 as usize] >> shot) & 1, "A lane={ix} shot={shot} fullq={fq:#x}");
        }
        for (ix, (fb, pb)) in full.bb.iter().zip(&page.bb).enumerate() {
            assert_eq!((sf.qubits[fb.0 as usize] >> shot) & 1, (sp.qubits[pb.0 as usize] >> shot) & 1, "B lane={ix} shot={shot} fullq={fq:#x}");
        }
        assert_eq!(get_u64(&sf.qubits, &full.j, shot), get_u64(&sp.qubits, &page.j, shot));
        assert_eq!((sf.qubits[full.par.0 as usize] >> shot) & 1, (sp.qubits[page.par.0 as usize] >> shot) & 1);
    }
    eprintln!("PAGE21_FIRST tick={tick} selected={selected}");
    assert!(selected > 0);
}

#[test]
fn page21_double_controlled_rotation_matches_clean_helper() {
    const N: usize = 23;
    for r in [1usize, 2, 4, 8, 16, 22] {
        let mut a = B::new();
        let av = a.alloc_n(N);
        let ac1 = a.alloc();
        let ac2 = a.alloc();
        let ah = a.alloc();
        a.and_c(ac1, ac2, ah);
        crot_up(&mut a, ah, &av, r);
        a.and_u(ac1, ac2, ah);

        let mut d = B::new();
        let dv = d.alloc_n(N);
        let dc1 = d.alloc();
        let dc2 = d.alloc();
        let dirty = d.alloc_n(4);
        ccrot_up_test(&mut d, dc1, dc2, &dv, r, &dirty);

        let mut xa = Fixed(0);
        let mut xd = Fixed(0);
        let mut sa = Simulator::new(a.width() as usize, 1, &mut xa);
        let mut sd = Simulator::new(d.width() as usize, 1, &mut xd);
        for shot in 0..64 {
            let value = ((shot as u64 * 0x51ed) ^ 0x52_4242) & ((1u64 << N) - 1);
            put_u64(&mut sa.qubits, &av, shot, value);
            put_u64(&mut sd.qubits, &dv, shot, value);
            if shot & 1 != 0 {
                sa.qubits[ac1.0 as usize] |= 1 << shot;
                sd.qubits[dc1.0 as usize] |= 1 << shot;
            }
            if shot & 2 != 0 {
                sa.qubits[ac2.0 as usize] |= 1 << shot;
                sd.qubits[dc2.0 as usize] |= 1 << shot;
            }
        }
        sa.apply_iter(a.ops.iter());
        sd.apply_iter(d.ops.iter());
        for shot in 0..64 {
            assert_eq!(get_u64(&sa.qubits, &av, shot), get_u64(&sd.qubits, &dv, shot), "r={r} shot={shot}");
        }
        assert_eq!(sa.phase, sd.phase, "r={r}");
        for q in dirty {
            assert_eq!(sd.qubits[q.0 as usize], 0, "r={r} dirty q{}", q.0);
        }
    }
}
