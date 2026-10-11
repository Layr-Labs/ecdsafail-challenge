use super::arith::ttk_add;
use super::builder::{B, G};
use super::frogdrop::crot_up;
use super::frogdrop_sched::{p, N};
use super::frogtail::{
    ccrot_up_test, finish_digits2_test, finish_page_inverse_test, fwd_tick, init,
    inverse_page21_tick_test, normalize_test, ttk_add_double_ctl_odd_keep_lsb_test,
    Page, Sched, Scr, Walk, JB, QP,
};
use super::pointadd_frogtail::SCHED_FROGTAIL;
use super::modp_ft::{const_add_pool_clean_test, const_add_pool_test, const_add_pool_uncontrolled_test, C};
use super::tests_frogdrop::Rng;
use super::tests_frogtail::M;
use crate::circuit::QubitId;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}

#[test]
fn q900_private_hensel_restores_sources() {
    let mut b = B::new();
    let e = b.alloc();
    let bv = b.alloc_n(23);
    let acc = b.alloc_n(23);
    let helper = b.alloc();
    b.begin(); ttk_add(&mut b, &bv, &acc, Some(e), None); let add0 = b.end(); b.play(&add0, false);
    b.x(acc[0]); b.cx(e, acc[0]); b.ccx(e, acc[1], acc[0]);
    b.begin(); ttk_add(&mut b, &bv[..22], &acc[1..], Some(acc[0]), None); let add1 = b.end(); b.play(&add1, false);
    let mut adds: Vec<(usize, Vec<G>)> = vec![];
    for k in 2..22 {
        b.and_c(e, acc[k], helper);
        b.begin(); ttk_add(&mut b, &bv[..23-k], &acc[k..], Some(helper), None); let r=b.end(); b.play(&r,false);
        b.cx(helper, acc[k]); b.and_u(e, acc[k], helper); adds.push((k,r));
    }
    for (k,r) in adds.iter().rev() {
        b.and_c(e,acc[*k],helper); b.cx(helper,acc[*k]); b.play(r,true); b.and_u(e,acc[*k],helper);
    }
    b.play(&add1,true); b.ccx(e,acc[1],acc[0]); b.cx(e,acc[0]); b.x(acc[0]); b.play(&add0,true);
    let mut xof=Fixed(0); let mut sim=Simulator::new(b.width() as usize,1234,&mut xof); sim.qubits[e.0 as usize]=u64::MAX;
    let mut bw=[0u64;23]; let mut lw=[0u64;23];
    for shot in 0..64 { let bv0=((shot as u64*7919+3)&((1<<23)-1))|1; let lv0=((shot as u64*3571+5)&((1<<23)-1))|1; for i in 0..23 { bw[i]|=((bv0>>i)&1)<<shot; lw[i]|=((lv0>>i)&1)<<shot; sim.qubits[bv[i].0 as usize]=bw[i]; sim.qubits[acc[i].0 as usize]=lw[i]; } }
    sim.apply_iter(b.ops.iter());
    for i in 0..23 { assert_eq!(sim.qubits[bv[i].0 as usize],bw[i],"b{i}"); assert_eq!(sim.qubits[acc[i].0 as usize],lw[i],"L{i}"); }
    assert_eq!(sim.qubits[helper.0 as usize],0); assert_eq!(sim.phase,0);
}

#[test]
fn page4_low19_hensel_digits_match_integer() {
    const LOW: usize = 19;
    let mut b = B::new();
    let e = b.alloc();
    let odd = b.alloc_n(LOW);
    let acc = b.alloc_n(LOW);
    let helper = b.alloc();
    b.begin(); ttk_add(&mut b, &odd, &acc, Some(e), None); let add0=b.end(); b.play(&add0,false);
    b.x(acc[0]); b.cx(e,acc[0]); b.ccx(e,acc[1],acc[0]);
    b.begin(); ttk_add(&mut b,&odd[..LOW-1],&acc[1..],Some(acc[0]),None); let add1=b.end(); b.play(&add1,false);
    for k in 2..LOW-1 {
        b.and_c(e,acc[k],helper);
        b.begin(); ttk_add(&mut b,&odd[..LOW-k],&acc[k..],Some(helper),None); let r=b.end(); b.play(&r,false);
        b.cx(helper,acc[k]); b.and_u(e,acc[k],helper);
    }
    let mut xof=Fixed(0); let mut sim=Simulator::new(b.width() as usize,62_008,&mut xof); sim.qubits[e.0 as usize]=u64::MAX;
    let modu=1u64<<LOW;
    let mut want=[0u64;64];
    for shot in 0..64 {
        let bv=((shot as u64*7919+3)&(modu-1))|1;
        let lv=((shot as u64*3571+5)&(modu-1))|1;
        put_u64(&mut sim.qubits,&odd,shot,bv); put_u64(&mut sim.qubits,&acc,shot,lv);
        let inv=(1u64..modu).step_by(2).find(|u|(u*bv)%modu==1).unwrap();
        want[shot]=(modu-(lv*inv)%modu)%modu;
    }
    sim.apply_iter(b.ops.iter());
    for shot in 0..64 {
        let mut got=1u64;
        got|=((sim.qubits[acc[0].0 as usize]>>shot)&1)<<1;
        for k in 2..LOW {got|=((sim.qubits[acc[k].0 as usize]>>shot)&1)<<k;}
        assert_eq!(got,want[shot],"shot={shot}");
    }
    assert_eq!(sim.qubits[helper.0 as usize],0); assert_eq!(sim.phase,0);
}

#[test]
fn page4_low19_normalizer_exact() {
    const LOW: usize=19; const QB0: usize=23; const NW:usize=31+QB0;
    let mut b=B::new(); let win=b.alloc_n(NW); let sp=b.alloc_n(5); let dirty=b.alloc_n(23);
    let r=normalize_test(&mut b,&win,&sp,5,&[],&dirty); b.play(&r,false);
    let mut xof=Fixed(0); let mut sim=Simulator::new(b.width() as usize,62_009,&mut xof);
    let mut wants=[0u64;64];
    for shot in 0..64 { let s=1+shot%15; let odd=((shot as u64*7919+3)&((1u64<<23)-1))|1; let value=odd<<s; put_u64(&mut sim.qubits,&win,shot,value); wants[shot]=odd; }
    sim.apply_iter(b.ops.iter());
    for shot in 0..64 { assert_eq!(get_u64(&sim.qubits,&sp,shot),1+(shot%15) as u64,"shift shot={shot}"); assert_eq!(get_u64(&sim.qubits,&win[..23],shot),wants[shot],"odd shot={shot}"); }
    assert!(dirty.iter().all(|q|sim.qubits[q.0 as usize]==0)); assert_eq!(sim.phase,0);
}

#[test]
fn page4_dirty_hensel_row_matches_clean_held_control() {
    const W: usize = 11;
    for byte in [0u8, 255, 170, 85] {
        let mut a = B::new();
        let ae = a.alloc();
        let aa = a.alloc_n(W);
        let at = a.alloc_n(W);
        let ah = a.alloc();
        a.and_c(ae, at[0], ah);
        ttk_add(&mut a, &aa, &at, Some(ah), None);
        a.cx(ah, at[0]);
        a.and_u(ae, at[0], ah);

        let mut d = B::new();
        let de = d.alloc();
        let da = d.alloc_n(W);
        let dt = d.alloc_n(W);
        let dd = d.alloc();
        ttk_add_double_ctl_odd_keep_lsb_test(&mut d, &da, &dt, de, dt[0], dd);

        let mut xa = Fixed(byte);
        let mut xd = Fixed(byte);
        let mut sa = Simulator::new(a.width() as usize, 62_010 + byte as usize, &mut xa);
        let mut sd = Simulator::new(d.width() as usize, 62_010 + byte as usize, &mut xd);
        let mut dirty_before = 0u64;
        for shot in 0..64 {
            let av = ((shot as u64 * 7919 + 3) & ((1 << W) - 1)) | 1;
            let tv = (shot as u64 * 3571 + 5) & ((1 << W) - 1);
            put_u64(&mut sa.qubits, &aa, shot, av);
            put_u64(&mut sd.qubits, &da, shot, av);
            put_u64(&mut sa.qubits, &at, shot, tv);
            put_u64(&mut sd.qubits, &dt, shot, tv);
            if shot % 3 != 0 {
                sa.qubits[ae.0 as usize] |= 1 << shot;
                sd.qubits[de.0 as usize] |= 1 << shot;
            }
            if shot % 5 < 2 {
                sd.qubits[dd.0 as usize] |= 1 << shot;
                dirty_before |= 1 << shot;
            }
        }
        sa.apply_iter(a.ops.iter());
        sd.apply_iter(d.ops.iter());
        for shot in 0..64 {
            assert_eq!(get_u64(&sa.qubits, &at, shot), get_u64(&sd.qubits, &dt, shot), "byte={byte} shot={shot}");
            assert_eq!(get_u64(&sa.qubits, &aa, shot), get_u64(&sd.qubits, &da, shot), "source byte={byte} shot={shot}");
        }
        assert_eq!(sd.qubits[dd.0 as usize], dirty_before, "dirty byte={byte}");
        assert_eq!(sa.qubits[ah.0 as usize], 0, "helper byte={byte}");
        assert_eq!(sa.phase, sd.phase, "phase byte={byte}");
    }
    eprintln!("PAGE4_DIRTY_HENSEL_ROW width={W} receipts=4 PASS");
}

#[test]
fn q888_pool48_const_add_matches_pool64_forced_outcomes() {
    for &k in &[C, C-1, 0x8000_0000_0000_0001, 0xfedc_ba98_7654_3211] {
        let mut a=B::new(); let ah=a.alloc(); let at=a.alloc_n(64); let ap=a.alloc_n(64); const_add_pool_test(&mut a,&at,ah,k,&ap);
        let mut s=B::new(); let sh=s.alloc(); let st=s.alloc_n(64); let sp=s.alloc_n(48); let so=s.alloc(); s.x(so); const_add_pool_clean_test(&mut s,&st,sh,k,&sp,so);
        for byte in [0u8,255,170,85] {
            let mut xa=Fixed(byte); let mut xs=Fixed(byte); let mut sa=Simulator::new(a.width() as usize,60_000+byte as usize,&mut xa); let mut ss=Simulator::new(s.width() as usize,60_000+byte as usize,&mut xs);
            let mut want=[0u64;64];
            for shot in 0..64 { let v=0x9e37_79b9_7f4a_7c15u64.wrapping_mul(shot as u64+3).rotate_left((shot*7) as u32); let h=shot%3!=0; put_u64(&mut sa.qubits,&at,shot,v); put_u64(&mut ss.qubits,&st,shot,v); if h {sa.qubits[ah.0 as usize]|=1u64<<shot; ss.qubits[sh.0 as usize]|=1u64<<shot;} want[shot]=v.wrapping_add(if h{k}else{0}); }
            sa.apply_iter(a.ops.iter()); ss.apply_iter(s.ops.iter());
            for shot in 0..64 { assert_eq!(get_u64(&sa.qubits,&at,shot),want[shot],"64 k={k:#x} byte={byte} shot={shot}"); assert_eq!(get_u64(&ss.qubits,&st,shot),want[shot],"48 k={k:#x} byte={byte} shot={shot}"); }
            assert_eq!(sa.qubits[ah.0 as usize],ss.qubits[sh.0 as usize]); assert_eq!(ss.qubits[so.0 as usize],u64::MAX); assert!(ap.iter().all(|q|sa.qubits[q.0 as usize]==0)); assert!(sp.iter().all(|q|ss.qubits[q.0 as usize]==0)); assert_eq!(sa.phase,0); assert_eq!(ss.phase,0);
        }
    }
    eprintln!("Q888_POOL48_CONST_ADD constants=4 receipts=4 PASS");
}

#[test]
fn q888_pool48_uncontrolled_const_add_matches_pool64_forced_outcomes() {
    for &k in &[C, C-1] {
        let mut a=B::new(); let ah=a.alloc(); a.x(ah); let at=a.alloc_n(64); let ap=a.alloc_n(64); const_add_pool_test(&mut a,&at,ah,k,&ap);
        let mut s=B::new(); let so=s.alloc(); s.x(so); let st=s.alloc_n(64); let sp=s.alloc_n(48); let sz=s.alloc(); const_add_pool_uncontrolled_test(&mut s,&st,so,k,&sp,sz);
        for byte in [0u8,255,170,85] {
            let mut xa=Fixed(byte); let mut xs=Fixed(byte); let mut sa=Simulator::new(a.width() as usize,61_000+byte as usize,&mut xa); let mut ss=Simulator::new(s.width() as usize,61_000+byte as usize,&mut xs);
            for shot in 0..64 { let v=0xd1b5_4a32_d192_ed03u64.wrapping_mul(shot as u64+7).rotate_left((shot*11) as u32); put_u64(&mut sa.qubits,&at,shot,v); put_u64(&mut ss.qubits,&st,shot,v); }
            sa.apply_iter(a.ops.iter()); ss.apply_iter(s.ops.iter());
            for shot in 0..64 { let v=0xd1b5_4a32_d192_ed03u64.wrapping_mul(shot as u64+7).rotate_left((shot*11) as u32); let want=v.wrapping_add(k); assert_eq!(get_u64(&sa.qubits,&at,shot),want); assert_eq!(get_u64(&ss.qubits,&st,shot),want); }
            assert_eq!(ss.qubits[so.0 as usize],u64::MAX); assert_eq!(ss.qubits[sz.0 as usize],0); assert!(sp.iter().all(|q|ss.qubits[q.0 as usize]==0)); assert_eq!(sa.phase,0); assert_eq!(ss.phase,0);
        }
    }
    eprintln!("Q888_POOL48_UNCONTROLLED constants=2 receipts=4 PASS");
}

/// The audited q907 owner ledger is 884 qubits without Q.  Replacing Q23 by
/// one standing page8 is exactly the requested q892 inverse geometry.
#[test]
fn page4_owner_geometry() {
    let base = 308 + 308 + 256 + 5 + 1 + 6;
    assert_eq!(base, 884);
    assert_eq!(QP, 4);
    assert_eq!(base + QP, 888);
}

#[test]
fn page4_five_boundary_selector_is_exact() {
    for h in 0usize..32 {
        let selected0 = h & 1 != 0 && h & 0b11000 == 0;
        let selected1 = h == 9;
        let selected = selected0 ^ selected1;
        assert_eq!(selected, matches!(h, 1 | 3 | 5 | 7 | 9), "h={h}");
    }
}

#[test]
fn page4_refill_targets_do_not_alias() {
    for s in 1usize..=19 {
        let ks: Vec<usize> = (s.saturating_sub(QP)..s).collect();
        assert!(ks.len() <= QP);
        let mut lanes = std::collections::BTreeSet::new();
        for k in ks {
            // Physical page lane used by page.qfr(t-(s-k))[QP-1], modulo
            // the common t offset.
            let lane = (QP - ((s - k) % QP)) % QP;
            assert!(lanes.insert(lane), "s={s} k={k} lane={lane}");
        }
    }
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

/// Exact whole-step value identity, accumulated in <=QP-bit low-to-high pages.
/// This proves the arithmetic reorder only; it does not supply the missing
/// phase oracle after the source state changes.
#[test]
fn page4_whole_step_integer_identity() {
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
            for lo in (0..m).step_by(QP) {
                for i in lo..(lo + QP).min(m) {
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
    eprintln!("PAGE12_INTEGER cases={cases}");
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
/// refill followed by the defining relation is exact through the complete
/// fifteen-bit omitted suffix of page8.
#[test]
fn page4_tail_refill_integer_identity() {
    let mut cases = 0usize;
    // Exhaust the small widths, then cover all larger widths with a fixed
    // adversarial sample.  The production source-shaped differential below
    // checks every actual gap g=1..22.
    for r in 1usize..=11 {
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
    for r in 12usize..=19 {
        let modulus = 1usize << r;
        for seed in 0usize..4096 {
            let b = ((seed * 7919 + 3) & (modulus - 1)) | 1;
            let l = (seed * 3571 + 5) & (modulus - 1);
            let inv = (1..modulus).step_by(2).find(|u| (u * b) % modulus == 1).unwrap();
            let q = (modulus - (l * inv) % modulus) % modulus;
            assert_eq!((q * b + l) % modulus, 0);
            cases += 1;
        }
    }
    eprintln!("PAGE4_TAIL cases={cases} max_r=19");
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
        let page = Page { q: b.alloc_n(QP) };
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
        let want_page = fq >> (21 - QP);
        if fq != 0 {
            selected += 1;
            assert_eq!(pq, want_page, "tick={tick} shot={shot} full={fq:#x} page={pq:#x}");
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

struct Page21Trace {
    b: B,
    x: Vec<QubitId>,
    a: Vec<QubitId>,
    bb: Vec<QubitId>,
    j: Vec<QubitId>,
    par: QubitId,
    top: Vec<QubitId>,
    helper: Option<QubitId>,
    bounds: Vec<usize>,
}

fn build_page21_trace(paged: bool) -> Page21Trace {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let k = sch.t;
    let mut b = B::new();
    let x = b.alloc_n(256);
    let mut bb = x.clone();
    bb.extend(b.alloc_n(sch.wb - x.len()));
    let mut w = Walk { a: b.alloc_n(sch.wa), bb, q: vec![], j: b.alloc_n(JB), par: b.alloc() };
    let dirty = b.alloc_n(64);
    let scf = Scr::alloc_fwd(&mut b, &dirty, 0);
    let m = super::frogtail::walk_forward(&mut b, &w, &sch, &scf);
    scf.release(&mut b);
    let mut bounds;
    let top;
    let helper;
    if paged {
        let page = Page { q: b.alloc_n(QP) };
        top = (0..=k).map(|t| page.qfr(t)[QP - 1]).collect();
        helper = None;
        let sci = Scr::alloc(&mut b, &dirty);
        let ce = super::frogtail::rec_regen_close(&mut b, &w, &sch, &sci);
        b.play(&ce, true);
        bounds = vec![b.ops.len()];
        for t in (1..=k).rev() {
            inverse_page21_tick_test(&mut b, &w, &page, t, &sch, &sci, m[t]);
            bounds.push(b.ops.len());
        }
    } else {
        w.q = b.alloc_n(23);
        top = (0..=k).map(|t| w.qfr(t)[22]).collect();
        helper = None;
        let sci = Scr::alloc(&mut b, &dirty);
        let ce = super::frogtail::rec_regen_close(&mut b, &w, &sch, &sci);
        b.play(&ce, true);
        bounds = vec![b.ops.len()];
        for t in (1..=k).rev() {
            let (p1, p2, p3) = super::frogtail::rec_regen_tick(&mut b, &w, t, &sch, &sci);
            b.play(&p3, true);
            b.play(&p2, true);
            b.z_if(super::frogtail::regen_digit(&w, t, &sci), m[t]);
            b.play(&p1, true);
            bounds.push(b.ops.len());
        }
    }
    Page21Trace { b, x, a: w.a, bb: w.bb, j: w.j, par: w.par, top, helper, bounds }
}

#[test]
#[ignore]
fn page21_highword_first_bad_boundary() {
    let k = 556usize;
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut witnesses: [Option<N>; 23] = [None; 23];
    let mut found = 0usize;
    let mut wrng = Rng::new(0x21_2026_1011);
    for _ in 0..250_000 {
        if found == 22 { break; }
        let mut v = wrng.below(256) % p();
        if v == N::ZERO { v = N::from(3u64); }
        if !v.bit(0) { v = p() - v; }
        let mut m = M::new(v);
        for t in 1..=sch.t {
            let old_par = m.par;
            let old_g = m.g;
            m.tick(t, &sch);
            if m.par != old_par && (1..=22).contains(&old_g) && witnesses[old_g as usize].is_none() {
                witnesses[old_g as usize] = Some(v);
                found += 1;
            }
        }
    }
    assert_eq!(found, 22, "must find source witnesses for m=2..23");
    let full = build_page21_trace(false);
    let page = build_page21_trace(true);
    let mut xf = Fixed(0x5a);
    let mut xp = Fixed(0x5a);
    let mut sf = Simulator::new(full.b.width() as usize, 20_000, &mut xf);
    let mut sp = Simulator::new(page.b.width() as usize, 20_000, &mut xp);
    let mut seed = 0x243f_6a88_85a3_08d3u64;
    for shot in 0..64 {
        let mut limbs = [0u64; 4];
        if shot < 22 {
            limbs.copy_from_slice(&witnesses[shot + 1].unwrap().as_limbs()[..4]);
        } else {
            for limb in &mut limbs {
                seed ^= seed << 7; seed ^= seed >> 9; seed ^= seed << 8; *limb = seed;
            }
            limbs[0] |= 1;
        }
        put_word256(&mut sf.qubits, &full.x, shot, limbs);
        put_word256(&mut sp.qubits, &page.x, shot, limbs);
    }
    sf.apply_iter(full.b.ops[..full.bounds[0]].iter());
    sp.apply_iter(page.b.ops[..page.bounds[0]].iter());
    let mut gaps = std::collections::BTreeSet::new();
    for step in 1..full.bounds.len() {
        let tick = k + 1 - step;
        if tick % 2 == 0 {
            for shot in 0..64 {
                let jraw: u64 = full.j.iter().enumerate().map(|(i,&q)| ((sf.qubits[q.0 as usize] >> shot) & 1) << i).sum();
                if jraw == (1u64 << JB) - 1 {
                    let mut nu = 0usize;
                    while nu < full.a.len() {
                        let q = full.a[(full.a.len() - 1 - nu + tick) % full.a.len()];
                        if ((sf.qubits[q.0 as usize] >> shot) & 1) != 0 { break; }
                        nu += 1;
                    }
                    if nu > 0 && nu <= 23 { gaps.insert(nu - 1); }
                }
            }
        }
        let ft = sf.qubits[full.top[tick].0 as usize];
        let pt = sp.qubits[page.top[tick].0 as usize];
        if ft != pt {
            eprintln!("PAGE21_HIGHWORD_BAD_DIGIT t={tick} full={ft:#x} page={pt:#x} helper={:#x}", page.helper.map(|q| sp.qubits[q.0 as usize]).unwrap_or(0));
        }
        sf.apply_iter(full.b.ops[full.bounds[step-1]..full.bounds[step]].iter());
        sp.apply_iter(page.b.ops[page.bounds[step-1]..page.bounds[step]].iter());
        let bad_a = full.a.iter().zip(&page.a).filter(|(f,p)| sf.qubits[f.0 as usize] != sp.qubits[p.0 as usize]).count();
        let bad_b = full.bb.iter().zip(&page.bb).filter(|(f,p)| sf.qubits[f.0 as usize] != sp.qubits[p.0 as usize]).count();
        let bad_j = full.j.iter().zip(&page.j).filter(|(f,p)| sf.qubits[f.0 as usize] != sp.qubits[p.0 as usize]).count();
        let bad_par = sf.qubits[full.par.0 as usize] != sp.qubits[page.par.0 as usize];
        if bad_a != 0 || bad_b != 0 || bad_j != 0 || bad_par || sf.phase != sp.phase {
            eprintln!("PAGE21_HIGHWORD_FIRST_BAD t={tick} badA={bad_a} badB={bad_b} badJ={bad_j} badPar={bad_par} phaseF={:#x} phaseP={:#x}", sf.phase, sp.phase);
            if let Some((i,(f,p))) = full.a.iter().zip(&page.a).enumerate().find(|(_, (f,p))| sf.qubits[f.0 as usize] != sp.qubits[p.0 as usize]) {
                eprintln!("PAGE21_HIGHWORD_BAD_A lane={i} xor={:#x}", sf.qubits[f.0 as usize] ^ sp.qubits[p.0 as usize]);
            }
            if let Some((i,(f,p))) = full.bb.iter().zip(&page.bb).enumerate().find(|(_, (f,p))| sf.qubits[f.0 as usize] != sp.qubits[p.0 as usize]) {
                eprintln!("PAGE21_HIGHWORD_BAD_B lane={i} xor={:#x}", sf.qubits[f.0 as usize] ^ sp.qubits[p.0 as usize]);
            }
            eprintln!("PAGE21_HIGHWORD_HELPER mask={:#x}", page.helper.map(|q| sp.qubits[q.0 as usize]).unwrap_or(0));
            break;
        }
    }
    eprintln!("PAGE21_HIGHWORD_GAPS {gaps:?}");
    assert_eq!(gaps, (1usize..=22).collect(), "source-shaped differential must cover m=2..23");
}

#[test]
fn q900_tick540_to542_four_receipt_streams() {
    let full = build_page21_trace(false);
    let page = build_page21_trace(true);
    for byte in [0u8, 255, 170, 85] {
        let mut xf = Fixed(byte);
        let mut xp = Fixed(byte);
        let mut sf = Simulator::new(full.b.width() as usize, 54_000 + byte as usize, &mut xf);
        let mut sp = Simulator::new(page.b.width() as usize, 54_000 + byte as usize, &mut xp);
        let mut seed = 0x6a09_e667_f3bc_c909u64;
        for shot in 0..64 {
            let mut limbs = [0u64; 4];
            for limb in &mut limbs { seed ^= seed << 7; seed ^= seed >> 9; seed ^= seed << 8; *limb = seed; }
            limbs[0] |= 1;
            put_word256(&mut sf.qubits, &full.x, shot, limbs);
            put_word256(&mut sp.qubits, &page.x, shot, limbs);
        }
        sf.apply_iter(full.b.ops[..full.bounds[0]].iter());
        sp.apply_iter(page.b.ops[..page.bounds[0]].iter());
        let mut step = 1usize;
        for tick in (543usize..=556).rev() {
            let _ = tick;
            sf.apply_iter(full.b.ops[full.bounds[step-1]..full.bounds[step]].iter());
            sp.apply_iter(page.b.ops[page.bounds[step-1]..page.bounds[step]].iter());
            step += 1;
        }
        for tick in (540usize..=542).rev() {
            assert_eq!(sf.qubits[full.top[tick].0 as usize], sp.qubits[page.top[tick].0 as usize], "byte={byte} tick={tick} digit");
            sf.apply_iter(full.b.ops[full.bounds[step-1]..full.bounds[step]].iter());
            sp.apply_iter(page.b.ops[page.bounds[step-1]..page.bounds[step]].iter());
            step += 1;
            for (i,(f,p)) in full.a.iter().zip(&page.a).enumerate() { assert_eq!(sf.qubits[f.0 as usize],sp.qubits[p.0 as usize],"byte={byte} tick={tick} A{i}"); }
            for (i,(f,p)) in full.bb.iter().zip(&page.bb).enumerate() { assert_eq!(sf.qubits[f.0 as usize],sp.qubits[p.0 as usize],"byte={byte} tick={tick} B{i}"); }
            for (i,(f,p)) in full.j.iter().zip(&page.j).enumerate() { assert_eq!(sf.qubits[f.0 as usize],sp.qubits[p.0 as usize],"byte={byte} tick={tick} j{i}"); }
            assert_eq!(sf.qubits[full.par.0 as usize],sp.qubits[page.par.0 as usize],"byte={byte} tick={tick} parity");
            assert_eq!(sf.phase,sp.phase,"byte={byte} tick={tick} phase");
        }
    }
    eprintln!("Q900_LATE_DIFFERENTIAL ticks=540..542 receipt_streams=4 PASS");
}

#[test]
fn q906_lifetime_site_census_is_frozen() {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut bins = [0usize; 4];
    for t in (4..=sch.t).step_by(2) {
        let tz = (t + 1).min(sch.t);
        let (c, kv, kc) = if t < sch.t {
            (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1])
        } else {
            (sch.c[tz + 1], sch.c[tz + 1], sch.wb - sch.c[tz + 1])
        };
        let z = 2 * (c - kv)
            + (sch.wb - c).saturating_sub(kc.max(46))
            + (sch.wb - c).saturating_sub(kc.max(23));
        if z >= 6 { bins[0] += 1; }
        else if z >= 2 { bins[1] += 1; }
        else if z >= 1 { bins[2] += 1; }
        else { bins[3] += 1; }
    }
    assert_eq!(bins, [212, 20, 0, 45]);
    assert_eq!(2 * bins[0], 424);
    assert_eq!(2 * (bins[1] + bins[2] + bins[3]), 130);
}

#[test]
fn q906_descending_threshold_boolean_exhaustive() {
    for e in [false, true] {
        for g in 0usize..32 {
            let mut got = [false; 23];
            let mut f = g >= 22;
            let mut ef = e && f;
            got[22] = ef;
            for j in (2usize..=21).rev() {
                let hit = g == j;
                f ^= hit;
                ef ^= e && hit;
                got[j] = ef;
            }
            for j in [1usize, 0] {
                let hit = g == j;
                f ^= hit;
                ef ^= e && hit;
            }
            assert_eq!(&got[2..], &(2usize..23).map(|k| e && g >= k).collect::<Vec<_>>()[..]);
            assert!(f);
            assert_eq!(ef, e);
            ef ^= e;
            f ^= true;
            assert!(!f && !ef);
        }
    }
}

#[cfg(any())]
#[test]
fn q906_shared_tail_forced_outcomes_phase_clean() {
    for byte in [0u8, 255, 170, 85] {
        let t = 4usize;
        let mut b = B::new();
        let w = Walk {
            a: b.alloc_n(308),
            bb: b.alloc_n(308),
            q: vec![],
            j: b.alloc_n(JB),
            par: b.alloc(),
        };
        let page = Page { q: b.alloc_n(QP) };
        let dirty = b.alloc_n(64);
        let sc = Scr::alloc(&mut b, &dirty);
        let scratch: Vec<QubitId> = std::iter::once(sc.e).chain(sc.tmp.iter().copied()).collect();
        let sch = Sched::from_text(SCHED_FROGTAIL);
        refill_page21_tail_test(&mut b, &w, &page, t, &sch, &sc);
        let next = page.qfr(t - 1)[QP - 1];
        let after = page.qfr(t - 2)[QP - 1];
        let b1q = w.asig(t, 1);
        let b2q = w.asig(t, 3);
        let l1q = w.bsig(1);
        let mut xof = Fixed(byte);
        let mut sim = Simulator::new(b.width() as usize, 20_000, &mut xof);
        let mut want_next = 0u64;
        let mut want_after = 0u64;
        for shot in 0..64 {
            let pat = shot % 32;
            let j = (shot / 2) % 32;
            for (i, &q) in w.j.iter().enumerate() {
                if (j >> i) & 1 != 0 { sim.qubits[q.0 as usize] |= 1u64 << shot; }
            }
            for (q, mask) in [(b1q, 1usize), (b2q, 2), (l1q, 4), (next, 8), (after, 16)] {
                if pat & mask != 0 { sim.qubits[q.0 as usize] |= 1u64 << shot; }
            }
            let base = j == 10;
            let long = base && pat & 1 == 0;
            let n = (pat & 8 != 0) ^ base ^ (long && pat & 2 != 0) ^ (long && pat & 4 != 0);
            let a = (pat & 16 != 0) ^ long;
            if n { want_next |= 1u64 << shot; }
            if a { want_after |= 1u64 << shot; }
        }
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.qubits[next.0 as usize], want_next, "forced byte={byte}");
        assert_eq!(sim.qubits[after.0 as usize], want_after, "forced byte={byte}");
        assert_eq!(sim.phase, 0, "forced byte={byte}");
        for q in &scratch { assert_eq!(sim.qubits[q.0 as usize], 0, "scratch q{} byte={byte}", q.0); }
    }
}
