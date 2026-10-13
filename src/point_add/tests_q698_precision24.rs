//! Finite physical698-wire split-remainder evidence; not a whole replay.
use super::builder::{B, G};
use super::frogdrop_col::{ColPar, rec};
use super::frogdrop_sched::N;
use super::midg::{S1, stage1_v, TC};
use super::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, n: N) {
    for (i, &q) in qs.iter().enumerate() {
        w[q.0 as usize] = (w[q.0 as usize] & !(1u64 << shot))
            | (u64::from(n.bit(i)) << shot);
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    qs.iter().enumerate().fold(N::ZERO, |v,(i,q)|
        v | (N::from((w[q.0 as usize] >> shot) & 1) << i))
}

fn symbolic(ops: &[Op], mut q: Vec<u64>) -> Vec<u64> {
    let mut measured = std::collections::BTreeMap::new();
    let mut phase = Vec::<u64>::new();
    let mut constant = 0u64;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        match op.kind {
            K::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
            K::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
            K::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
            K::Swap => { assert_eq!(op.c_condition, NO_BIT); q.swap(a,t); }
            K::Hmr => {
                assert_eq!(op.c_condition, NO_BIT);
                assert_ne!(op.c_target, NO_BIT);
                measured.insert(op.c_target, phase.len()); phase.push(q[t]); q[t] = 0;
            }
            K::CZ => {
                if op.c_condition == NO_BIT { constant ^= q[a] & q[t]; }
                else { phase[measured[&op.c_condition]] ^= q[a] & q[t]; }
            }
            other => panic!("unexpected split-head operation {other:?}"),
        }
    }
    assert_eq!(constant, 0, "constant phase");
    assert!(phase.iter().all(|&x| x == 0), "independent HMR phase coefficient");
    q
}

fn apply(ops: &[Op], initial: &[u64]) -> Vec<u64> {
    let expected = symbolic(ops, initial.to_vec());
    let actual = run(ops, initial.len(), &|w| w.copy_from_slice(initial));
    assert_eq!(actual.phase, 0, "native measurement phase");
    assert_eq!(actual.q, expected, "native versus symbolic state");
    actual.q
}

#[test]
fn q698_split24_full_state_phase_and_cancellations() {
    let schedule = super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&schedule);
    let mut wide = cols[0].clone(); wide.sz = (57,256); wide.sy = (1,128);
    wide.smax = (1,128); wide.m = 128; wide.xw = 128; wide.dn = true;
    let profiles: Vec<ColPar> = vec![cols[10].clone(), cols[85].clone(), wide];
    let mut fixtures = 0usize;
    let mut applications = 0usize;
    for (profile, cp) in profiles.iter().enumerate() {
        assert_eq!((cp.n,cp.nq,cp.k,cp.h), (281,128,22,24));
        assert!(cp.sz.0 >= 57);
        for helpers in [0usize,1,2,39] {
            for mode in 0..3 {
                let mut b = B::new();
                let ring = b.alloc_n(281);
                let qword = b.alloc_n(128);
                let _sy = b.alloc_n(8);
                let sx = b.alloc_n(8);
                let _ph = b.alloc();
                let pool = b.alloc_n(13);
                let dirty = b.alloc_n(259);
                assert_eq!(b.width(), 698);
                let act = pool[12];
                let mut size = pool[..8].to_vec();
                if cp.sz.1 == 256 { size.push(pool[8]); }
                // Fixed helper cohorts are unit-test loans, not sampled contest
                // bounds. All bank lanes startclean and are returned.
                let bank = qword[128-helpers..].to_vec();
                let mut r = ring[..23].to_vec(); r.extend([sx[2],sx[3]]);
                let mut gt = vec![sx[0]];
                if let Some(&p) = bank.first() { gt.push(p); }
                if let Some(&p) = bank.get(1) { gt.push(p); }
                let s = S1 { r, f:sx[0], zero:ring[23], sgn:sx[0], gt,
                    anc:bank.iter().skip(2).copied().collect(), andc:bank.clone(),
                    chain:bank.clone(), dirty:dirty.clone() };
                let fv = stage1_v(&mut b, &ring[257..281], &ring[23..24+TC],
                                 &size, cp.sz, &s, act, true);
                let fr = stage1_v(&mut b, &ring[257..281], &ring[23..24+TC],
                                 &size, cp.sz, &s, act, false);
                let vform = rec(&mut b, |b| { b.play(&fv,false); b.play(&fr,true); });
                b.play(&vform,false); let forward = std::mem::take(&mut b.ops);
                b.play(&vform,true); let inverse = std::mem::take(&mut b.ops);
                let mut rng = Rng::new(0x69824 + (profile*100+helpers*3+mode) as u64);
                let mut initial: Vec<u64> = (0..698).map(|_| rng.next()).collect();
                let active = [0,u64::MAX,0x00ff_0f0f_3333_5555][mode];
                initial[act.0 as usize] = active;
                initial[sx[0].0 as usize] = 0;
                for &p in &bank { initial[p.0 as usize] = 0; }
                for &p in s.r.iter().chain([ring[23]].iter()) {
                    initial[p.0 as usize] &= !active;
                }
                let sizes = [57usize,128,133,230,231,232,233,234,255,256];
                for shot in 0..64 {
                    let sz = sizes[shot%sizes.len()].max(cp.sz.0).min(cp.sz.1);
                    put(&mut initial,&size,shot,N::from(sz as u64));
                    if active>>shot&1 == 0 { continue; }
                    let zh = match shot%3 {
                        0 => N::from(1u64)<<23,
                        1 => (N::from(1u64)<<24)-N::from(1u64),
                        _ => rng.below(23)|(N::from(1u64)<<23),
                    };
                    put(&mut initial,&ring[257..281],shot,zh);
                    let divisor = zh|N::from(1u64);
                    let f = ((N::from(1u64)<<(280-sz))-N::from(1u64))/divisor;
                    let u = (257-sz).saturating_sub(TC);
                    let t = N::from(1u64)<<(257-sz);
                    let tie = (f>>u)<<u;
                    let w = match shot%4 {
                        0 => tie, 1 => tie+N::from(1u64),
                        2 => tie.saturating_sub(N::from(1u64)),
                        _ => rng.below(257-sz),
                    } & (t-N::from(1u64));
                    for i in 0..=TC {
                        let pos = 257isize-sz as isize-i as isize;
                        if pos>=0 {
                            let wire=ring[23+i];
                            initial[wire.0 as usize]=(initial[wire.0 as usize]&!(1u64<<shot))
                                |(u64::from(w.bit(pos as usize))<<shot);
                        }
                    }
                }
                let oracle = |inverse:bool| {
                    let mut out = initial.clone();
                    for shot in 0..64 {
                        if active>>shot&1 == 0 { continue; }
                        let sz = get(&initial,&size,shot).as_limbs()[0] as usize;
                        let divisor = get(&initial,&ring[257..281],shot)|N::from(1u64);
                        let f=((N::from(1u64)<<(280-sz))-N::from(1u64))/divisor;
                        let u=(257-sz).saturating_sub(TC);
                        let t=N::from(1u64)<<(257-sz);
                        let delta=t-(((f>>u)+N::from(1u64))<<u);
                        let mut w=N::ZERO;
                        for i in 0..=TC {
                            let pos=257isize-sz as isize-i as isize;
                            if pos>=0 && initial[ring[23+i].0 as usize]>>shot&1 !=0 {
                                w|=N::from(1u64)<<pos as usize;
                            }
                        }
                        let w=if inverse {(w+t-delta)&(t-N::from(1u64))}
                              else {(w+delta)&(t-N::from(1u64))};
                        for i in 1..=TC {
                            let pos=257isize-sz as isize-i as isize;
                            if pos>=0 {
                                let wire=ring[23+i];
                                out[wire.0 as usize]=(out[wire.0 as usize]&!(1u64<<shot))
                                    |(u64::from(w.bit(pos as usize))<<shot);
                            }
                        }
                    }
                    out
                };
                let fw=apply(&forward,&initial);
                let bw=apply(&inverse,&initial);
                assert_eq!(fw,oracle(false),"forward profile{profile} helpers{helpers} mode{mode}");
                assert_eq!(bw,oracle(true),"inverse profile{profile} helpers{helpers} mode{mode}");
                assert_eq!(apply(&inverse,&fw),initial,"forward/inverse full698 state");
                assert_eq!(apply(&forward,&bw),initial,"inverse/forward full698 state");
                applications+=4*(forward.len()+inverse.len()); fixtures+=1;
            }
        }
    }
    assert_eq!(fixtures,36);
    eprintln!("SPLIT24_NATIVE_PASS fixtures36 packed_lanes2304 width698 helpers0_1_2_39 modes3 forward_inverse_both_orders=true symbolic_independent_phase_coefficients=true gate_applications={applications}");
}
