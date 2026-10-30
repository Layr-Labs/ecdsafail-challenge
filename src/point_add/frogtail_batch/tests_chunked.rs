use super::frogdrop_sched::N;
use super::tests_frogdrop::Rng;
use super::{builder::B, chunked};
use crate::circuit::QubitId as Q;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}
fn put(words: &mut [u64], qs: &[Q], shot: usize, x: N) {
    for (i, q) in qs.iter().enumerate() {
        if x.bit(i) {
            words[q.0 as usize] |= 1 << shot;
        }
    }
}
fn get(words: &[u64], qs: &[Q], shot: usize) -> N {
    let mut x = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 != 0 {
            x |= N::from(1u64) << i;
        }
    }
    x
}

fn check(n: usize, room: usize, flagged: bool, cases: &[(N, N, bool, bool)]) {
    let Some(sizes) = chunked::plan(n, room, flagged) else {
        return;
    };
    let mut b = B::new();
    let a = b.alloc_n(n);
    let t = b.alloc_n(n);
    let ctl = b.alloc();
    let flag = b.alloc();
    let pool = b.alloc_n(room);
    let extra: usize = sizes[..sizes.len() - 1].iter().map(|k| k - 1).sum();
    b.begin();
    b.chunk_add(chunked::Call { debts: vec![],
        a: a.clone(),
        t: t.clone(),
        ctl,
        cout: flagged.then_some(flag),
        cin: None,
        pool: pool.clone(),
        sizes: sizes.clone(),
        pair: None,
    });
    let r = b.end();
    b.play(&r, false);
    let split = b.ops.len();
    b.play(&r, true);
    let mask = (N::from(1u64) << n) - N::from(1u64);
    for byte in [0u8, 255, 170] {
        for batch in cases.chunks(64) {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            for (i, &(aa, tt, cc, ff)) in batch.iter().enumerate() {
                put(&mut sim.qubits, &a, i, aa);
                put(&mut sim.qubits, &t, i, tt);
                if cc {
                    sim.qubits[ctl.0 as usize] |= 1 << i;
                }
                if ff {
                    sim.qubits[flag.0 as usize] |= 1 << i;
                }
            }
            let initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..split].iter());
            let base = 2 * n + if flagged { 1 } else { 0 };
            let base = if flagged { base } else { base - 1 };
            assert_eq!(
                sim.stats.toffoli_gates,
                64 * base as u64 + (byte.count_ones() * 8) as u64 * extra as u64,
                "charged T n{n} room{room} flag{flagged} byte{byte}"
            );
            let lane_mask = if batch.len() == 64 {
                u64::MAX
            } else {
                (1u64 << batch.len()) - 1
            };
            assert_eq!(
                sim.phase & lane_mask,
                0,
                "forward phase n{n} room{room} flag{flagged} byte{byte}"
            );
            for (i, &(aa, tt, cc, ff)) in batch.iter().enumerate() {
                let sum = tt + if cc { aa } else { N::ZERO };
                assert_eq!(
                    get(&sim.qubits, &t, i),
                    sum & mask,
                    "sum n{n} room{room} lane{i}"
                );
                assert_eq!(get(&sim.qubits, &a, i), aa);
                assert_eq!(
                    (sim.qubits[flag.0 as usize] >> i) & 1,
                    (ff ^ (flagged && cc && sum.bit(n))) as u64,
                    "carry flag n{n} room{room} lane{i}"
                );
            }
            for q in &pool {
                assert_eq!(sim.qubits[q.0 as usize] & lane_mask, 0, "clean carry bank");
            }
            sim.apply_iter(b.ops[split..].iter());
            assert_eq!(sim.phase & lane_mask, 0, "inverse phase");
            for (got, want) in sim.qubits.iter().zip(&initial) {
                assert_eq!(got & lane_mask, want & lane_mask, "inverse state");
            }
        }
    }
    eprintln!(
        "CHUNK n={n} room={room} flag={flagged} chunks={sizes:?} expected_T={} cases={}",
        2. * n as f64 + if flagged { 1. } else { -1. } + extra as f64 / 2.,
        cases.len()
    );
}

#[test]
fn chunked_add_exact_and_average() {
    for n in 2..=5usize {
        let cases: Vec<_> = (0..1u64 << n)
            .flat_map(|a| {
                (0..1u64 << n).flat_map(move |t| {
                    [false, true].into_iter().flat_map(move |c| {
                        [false, true]
                            .into_iter()
                            .map(move |f| (N::from(a), N::from(t), c, f))
                    })
                })
            })
            .collect();
        for room in 2..=n {
            for flag in [false, true] {
                check(n, room, flag, &cases);
            }
        }
    }
    let mut rng = Rng::new(976131);
    for (n, room) in [
        (9, 4),
        (32, 8),
        (128, 17),
        (256, 24),
        (308, 25),
        (256, 159),
        (308, 91),
    ] {
        let cases: Vec<_> = (0..256)
            .map(|i| (rng.below(n), rng.below(n), i % 2 == 0, i % 3 == 0))
            .collect();
        for flag in [false, true] {
            check(n, room, flag, &cases);
        }
    }
}

pub fn expected_t(ops: &[crate::circuit::Op]) -> f64 {
    use crate::circuit::{OperationType as K, NO_BIT};
    let mut weight = 1.;
    let mut stack = vec![];
    let mut total = 0.;
    let mut native = 0usize;
    for (i, op) in ops.iter().enumerate() {
        match op.kind {
            K::PushCondition => {
                assert!(
                    i > 0 && ops[i - 1].kind == K::Hmr && ops[i - 1].c_target == op.c_condition
                );
                stack.push(weight);
                weight *= 0.5;
            }
            K::PopCondition => weight = stack.pop().unwrap(),
            K::CCX | K::CCZ => {
                assert_eq!(op.c_condition, NO_BIT);
                total += weight;
                native += 1;
            }
            _ => {}
        }
    }
    assert!(stack.is_empty());
    eprintln!("ANALYTIC native={native} expected={total}");
    total
}

fn check_deferred(n: usize, pf: usize, pi: usize, flagged: bool, cases: &[(N, N, bool, bool)]) {
    use chunked::{AddRole, Pair, PairKey};
    use crate::circuit::analyze_ops;
    let sf = chunked::plan(n, pf, flagged).unwrap();
    let si = chunked::plan(n, pi, flagged).unwrap();
    let mut b = B::new();
    let a = b.alloc_n(n); let t = b.alloc_n(n);
    let ctl = b.alloc(); let flag = b.alloc(); let sign = b.alloc();
    let spectator = b.alloc(); let mid = b.alloc(); let cin = b.alloc();
    let pool = b.alloc_n(pf.max(pi));
    let division = b.new_division();
    let key = PairKey { division, tick: 1, role: AddRole::Value };
    for &q in &t { b.cx(sign, q); }
    b.chunk_add(chunked::Call { debts: vec![], a: a.clone(), t: t.clone(), ctl,
        cout: flagged.then_some(flag), cin: Some(cin), pool: pool[..pf].to_vec(), sizes: sf.clone(), pair: Some(Pair::Forward(key)) });
    for &q in &t { b.cx(sign, q); }
    let forward = b.ops.len();
    // Change all operand IDs, and reuse the immediate HMR bit between passes.
    for i in 0..n { b.swap(a[i], t[n-1-i]); }
    b.cx(ctl, spectator);
    b.and_c(ctl, spectator, mid); b.and_u(ctl, spectator, mid);
    let ia: Vec<_> = t.iter().rev().copied().collect();
    let it: Vec<_> = a.iter().rev().copied().collect();
    b.begin();
    for &q in &it { b.cx(sign, q); }
    b.chunk_add(chunked::Call { debts: vec![], a: ia, t: it.clone(), ctl,
        cout: flagged.then_some(flag), cin: Some(cin), pool: pool[..pi].to_vec(), sizes: si.clone(), pair: Some(Pair::Inverse(key)) });
    for &q in &it { b.cx(sign, q); }
    let inverse = b.end();
    b.play(&inverse, true);
    b.cx(ctl, spectator);
    for i in 0..n { b.swap(a[i], t[n-1-i]); }
    assert_eq!(b.close_division(division), 1);
    assert_eq!(b.width() as usize, 2*n + 6 + pf.max(pi), "extra physical owner");
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mask = (N::from(1u64) << n) - N::from(1u64);
    for (fb, ib) in [(0u8,0u8),(0,255),(255,0),(255,255),(170,85),(85,170)] {
        for cinv in [false,true] { for signed in [false,true] {
            for batch in cases.chunks(64) {
                let mut xof = Fixed(fb);
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
                for (i,&(av,tv,cv,fv)) in batch.iter().enumerate() {
                    put(&mut sim.qubits,&a,i,av); put(&mut sim.qubits,&t,i,tv);
                    if cv { sim.qubits[ctl.0 as usize] |= 1<<i; }
                    if fv { sim.qubits[flag.0 as usize] |= 1<<i; }
                    if signed { sim.qubits[sign.0 as usize] |= 1<<i; }
                    if cinv { sim.qubits[cin.0 as usize] |= 1<<i; }
                    if i%3==0 { sim.qubits[spectator.0 as usize] |= 1<<i; }
                }
                let initial = sim.qubits.clone();
                sim.apply_iter(b.ops[..forward].iter());
                let lanes = if batch.len()==64 { u64::MAX } else { (1<<batch.len())-1 };
                for (i,&(av,tv,cv,fv)) in batch.iter().enumerate() {
                    let add = av + N::from(cinv as u64);
                    let want = if !cv { tv } else if signed { tv.wrapping_sub(add) } else { tv+add };
                    assert_eq!(get(&sim.qubits,&t,i),want&mask,"forward spec n{n} signed{signed}");
                    assert_eq!(get(&sim.qubits,&a,i),av);
                    let normalized = if signed { tv ^ mask } else { tv };
                    let overflow = cv && (normalized+add).bit(n);
                    assert_eq!((sim.qubits[flag.0 as usize]>>i)&1,(fv^(flagged&&overflow)) as u64);
                }
                for q in &pool { assert_eq!(sim.qubits[q.0 as usize]&lanes,0); }
                sim.xof.0=ib;
                sim.apply_iter(b.ops[forward..].iter());
                assert_eq!(sim.phase&lanes,0,"deferred phase n{n} pf{pf} pi{pi} signed{signed} HMR{fb}/{ib}");
                for (got,want) in sim.qubits.iter().zip(&initial) { assert_eq!(got&lanes,want&lanes,"deferred state"); }
            }
        } }
    }
    eprintln!("DEFERRED n={n} flag={flagged} forward={sf:?} inverse={si:?} receipts={} native={} expected={} cases={}",sf.len()-1,b.tof,expected_t(&b.ops),cases.len()*24);
}

#[test]
fn deferred_chunk_native_exact() {
    for n in 3..=7 {
        let cases: Vec<_> = (0..1u64<<n).flat_map(|a| (0..1u64<<n).flat_map(move |t|
            [false,true].into_iter().flat_map(move |c| [false,true].into_iter().map(move |f| (N::from(a),N::from(t),c,f))))).collect();
        for flagged in [false,true] {
            let pi = if flagged && n == 7 { 4 } else { 3 };
            check_deferred(n, (n/2+1).max(3), pi, flagged, &cases);
        }
    }
    let mut rng = Rng::new(97546308);
    for (n,pf,pi) in [(259,153,133),(308,73,53)] {
        let cases: Vec<_> = (0..256).map(|i| (rng.below(n),rng.below(n),i%2==0,i%3==0)).collect();
        check_deferred(n,pf,pi,false,&cases);
    }
}

#[test]
fn rolling_forward_boundaries_exact() {
    use chunked::{AddRole, Pair, PairKey};
    use crate::circuit::analyze_ops;
    for (n, pf, pi) in [(8, 2, 2), (10, 3, 2), (12, 4, 3)] {
        assert!(chunked::plan(n, pf, false).is_none());
        let mut b = B::new();
        let a = b.alloc_n(n);
        let t = b.alloc_n(n);
        let ctl = b.alloc();
        let pool = b.alloc_n(pf.max(pi));
        let division = b.new_division();
        let key = PairKey { division, tick: n, role: AddRole::Cofactor };
        assert!(chunked::try_add_paired(&mut b, &a, &t, ctl, None,
            &pool[..pf], Some(Pair::Forward(key))));
        let forward = b.ops.len();
        b.begin();
        assert!(chunked::try_add_paired(&mut b, &a, &t, ctl, None,
            &pool[..pi], Some(Pair::Inverse(key))));
        let inverse = b.end();
        b.play(&inverse, true);
        assert_eq!(b.close_division(division), 1);
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        let mask = (1u64 << n) - 1;
        let mut cases = Vec::new();
        for i in 0..256u64 {
            let av = (i.wrapping_mul(173) ^ (i >> 2)) & mask;
            let tv = (i.wrapping_mul(91) ^ (i << 3) ^ mask) & mask;
            cases.push((av, tv, i & 1 != 0));
        }
        cases.extend([(0, 0, false), (mask, mask, true), (mask, 1, true), (1, mask, true)]);
        for (fb, ib) in [(0u8, 0u8), (0, 255), (255, 0), (255, 255), (170, 85), (85, 170)] {
            for batch in cases.chunks(64) {
                let mut xof = Fixed(fb);
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
                for (lane, &(av, tv, enabled)) in batch.iter().enumerate() {
                    put(&mut sim.qubits, &a, lane, N::from(av));
                    put(&mut sim.qubits, &t, lane, N::from(tv));
                    if enabled { sim.qubits[ctl.0 as usize] |= 1 << lane; }
                }
                let initial = sim.qubits.clone();
                sim.apply_iter(b.ops[..forward].iter());
                for (lane, &(av, tv, enabled)) in batch.iter().enumerate() {
                    let want = (tv + if enabled { av } else { 0 }) & mask;
                    assert_eq!(get(&sim.qubits, &t, lane), N::from(want));
                }
                for &q in &pool { assert_eq!(sim.qubits[q.0 as usize], 0); }
                sim.xof.0 = ib;
                sim.apply_iter(b.ops[forward..].iter());
                assert_eq!(sim.phase, 0, "rolling phase n{n} pool{pf}/{pi} HMR{fb}/{ib}");
                assert_eq!(sim.qubits, initial, "rolling state n{n} pool{pf}/{pi}");
            }
        }
    }
}

/// Carry-in translation check: finite exhaustive n<=6, parameter coverage
/// n2..40 x room1..12, all 16 forward/inverse HMR tape combinations.
#[test]
fn c49_cin_pair_exact() {
    use chunked::{AddRole,Pair,PairKey};
    use super::builder::ONE;
    use crate::circuit::analyze_ops;
    let mut checked=0usize;
    for n in 2..=40 { for room in 1..=12 { for unconditional in [false,true] {
        let pf=(room+1).min(12); let pi=room;
        let mut b=B::new();
        let a=b.alloc_n(n);let t=b.alloc_n(n);let ctl=b.alloc();let cin=b.alloc();
        let pool=b.alloc_n(pf.max(pi));
        let division=b.new_division();let key=PairKey{division,tick:n,role:AddRole::ValueHi2};
        let c=if unconditional{ONE}else{ctl};
        assert!(chunked::try_add_paired_cin(&mut b,&a,&t,c,None,Some(cin),&pool[..pf],Some(Pair::Forward(key))));
        let split=b.ops.len();
        b.begin();
        assert!(chunked::try_add_paired_cin(&mut b,&a,&t,c,None,Some(cin),&pool[..pi],Some(Pair::Inverse(key))));
        let ir=b.end();b.play(&ir,true);assert_eq!(b.close_division(division),1);
        let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
        let cases:Vec<_>=if n<=6 && room<=3 {
            (0..1u64<<n).flat_map(|a|(0..1u64<<n).flat_map(move|t|(0..4).map(move|c|(a,t,c&1!=0,c&2!=0)))).collect()
        } else {(0..64u64).map(|i|((i.wrapping_mul(0x59d81a723b)^(mask>>(i%8)))&mask,
            (i.wrapping_mul(0x17a95c4d11)^mask)&mask,i&1!=0,i&2!=0)).collect()};
        for fb in [0u8,255,170,85] {for ib in [0u8,255,170,85] {for batch in cases.chunks(64) {
            let mut xof=Fixed(fb);let mut sim=Simulator::new(nq as usize,nb as usize,&mut xof);
            for(i,&(av,tv,cv,ci))in batch.iter().enumerate(){
                put(&mut sim.qubits,&a,i,N::from(av));put(&mut sim.qubits,&t,i,N::from(tv));
                if cv{sim.qubits[ctl.0 as usize]|=1<<i;}if ci{sim.qubits[cin.0 as usize]|=1<<i;}
            }
            let init=sim.qubits.clone();sim.apply_iter(b.ops[..split].iter());
            for(i,&(av,tv,cv,ci))in batch.iter().enumerate(){
                let want=(tv+if unconditional||cv{av+ci as u64}else{0})&mask;
                assert_eq!(get(&sim.qubits,&t,i),N::from(want),"cin forward n{n} room{room}");
                assert_eq!(get(&sim.qubits,&a,i),N::from(av));
            }
            for q in &pool{assert_eq!(sim.qubits[q.0 as usize],0);}
            sim.xof.0=ib;sim.apply_iter(b.ops[split..].iter());
            assert_eq!(sim.qubits,init,"cin allwire n{n} room{room} HMR{fb}/{ib}");
            assert_eq!(sim.phase,0,"cin phase n{n} room{room} HMR{fb}/{ib}");checked+=batch.len();
        }}}
    }}}
    eprintln!("C49_CIN_PAIR_EXACT {checked} lane cases");
}
