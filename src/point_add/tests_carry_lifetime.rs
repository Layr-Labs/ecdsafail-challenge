//! Physical emitted operations, with one independent phase symbol per Hmr.
//! Zero coefficients prove phase cleanliness for every measurement outcome.
use super::builder::B;
use super::frogdrop::cadd_tail_and;
use super::frogdrop_sched::N;
use super::tests_frogdrop::Rng;
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

fn symbolic(ops: &[Op], mut q: Vec<u64>) -> Vec<u64> {
    let mut measured = std::collections::BTreeMap::new();
    let mut phase = Vec::<u64>::new();
    let mut constant_phase = 0u64;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        match op.kind {
            K::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
            K::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
            K::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
            K::Swap => q.swap(a, t),
            K::Hmr => {
                measured.insert(op.c_target, phase.len());
                phase.push(q[t]);
                q[t] = 0;
            }
            K::CZ => {
                if op.c_condition == NO_BIT { constant_phase ^= q[a] & q[t]; }
                else { phase[measured[&op.c_condition]] ^= q[a] & q[t]; }
            }
            other => panic!("unexpected local operation {other:?}"),
        }
    }
    assert_eq!(constant_phase, 0);
    assert!(phase.iter().all(|&coefficient| coefficient == 0), "nonzero symbolic measurement phase");
    q
}
fn put(q: &mut [u64], ports: &[QubitId], lane: usize, value: N) {
    for (i, port) in ports.iter().enumerate() {
        if value.bit(i) { q[port.0 as usize] |= 1u64 << lane; }
    }
}
fn get(q: &[u64], ports: &[QubitId], lane: usize) -> N {
    let mut value = N::ZERO;
    for (i, port) in ports.iter().enumerate() {
        if (q[port.0 as usize] >> lane) & 1 != 0 { value |= N::from(1u64) << i; }
    }
    value
}

#[test]
fn reused_tail_prefixes_every_measurement_phase_and_inverse() {
    let mut cases = 0usize;
    let mut streams = 0usize;
    for n in (1..=8).chain([12, 29, 30, 64, 127, 137]) {
        for nt in [0usize, 1, 2, 3, 8, 39, 40] {
            let mut b = B::new();
            let t = b.alloc_n(n);
            let s = b.alloc_n(n);
            let tail = b.alloc_n(nt);
            let g = b.alloc();
            let c0 = b.alloc();
            let h = b.alloc();
            let anc = b.alloc_n(39);
            let spare = b.alloc_n(9);
            let used = nt.saturating_sub(1);
            let mut carry = spare.clone();
            carry.extend(&anc[used..]);
            if nt == 0 { carry.push(h); }
            carry.truncate(n);
            b.begin();
            cadd_tail_and(&mut b, g, &t, &s, &tail, c0, h, &anc[..used], &carry);
            let recipe = b.end();
            b.play(&recipe, false);
            let forward = std::mem::take(&mut b.ops);
            b.play(&recipe, true);
            let inverse = std::mem::take(&mut b.ops);
            let total_bits = 2*n + nt + 1;
            let exhaustive = n <= 5 && nt <= 3;
            let count = if exhaustive { 1usize << total_bits } else { 512 };
            let mask = (N::from(1u64) << (n + nt)) - N::from(1u64);
            let mut rng = Rng::new((n*113 + nt) as u64);
            for first in (0..count).step_by(64) {
                let mut start = vec![0u64; b.width() as usize];
                let mut values = Vec::new();
                for lane in 0..64.min(count-first) {
                    let (tv, sv, lv, gv) = if exhaustive {
                        let code = first + lane;
                        let low = (1usize << n) - 1;
                        (N::from((code & low) as u64), N::from(((code >> n) & low) as u64),
                         N::from(((code >> (2*n)) & ((1usize << nt)-1)) as u64), (code >> (2*n+nt)) & 1)
                    } else { (rng.below(n), rng.below(n), rng.below(nt), (rng.next() & 1) as usize) };
                    put(&mut start, &t, lane, tv);
                    put(&mut start, &s, lane, sv);
                    put(&mut start, &tail, lane, lv);
                    if gv != 0 { start[g.0 as usize] |= 1u64 << lane; }
                    values.push((tv, sv, lv, gv));
                }
                let end = symbolic(&forward, start.clone());
                for (lane, (tv, sv, lv, gv)) in values.iter().copied().enumerate() {
                    let want = (tv + (lv << n) + if gv != 0 { sv } else { N::ZERO }) & mask;
                    assert_eq!(get(&end, &t, lane) + (get(&end, &tail, lane) << n), want);
                    assert_eq!(get(&end, &s, lane), sv);
                }
                for helper in anc.iter().chain(&spare).chain([c0,h].iter()) {
                    assert_eq!(end[helper.0 as usize], 0);
                }
                assert_eq!(symbolic(&inverse, end), start, "inverse n={n} nt={nt}");
                cases += values.len();
            }
            streams += 2;
        }
    }
    eprintln!("CARRY_LIFETIME_ALL_PHASE_PASS streams={streams} cases={cases} tail=0..40 all_measurement_outcomes=true forward_and_inverse=true");
}
