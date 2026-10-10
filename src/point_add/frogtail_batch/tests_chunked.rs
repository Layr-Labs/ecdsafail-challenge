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
    b.chunk_add(chunked::Call {
        a: a.clone(),
        t: t.clone(),
        ctl,
        cout: flagged.then_some(flag),
        pool: pool.clone(),
        sizes: sizes.clone(),
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
