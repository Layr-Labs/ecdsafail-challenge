use super::builder::B;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}

#[test]
fn average_carry_erase_forced_measurements() {
    for n in [2usize, 4, 8, 32] {
        let mut b = B::new();
        let a = b.alloc_n(n);
        let t = b.alloc_n(n);
        let ctl = b.alloc();
        let flag = b.alloc();
        let pool = b.alloc_n(n);
        b.begin();
        b.carry_erase(&a, &t, ctl, flag, &pool);
        let r = b.end();
        b.play(&r, false);
        let split = b.ops.len();
        b.play(&r, true);
        for byte in [0u8, 255, 170] {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            let mask = (1u64 << n) - 1;
            for shot in 0..64 {
                let aa = if shot % 3 == 0 {
                    mask
                } else {
                    ((shot * 17) as u64) & mask
                };
                let tt = if shot % 5 == 0 {
                    mask
                } else {
                    ((shot * 29) as u64) & mask
                };
                let cc = shot % 2 == 0;
                for (i, q) in a.iter().enumerate() {
                    sim.qubits[q.0 as usize] |= ((aa >> i) & 1) << shot;
                }
                for (i, q) in t.iter().enumerate() {
                    sim.qubits[q.0 as usize] |= ((tt >> i) & 1) << shot;
                }
                if cc {
                    sim.qubits[ctl.0 as usize] |= 1 << shot;
                }
                if cc && aa + tt > mask {
                    sim.qubits[flag.0 as usize] |= 1 << shot;
                }
            }
            let initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..split].iter());
            assert_eq!(sim.qubits[flag.0 as usize], 0);
            assert_eq!(sim.phase, 0, "n={n} outcome={byte}");
            for q in &pool {
                assert_eq!(sim.qubits[q.0 as usize], 0);
            }
            let active = (byte.count_ones() * 8) as u64;
            assert_eq!(
                sim.stats.toffoli_gates,
                n as u64 * active,
                "conditional execution count"
            );
            sim.apply_iter(b.ops[split..].iter());
            assert_eq!(sim.qubits, initial, "n={n} outcome={byte} reverse");
            assert_eq!(sim.phase, 0);
        }
    }
}
