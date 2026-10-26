use super::*;
use crate::circuit::analyze_ops;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
}

fn put(words: &mut [u64], qs: &[QubitId], shot: usize, value: u64) {
    for (i, q) in qs.iter().enumerate() {
        if value >> i & 1 != 0 { words[q.0 as usize] |= 1u64 << shot; }
    }
}

fn get(words: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter().enumerate().map(|(i, q)| ((words[q.0 as usize] >> shot) & 1) << i).sum()
}

#[test]
fn terminal_sp0_high_h_lease_fix_exact_channel() {
    let mut b = B::new();
    let h = b.alloc_n(6);
    let e = b.alloc();
    let cf = b.alloc();
    let sigma = b.alloc();
    let gap = b.alloc_n(4);
    let dirty = b.alloc_n(7);
    b.begin();
    toggle_terminal_sp0_high_h_leases(&mut b, &h, e, &dirty);
    let fix = b.end();
    b.play(&fix, false);
    let split = b.ops.len();
    b.play(&fix, true);
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());

    let mut cases = vec![];
    for hv in 0u64..64 {
        for ev in 0u64..2 {
            for cfv in 0u64..2 {
                for sgv in 0u64..2 {
                    for gapv in 0u64..16 {
                        for dirtyv in 0u64..8 {
                            cases.push((hv, ev, cfv, sgv, gapv, dirtyv));
                        }
                    }
                }
            }
        }
    }
    for byte in [0u8, 0xff, 0xaa, 0x55, 0x0f, 0xf0, 0x33, 0xcc] {
        for chunk in cases.chunks(64) {
            let mut fixed = Fixed(byte);
            let mut s = Simulator::new(nq.max(b.width()) as usize, nb.max(1) as usize, &mut fixed);
            for (shot, &(hv, ev, cfv, sgv, gapv, dirtyv)) in chunk.iter().enumerate() {
                put(&mut s.qubits, &h, shot, hv);
                put(&mut s.qubits, &[e], shot, ev);
                put(&mut s.qubits, &[cf], shot, cfv);
                put(&mut s.qubits, &[sigma], shot, sgv);
                put(&mut s.qubits, &gap, shot, gapv);
                put(&mut s.qubits, &dirty, shot, dirtyv);
            }
            let initial = s.qubits.clone();
            s.apply_iter(b.ops[..split].iter());
            assert_eq!(s.phase, 0, "forced HMR byte {byte:#x}");
            for (shot, &(hv, ev, cfv, sgv, gapv, dirtyv)) in chunk.iter().enumerate() {
                let flip = ev & (((hv >> 2) & 1) | ((hv >> 3) & 1));
                let want = hv ^ (flip << 4) ^ (flip << 5);
                assert_eq!(get(&s.qubits, &h, shot), want);
                assert_eq!(get(&s.qubits, &[e], shot), ev);
                assert_eq!(get(&s.qubits, &[cf], shot), cfv);
                assert_eq!(get(&s.qubits, &[sigma], shot), sgv);
                assert_eq!(get(&s.qubits, &gap, shot), gapv);
                assert_eq!(get(&s.qubits, &dirty, shot), dirtyv);
            }
            s.apply_iter(b.ops[split..].iter());
            assert_eq!(s.phase, 0);
            assert_eq!(s.qubits, initial);
        }
    }
    eprintln!(
        "TERMINAL_SP0_HIGH_H_FIX cases={} forced_hmr=8 T={} phase=0 dirty_restored",
        cases.len(),
        b.measure(&fix, false)
    );
}

#[test]
fn terminal_sp0_b_eff_predicates_exact_channel() {
    let mut b = B::new();
    let h = b.alloc_n(6);
    let e = b.alloc();
    let sigma = b.alloc();
    let b_target = b.alloc();
    let top_target = b.alloc();
    let cf = b.alloc();
    let control = b.alloc();
    let gap = b.alloc_n(4);
    let dirty = b.alloc_n(7);
    b.begin();
    toggle_terminal_sp0_b_eff(&mut b, &h, sigma, b_target, &dirty, 4, true);
    toggle_terminal_sp0_e_b_eff(&mut b, &h, e, sigma, top_target, &dirty, 4, true);
    let predicates = b.end();
    b.play(&predicates, false);
    let split = b.ops.len();
    b.play(&predicates, true);
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());

    let mut cases = vec![];
    for hv in 0u64..64 {
        for ev in 0u64..2 {
            for sgv in 0u64..2 {
                for cfv in 0u64..2 {
                    for cv in 0u64..2 {
                        for gapv in 0u64..16 {
                            cases.push((hv, ev, sgv, cfv, cv, gapv));
                        }
                    }
                }
            }
        }
    }
    for byte in [0u8, 0xff, 0xaa, 0x55, 0x0f, 0xf0, 0x33, 0xcc] {
        for chunk in cases.chunks(64) {
            let mut fixed = Fixed(byte);
            let mut s = Simulator::new(nq.max(b.width()) as usize, nb.max(1) as usize, &mut fixed);
            for (shot, &(hv, ev, sgv, cfv, cv, gapv)) in chunk.iter().enumerate() {
                let dirtyv = (hv.wrapping_mul(0x35) ^ gapv.wrapping_mul(0x4b) ^ shot as u64) & 0x7f;
                put(&mut s.qubits, &h, shot, hv);
                put(&mut s.qubits, &[e], shot, ev);
                put(&mut s.qubits, &[sigma], shot, sgv);
                put(&mut s.qubits, &[b_target], shot, cfv);
                put(&mut s.qubits, &[top_target], shot, cv);
                put(&mut s.qubits, &[cf], shot, cfv);
                put(&mut s.qubits, &[control], shot, cv);
                put(&mut s.qubits, &gap, shot, gapv);
                put(&mut s.qubits, &dirty, shot, dirtyv);
            }
            let initial = s.qubits.clone();
            s.apply_iter(b.ops[..split].iter());
            assert_eq!(s.phase, 0, "forced HMR byte {byte:#x}");
            for (shot, &(hv, ev, sgv, cfv, cv, gapv)) in chunk.iter().enumerate() {
                let dirtyv = (hv.wrapping_mul(0x35) ^ gapv.wrapping_mul(0x4b) ^ shot as u64) & 0x7f;
                let low_zero = u64::from(hv & 15 == 0);
                let high_or = ((hv >> 2) & 1) | ((hv >> 3) & 1);
                let b_eff = (sgv ^ 1) & (low_zero ^ high_or);
                assert_eq!(get(&s.qubits, &[b_target], shot), cfv ^ b_eff);
                assert_eq!(get(&s.qubits, &[top_target], shot), cv ^ (ev & b_eff));
                assert_eq!(get(&s.qubits, &h, shot), hv);
                assert_eq!(get(&s.qubits, &[e], shot), ev);
                assert_eq!(get(&s.qubits, &[sigma], shot), sgv);
                assert_eq!(get(&s.qubits, &[cf], shot), cfv);
                assert_eq!(get(&s.qubits, &[control], shot), cv);
                assert_eq!(get(&s.qubits, &gap, shot), gapv);
                assert_eq!(get(&s.qubits, &dirty, shot), dirtyv);
            }
            s.apply_iter(b.ops[split..].iter());
            assert_eq!(s.phase, 0);
            assert_eq!(s.qubits, initial);
        }
    }
    eprintln!(
        "TERMINAL_SP0_B_EFF cases={} forced_hmr=8 T={} phase=0 dirty_restored",
        cases.len(),
        b.measure(&predicates, false)
    );
}
