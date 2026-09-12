//! Emitted-gate checks for the support-specialized swap boundary.
//! These component tests do not establish whole-prefix/whole-circuit success.
use super::*;
use crate::circuit::{analyze_ops, Op};
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};

struct Measurements(Option<u8>, sha3::Shake256Reader);
impl Measurements {
    fn new(mode: usize) -> Self {
        let mut h = Shake256::default();
        h.update(b"prefix-no-terminal-boundary-20260910");
        Self([Some(0), Some(255), Some(0x55), None][mode], h.finalize_xof())
    }
}
impl XofReader for Measurements {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(value) = self.0 { out.fill(value); } else { self.1.read(out); }
    }
}
fn emitted(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}
fn check<R: XofReader>(sim: &Simulator<'_, R>, ids: &[QubitId], words: &[usize], live: u64) {
    assert_eq!(sim.phase & live, 0xa53c_09f0_1278_ee11 & live, "phase changed");
    for (bit, &id) in ids.iter().enumerate() {
        let expected = words.iter().enumerate().fold(0u64, |v, (lane, word)|
            v | (((word >> bit) & 1) as u64) << lane);
        assert_eq!(sim.qubit(id) & live, expected & live, "data bit {bit}");
    }
    for (i, &value) in sim.qubits.iter().enumerate() {
        if !ids.contains(&QubitId(i as u64)) { assert_eq!(value & live, 0, "scratch {i}"); }
    }
}
fn one(no_terminal: bool, measured: bool, chunked: bool) -> (usize, usize) {
    std::env::set_var("MIDQ_MEASURE_PREDICATE", if measured { "1" } else { "0" });
    std::env::set_var("MIDQ_CHUNKED_PREDICATE", if chunked { "1" } else { "0" });
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("a", 2);
    let b = c.alloc_qreg_bits("b", 2);
    let ca = c.alloc_qreg_bits("ca", 2);
    let cb = c.alloc_qreg_bits("cb", 2);
    let q = c.alloc_qreg_bits("q", 2);
    let counter = c.alloc_qreg_bits("counter", 2);
    let parity = c.alloc_qreg("parity");
    let ids: Vec<_> = a.iter().chain(&b).chain(&ca).chain(&cb).chain(&q)
        .chain(&counter).chain([&parity]).map(|q| QubitId(q.id().into())).collect();
    let active_counter: &[QReg] = if no_terminal { &[] } else { &counter };
    let active = compute_active(&mut c, active_counter);
    swap_and_done_forward(&mut c, &a, &b, &ca, &cb, &q, &counter, &parity, active, no_terminal);
    let split = c.b.ops.len();
    let active = undo_done_and_swap(&mut c, &a, &b, &ca, &cb, &q, &counter, &parity, no_terminal);
    uncompute_active(&mut c, active_counter, &active);
    c.zero_and_free(active);
    for op in &c.b.ops { op.validate(); }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let nq = nq.max(ids.iter().map(|q| q.0+1).max().unwrap());
    // Support: counter=0, B>0, and q=0 implies A>0. Include A=0,q>0
    // because draining a pending final quotient is not terminal.
    let inputs: Vec<_> = (0..1usize << ids.len()).filter(|v|
        (v >> 10) & 3 == 0 && (v >> 2) & 3 != 0
            && !(v & 3 == 0 && (v >> 8) & 3 == 0)).collect();
    for mode in 0..4 {
        let mut rng = Measurements::new(mode);
        let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
        for batch in inputs.chunks(64) {
            sim.clear_for_shot();
            let live = u64::MAX >> (64-batch.len());
            for (bit, &id) in ids.iter().enumerate() {
                *sim.qubit_mut(id) = batch.iter().enumerate().fold(0, |v, (lane, word)|
                    v | (((word >> bit)&1) as u64) << lane);
            }
            sim.phase = 0xa53c_09f0_1278_ee11;
            let expected: Vec<_> = batch.iter().map(|&v| {
                if (v >> 8) & 3 != 0 { v } else {
                    let changed = (v ^ (v >> 2)) & 0x33;
                    v ^ changed ^ (changed << 2) ^ (1 << 12)
                }
            }).collect();
            predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops[..split], live);
            check(&sim, &ids, &expected, live);
            predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops[split..], live);
            check(&sim, &ids, batch, live);
        }
    }
    (inputs.len()*4, emitted(&c.b.ops))
}
pub(crate) fn run() {
    let mut checked=0;
    for measured in [false,true] {
        for chunked in [false,true] {
            let (n, old_t)=one(false,measured,chunked);
            let (m, new_t)=one(true,measured,chunked);
            assert_eq!(n,m); checked+=n+m;
            eprintln!("PREFIX_NO_TERMINAL_BOUNDARY measured={measured} chunked={chunked} cases_each={n} old_emitted={old_t} new_emitted={new_t}");
        }
    }
    eprintln!("PREFIX_NO_TERMINAL_BOUNDARY PASS checked={checked}; independent midpoint outputs, inverse, phase, every reset and scratch; not whole-prefix validation");
}

// Build just the boundary helpers at each configured production width. This
// isolates their raw emitted cost with representative persistent passengers;
// it does not replace a full optimized circuit profile or benchmark.
pub(crate) fn profile() {
    crate::point_add::trailmix_port::configure_sub1000_trailmix_route();
    std::env::set_var("MIDQ_PREFIX_NO_TERMINAL", "1");
    assert!(prefix_no_terminal_eligible(0), "production guard must pass for this profile");
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    let mut totals=[0usize;2];
    let mut peaks=[0u64;2];
    for i in 0..MIDQ_PZ_CUT {
        let (wa,wb,wca,wcb,wq)=reg_widths(i);
        let wg=trailmix_ab_width(wa.max(wb));
        let wc=trailmix_cacb_width(wca.max(wcb));
        let wq=trailmix_q_width_step(wq,wa,wb,wca,wcb);
        for (which,no_terminal) in [false,true].into_iter().enumerate() {
            let mut c=Circuit::new();
            //256-bit passenger, external sign, s_rot and offset; parity and
            //counter are allocated separately below, as in the live prefix.
            let _passenger=c.alloc_qreg_bits("profile.passenger",256+1+trailmix_srot_width()+1);
            let a=c.alloc_qreg_bits("a",wg); let b=c.alloc_qreg_bits("b",wg);
            let ca=c.alloc_qreg_bits("ca",wc); let cb=c.alloc_qreg_bits("cb",wc);
            let q=c.alloc_qreg_bits("q",wq);
            let counter=c.alloc_qreg_bits("counter",trailmix_counter_width());
            let parity=c.alloc_qreg("parity");
            let active_counter: &[QReg]=if no_terminal {&[]} else {&counter};
            let active=compute_active(&mut c,active_counter);
            swap_and_done_forward(&mut c,&a,&b,&ca,&cb,&q,&counter,&parity,active,no_terminal);
            let active=undo_done_and_swap(&mut c,&a,&b,&ca,&cb,&q,&counter,&parity,no_terminal);
            uncompute_active(&mut c,active_counter,&active);c.zero_and_free(active);
            totals[which]+=emitted(&c.b.ops);
            peaks[which]=peaks[which].max(c.b.peak_qubits as u64);
        }
    }
    eprintln!("PREFIX_NO_TERMINAL_PROFILE prefix_pair_old={} prefix_pair_new={} full_point_add_raw_boundary_saved={} helper_peak_old={} helper_peak_new={}; unoptimized emitted boundary census only, not executed T",totals[0],totals[1],2*(totals[0]-totals[1]),peaks[0],peaks[1]);
}
