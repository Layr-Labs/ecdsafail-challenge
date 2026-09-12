//! Exact quotient-popcount cache in the no-terminal prefix's idle counter.
use super::*;

pub(super) const BITS: usize = 6;

pub(super) fn enabled(counter: &[QReg]) -> bool {
    if std::env::var("MIDQ_PREFIX_POPCOUNT").ok().as_deref() != Some("1")
        || !prefix_no_terminal_eligible(0)
        || !lowq_hybrid_gate_hold_enabled()
        || lowq_inline_active_enabled()
        || lowq_recompute_gate_predicate_enabled()
        || counter.len() != counter_tape::BITS
        || counter.len() < BITS
    {
        return false;
    }
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    (0..MIDQ_PZ_CUT).all(|i| {
        let (wa, wb, wca, wcb, wq) = reg_widths(i);
        trailmix_q_width_step(wq, wa, wb, wca, wcb) < (1 << BITS)
    })
}

// role=1 is the original multiply role A<B, role=0 is division. No extra
// quantum control is synthesized: no-terminal proves the existing active=1.
// XOR-complement framing conjugates +1 into -1 when role=1.
pub(super) fn update(c: &mut Circuit, counter: &[QReg], role: &QReg, active: &QReg, inverse: bool) {
    assert!(counter.len() >= BITS);
    let count = &counter[..BITS];
    for bit in count {
        c.cx(role, bit);
    }
    if inverse {
        ctrl_dec(c, active, count);
    } else {
        ctrl_inc(c, active, count);
    }
    for bit in count {
        c.cx(role, bit);
    }
}

// q is preserved. Forward cut: C -= popcount(q), so all eight physical
// counter bits are zero when passed to the unchanged tail counter codec.
// After tail inverse: C += popcount(q) before the first reverse swap.
pub(super) fn from_quotient(c: &mut Circuit, counter: &[QReg], q: &[QReg], erase: bool) {
    assert!(counter.len() >= BITS && q.len() < (1 << BITS));
    let count = &counter[..BITS];
    if erase {
        for bit in q.iter().rev() {
            ctrl_dec(c, bit, count);
        }
    } else {
        for bit in q {
            ctrl_inc(c, bit, count);
        }
    }
}

#[path = "prefix_popcount_selftest.rs"]
mod checks;
pub(crate) use checks::{profile, run as selftest};
