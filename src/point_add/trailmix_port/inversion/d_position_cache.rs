//! Isolated cached-position iteration. No production-driver activation.
use super::*;

pub(crate) fn floor(index: usize) -> usize {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    assert!(index <= MIDQ_PZ_CUT);
    if index == MIDQ_PZ_CUT {
        return 0;
    }
    (0..=index)
        .map(|i| {
            let (_, _, a, b, _) = reg_widths(i);
            223usize.saturating_sub(trailmix_cacb_width(a.max(b)))
        })
        .min()
        .unwrap()
}

pub(crate) struct Cache {
    alpha: Option<Vec<QReg>>,
    beta: Vec<QReg>,
    index: usize,
}
impl Cache {
    /// Call on raw A/B. A known-initial cache is only for A=p at index0.
    pub(crate) fn begin_raw(
        c: &mut Circuit,
        a: &[QReg],
        b: &[QReg],
        index: usize,
        known_initial: bool,
    ) -> Self {
        let lo = floor(index);
        assert!(lo < a.len() && lo < b.len());
        let alpha = if known_initial {
            assert_eq!(index, 0);
            assert_eq!(a.len(), 256);
            let q = c.alloc_qreg_bits("cache.Apos", 9);
            xor_const(c, &q, 255 - lo);
            q
        } else {
            clz_deposit_a(c, a, 9, lo)
        };
        let beta = clz_deposit_a(c, b, 9, lo);
        Self {
            alpha: Some(alpha),
            beta,
            index,
        }
    }
    pub(crate) fn close_raw(
        mut self,
        c: &mut Circuit,
        a: &[QReg],
        b: &[QReg],
        known_initial: bool,
    ) {
        let lo = floor(self.index);
        let alpha = self.alpha.take().expect("A cache present at boundary");
        if known_initial {
            assert_eq!(self.index, 0);
            xor_const(c, &alpha, 255 - lo);
            for q in alpha {
                c.zero_and_free(q);
            }
        } else {
            clz_undeposit_a(c, alpha, a, lo);
        }
        clz_undeposit_a(c, self.beta, b, lo);
    }
    fn erase_a(&mut self, c: &mut Circuit, a: &[QReg], lo: usize) {
        clz_undeposit_a(c, self.alpha.take().unwrap(), a, lo);
        c.flush_pending_frees();
    }
    fn create_a(&mut self, c: &mut Circuit, a: &[QReg], lo: usize) {
        assert!(self.alpha.is_none());
        self.alpha = Some(clz_deposit_a(c, a, 9, lo));
    }
    // Only for an emission-cost row whose live cache data are supplied by its
    // interface. This does not assert that zero data form a valid PZ state.
    fn placeholder(c: &mut Circuit, index: usize) -> Self {
        Self {
            alpha: Some(c.alloc_qreg_bits("cache.Apos", 9)),
            beta: c.alloc_qreg_bits("cache.Bpos", 9),
            index,
        }
    }
}

fn retune(c: &mut Circuit, beta: &[QReg], delta: usize, carry: &QReg, inverse: bool) {
    use crate::point_add::trailmix_port::arith::cuccaro::add_cuccaro_3n_uncontrolled_refs_with_carry;
    if delta == 0 {
        return;
    }
    assert!(delta < 512);
    assert_eq!(beta.len(), 9);
    let constant = c.alloc_qreg_bits("cache.floor.constant", 9);
    xor_const(c, &constant, delta);
    if inverse {
        for q in beta {
            c.x(q);
        }
    }
    add_cuccaro_3n_uncontrolled_refs_with_carry(
        c,
        &beta.iter().collect::<Vec<_>>(),
        &constant.iter().collect::<Vec<_>>(),
        carry,
    );
    if inverse {
        for q in beta {
            c.x(q);
        }
    }
    xor_const(c, &constant, delta);
    for q in constant {
        c.zero_and_free(q);
    }
}

fn swap_positions(c: &mut Circuit, g: &QReg, cache: &Cache) {
    for (a, b) in cache.alpha.as_ref().unwrap().iter().zip(&cache.beta) {
        c.cswap(g, a, b);
    }
}
fn swap(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    role: &QReg,
    cache: &Cache,
) {
    let source = if prefix_popcount::enabled(counter) {
        &counter[..prefix_popcount::BITS]
    } else {
        q
    };
    let zero = c.alloc_qreg("cache.swap.qzero");
    or_is_zero(c, source, &zero);
    for (a, b) in a.iter().zip(b) {
        c.cswap(&zero, a, b);
    }
    for (a, b) in ca.iter().zip(cb) {
        c.cswap(&zero, a, b);
    }
    c.cx(&zero, parity);
    c.cx(&zero, role);
    swap_positions(c, &zero, cache);
    clear_zero_predicate(c, source, &zero, false);
    c.zero_and_free(zero);
}

/// Entire cache lifetime must share any enclosing classical condition. Live
/// nonzero cache words cannot be independently skipped across host resizing.
#[allow(clippy::too_many_arguments)]
pub(crate) fn step_cached(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    srot: &[QReg],
    offset: &QReg,
    carry: Option<&QReg>,
    phi: &[QReg],
    role: &QReg,
    cache: &mut Cache,
    i: usize,
    inverse: bool,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{
        reg_los, reg_widths, shift_bounds,
    };
    assert!(prefix_no_terminal_eligible(i) && lowq_hybrid_gate_hold_enabled());
    assert!(!lowq_inline_active_enabled() && !lowq_recompute_gate_predicate_enabled());
    assert_eq!(
        std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref(),
        Some("1")
    );
    assert_eq!(qretain::fixed_width(), Some(32));
    assert_eq!(q.len(), 32);
    assert_eq!(cache.index, if inverse { i + 1 } else { i });
    assert_eq!(srot.len(), 5);
    assert_eq!(phi.len(), 5);
    let carry = carry.expect("cache retuning borrows the existing clean passenger carry");
    let (wa, wb, wca, wcb, _) = reg_widths(i);
    let n = trailmix_ab_width(wa.max(wb));
    let (pa, pb, _, _, _) = reg_widths(i.saturating_sub(1));
    let previous = trailmix_ab_width(pa.max(pb));
    let v = n.max(previous);
    assert_eq!(ca.len(), trailmix_cacb_width(wca.max(wcb)));
    assert_eq!(ca.len(), cb.len());
    let lo = floor(i);
    let next = floor(i + 1);
    assert!(next <= lo && lo < n);
    let delta = lo - next;
    let (_, _, lca, lcb, _) = reg_los(i);
    let (_, sm) = shift_bounds(i);
    let rb = (usize::BITS - sm.max(1).leading_zeros()) as usize;
    if !inverse {
        shrunken_pz_resize(c, a, v, "A");
        shrunken_pz_resize(c, b, v, "B");
        d_alignment_prep::apply_cached(
            c,
            a,
            b,
            ca,
            cb,
            q,
            phi,
            role,
            srot,
            offset,
            cache.alpha.as_ref().unwrap(),
            &cache.beta,
            false,
        );
        shrunken_pz_resize(c, a, n, "A");
        shrunken_pz_resize(c, b, n, "B");
        cache.erase_a(c, a, lo);
        let active = compute_active(c, &[]);
        if prefix_popcount::enabled(counter) {
            prefix_popcount::update(c, counter, role, &active, false);
        }
        let gate = HybridGateControl::new(&active, role);
        multiply_substep_windowed(
            c,
            ca,
            cb,
            q,
            srot,
            offset,
            GateControl::Hybrid(&gate),
            Some(carry),
            lca,
            lcb,
            rb,
        );
        gate.release(c);
        c.x(role);
        let gate = HybridGateControl::new(&active, role);
        with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
            retained_division::add_update(
                c,
                g,
                &a.iter().collect::<Vec<_>>(),
                &b.iter().collect::<Vec<_>>(),
                true,
            );
            set_bit_at_s_gated(c, q, phi, g);
        });
        gate.release(c);
        retune(c, &cache.beta, delta, carry, false);
        cache.create_a(c, a, next);
        cache.index = i + 1;
        swap(c, a, b, ca, cb, q, counter, parity, role, cache);
        uncompute_active(c, &[], &active);
        c.zero_and_free(active);
    } else {
        shrunken_pz_resize(c, a, n, "A");
        shrunken_pz_resize(c, b, n, "B");
        swap(c, a, b, ca, cb, q, counter, parity, role, cache);
        cache.erase_a(c, a, next);
        retune(c, &cache.beta, delta, carry, true);
        let active = compute_active(c, &[]);
        let gate = HybridGateControl::new(&active, role);
        with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
            set_bit_at_s_gated(c, q, phi, g);
            retained_division::add_update(
                c,
                g,
                &a.iter().collect::<Vec<_>>(),
                &b.iter().collect::<Vec<_>>(),
                false,
            );
        });
        gate.release(c);
        c.x(role);
        let gate = HybridGateControl::new(&active, role);
        multiply_substep_windowed_inv(
            c,
            ca,
            cb,
            q,
            srot,
            offset,
            GateControl::Hybrid(&gate),
            Some(carry),
            lca,
            lcb,
            rb,
        );
        gate.release(c);
        if prefix_popcount::enabled(counter) {
            prefix_popcount::update(c, counter, role, &active, true);
        }
        uncompute_active(c, &[], &active);
        c.zero_and_free(active);
        cache.create_a(c, a, lo);
        cache.index = i;
        shrunken_pz_resize(c, a, v, "A");
        shrunken_pz_resize(c, b, v, "B");
        d_alignment_prep::apply_cached(
            c,
            a,
            b,
            ca,
            cb,
            q,
            phi,
            role,
            srot,
            offset,
            cache.alpha.as_ref().unwrap(),
            &cache.beta,
            true,
        );
        shrunken_pz_resize(c, a, previous, "A");
        shrunken_pz_resize(c, b, previous, "B");
    }
}

#[path = "d_position_cache_selftest.rs"]
mod checks;
#[path = "d_position_cache_ledger.rs"]
mod ledger;
pub(crate) fn diagnostic() {
    if std::env::var_os("MIDQ_D_POSITION_CACHE_SELFTEST").is_some() {
        checks::run();
    } else {
        ledger::run();
    }
}
