//! Opt-in lifetime management for a persistent division frame across the PZ prefix.
//! The raw tail ABI never owns phi or role; both are discharged at the cut.
use super::*;

pub(super) struct Frame {
    phi: Vec<QReg>,
    role: QReg,
}

fn enabled(steps: usize, q: &[QReg], srot: &[QReg], counter: &[QReg]) -> bool {
    if std::env::var("MIDQ_D_ALIGN_DRIVER").ok().as_deref() != Some("1") {
        return false;
    }
    assert!(midq_tail_enabled(), "persistent frame requires the hybrid tail ABI");
    assert_eq!(q.len(), 32, "persistent frame requires the fixed q32 policy");
    assert_eq!(srot.len(), 5, "persistent frame requires the bounded five-bit shift support");
    assert_eq!(env_usize("HYBRID_QCAP", 0), 1100, "this integration is admitted only at hardQ1100");
    assert!(prefix_popcount::enabled(counter), "fixed q32 prefix popcount must remain enabled");
    assert!((0..steps).all(prefix_no_terminal_eligible),
        "persistent frame requires every prefix step to have exact nonterminal support");
    assert_eq!(std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref(), Some("1"),
        "this integration requires the measured common-floor PREP route");
    true
}

impl Frame {
    fn allocate(c: &mut Circuit) -> Self {
        Self {
            phi: c.alloc_qreg_bits("pz.frame.phi", 5),
            role: c.alloc_qreg("pz.frame.role"),
        }
    }

    pub(super) fn start(c: &mut Circuit, steps: usize, q: &[QReg], srot: &[QReg], counter: &[QReg])
        -> Option<Self>
    {
        if !enabled(steps, q, srot, counter) { return None; }
        // The forward ABI has ca=0, cb=1, q=0. Thus R=1 and phi=0.
        let frame = Self::allocate(c);
        c.x(&frame.role);
        Some(frame)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resume(c: &mut Circuit, steps: usize, b: &[QReg], ca: &[QReg], cb: &[QReg],
        q: &[QReg], srot: &[QReg], counter: &[QReg]) -> Option<Self>
    {
        if !enabled(steps, q, srot, counter) { return None; }
        // Tail replay and counter restoration have already recovered the raw cut state.
        let frame = Self::allocate(c);
        d_alignment_iteration::enter(c, b, ca, cb, q, &frame.phi, &frame.role);
        Some(frame)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn step(&self, c: &mut Circuit, a: &mut Vec<QReg>, b: &mut Vec<QReg>,
        ca: &[QReg], cb: &[QReg], q: &[QReg], counter: &[QReg], parity: &QReg,
        srot: &[QReg], offset: &QReg, carry: Option<&QReg>, i: usize, inverse: bool)
    {
        d_alignment_iteration::step(c, a, b, ca, cb, q, counter, parity, srot, offset,
            carry, &self.phi, &self.role, i, inverse);
    }

    pub(super) fn finish_forward(self, c: &mut Circuit, b: &[QReg], ca: &[QReg], cb: &[QReg], q: &[QReg]) {
        d_alignment_iteration::exit(c, b, ca, cb, q, &self.phi, &self.role);
        self.free_zero(c);
    }

    pub(super) fn finish_backward(self, c: &mut Circuit) {
        // The exact inverse prefix has restored ca=0, cb=1, q=0 and phi=0.
        c.x(&self.role);
        self.free_zero(c);
    }

    fn free_zero(self, c: &mut Circuit) {
        for bit in self.phi { c.zero_and_free(bit); }
        c.zero_and_free(self.role);
    }
}
