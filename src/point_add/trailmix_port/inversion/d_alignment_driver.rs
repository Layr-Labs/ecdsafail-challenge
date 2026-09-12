//! Opt-in lifetime management for a persistent division frame across the PZ prefix.
//! The raw tail ABI never owns phi or role; both are discharged at the cut.
use super::*;

pub(super) struct Frame {
    phi: Vec<QReg>,
    role: QReg,
    cache: Option<d_position_cache::Cache>,
}

fn cache_enabled(frame_enabled: bool, steps: usize) -> bool {
    let requested = match std::env::var("MIDQ_D_POSITION_CACHE").ok().as_deref() {
        None | Some("0") => false,
        Some("1") => true,
        _ => panic!("MIDQ_D_POSITION_CACHE must be0 or1"),
    };
    if !requested {
        return false;
    }
    assert!(
        frame_enabled,
        "position cache requires MIDQ_D_ALIGN_DRIVER=1 and its full admission guard"
    );
    assert_eq!(
        steps, MIDQ_PZ_CUT,
        "cache floor cursor covers the complete selected prefix"
    );
    assert_eq!(
        qretain::fixed_width(),
        Some(32),
        "position cache requires the fixed q32 policy"
    );
    for name in [
        "MIDQ_RETAIN_DIV_LENGTHS",
        "MIDQ_RETAIN_MUL_LENGTHS",
        "MIDQ_VARIABLE_CHUNKS",
        "MIDQ_CHUNKED_PREFIX",
        "MIDQ_CHUNK_COMPARE",
        "MIDQ_CHUNKED_CONTROLLED_ADD",
    ] {
        assert_eq!(
            std::env::var(name).ok().as_deref(),
            Some("1"),
            "position cache requires the measured backend setting {name}=1"
        );
    }
    true
}

fn enabled(steps: usize, q: &[QReg], srot: &[QReg], counter: &[QReg]) -> bool {
    if std::env::var("MIDQ_D_ALIGN_DRIVER").ok().as_deref() != Some("1") {
        return false;
    }
    assert!(
        midq_tail_enabled(),
        "persistent frame requires the hybrid tail ABI"
    );
    assert_eq!(
        q.len(),
        32,
        "persistent frame requires the fixed q32 policy"
    );
    assert_eq!(
        srot.len(),
        5,
        "persistent frame requires the bounded five-bit shift support"
    );
    assert_eq!(
        env_usize("HYBRID_QCAP", 0),
        1100,
        "this integration is admitted only at hardQ1100"
    );
    assert!(
        prefix_popcount::enabled(counter),
        "fixed q32 prefix popcount must remain enabled"
    );
    assert!(
        (0..steps).all(prefix_no_terminal_eligible),
        "persistent frame requires every prefix step to have exact nonterminal support"
    );
    assert_eq!(
        std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref(),
        Some("1"),
        "this integration requires the measured common-floor PREP route"
    );
    true
}

impl Frame {
    fn allocate(c: &mut Circuit) -> Self {
        Self {
            phi: c.alloc_qreg_bits("pz.frame.phi", 5),
            role: c.alloc_qreg("pz.frame.role"),
            cache: None,
        }
    }

    pub(super) fn start(
        c: &mut Circuit,
        steps: usize,
        a: &[QReg],
        b: &[QReg],
        q: &[QReg],
        srot: &[QReg],
        counter: &[QReg],
    ) -> Option<Self> {
        let use_frame = enabled(steps, q, srot, counter);
        let use_cache = cache_enabled(use_frame, steps);
        if !use_frame {
            return None;
        }
        // The forward ABI has ca=0, cb=1, q=0. Thus R=1 and phi=0.
        let mut frame = Self::allocate(c);
        c.x(&frame.role);
        if use_cache {
            // Raw S0 has A=p and phi=0. Keep the cache through the entire prefix.
            frame.cache = Some(d_position_cache::Cache::begin_raw(c, a, b, 0, true));
        }
        Some(frame)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resume(
        c: &mut Circuit,
        steps: usize,
        a: &[QReg],
        b: &[QReg],
        ca: &[QReg],
        cb: &[QReg],
        q: &[QReg],
        srot: &[QReg],
        counter: &[QReg],
    ) -> Option<Self> {
        let use_frame = enabled(steps, q, srot, counter);
        let use_cache = cache_enabled(use_frame, steps);
        if !use_frame {
            return None;
        }
        // Tail replay and counter restoration have already recovered the raw cut state.
        let mut frame = Self::allocate(c);
        if use_cache {
            // Cache beta must observe raw B before the frame's rotate-left.
            frame.cache = Some(d_position_cache::Cache::begin_raw(c, a, b, steps, false));
        }
        d_alignment_iteration::enter(c, b, ca, cb, q, &frame.phi, &frame.role);
        Some(frame)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn step(
        &mut self,
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
        i: usize,
        inverse: bool,
    ) {
        if let Some(cache) = self.cache.as_mut() {
            d_position_cache::step_cached(
                c, a, b, ca, cb, q, counter, parity, srot, offset, carry, &self.phi, &self.role,
                cache, i, inverse,
            );
        } else {
            d_alignment_iteration::step(
                c, a, b, ca, cb, q, counter, parity, srot, offset, carry, &self.phi, &self.role, i,
                inverse,
            );
        }
    }

    pub(super) fn finish_forward(
        mut self,
        c: &mut Circuit,
        a: &[QReg],
        b: &[QReg],
        ca: &[QReg],
        cb: &[QReg],
        q: &[QReg],
    ) {
        d_alignment_iteration::exit(c, b, ca, cb, q, &self.phi, &self.role);
        let cache = self.cache.take();
        self.free_zero(c);
        if let Some(cache) = cache {
            cache.close_raw(c, a, b, false);
        }
    }

    pub(super) fn finish_backward(mut self, c: &mut Circuit, a: &[QReg], b: &[QReg]) {
        // The exact inverse prefix has restored ca=0, cb=1, q=0 and phi=0.
        c.x(&self.role);
        let cache = self.cache.take();
        self.free_zero(c);
        if let Some(cache) = cache {
            cache.close_raw(c, a, b, true);
        }
    }

    fn free_zero(self, c: &mut Circuit) {
        assert!(
            self.cache.is_none(),
            "live position cache must be discharged explicitly"
        );
        for bit in self.phi {
            c.zero_and_free(bit);
        }
        c.zero_and_free(self.role);
    }
}
