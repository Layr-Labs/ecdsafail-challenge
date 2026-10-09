//! Hybrid walk: the public-layout walk (Skywalk rails, separate cofactor fields, two-step lookback decoder)
//! for the ticks before the switch tick `t1`, then the masked-ring walk for the rest; the walk back runs the
//! exact inverse. See [`super::conv`] for the switch.
use super::conv::{self, Switched};
use super::ring::{kbits, Ring};
use super::rwalk::{self, Parked, WEnv};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::skycof::walk::{self as pw, Envelope, WalkParams};

/// Parked state of the hybrid walk (the ring's parked state; the odometer is the ring's).
pub struct HParked {
    pub pk: Parked,
    pre: Pre,
}

/// What the walk back needs to rebuild the switch (classical).
struct Pre {
    sw_meta: Option<conv::Meta>,
}

pub fn forward(c: &mut Builder, renv: &WEnv, p: &WalkParams, penv: &Envelope, d: &[Q], t1: usize) -> HParked {
    let pf = pw::forward_prefix(c, p, penv, d, t1);
    let sw = conv::fwd(c, renv, p, penv, pf, t1);
    let (mut r, sign, mut h, meta) = sw.split();
    let mut odo: Vec<Q> = Vec::new();
    for t in t1..renv.r {
        if t == renv.tp {
            odo = c.alloc_qubits(renv.odo_bits);
        }
        rwalk::tick_fwd(c, renv, t, &mut r, &mut h, &odo, sign);
        rwalk::trace(c, "hyb-tick", t);
    }
    assert!(!odo.is_empty(), "the ring part must reach the park window");
    rwalk::park_consts(c, renv, &r);
    let n = renv.n;
    c.free_vec(&r.b);
    c.free_vec(&r.vb);
    c.free(r.a[0]);
    let s: Vec<Q> = (0..n - 1).map(|j| r.a[n - 1 - j]).collect();
    HParked { pk: Parked { s, ka: r.ka, h, odo, sign }, pre: Pre { sw_meta: Some(meta) } }
}

pub fn backward(c: &mut Builder, renv: &WEnv, p: &WalkParams, penv: &Envelope, hp: HParked, t1: usize) -> Vec<Q> {
    let n = renv.n;
    let HParked { pk, pre } = hp;
    let Parked { s, ka, mut h, odo, sign } = pk;
    let mut a = vec![c.alloc_qubit()];
    for i in 1..n {
        a.push(s[n - 1 - i]);
    }
    let kb = kbits(n);
    let b = c.alloc_qubits(n);
    let vb = c.alloc_qubits(kb);
    assert_eq!(ka.len(), kb);
    let mut r = Ring { n, cap: renv.cap, a, b, ka, vb, gate: None };
    rwalk::park_consts(c, renv, &r);
    let mut odo = odo;
    for t in (t1..renv.r).rev() {
        rwalk::tick_rev(c, renv, t, &mut r, &mut h, &odo, sign);
        if t == renv.tp {
            c.free_vec(&odo);
            odo = Vec::new();
        }
    }
    let sw = Switched::join(r, sign, h, pre.sw_meta.unwrap());
    let pf = conv::rev(c, renv, p, penv, sw, t1);
    pw::backward_prefix(c, p, penv, pf)
}
