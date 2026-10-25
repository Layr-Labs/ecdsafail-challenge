//! Adapter: run `lowq_mm`'s modular products on this tree's `Builder` in place of `skycof_mm`.
//! `mulf(a, b, k, neg)` = a * b * 2^-k * (-1)^neg with (k, neg) = (0, false) or (404, true), out fresh;
//! `mulf_inv` is its exact inverse and frees `out`. Room = cap - live (- the output for the forward call), as in
//! `skycof::pointadd::mm_cfg`. Wires the products return are already |0>, so they are released without a reset.
use super::builder::Builder;
use super::lowq_mm::{self, Circ, Kind, P, Q};
use crate::circuit::{BitId, NO_BIT};

impl Circ for Builder {
    fn q(&mut self) -> Q {
        self.alloc_qubit()
    }
    fn free(&mut self, q: Q) {
        self.release_clean(q)
    }
    fn bit(&mut self) -> BitId {
        self.alloc_bit()
    }
    fn free_bit(&mut self, b: BitId) {
        Builder::free_bit(self, b)
    }
    fn x(&mut self, t: Q) {
        Builder::x(self, t)
    }
    fn z(&mut self, t: Q) {
        self.z_if(t, NO_BIT)
    }
    fn cx(&mut self, c: Q, t: Q) {
        Builder::cx(self, c, t)
    }
    fn ccx(&mut self, a: Q, b: Q, t: Q) {
        Builder::ccx(self, a, b, t)
    }
    fn cz(&mut self, a: Q, b: Q) {
        Builder::cz(self, a, b)
    }
    fn cz_if(&mut self, a: Q, b: Q, m: BitId) {
        Builder::cz_if(self, a, b, m)
    }
    fn hmr(&mut self, t: Q, m: BitId) {
        Builder::hmr(self, t, m)
    }
    fn push(&mut self, m: BitId) {
        self.push_condition(m)
    }
    fn pop(&mut self) {
        self.pop_condition()
    }
    fn phase(&mut self, p: &'static str) {
        let e = self.report_totals().map_or(0.0, |x| x.1);
        let mut g = PH.lock().unwrap();
        if let Some((cur, t)) = g.0.take() {
            *g.1.entry(cur).or_insert(0.0) += e - t;
        }
        g.0 = Some((p, e));
    }
}

type PhAcc = (Option<(&'static str, f64)>, std::collections::BTreeMap<&'static str, f64>);
static PH: std::sync::Mutex<PhAcc> = std::sync::Mutex::new((None, std::collections::BTreeMap::new()));

fn ph_dump(c: &Builder, tag: &str) {
    let e = c.report_totals().map_or(0.0, |x| x.1);
    let mut g = PH.lock().unwrap();
    if let Some((cur, t)) = g.0.take() {
        *g.1.entry(cur).or_insert(0.0) += e - t;
    }
    let v: Vec<String> = g.1.iter().map(|(k, v)| format!("{k}={v:.0}")).collect();
    eprintln!("LOWQ_PH {tag} {}", v.join(" "));
    g.1.clear();
}

fn kind(k: usize, neg: bool) -> Kind {
    match (k, neg) {
        (0, false) => Kind::Mu,
        (k, true) if k == lowq_mm::MUC_K => Kind::MuC,
        _ => panic!("lowq_adapter: unsupported product k={k} neg={neg}"),
    }
}

pub(crate) fn mulf(c: &mut Builder, cap: usize, guard: usize, cmpw: usize, a: &[Q], b: &[Q], k: usize, neg: bool) -> Vec<Q> {
    let room = cap.saturating_sub(c.active_qubits() as usize + lowq_mm::N);
    assert!(room >= 90, "lowq mulf: room {room} too small (live {})", c.active_qubits());
    let p = P { g: guard, cw: cmpw, room };
    let t0 = c.report_totals().map_or(0.0, |x| x.1);
    let out = lowq_mm::product_fwd(c, &p, kind(k, neg), a, b);
    ph_dump(c, "fwd");
    eprintln!("LOWQ_PROD fwd k={k} room={room} maxc={} live={} T={:.0}", p.maxc(), c.active_qubits(), c.report_totals().map_or(0.0, |x| x.1) - t0);
    out
}

pub(crate) fn mulf_inv(c: &mut Builder, cap: usize, guard: usize, cmpw: usize, a: &[Q], b: &[Q], k: usize, neg: bool, out: Vec<Q>) {
    let room = cap.saturating_sub(c.active_qubits() as usize);
    assert!(room >= 90, "lowq mulf_inv: room {room} too small (live {})", c.active_qubits());
    let p = P { g: guard, cw: cmpw, room };
    let t0 = c.report_totals().map_or(0.0, |x| x.1);
    lowq_mm::product_inv(c, &p, kind(k, neg), a, b, out);
    ph_dump(c, "inv");
    eprintln!("LOWQ_PROD inv k={k} room={room} maxc={} live={} T={:.0}", p.maxc(), c.active_qubits(), c.report_totals().map_or(0.0, |x| x.1) - t0);
}
