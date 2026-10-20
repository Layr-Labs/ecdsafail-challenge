//! round10/square-chains, follow-up 4: native depth-D conditioning of the leaf-inverse rows (rows m-2 .. 2).
//!
//! Row rho (k = m-1-rho operand bits, window acc[j] = P[2rho+1+j], top acc[k] = tau_rho = P[rho+m]) is the same
//! frame + ripple + frame as main's `row_addsub_cin(inverse)`, written with held carries (fold, AND, unfold) and:
//! * every top tau_r (2 <= r <= m-2) is X-measured once, early: at row r+e's start in the branch where no enabled read
//!   is left (flags), else right after its last read (the terminal repair of row r+1); bits beta_r, done_r, nd_r;
//! * every later write to a measured wire is its phase twin: CX(c->w) -> Z(c)?beta_w, X(w) -> (-1)^beta_w;
//! * carry c_{k-d} (d = 1..D) is computed only under G_d = beta_rho | ... | beta_{rho-d+1}; when it is skipped, its sum
//!   lands on tau_{rho-d}, which is measured in exactly that branch, and the twin Z(c_{k-d}) is paid as
//!   CZ(a, s) CZ(c_{k-d-1}, a^s) of the position below (c_{k-d-1} is computed whenever beta_{rho-d} = 1);
//! * the top carry is never computed: its twin Z(c_k)?beta_rho = CZ(a, s) CZ(c_{k-1}, a^s) (main's terminal repair).
//! Reads of a top happen only under flags that exclude its measurement (see SQUARE-CHAINS.md section 12).
use super::Builder;
use crate::circuit::{BitId, QubitId};
use std::cell::Cell;

thread_local! { static ACTIVE: Cell<bool> = const { Cell::new(false) }; }
pub(super) fn depth() -> usize { std::env::var("SQC_LEAF_D").ok().and_then(|v| v.parse().ok()).unwrap_or(8) }
pub(super) fn active() -> bool { ACTIVE.with(|a| a.get()) && depth() > 0 }
pub(super) fn scoped<R>(on: bool, f: impl FnOnce() -> R) -> R {
    let old = ACTIVE.with(|a| a.replace(on));
    let r = f();
    ACTIVE.with(|a| a.set(old));
    r
}

struct Top { beta: BitId, done: BitId, nd: BitId }
struct Ctx { one: QubitId, tops: Vec<Option<Top>>, m: usize }

impl Ctx {
    fn top_of(&self, p: usize, rho: usize) -> Option<usize> {
        // product position p is tau_r = r + m for some measurable r <= rho
        if p < self.m + 2 { return None; }
        let r = p - self.m;
        (r <= rho && r <= self.m - 2).then_some(r)
    }
    fn t(&self, r: usize) -> &Top { self.tops[r].as_ref().unwrap() }
    /// X-measure tau_r into beta_r if not yet measured (and `cond` holds, if given).
    fn meas(&self, c: &mut Builder, product: &[QubitId], r: usize, cond: Option<BitId>) {
        let t = self.t(r);
        if let Some(b) = cond { c.push_condition(b); }
        c.push_condition(t.nd);
        c.hmr(product[r + self.m], t.beta);
        c.bit_store1(t.done);
        c.bit_store0(t.nd);
        c.pop_condition();
        if cond.is_some() { c.pop_condition(); }
    }
    fn xw(&self, c: &mut Builder, q: QubitId, top: Option<usize>) {
        match top {
            None => c.x(q),
            Some(r) => { let t = self.t(r); c.push_condition(t.nd); c.x(q); c.pop_condition();
                         c.push_condition(t.done); c.z_if(self.one, t.beta); c.pop_condition(); }
        }
    }
    fn cxw(&self, c: &mut Builder, ctl: QubitId, q: QubitId, top: Option<usize>) {
        match top {
            None => c.cx(ctl, q),
            Some(r) => { let t = self.t(r); c.push_condition(t.nd); c.cx(ctl, q); c.pop_condition();
                         c.push_condition(t.done); c.z_if(ctl, t.beta); c.pop_condition(); }
        }
    }
}

fn erase_and(c: &mut Builder, t: QubitId, u: QubitId, v: QubitId) {
    let m = c.alloc_bit(); c.hmr(t, m); c.cz_if(u, v, m); c.free_bit(m); c.release_clean(t);
}
fn or_bits(c: &mut Builder, a: BitId, b: BitId) -> BitId {
    let o = c.alloc_bit(); c.bit_copy(o, a); c.push_condition(b); c.bit_store1(o); c.pop_condition(); o
}
fn not_bit(c: &mut Builder, a: BitId) -> BitId {
    let o = c.alloc_bit(); c.bit_store1(o); c.bit_xor_into(o, a); o
}
/// Phase (-1)^(MAJ(a, s, cin)) = CZ(a, s) CZ(cin, a ^ s), under the current condition stack.
fn maj_phase(c: &mut Builder, a: QubitId, s: QubitId, cin: QubitId) {
    c.cz(a, s); c.cx(a, s); c.cz(cin, s); c.cx(a, s);
}

/// Rows m-2 down to 2 of the leaf inverse (entry state: as main's loop at r = 0; exit: as main's loop before i = 1).
pub(super) fn rows(c: &mut Builder, x: &[QubitId], product: &[QubitId]) {
    let m = x.len();
    let dmax = depth();
    let one = c.alloc_qubit(); c.x(one);
    let mut tops: Vec<Option<Top>> = (0..m).map(|_| None).collect();
    for r in 2..=m - 2 {
        let (beta, done, nd) = (c.alloc_bit(), c.alloc_bit(), c.alloc_bit());
        c.bit_store0(done); c.bit_store1(nd);
        tops[r] = Some(Top { beta, done, nd });
    }
    let cx_ = Ctx { one, tops, m };
    for rho in (2..=m - 2).rev() {
        row(c, x, product, &cx_, rho, dmax);
    }
    for r in 2..=m - 2 { let t = cx_.t(r); for b in [t.beta, t.done, t.nd] { c.free_bit(b); } }
    c.x(one); c.release_clean(one);
}

fn row(c: &mut Builder, x: &[QubitId], product: &[QubitId], ctx: &Ctx, rho: usize, dmax: usize) {
    let m = x.len(); let k = m - 1 - rho;
    let acc: Vec<QubitId> = product[2 * rho + 1..=rho + m].to_vec();
    let a: Vec<QubitId> = x[rho + 1..rho + 1 + k].to_vec();
    let xi = x[rho];
    let top = |j: usize| ctx.top_of(2 * rho + 1 + j, rho);
    let dr = dmax.min(rho.saturating_sub(2)).min(k.saturating_sub(1));
    // this row's top: measured by now except at the head
    ctx.meas(c, product, rho, None);
    // conditions G_d (index d = 1..=dr) and early measurements of tau_{rho-d} under !G_d
    let mut g: Vec<Option<BitId>> = vec![None; dr + 2];
    let mut ng: Vec<Option<BitId>> = vec![None; dr + 2];
    let mut temps: Vec<BitId> = Vec::new();
    if dr >= 1 {
        let g1 = c.alloc_bit(); c.bit_copy(g1, ctx.t(rho).beta); g[1] = Some(g1); temps.push(g1);
        for d in 1..=dr {
            let n = not_bit(c, g[d].unwrap()); ng[d] = Some(n); temps.push(n);
            ctx.meas(c, product, rho - d, Some(n));
            if d < dr { let o = or_bits(c, g[d].unwrap(), ctx.t(rho - d).beta); g[d + 1] = Some(o); temps.push(o); }
        }
    }
    // cond of carry c_t (t = 1..k-1): depth d = k - t
    let cond = |t: usize| -> Option<BitId> { let d = k - t; if d >= 1 && d <= dr { g[d] } else { None } };
    let ncond = |t: usize| -> Option<BitId> { let d = k - t; if d >= 1 && d <= dr { ng[d] } else { None } };
    // frames (main: top frame, then x_all/cx_all on acc[..k], then x_all(acc) for the inverse)
    ctx.xw(c, acc[k], top(k)); ctx.cxw(c, xi, acc[k], top(k));
    for j in 0..k { ctx.xw(c, acc[j], top(j)); }
    for j in 0..k { ctx.cxw(c, xi, acc[j], top(j)); }
    for j in 0..=k { ctx.xw(c, acc[j], top(j)); }
    // forward: carries c_1..c_{k-1} (held), c_0 = xi
    let mut cw: Vec<Option<QubitId>> = vec![None; k];
    for t in 1..k {
        let j = t - 1; let prev = if j == 0 { xi } else { cw[j].unwrap() };
        let q = c.alloc_qubit();
        if let Some(b) = cond(t) { c.push_condition(b); }
        c.cx(prev, a[j]); c.cx(prev, acc[j]); c.ccx(a[j], acc[j], q); c.cx(prev, q); c.cx(prev, acc[j]); c.cx(prev, a[j]);
        if cond(t).is_some() { c.pop_condition(); }
        cw[t] = Some(q);
    }
    let carry = |t: usize| -> QubitId { if t == 0 { xi } else { cw[t].unwrap() } };
    // top carry twin under beta_rho: Z(c_k) = CZ(a, s) CZ(c_{k-1}, a^s) at position k-1
    c.push_condition(ctx.t(rho).beta);
    maj_phase(c, a[k - 1], acc[k - 1], carry(k - 1));
    c.pop_condition();
    if rho - 1 >= 2 { ctx.meas(c, product, rho - 1, None); }
    // backward: sum write at position j (acc[j] ^= a[j] ^ c_j), then erase c_j at position j-1
    for j in (0..k).rev() {
        if j + 1 < k {
            // erase c_{j+1} (computed under cond(j+1)), from the original a[j], acc[j] and c_j
            let t = j + 1; let prev = carry(j); let q = cw[t].unwrap();
            if let Some(b) = cond(t) { c.push_condition(b); }
            c.cx(prev, a[j]); c.cx(prev, acc[j]); c.cx(prev, q);
            let mb = c.alloc_bit(); c.hmr(q, mb); c.cz_if(a[j], acc[j], mb); c.free_bit(mb);
            c.cx(prev, acc[j]); c.cx(prev, a[j]);
            if cond(j + 1).is_some() { c.pop_condition(); }
            c.release_clean(q);
        }
        sum_write(c, ctx, &a, &acc, j, top(j), carry(j), j >= 1 && cond(j).is_some(), cond(j), ncond(j),
                  if j >= 1 { Some((a[j - 1], acc[j - 1], carry(j - 1))) } else { None });
    }
    // frames back (main: x_all(acc); then x_all/cx_all on acc[..k])
    for j in 0..=k { ctx.xw(c, acc[j], top(j)); }
    for j in 0..k { ctx.xw(c, acc[j], top(j)); }
    for j in 0..k { ctx.cxw(c, xi, acc[j], top(j)); }
    for b in temps { c.free_bit(b); }
}

/// acc[j] ^= a[j] ^ c_j, real if acc[j] is not measured, else its twins; a skipped c_j is paid via the position below.
#[allow(clippy::too_many_arguments)]
fn sum_write(c: &mut Builder, ctx: &Ctx, a: &[QubitId], acc: &[QubitId], j: usize, top: Option<usize>, cj: QubitId,
             conditional: bool, cond: Option<BitId>, ncond: Option<BitId>, below: Option<(QubitId, QubitId, QubitId)>) {
    match top {
        None => { assert!(!conditional, "a conditional carry lands below the top region"); c.cx(a[j], acc[j]); c.cx(cj, acc[j]); }
        Some(r) => {
            let t = ctx.t(r);
            c.push_condition(t.nd);
            c.cx(a[j], acc[j]);
            if let Some(b) = cond { c.push_condition(b); }
            c.cx(cj, acc[j]);
            if cond.is_some() { c.pop_condition(); }
            c.pop_condition();
            c.push_condition(t.done);
            c.z_if(a[j], t.beta);
            if let Some(b) = cond { c.push_condition(b); }
            c.z_if(cj, t.beta);
            if cond.is_some() { c.pop_condition(); }
            if let (Some(nb), Some((a1, s1, c1))) = (ncond, below) {
                c.push_condition(nb); c.push_condition(t.beta);
                maj_phase(c, a1, s1, c1);
                c.pop_condition(); c.pop_condition();
            }
            c.pop_condition();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{analyze_ops, QubitOrBit};
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};

    /// Leaf forward (main) + leaf inverse (native when SQC_LEAF_D > 0, else main); random x per shot.
    #[test]
    fn sqleaf_unit() {
        let m: usize = std::env::var("SQLEAF_M").ok().and_then(|v| v.parse().ok()).unwrap_or(32);
        let batches: usize = std::env::var("SQLEAF_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(64);
        let d = std::env::var("SQC_LEAF_D").unwrap_or_else(|_| "8".into());
        super::super::clear_process_env();
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("EXACT_PAIR_CARRY", "1");
        super::super::leapfrog::install_recipe();
        std::env::set_var("SQC_LEAF_D", &d);
        let mut c = Builder::new();
        let x = c.alloc_qubits(m);
        let p = c.alloc_qubits(2 * m);
        super::super::square::sqc_leaf(&mut c, &x, &p, false);
        super::super::square::sqc_leaf(&mut c, &x, &p, true);
        c.declare_qubit_register(&x);
        c.declare_qubit_register(&p);
        let ops = c.take_ops();
        let (nq, nb, _, _) = analyze_ops(ops.iter());
        let rx: Vec<QubitOrBit> = x.iter().map(|&q| QubitOrBit::Qubit(q)).collect();
        let rp: Vec<QubitOrBit> = p.iter().map(|&q| QubitOrBit::Qubit(q)).collect();
        let mut h = sha3::Shake256::default();
        h.update(b"sqleaf");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, (nb as usize).max(1), &mut xof);
        let mut s = 0x2545_f491_4f6c_dd1du64;
        let (mut xbad, mut pbad, mut phase, mut anc) = (0usize, 0usize, 0usize, 0usize);
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut xs = Vec::new();
            for shot in 0..64 {
                s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                let mut v = U256::from(s) | (U256::from(s.rotate_left(17)) << 64);
                v &= (U256::from(1) << m) - U256::from(1);
                sim.set_register(&rx, v, shot);
                xs.push(v);
            }
            sim.apply_iter(ops.iter());
            for (shot, v) in xs.iter().enumerate() {
                if sim.get_register(&rx, shot) != *v { xbad += 1; }
                if sim.get_register(&rp, shot) != U256::ZERO { pbad += 1; }
            }
            phase += sim.phase.count_ones() as usize;
            for q in x.iter().chain(p.iter()) { *sim.qubit_mut(*q) = 0; }
            if sim.qubits.iter().any(|&v| v != 0) { anc += 1; }
        }
        eprintln!("SQLEAF m={m} D={d} wires={nq} T/shot={:.2} shots={} x_bad={xbad} p_bad={pbad} phase_bad={phase} ancilla_bad_batches={anc}",
            sim.stats.toffoli_gates as f64 / (64 * batches) as f64, 64 * batches);
        assert_eq!((xbad, pbad, phase, anc), (0, 0, 0, 0));
    }
}
