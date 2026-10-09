//! froghop-single: packed cross-paired Euclid inversion with a fixed boundary schedule, one hop (one
//! up-and-down excursion of V) per Euclid step. Design notes: memory/FROGHOP_SINGLE.md.
//!
//! Registers D (dividend) and V (divisor), W lanes each. D logical lane j: cofactor td on [0, M), remainder R on
//! [M, W). V is kept "aligned": V lane j is matched with D lane j, and holds V-frame lane j - pi (V rotated up by
//! pi). M = M(sigma) is classical; moving it between slots is a relabel of lanes [M, W) of both registers.
//!
//! One slot (every op provisioned on every shot):
//!   0  frozen counter (DONE shots)
//!   1  pop (OUT with a nonempty stack) into `be`
//!   2  r-ladder P1 at pi: compare, conditional subtract in RET/DIV; mid: xd (RET/DIV result), tt (OUT turn)
//!   3  step-end logic, push of xd, bit 0 into `be`, role swap
//!   4  t-ladder P2 at pi: COEF td += be * (tv << pi), mid-erasure of be and of the pop flag
//!   5  termination test, phase update, post-state erasures
//!   6  t-ladder P3 at pi + 1: mid-erasure of the turn flag
//!   7  rotation of V and pi update from the post phase, relabel to M(sigma + 1)

use super::arith::{and_lits, cshift, cswap_regs, dec, down, inc, rot2_up, up};
use super::builder::{B, G};
use crate::circuit::QubitId;

#[derive(Clone)]
pub struct Lay {
    pub w: usize,
    pub s: usize,
    pub m: Vec<usize>,
    pub smax: usize,
    /// slots < f1w provision the first-step (f1) logic
    pub f1w: usize,
}

impl Lay {
    pub fn from_text(txt: &str, smax: usize, f1w: usize) -> Lay {
        let mut it = txt.split_whitespace().map(|t| t.parse::<usize>().unwrap());
        let w = it.next().unwrap();
        let s = it.next().unwrap();
        let m: Vec<usize> = it.collect();
        assert_eq!(m.len(), s);
        Lay { w, s, m, smax, f1w }
    }
    fn mm(&self, sigma: usize) -> usize {
        self.m[sigma.min(self.s - 1)]
    }
}

/// Slot scratch pool (all |0> between slots). Roles share qubits by lifetime (see `slot`).
pub struct Sc {
    pub p: Vec<QubitId>,
}
pub const POOL: usize = 13;

pub struct Fh {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    pub pi: Vec<QubitId>,
    pub fo: QubitId,
    /// RET has no qubit: fr = 1 ^ fo ^ fd ^ fnn (the phase flags are one-hot); `fr_swap` turns fd's qubit into fr
    pub fd: QubitId,
    pub fnn: QubitId,
    pub stk: Vec<QubitId>,
    pub dep: Vec<QubitId>,
    pub f1: QubitId,
    pub par: QubitId,
    pub own_par: bool,
    pub sc: Sc,
    pub dirty: Vec<QubitId>,
}

pub const PIB: usize = 5;
/// Lanes of the t-region compared by the third ladder.
pub const P3TOP: usize = 96;
pub const DEPB: usize = 5;
/// Frozen-slot counter of DONE shots, kept in the (then empty) stack wires.
pub const CNTB: usize = 8;

impl Fh {
    /// Allocate the traversal state around existing D/V lane lists (all other qubits fresh |0>).
    /// `par`: Some(q) borrows q as the swap-parity qubit (it is toggled at every step end and not freed with the
    /// traversal state), None allocates one.
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, lay: &Lay, dirty: Vec<QubitId>, par: Option<QubitId>)
                 -> Fh {
        let sc = Sc { p: b.alloc_n(POOL) };
        let own_par = par.is_none();
        let mut q = || b.alloc();
        let mut f = Fh { d, v, pi: vec![], fo: q(), fd: q(), fnn: q(), stk: vec![], dep: vec![], f1: QubitId(0),
                         par: par.unwrap_or_else(|| q()), own_par, sc, dirty };
        // no shot can be DONE in the first-step slots (sigma < f1w), so the DONE flag's qubit holds f1 there
        f.f1 = f.fnn;
        f.pi = b.alloc_n(PIB);
        f.stk = b.alloc_n(lay.smax);
        f.dep = b.alloc_n(DEPB);
        f
    }

    /// fd <-> fr in fd's qubit (fd ^= 1 ^ fo ^ fnn); self-inverse, needs one-hot phase flags.
    fn fr_swap(&self, b: &mut B, f1on: bool) {
        b.cx(self.fo, self.fd);
        if !f1on {
            b.cx(self.fnn, self.fd);
        }
        b.x(self.fd);
    }

    pub fn cnt(&self) -> &[QubitId] {
        &self.stk[0..CNTB]
    }

    /// Scratch pool first, then the persistent state.
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.sc.p.clone();
        v.extend(&self.pi);
        v.extend([self.fo, self.fd, self.fnn]);
        if self.own_par {
            v.push(self.par);
        }
        v.extend(&self.stk);
        v.extend(&self.dep);
        v
    }

    /// Initial state: D = (R = p, td = 1), V = (rv = x' already in V lanes, tv = 0); pi = 1, phase OUT, f1 = 1.
    /// (D lanes are |0> on entry; V's r lanes already hold x'.)
    pub fn init(&mut self, b: &mut B, lay: &Lay) {
        let m0 = lay.m[0];
        let pp = super::refmodel::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[m0 + i]);
            }
        }
        b.x(self.d[0]);
        b.x(self.pi[0]);
        b.x(self.fo);
        b.x(self.f1);
    }

    fn relabel(lanes: &mut Vec<QubitId>, from: usize, to: usize) {
        let w = lanes.len();
        if to > from {
            for m in from..to {
                let top = lanes[w - 1];
                for j in (m..w - 1).rev() {
                    lanes[j + 1] = lanes[j];
                }
                lanes[m] = top;
            }
        } else {
            for m in (to..from).rev() {
                let low = lanes[m];
                for j in m..w - 1 {
                    lanes[j] = lanes[j + 1];
                }
                lanes[w - 1] = low;
            }
        }
    }

    /// Record slot sigma (gates go to the open recording / op stream) and advance the lane maps to sigma + 1.
    pub fn slot(&mut self, b: &mut B, lay: &Lay, sigma: usize) {
        let w = lay.w;
        let mm = lay.mm(sigma);
        let mnext = if sigma + 1 < lay.s { lay.m[sigma + 1] } else { mm };
        let f1on = sigma < lay.f1w;
        let termon = mm >= 256;
        // pi moves by exactly +-1 on every shot in every slot and is 1 at slot 0, so pi == 0 (and with it a step
        // end and the D/V swap) can only happen on odd slots: z0, se and everything they control are skipped on even
        // slots
        let odd = sigma % 2 == 1;
        assert!(!(f1on && termon));
        // pool roles (lifetimes in the step comments): p0 ladder carry-in, and outside the ladders te / cf and the
        // depth counter's top carry; p1 po; p2 be; p3 tt; p4 xd / h; p5 dn / ww; p6 se; p7 z0; p8..p11 AND chains
        // and counter carries; p12 u / dv / kq / tq
        let p = self.sc.p.clone();
        let (c0, po, be, tt, xd, h, dn, ww, se, z0, te, cf, kq, tq, u, dv, pu) =
            (p[0], p[1], p[2], p[3], p[4], p[4], p[5], p[5], p[6], p[7], p[0], p[0], p[12], p[12], p[12], p[11], p[12]);
        let chain = [p[8], p[9], p[10], p[11]];
        let nz = chain[0];
        let na = [chain[1], chain[2], chain[3]];
        let e1 = chain[0];
        let cnt: Vec<QubitId> = self.cnt().to_vec();
        let (fo, fd, fnn) = (self.fo, self.fd, self.fnn);
        let negdep: Vec<(QubitId, bool)> = self.dep.iter().map(|&q| (q, true)).collect();

        // 0. frozen counter (DONE shots), carries in p0..p6
        if !f1on {
            inc(b, fnn, &cnt, &p[0..7]);
        }

        // 1. pop: po = fo & (dep != 0)
        let r_nz = and_lits(b, &negdep, nz, &na);
        b.play(&r_nz, false);
        b.x(nz);
        b.and_c(fo, nz, po);
        b.x(nz);
        b.play(&r_nz, true);
        b.cswap(po, be, self.stk[0]);
        cshift(b, po, &self.stk, false);
        dec(b, po, &self.dep, &[p[3], p[4], p[5], p[6]]);

        // 2. u = fo & (dep == 0) [post-pop]; P1 r-ladder
        b.play(&r_nz, false);
        b.and_c(fo, nz, u);
        // dn = RET | DIV = !(fo ^ fnn)
        b.x(dn);
        b.cx(fo, dn);
        if !f1on {
            b.cx(fnn, dn);
        }
        {
            let t: Vec<QubitId> = self.d[mm..w].to_vec();
            let s: Vec<QubitId> = self.v[mm..w].to_vec();
            let rup = up(b, &t, &s, c0);
            let rdn = down(b, &t, &s, c0, Some(xd));
            b.play(&rup, false);
            let ctop = s[s.len() - 1]; // [rv<<pi > R]
            b.x(ctop);
            b.and_c(dn, ctop, xd); // xd = dn & [R >= rv<<pi]
            b.x(ctop);
            b.and_c(u, ctop, tt); // OUT turn: stack empty after pop and R < rv<<pi
            b.play(&rdn, false);
        }
        if !f1on {
            b.cx(fnn, dn);
        }
        b.cx(fo, dn);
        b.x(dn);
        b.and_u(fo, nz, u);
        b.play(&r_nz, true);

        // 3. step end, push, bit 0, role swap.  z0 = [pi == 0] keeps only its output (chain recomputed in 7)
        let negpi: Vec<(QubitId, bool)> = self.pi[0..PIB - 1].iter().map(|&q| (q, true)).collect();
        let r_pc = and_lits(b, &negpi, p[10], &[p[8], p[9]]);
        let pi4 = self.pi[PIB - 1];
        if odd {
            b.play(&r_pc, false);
            b.x(pi4);
            b.and_c(p[10], pi4, z0);
            b.x(pi4);
            b.play(&r_pc, true);
        }
        self.fr_swap(b, f1on);
        b.and_c(fd, xd, ww); // RET with c = 1 (fd's qubit holds fr)
        self.fr_swap(b, f1on);
        b.cx(fd, dv);
        b.cx(ww, dv); // dv = DIV after the RET->DIV transition
        if odd {
            b.and_c(dv, z0, se); // step end
        }
        b.cx(dv, pu);
        if odd {
            b.cx(se, pu); // push = dv & !se
        }
        cshift(b, pu, &self.stk, true);
        b.cswap(pu, xd, self.stk[0]);
        inc(b, pu, &self.dep, &[p[8], p[9], p[10], p[0]]);
        if odd {
            b.cswap(se, xd, be); // bit 0 of the quotient becomes the COEF control
            b.cx(se, pu);
        }
        b.cx(dv, pu);
        b.cx(ww, dv);
        b.cx(fd, dv);
        if f1on && odd {
            b.and_c(se, self.f1, cf);
            b.cx(cf, self.f1);
        }
        if odd {
            b.cx(se, self.par);
            cswap_regs(b, se, &self.d, &self.v);
        }
        if f1on && odd {
            // cf = se & f1_pre, and at a step end f1_pre = [new D.t == 0]: erase with a dirty-ancilla MCX
            let mut ctrl = vec![se];
            for j in 0..mm {
                b.x(self.d[j]);
                ctrl.push(self.d[j]);
            }
            mcx_dirty(b, &ctrl, cf, &self.dirty);
            for j in 0..mm {
                b.x(self.d[j]);
            }
        }

        // 4. P2: COEF td += be * (tv << pi) with mid-erasure of be and po
        b.play(&r_nz, false); // nz = [dep == 0] (post push; only used with fo, where no push happened)
        {
            let t: Vec<QubitId> = self.d[0..mm].to_vec();
            let s: Vec<QubitId> = self.v[0..mm].to_vec();
            let rup = up(b, &t, &s, c0);
            let rdn = down(b, &t, &s, c0, Some(be));
            b.play(&rdn, true);
            let ctop = s[s.len() - 1]; // [tv<<pi > td_post]; cmp = !ctop
            // be ^= (po | se) & cmp  (po, se exclusive; po is erased below)
            b.x(ctop);
            b.ccx(po, ctop, be);
            if odd {
                b.ccx(se, ctop, be);
            }
            b.x(ctop);
            // po ^= fo & (ne || (cmp & !f1))  ==  fo & !(nz & !(cmp & !f1))
            if f1on {
                b.x(ctop);
                b.x(self.f1);
                b.and_c(ctop, self.f1, kq); // kq = cmp & !f1
                b.x(self.f1);
                b.x(ctop);
                b.x(kq);
                b.and_c(nz, kq, h); // h = nz & !kq
                b.x(kq);
            } else {
                b.and_c(nz, ctop, h); // h = nz & !cmp
            }
            b.x(h);
            b.ccx(fo, h, po);
            b.x(h);
            if f1on {
                b.x(kq);
                b.and_u(nz, kq, h);
                b.x(kq);
                b.x(ctop);
                b.x(self.f1);
                b.and_u(ctop, self.f1, kq);
                b.x(self.f1);
                b.x(ctop);
            } else {
                b.and_u(nz, ctop, h);
            }
            b.play(&rup, true);
        }
        b.play(&r_nz, true);

        // 5. termination, phase update, erasures
        if termon {
            b.and_c(fo, self.d[255], te);
        }
        // DIV -> OUT at a step end (se & !w)
        if odd {
            b.x(ww);
            b.ccx(se, ww, fd);
            b.ccx(se, ww, fo);
            b.x(ww);
        }
        // RET -> (z0 ? OUT : DIV) when w (fr is implicit)
        if odd {
            b.ccx(ww, z0, fo);
            b.x(z0);
            b.ccx(ww, z0, fd);
            b.x(z0);
        } else {
            b.cx(ww, fd); // z0 = 0: RET with c = 1 always goes to DIV
        }
        if termon {
            b.cx(te, fo);
            b.cx(te, fnn);
        }
        b.cx(tt, fo);
        // se: post OUT with pi_pre == 0
        if odd {
            b.ccx(fo, z0, se);
        }
        // w: (post DIV & dep == 1) ^ (post OUT & z0 & dep == 0)
        {
            let mut l1: Vec<(QubitId, bool)> = vec![(self.dep[0], false)];
            l1.extend(self.dep[1..].iter().map(|&q| (q, true)));
            let r_e1 = and_lits(b, &l1, e1, &na);
            b.play(&r_e1, false);
            b.ccx(fd, e1, ww);
            b.play(&r_e1, true);
            if odd {
                b.play(&r_nz, false);
                b.and_c(fo, z0, tq);
                b.ccx(tq, nz, ww);
                b.and_u(fo, z0, tq);
                b.play(&r_nz, true);
            }
        }
        if termon {
            let lits: Vec<(QubitId, bool)> = cnt.iter().map(|&q| (q, true)).collect();
            let r_c = and_lits(b, &lits, kq, &[p[8], p[9], p[10], p[11], p[1], p[2]]);
            b.play(&r_c, false);
            b.ccx(fnn, kq, te);
            b.play(&r_c, true);
        }

        // 6. P3 at pi + 1: erase tt = fr_post & (f1 | !z).  Only the top P3TOP lanes of the t-region are compared:
        //    z is used on post-RET states, where td >= X or X - td >= ~2^-46 X (exact w.p. 1 - O(2^-40))
        {
            let lo = mm.saturating_sub(P3TOP);
            let t: Vec<QubitId> = self.d[lo..mm].to_vec();
            let mut s: Vec<QubitId> = if lo == 0 { vec![self.v[w - 1]] } else { vec![] };
            s.extend(&self.v[lo.saturating_sub(1)..mm - 1]);
            assert_eq!(s.len(), t.len());
            let rup = up(b, &t, &s, c0);
            b.play(&rup, false);
            let ctop = s[s.len() - 1]; // [tv<<(pi+1) > td] = !z
            self.fr_swap(b, f1on); // fd's qubit holds fr_post
            let fr = fd;
            if f1on {
                b.x(self.f1);
                b.x(ctop);
                b.and_c(self.f1, ctop, kq); // kq = !f1 & z
                b.x(kq);
                b.ccx(fr, kq, tt);
                b.x(kq);
                b.and_u(self.f1, ctop, kq);
                b.x(ctop);
                b.x(self.f1);
            } else {
                b.ccx(fr, ctop, tt);
            }
            self.fr_swap(b, f1on);
            b.play(&rup, true);
        }

        // 7. z0 uncompute (pi unchanged so far), rotation and pi update from the post phase
        if odd {
            b.play(&r_pc, false);
            b.x(pi4);
            b.and_u(p[10], pi4, z0);
            b.x(pi4);
            b.play(&r_pc, true);
        }
        // relabel V by -1, then rotate up by 2 when `up` (net +1) else stay (net -1).  up = OUT post phase, or
        // DONE on even slots (DONE shots oscillate +1/-1 so the rotation has only two outcomes)
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        let upq = dn;
        b.cx(fo, upq);
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        rot2_up(b, upq, &self.v);
        // pi += up ? +1 : -1  ==  pi - 1 + 2 up
        let pa = [p[8], p[9], p[10], p[11]];
        let one = p[12];
        b.x(one);
        dec(b, one, &self.pi, &pa);
        b.x(one);
        inc(b, upq, &self.pi[1..], &pa);
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        b.cx(fo, upq);
        let _ = G::X;

        // boundary move (free relabel)
        Self::relabel(&mut self.d, mm, mnext);
        Self::relabel(&mut self.v, mm, mnext);
    }
}

impl Fh {
    /// Forward traversal: all slots, emitting directly. Returns the lane maps at the start of every slot.
    pub fn forward(&mut self, b: &mut B, lay: &Lay) -> Vec<(Vec<QubitId>, Vec<QubitId>)> {
        let mut maps = Vec::with_capacity(lay.s);
        for sigma in 0..lay.s {
            maps.push((self.d.clone(), self.v.clone()));
            self.slot(b, lay, sigma);
        }
        maps
    }
    /// Exact inverse of `forward` (slot recordings played inverted, last slot first).
    pub fn inverse(&mut self, b: &mut B, lay: &Lay, maps: &[(Vec<QubitId>, Vec<QubitId>)]) {
        for sigma in (0..lay.s).rev() {
            self.d = maps[sigma].0.clone();
            self.v = maps[sigma].1.clone();
            b.begin();
            self.slot(b, lay, sigma);
            let rec = b.end();
            b.play(&rec, true);
            self.d = maps[sigma].0.clone();
            self.v = maps[sigma].1.clone();
        }
    }
}

/// Multi-controlled X with dirty (arbitrary-state, restored) ancillas: 4(k-2) Toffoli for k >= 3 controls.
pub fn mcx_dirty(b: &mut B, ctrl: &[QubitId], t: QubitId, dirty: &[QubitId]) {
    let k = ctrl.len();
    match k {
        0 => b.x(t),
        1 => b.cx(ctrl[0], t),
        2 => b.ccx(ctrl[0], ctrl[1], t),
        _ => {
            let a = &dirty[..k - 2];
            assert!(dirty.len() >= k - 2, "not enough dirty ancillas");
            // V-chain (Barenco et al. Lemma 7.2): t ^= c_{k-1} & a_{k-3}, a_i ^= c_{i+1} & a_{i-1}, a_0 ^= c_0 & c_1
            let down_chain = |b: &mut B| {
                for i in (1..k - 2).rev() {
                    b.ccx(ctrl[i + 1], a[i - 1], a[i]);
                }
            };
            let up_chain = |b: &mut B| {
                for i in 1..k - 2 {
                    b.ccx(ctrl[i + 1], a[i - 1], a[i]);
                }
            };
            for _ in 0..2 {
                b.ccx(ctrl[k - 1], a[k - 3], t);
                down_chain(b);
                b.ccx(ctrl[0], ctrl[1], a[0]);
                up_chain(b);
            }
        }
    }
}
