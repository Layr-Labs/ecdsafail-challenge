//! froghop-one: froghop-single's one-hop slot machine (one up-and-down excursion of V per Euclid step) on
//! froghop-double's exact-packed registers. Integer model: refmodel_one.rs.
//!
//! D = (r: dividend r_{j-1}, cd: cofactor t_{j-1}), V = (rv: divisor r_j, cv: cofactor target t_{j-2} -> t_j), each
//! W lanes with the value LSB at lane 0 (growing up) and the cofactor LSB at lane W-1 (growing down). V is rotated
//! up by pi against D (aligned lane u + pi holds V-frame lane u). The previous quotient's bits are popped on the
//! up-ramp (cofactor update cv += bit * (cd << pi), the bit erased by [cv >= cd << pi]) while the same ramp searches
//! the alignment of the next division; the division runs on the down-ramp and pushes the quotient bits.
//!
//! Quotient bits live in the register gaps: the division pushes them into V's gap (V frame lanes b + 1 .. b + d above
//! the divisor), and after the step-end swap the up-ramp pops them from D's gap (lanes b + 1 .. b + d above the
//! dividend, top first). D is not written during OUT, and V holds the divisor and its finished cofactor during DIV.
//!
//! One boundary register b (6-bit offset from a per-slot base): the dividend's bit length until the step turns, the
//! divisor's afterwards. k (5 bits) holds the alignment height (0 before it), which makes the alignment event
//! recoverable (k == pi) and is cleared at the step end against the stack depth; at the turn (stack empty) b converts
//! to the divisor's length. Masks: the value ladder works on lanes [pi, B1], B1 = b + [k != 0] pi (its result is not
//! used by aligned OUT shots); the cofactor ladder on lanes > B1 + d, the turn discriminator (source read one lane up)
//! on lanes > B1 + d - 1. A DONE shot keeps its slot counter in k and the low depth bits.
//!
//! Slot: S0 frozen counter; S1 pop (scan of D's gap); S2 value ladder P1 (turn flag tt, division bit xd, alignment
//! flag ta); S3 alignment (k = pi, erase ta) and turn (b -> divisor length); S4 step end, push (scan of V's gap),
//! bit 0, swap; S5 cofactor ladder P2; S6 termination and phase update; S7 turn discriminator P3 (erase tt);
//! S8 rotation and pi update.

use super::arith::{and_lits, cswap_regs, dec, down_m, inc, rot2_up, up_m, Dm};
use super::builder::B;
use super::mask::{mdown, mup, onehot_scan, top_carry, Lad, Mscr, Src};
use crate::circuit::QubitId;

pub const W1: usize = 259;
pub const PIB: usize = 5;
pub const KB: usize = 5;
pub const DEPB: usize = 5;
/// b (1..=256) is stored as the offset u = b - 1 - base(sigma) in BB bits; base is a per-slot classical constant
/// (193 in the first-step slots, 0 where some shot may be in the last step) that keeps every value the slot decodes
/// within [0, 2^BB)
pub const BB: usize = 6;
pub const CNTB: usize = 8;
pub const POOL_1: usize = 20;

#[derive(Clone)]
pub struct LayOne {
    pub w: usize,
    pub s: usize,
    /// per slot: lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 fin 0 termon (fin: some shot may be in the last step, b == 1)
    pub rows: Vec<[usize; 12]>,
    pub smax: usize,
    /// slots < f1w: first-step logic (f1 lives in the DONE flag's qubit there)
    pub f1w: usize,
    /// per slot: base of the offset boundary register
    pub base: Vec<usize>,
    /// per slot: stack windows (pop lanes of D [q0, q1), push lanes of V [u0, u1))
    pub scan: Vec<[usize; 4]>,
}

impl LayOne {
    pub fn from_text(txt: &str, smax: usize) -> LayOne {
        let mut lines = txt.lines();
        let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        let mut base = vec![];
        let mut scan = vec![];
        let rows: Vec<[usize; 12]> = lines
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                let mut r = [0usize; 12];
                r.copy_from_slice(&v[..12]);
                base.push(if v.len() > 12 { v[12] } else { 0 });
                scan.push(if v.len() > 16 { [v[13], v[14], v[15], v[16]] } else { [0, 0, 0, 0] });
                r
            })
            .collect();
        assert_eq!(rows.len(), hdr[1]);
        assert_eq!(*base.last().unwrap(), 0, "the last slot must leave b - 1 unshifted");
        LayOne { w: hdr[0], s: hdr[1], rows, smax, f1w: hdr[2], base, scan }
    }
}

/// Scratch hand-out for one slot (LIFO). Every qubit goes back |0>.
pub struct Pl {
    free: Vec<QubitId>,
    pub n: usize,
    pub hw: usize,
    pub cur: &'static str,
    pub hw_at: &'static str,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
}

impl Pl {
    fn new(pool: &[QubitId]) -> Pl {
        let mut free = pool.to_vec();
        free.reverse();
        Pl { free, n: pool.len(), hw: 0, cur: "", hw_at: "", peaks: Default::default() }
    }
    fn get(&mut self) -> QubitId {
        let q = self.free.pop().expect("froghop-one scratch pool exhausted");
        let used = self.n - self.free.len();
        let e = self.peaks.entry(self.cur).or_insert(0);
        *e = (*e).max(used);
        if self.n - self.free.len() > self.hw {
            self.hw = self.n - self.free.len();
            self.hw_at = self.cur;
        }
        q
    }
    fn get_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.get()).collect()
    }
    fn put(&mut self, q: QubitId) {
        debug_assert!(!self.free.contains(&q));
        self.free.push(q);
    }
    fn put_n(&mut self, qs: &[QubitId]) {
        for &q in qs.iter().rev() {
            self.put(q);
        }
    }
}

/// out ^= AND of literals (qubit, negated?), transient chain from the pool (n >= 2). `undo`: measurement-uncompute
/// (out must hold exactly that AND).
fn and_into(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], out: QubitId, undo: bool) {
    let n = lits.len();
    assert!(n >= 2);
    let (q, neg) = lits[n - 1];
    if n == 2 {
        let (p, ng) = lits[0];
        if ng {
            b.x(p);
        }
        if neg {
            b.x(q);
        }
        if undo { b.and_u(p, q, out) } else { b.and_c(p, q, out) }
        if neg {
            b.x(q);
        }
        if ng {
            b.x(p);
        }
        return;
    }
    let m = pl.get();
    let anc = pl.get_n(n.saturating_sub(3));
    let r = and_lits(b, &lits[..n - 1], m, &anc);
    b.play(&r, false);
    if neg {
        b.x(q);
    }
    if undo { b.and_u(m, q, out) } else { b.and_c(m, q, out) }
    if neg {
        b.x(q);
    }
    b.play(&r, true);
    pl.put_n(&anc);
    pl.put(m);
}

pub struct FhOne {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    pub pi: Vec<QubitId>,
    pub k: Vec<QubitId>,
    pub fo: QubitId,
    pub fd: QubitId,
    /// RET has no qubit: fr = 1 ^ fo ^ fd ^ fnn (one-hot phase flags); in the first-step slots fnn's qubit holds f1
    pub fnn: QubitId,
    pub dep: Vec<QubitId>,
    /// b - 1
    pub bq: Vec<QubitId>,
    /// swap parity (starts as the caller's reflection bit)
    pub par: QubitId,
    pub pool: Vec<QubitId>,
    pub gp: Vec<QubitId>,
    /// passenger lanes lent as dirty ancillas
    pub dirty: Vec<QubitId>,
    pub hw: usize,
    pub hw_at: &'static str,
    pub marks: Vec<(&'static str, usize)>,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
}

impl FhOne {
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, _lay: &LayOne, par: QubitId, dirty: Vec<QubitId>,
                 gpool: usize) -> FhOne {
        let mut q = || b.alloc();
        let (fo, fd, fnn) = (q(), q(), q());
        let pi = b.alloc_n(PIB);
        let k = b.alloc_n(KB);
        let dep = b.alloc_n(DEPB);
        let bq = b.alloc_n(BB);
        let pool = b.alloc_n(POOL_1);
        let gp = b.alloc_n(gpool);
        FhOne { d, v, pi, k, fo, fd, fnn, dep, bq, par, pool, gp, dirty, hw: 0, hw_at: "", marks: vec![], peaks: Default::default() }
    }

    /// every qubit the traversal allocated (not D, V or par)
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.pool.clone();
        v.extend(&self.gp);
        v.extend(&self.pi);
        v.extend(&self.k);
        v.extend([self.fo, self.fd, self.fnn]);
        v.extend(&self.dep);
        v.extend(&self.bq);
        v
    }

    /// DONE counter: k and the low depth bits (k == 0 and depth == 0 at the termination; neither is read for a DONE
    /// shot otherwise)
    pub fn cnt(&self) -> Vec<QubitId> {
        let mut v = self.k.clone();
        v.extend(&self.dep[..CNTB - KB]);
        v
    }

    /// Initial state: D = (r = p, cd = 0), V = (rv = x' already in V lanes [1, 257), cv = 1 at V lane 0), b = 256,
    /// pi = 1, OUT, f1 = 1 (in fnn's qubit).
    pub fn init(&mut self, b: &mut B, lay: &LayOne) {
        let pp = super::refmodel_one::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[i]);
            }
        }
        b.x(self.v[0]); // V-frame lane W-1 (cv bit 0) sits at aligned lane 0 when pi = 1
        let u0 = 255 - lay.base[0]; // b - 1 = 255
        assert!(u0 < 1 << BB);
        for (i, &q) in self.bq.iter().enumerate() {
            if (u0 >> i) & 1 == 1 {
                b.x(q);
            }
        }
        b.x(self.pi[0]);
        b.x(self.fo);
        b.x(self.fnn); // f1
    }

    /// bq += pi (sub = false) or bq -= pi (sub = true), mod 2^BB, everywhere (g = None) or where g = 1.
    /// `inverse` plays the exact inverse. Scratch is transient.
    fn bq_pi(&self, b: &mut B, pl: &mut Pl, g: Option<QubitId>, sub: bool, inverse: bool) {
        let c0 = pl.get();
        let tmp = pl.get();
        let anc = pl.get_n(BB - PIB - 1);
        let t = &self.bq;
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let mode = match g {
            Some(q) => Dm::Cond(q),
            None => Dm::Sum,
        };
        let u = up_m(b, &t[..PIB], &self.pi, c0, false);
        let dd = down_m(b, &t[..PIB], &self.pi, c0, mode, false);
        b.play(&u, false);
        let carry = self.pi[PIB - 1];
        let ctl = match g {
            Some(gq) => {
                b.and_c(gq, carry, tmp);
                tmp
            }
            None => carry,
        };
        inc(b, ctl, &t[PIB..], &anc);
        if let Some(gq) = g {
            b.and_u(gq, carry, tmp);
        }
        b.play(&dd, false);
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
        pl.put_n(&anc);
        pl.put(tmp);
        pl.put(c0);
    }

    /// bq += src (sub = false) or bq -= src, mod 2^BB, for a 5-bit register src, everywhere (g = None) or where g = 1.
    fn bq_reg(&self, b: &mut B, pl: &mut Pl, src: &[QubitId], g: Option<QubitId>, sub: bool, inverse: bool) {
        assert_eq!(src.len(), PIB);
        let c0 = pl.get();
        let tmp = pl.get();
        let anc = pl.get_n(BB - PIB - 1);
        let t = &self.bq;
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let mode = match g {
            Some(q) => Dm::Cond(q),
            None => Dm::Sum,
        };
        let u = up_m(b, &t[..PIB], src, c0, false);
        let dd = down_m(b, &t[..PIB], src, c0, mode, false);
        b.play(&u, false);
        let carry = src[PIB - 1];
        let ctl = match g {
            Some(gq) => {
                b.and_c(gq, carry, tmp);
                tmp
            }
            None => carry,
        };
        inc(b, ctl, &t[PIB..], &anc);
        if let Some(gq) = g {
            b.and_u(gq, carry, tmp);
        }
        b.play(&dd, false);
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
        pl.put_n(&anc);
        pl.put(tmp);
        pl.put(c0);
    }

    /// u ^= fo & [dep == 0] (& [b != 1] in `fin` slots); `undo`: measurement-uncompute.
    fn u_flag(&self, b: &mut B, pl: &mut Pl, u: QubitId, fin: bool, undo: bool) {
        let negdep = self.negdep();
        let nz = pl.get();
        and_into(b, pl, &negdep, nz, false);
        if fin {
            let nb = pl.get();
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
            and_into(b, pl, &bz, nb, false);
            and_into(b, pl, &[(self.fo, false), (nz, false), (nb, true)], u, undo);
            and_into(b, pl, &bz, nb, true);
            pl.put(nb);
        } else if undo {
            b.and_u(self.fo, nz, u);
        } else {
            b.and_c(self.fo, nz, u);
        }
        and_into(b, pl, &negdep, nz, true);
        pl.put(nz);
    }

    fn negdep(&self) -> Vec<(QubitId, bool)> {
        self.dep.iter().map(|&q| (q, true)).collect()
    }
    fn negk(&self) -> Vec<(QubitId, bool)> {
        self.k.iter().map(|&q| (q, true)).collect()
    }

    /// fd <-> fr in fd's qubit (fd ^= 1 ^ fo ^ fnn); self-inverse, needs one-hot phase flags.
    fn fr_swap(&self, b: &mut B, f1on: bool) {
        b.cx(self.fo, self.fd);
        if !f1on {
            b.cx(self.fnn, self.fd);
        }
        b.x(self.fd);
    }

    pub fn slot(&mut self, b: &mut B, lay: &LayOne, sigma: usize) {
        let w = W1;
        let row = lay.rows[sigma];
        let (lv, jw, p1lo, lc, p2hi, pb0, pb1, pe0, pe1, fin, termon) = (row[0], row[1], row[2], row[3], row[4],
            row[5], row[6].min(w), row[7], row[8].min(w), row[9] != 0, row[11] != 0);
        let f1on = sigma < lay.f1w;
        assert!(!(f1on && termon));
        // pi moves by +-1 on every shot every slot and is 1 at slot 0: pi == 0 (step ends, the swap) only on odd slots
        let odd = sigma % 2 == 1;
        let mut pl = Pl::new(&self.pool);
        let (fo, fd, fnn) = (self.fo, self.fd, self.fnn);
        let f1 = fnn; // meaningful only in the first-step slots
        let negdep = self.negdep();
        let negpi: Vec<(QubitId, bool)> = self.pi.iter().map(|&q| (q, true)).collect();
        let cnt: Vec<QubitId> = self.cnt();
        let [pop0, pop1, push0, push1] = lay.scan[sigma];
        // gated scans decode (offset value, gate) with the gate as top bit: a lane can only match a gated shot when its
        // offset value j - 1 - base (j - base for the D probe) is in [0, 2^BB), so clip the windows to those lanes (a
        // lane outside would match ungated shots)
        let bu = lay.base[sigma];
        let clip1 = |lo: usize, hi: usize| (lo.max(bu + 1), hi.min(w).min(bu + 1 + (1 << BB)));
        let (pop0, pop1) = clip1(pop0, pop1);
        let (push0, push1) = clip1(push0, push1);
        let (pb0, pb1) = clip1(pb0, pb1);
        let (pe0, pe1) = (pe0.max(bu), pe1.min(w).min(bu + (1 << BB)));

        // offset register: u += base(sigma - 1) - base(sigma)
        let base = lay.base[sigma] as isize;
        if sigma > 0 {
            let c = (lay.base[sigma - 1] as isize - base).rem_euclid(1 << BB) as usize;
            self.bq_add_const(b, &mut pl, c);
        }
        if fin || termon {
            assert_eq!(base, 0, "slot {sigma}: [b == 1] needs base 0");
        }
        if f1on {
            assert_eq!(base, 193, "slot {sigma}: the first-step marker needs base 193");
        }

        // S0 frozen counter (DONE shots)
        self.marks.push(("S0", b.ops.len()));
        pl.cur = "S0";
        if !f1on {
            let anc = pl.get_n(CNTB - 1);
            inc(b, fnn, &cnt, &anc);
            pl.put_n(&anc);
        }

        // S1 pop: po = fo & (dep != 0); the popped bit goes to be
        self.marks.push(("S1", b.ops.len()));
        pl.cur = "S1";
        let po = pl.get();
        let be = pl.get();
        {
            let nz = pl.get();
            and_into(b, &mut pl, &negdep, nz, false);
            b.x(nz);
            b.and_c(fo, nz, po);
            b.x(nz);
            and_into(b, &mut pl, &negdep, nz, true);
            pl.put(nz);
            // the stack top (depth d) sits in D's gap at lane b + d (b: the dividend's length through OUT)
            if pop1 > pop0 {
                let dep = self.dep.clone();
                self.bq_reg(b, &mut pl, &dep, None, false, false); // bq = b - 1 + d
                let mut bpo = self.bq.clone();
                bpo.push(po);
                let pre = pl.get_n(BB);
                let dref = self.d.clone();
                onehot_scan(b, &bpo, &pre, pop0, pop1, (1isize << BB) - 1 - base, |b, j, o| {
                    b.cswap(o, be, dref[j]);
                });
                pl.put_n(&pre);
                self.bq_reg(b, &mut pl, &dep, None, false, true);
            }
            let anc = pl.get_n(DEPB - 1);
            dec(b, po, &self.dep, &anc);
            pl.put_n(&anc);
        }

        // S2 value ladder P1 over lanes [0, lv), active [pi, B1]: xd = division bit, tt = OUT turn, ta = alignment
        self.marks.push(("S2", b.ops.len()));
        pl.cur = "S2";
        let xd = pl.get();
        let tt = pl.get();
        let ta = pl.get();
        {
            // g = fo & !al (OUT, not aligned, not the last step), kept through the ladder in place of al
            // (al = !g on every shot: RET / DIV shots are aligned and DONE shots have b == 1)
            let g = pl.get();
            {
                let (al, alr) = self.al_on(b, &mut pl, fin);
                b.x(al);
                b.and_c(fo, al, g);
                b.x(al);
                self.al_off(b, &mut pl, fin, al, alr);
            }
            // u = fo & [dep == 0] post-pop, and [b != 1] where some shot may be in the last step (that step never
            // turns: it ends when its stack is empty)
            let u = pl.get();
            self.u_flag(b, &mut pl, u, fin, false);
            if lv > 0 {
                b.x(g);
                self.bq_pi(b, &mut pl, Some(g), false, false); // bq = B1 - 1
                b.x(g);
            }
            if lv > 0 {
                let c0 = pl.get();
                let mf = pl.get_n(3);
                let pa = pl.get_n(PIB - 1);
                let pre = pl.get_n(BB - 1);
                let t: Vec<QubitId> = self.d[0..lv].to_vec();
                let s: Vec<QubitId> = self.v[0..lv].to_vec();
                let mut srcs =
                    vec![Src { lo: 0, hi: jw.min(lv), v: self.pi.clone(), a: 0, d: 1, pre: pa.clone(), late: false }];
                if p1lo < lv {
                    srcs.push(Src { lo: p1lo, hi: lv, v: self.bq.clone(), a: -2 - base, d: 1, pre: pre.clone(), late: false });
                }
                let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &ms, g: &self.gp };
                let ru = mup(b, &ld);
                let rd = mdown(b, &ld, Some(xd));
                b.play(&ru, false);
                let ct = top_carry(&ld); // [rv<<pi > R]
                // division bit xd = (RET | DIV) & !ct, as DIV & !ct ^ RET & !ct (fd's qubit holds fr after fr_swap)
                b.x(ct);
                b.ccx(fd, ct, xd);
                self.fr_swap(b, f1on);
                b.ccx(fd, ct, xd);
                self.fr_swap(b, f1on);
                b.x(ct);
                b.and_c(g, ct, ta); // alignment found
                // OUT turn: stack empty after the pop and aligned (now or before): tt = u & !(g & !ct) = u & !(g ^ ta)
                b.cx(g, ta);
                b.x(ta);
                b.and_c(u, ta, tt);
                b.x(ta);
                b.cx(g, ta);
                b.play(&rd, false);
                pl.put_n(&pre);
                pl.put_n(&pa);
                pl.put_n(&mf);
                pl.put(c0);
            }
            if lv > 0 {
                b.x(g);
                self.bq_pi(b, &mut pl, Some(g), false, true);
                b.x(g);
            }
            self.u_flag(b, &mut pl, u, fin, true);
            pl.put(u);
            {
                let (al, alr) = self.al_on(b, &mut pl, fin);
                b.x(al);
                b.and_u(fo, al, g);
                b.x(al);
                self.al_off(b, &mut pl, fin, al, alr);
            }
            pl.put(g);
        }

        // S3 alignment (ta shots): k = pi; erase ta = fo & [k == pi].  Turn (tt shots, stack empty): b <- b - k + 1 - dl
        // (the divisor's length) with dl = !V[b - k] (V frame, phys b - k + pi), erased with D[b_new + k - 1]
        self.marks.push(("S3", b.ops.len()));
        pl.cur = "S3";
        {
            for i in 0..KB {
                b.ccx(ta, self.pi[i], self.k[i]);
            }
            // ta = fo & [k == pi]: no other OUT shot has k == pi (k == 0 or k < pi)
            for i in 0..PIB {
                b.cx(self.k[i], self.pi[i]);
            }
            let e = pl.get();
            and_into(b, &mut pl, &negpi, e, false);
            b.ccx(fo, e, ta);
            and_into(b, &mut pl, &negpi, e, true);
            pl.put(e);
            for i in 0..PIB {
                b.cx(self.k[i], self.pi[i]);
            }
        }
        pl.put(ta);
        {
            let kk = self.k.clone();
            let pp = self.pi.clone();
            let dl = pl.get();
            let mut btt = self.bq.clone();
            btt.push(tt);
            let ttoff = 1isize << BB;
            self.bq_reg(b, &mut pl, &kk, Some(tt), true, false); // tt: bq = b - 1 - k
            if pb1 > pb0 {
                self.bq_reg(b, &mut pl, &pp, None, false, false);
                let pre = pl.get_n(BB);
                let vref = self.v.clone();
                onehot_scan(b, &btt, &pre, pb0, pb1, ttoff - 1 - base, |b, j, o| {
                    b.x(vref[j]);
                    b.ccx(o, vref[j], dl);
                    b.x(vref[j]);
                });
                pl.put_n(&pre);
                self.bq_reg(b, &mut pl, &pp, None, false, true);
            }
            {
                let h = pl.get();
                b.x(dl);
                b.and_c(tt, dl, h);
                b.x(dl);
                let anc = pl.get_n(BB - 1);
                inc(b, h, &self.bq, &anc);
                pl.put_n(&anc);
                b.x(dl);
                b.and_u(tt, dl, h);
                b.x(dl);
                pl.put(h);
            }
            if pe1 > pe0 {
                self.bq_reg(b, &mut pl, &kk, None, false, false); // tt: bq = b_new - 1 + k
                let pre = pl.get_n(BB);
                let dref = self.d.clone();
                onehot_scan(b, &btt, &pre, pe0, pe1, ttoff - base, |b, j, o| {
                    b.ccx(o, dref[j], dl);
                });
                pl.put_n(&pre);
                self.bq_reg(b, &mut pl, &kk, None, false, true);
            }
            pl.put(dl);
        }

        // S4 step end, push, bit 0 into be, k cleared, swap.  z0 = [pi == 0] until S8 (odd slots only)
        self.marks.push(("S4", b.ops.len()));
        pl.cur = "S4";
        // z0 lives only on odd slots: S4 (step end), then again from S6 to S8
        let mut z0 = QubitId(u64::MAX);
        if odd {
            z0 = pl.get();
            and_into(b, &mut pl, &negpi, z0, false);
        }
        let ww = pl.get(); // RET with c = 1
        let se = pl.get(); // step end
        {
            self.fr_swap(b, f1on);
            b.and_c(fd, xd, ww);
            self.fr_swap(b, f1on);
            let dv = pl.get();
            b.cx(fd, dv);
            b.cx(ww, dv); // DIV after the RET->DIV transition
            if odd {
                b.and_c(dv, z0, se);
            }
            let pu = pl.get();
            b.cx(dv, pu);
            if odd {
                b.cx(se, pu); // push = dv & !se
            }
            let anc = pl.get_n(DEPB - 1);
            inc(b, pu, &self.dep, &anc);
            pl.put_n(&anc);
            // the pushed bit goes to V's gap at V-frame lane b + d (b: the divisor's length), phys b + d + pi
            if push1 > push0 {
                let dep = self.dep.clone();
                let pp = self.pi.clone();
                self.bq_reg(b, &mut pl, &dep, None, false, false);
                self.bq_reg(b, &mut pl, &pp, None, false, false); // bq = b - 1 + d + pi
                let mut bpu = self.bq.clone();
                bpu.push(pu);
                let pre = pl.get_n(BB);
                let vref = self.v.clone();
                onehot_scan(b, &bpu, &pre, push0, push1, (1isize << BB) - 1 - base, |b, j, o| {
                    b.cswap(o, xd, vref[j]);
                });
                pl.put_n(&pre);
                self.bq_reg(b, &mut pl, &pp, None, false, true);
                self.bq_reg(b, &mut pl, &dep, None, false, true);
            }
            if odd {
                b.cswap(se, xd, be); // bit 0 of the quotient becomes the cofactor control
                b.cx(se, pu);
            }
            b.cx(dv, pu);
            pl.put(pu);
            b.cx(ww, dv);
            b.cx(fd, dv);
            pl.put(dv);
            if odd {
                let cf = pl.get();
                if f1on {
                    // first step end: cf = se & f1; f1 cleared.  The first step divides p (256 bits), so there b + k =
                    // 257; every later dividend is shorter, b + k <= 256: erase cf with se & [bq + k >= 256]
                    b.and_c(se, f1, cf);
                    b.cx(cf, f1);
                    let cy = pl.get();
                    let r = self.bq_k_carry(b, &mut pl, cy);
                    b.play(&r.0, false);
                    b.and_u(se, cy, cf);
                    b.play(&r.0, true);
                    pl.put_n(&r.1);
                    pl.put(cy);
                }
                pl.put(cf);
                // k == dep + 1 at a step end (bit 0 is in be, bits k-1 .. 1 on the stack): clear it
                let anc = pl.get_n(DEPB - 1);
                inc(b, se, &self.dep, &anc);
                for i in 0..KB {
                    b.ccx(se, self.dep[i], self.k[i]);
                }
                dec(b, se, &self.dep, &anc);
                pl.put_n(&anc);
                b.cx(se, self.par);
                cswap_regs(b, se, &self.d, &self.v);
                // z0 is idle in S5: erase it here, recompute it in S6
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        }
        pl.put(xd);

        // termination flag (OUT, b == 1, k == 0, empty stack after the pop), taken before bq holds B1 - 1
        let te = pl.get();
        if termon {
            // in two parts to keep the AND chains short: nb = [bq == 0], te = fo & nb & [k == 0] & [dep == 0]
            let nb = pl.get();
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&q| (q, true)).collect();
            and_into(b, &mut pl, &bz, nb, false);
            let mut lits: Vec<(QubitId, bool)> = vec![(nb, false)];
            lits.extend(self.k.iter().map(|&q| (q, true)));
            lits.extend(self.dep.iter().map(|&q| (q, true)));
            lits.push((fo, false));
            and_into(b, &mut pl, &lits, te, false);
            and_into(b, &mut pl, &bz, nb, true);
            pl.put(nb);
        }

        // S5 cofactor ladder P2 over phys [lc, W) (ladder lane l <-> phys W-1-l), active phys > B1:
        // cv += be * (cd << pi), with the mid-ladder erasure of be and po.  bq holds B1 - 1 from here to the end of S7.
        self.marks.push(("S5", b.ops.len()));
        pl.cur = "S5";
        let (al, alr) = self.al_on(b, &mut pl, fin);
        self.bq_pi(b, &mut pl, Some(al), false, false); // bq = B1 - 1
        let depq = self.dep.clone();
        self.bq_reg(b, &mut pl, &depq, None, false, false); // bq = B1 + d - 1: above D's stack (OUT shots)
        {
            if lc < w {
                let n = w - lc;
                let c0 = pl.get();
                let mf = pl.get_n(3);
                let pre = pl.get_n(BB - 1);
                let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
                let s: Vec<QubitId> = (0..n).map(|l| self.d[w - 1 - l]).collect();
                let mut srcs = vec![];
                if p2hi > lc {
                    srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq.clone(), a: w as isize - 2 - base, d: -1,
                                    pre: pre.clone(), late: false });
                }
                let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &self.gp };
                let ru = mup(b, &ld);
                let rd = mdown(b, &ld, Some(be));
                b.play(&rd, true);
                let ct = top_carry(&ld); // [cd<<pi > cv_post]; cmp = !ct
                // be ^= (po | se) & cmp  (po, se exclusive)
                b.x(ct);
                b.ccx(po, ct, be);
                if odd {
                    b.ccx(se, ct, be);
                }
                b.x(ct);
                // po ^= fo & (ne | (cmp & !f1))  ==  fo & !(nz & !(cmp & !f1))
                let nz = pl.get();
                and_into(b, &mut pl, &negdep, nz, false);
                let h = pl.get();
                if f1on {
                    let kq = pl.get();
                    b.x(ct);
                    b.x(f1);
                    b.and_c(ct, f1, kq); // kq = cmp & !f1
                    b.x(f1);
                    b.x(ct);
                    b.x(kq);
                    b.and_c(nz, kq, h); // h = nz & !kq
                    b.x(kq);
                    b.x(h);
                    b.ccx(fo, h, po);
                    b.x(h);
                    b.x(kq);
                    b.and_u(nz, kq, h);
                    b.x(kq);
                    b.x(ct);
                    b.x(f1);
                    b.and_u(ct, f1, kq);
                    b.x(f1);
                    b.x(ct);
                    pl.put(kq);
                } else {
                    b.and_c(nz, ct, h); // h = nz & !cmp
                    b.x(h);
                    b.ccx(fo, h, po);
                    b.x(h);
                    b.and_u(nz, ct, h);
                }
                pl.put(h);
                and_into(b, &mut pl, &negdep, nz, true);
                pl.put(nz);
                b.play(&ru, true);
                pl.put_n(&pre);
                pl.put_n(&mf);
                pl.put(c0);
            }
        }
        pl.put(be);
        pl.put(po);

        // S6 termination (OUT, b == 1, k == 0, empty stack after the pop), phase update, erasures of se and ww
        self.marks.push(("S6", b.ops.len()));
        pl.cur = "S6";
        if odd {
            z0 = pl.get();
            and_into(b, &mut pl, &negpi, z0, false);
        }
        self.marks.push(("S6a", b.ops.len()));
        pl.cur = "S6a";
        // DIV -> OUT at a step end (se & !ww)
        if odd {
            b.x(ww);
            b.ccx(se, ww, fd);
            b.ccx(se, ww, fo);
            b.x(ww);
        }
        // RET -> (z0 ? OUT : DIV) when ww (fr is implicit)
        if odd {
            b.ccx(ww, z0, fo);
            b.x(z0);
            b.ccx(ww, z0, fd);
            b.x(z0);
        } else {
            b.cx(ww, fd);
        }
        if termon {
            b.cx(te, fo);
            b.cx(te, fnn);
        }
        b.cx(tt, fo); // OUT -> RET
        // se: post OUT with pi == 0
        if odd {
            b.ccx(fo, z0, se);
        }
        pl.put(se);
        self.marks.push(("S6b", b.ops.len()));
        pl.cur = "S6b";
        // ww: (post DIV & dep == 1) ^ (post OUT & z0 & dep == 0)
        {
            let mut l1: Vec<(QubitId, bool)> = vec![(self.dep[0], false)];
            l1.extend(self.dep[1..].iter().map(|&q| (q, true)));
            let e1 = pl.get();
            and_into(b, &mut pl, &l1, e1, false);
            b.ccx(fd, e1, ww);
            and_into(b, &mut pl, &l1, e1, true);
            pl.put(e1);
            if odd {
                let nz = pl.get();
                and_into(b, &mut pl, &negdep, nz, false);
                let tq = pl.get();
                b.and_c(fo, z0, tq);
                b.ccx(tq, nz, ww);
                b.and_u(fo, z0, tq);
                pl.put(tq);
                and_into(b, &mut pl, &negdep, nz, true);
                pl.put(nz);
            }
        }
        pl.put(ww);
        self.marks.push(("S6c", b.ops.len()));
        pl.cur = "S6c";
        if termon {
            // te = DONE shots with cnt == 0 (the termination slot)
            let mut lits: Vec<(QubitId, bool)> = cnt.iter().map(|&q| (q, true)).collect();
            lits.push((fnn, false));
            and_into(b, &mut pl, &lits, te, true);
        }
        pl.put(te);

        // S7 turn discriminator P3: z = [cv >= cd << (pi + 1)]; erase tt = fr_post & (f1 | !z).  Ladder lane l: target
        // V lane W-1-l (cv bit l + pi), source D lane W-l (cd bit l - 1), active phys > B1
        self.marks.push(("S7", b.ops.len()));
        pl.cur = "S7";
        if lc < w {
            let n = w - lc;
            let c0 = pl.get();
            let mf = pl.get_n(3);
            let pre = pl.get_n(BB - 1);
            let zl = pl.get();
            let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (0..n).map(|l| if l < 1 { zl } else { self.d[w - l] }).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq.clone(), a: w as isize - 1 - base, d: -1,
                                pre: pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &self.gp };
            let ru = mup(b, &ld);
            b.play(&ru, false);
            let ct = top_carry(&ld); // [cd<<(pi+1) > cv] = !z
            self.fr_swap(b, f1on); // fd's qubit holds fr_post
            if f1on {
                let kq = pl.get();
                b.x(f1);
                b.x(ct);
                b.and_c(f1, ct, kq); // kq = !f1 & z
                b.x(kq);
                b.ccx(fd, kq, tt);
                b.x(kq);
                b.and_u(f1, ct, kq);
                b.x(ct);
                b.x(f1);
                pl.put(kq);
            } else {
                b.ccx(fd, ct, tt);
            }
            self.fr_swap(b, f1on);
            b.play(&ru, true);
            pl.put(zl);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        }
        self.bq_reg(b, &mut pl, &depq, None, false, true);
        self.bq_pi(b, &mut pl, Some(al), false, true);
        self.al_off(b, &mut pl, fin, al, alr);
        pl.put(tt);

        // S8 z0 erase, rotation and pi update: up = OUT post, or DONE on even slots
        self.marks.push(("S8", b.ops.len()));
        pl.cur = "S8";
        if odd {
            and_into(b, &mut pl, &negpi, z0, true);
            pl.put(z0);
        }
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        let upq = pl.get();
        b.cx(fo, upq);
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        rot2_up(b, upq, &self.v);
        {
            let one = pl.get();
            let anc = pl.get_n(PIB - 1);
            b.x(one);
            dec(b, one, &self.pi, &anc);
            b.x(one);
            inc(b, upq, &self.pi[1..], &anc[..PIB - 2]);
            pl.put_n(&anc);
            pl.put(one);
        }
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        b.cx(fo, upq);
        pl.put(upq);
        assert_eq!(pl.free.len(), self.pool.len(), "scratch leak");
        if pl.hw > self.hw {
            self.hw = pl.hw;
            self.hw_at = pl.hw_at;
        }
        for (k, v) in pl.peaks.iter() {
            let e = self.peaks.entry(k).or_insert(0);
            *e = (*e).max(*v);
        }
    }

    /// al = [k != 0] | [b == 1] (the second term only in `fin` slots, where some shot may be in the last step).
    /// Returns (al, extra qubit holding [b == 1] if computed).
    fn al_on(&self, b: &mut B, pl: &mut Pl, fin: bool) -> (QubitId, Option<QubitId>) {
        let nal = pl.get(); // [k == 0] & [b != 1]
        let mut lits = self.negk();
        let nb1 = if fin {
            let q = pl.get();
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
            and_into(b, pl, &bz, q, false);
            lits.push((q, true));
            Some(q)
        } else {
            None
        };
        and_into(b, pl, &lits, nal, false);
        if let Some(q) = nb1 {
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
            and_into(b, pl, &bz, q, true);
            pl.put(q);
        }
        b.x(nal);
        (nal, nb1.map(|_| QubitId(u64::MAX)))
    }
    fn al_off(&self, b: &mut B, pl: &mut Pl, fin: bool, al: QubitId, nb1: Option<QubitId>) {
        b.x(al);
        let mut lits = self.negk();
        let nb1 = nb1.map(|_| {
            let q = pl.get();
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
            and_into(b, pl, &bz, q, false);
            q
        });
        if let Some(q) = nb1 {
            lits.push((q, true));
        }
        and_into(b, pl, &lits, al, true);
        if let Some(q) = nb1 {
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
            and_into(b, pl, &bz, q, true);
            pl.put(q);
        }
        let _ = fin;
        pl.put(al);
    }

    /// bq += c (mod 2^BB) for a classical c: unconditional increments of bq[i..] for the set bits of c (or decrements
    /// of the complement when that is shorter). Scratch is transient.
    fn bq_add_const(&self, b: &mut B, pl: &mut Pl, c: usize) {
        let n = BB;
        let m = 1usize << n;
        let c = c % m;
        if c == 0 {
            return;
        }
        let (cc, neg) = if (m - c).count_ones() < c.count_ones() { (m - c, true) } else { (c, false) };
        for i in 0..n {
            if (cc >> i) & 1 == 0 {
                continue;
            }
            let t = &self.bq[i..];
            if neg {
                for &q in t {
                    b.x(q);
                }
            }
            if t.len() > 1 {
                let anc = pl.get_n(t.len() - 2);
                inc(b, t[0], &t[1..], &anc);
                pl.put_n(&anc);
            }
            b.x(t[0]);
            if neg {
                for &q in t {
                    b.x(q);
                }
            }
        }
    }

    /// Recording computing cy = [bq + k >= 2^BB] (carry out of the BB-bit sum bq + k) with logical-AND carries from
    /// the pool; returns (recording, carry qubits to hand back). Playing it inverted uncomputes the carries.
    /// cy = [bq + k + 1 >= 2^BB]: with base 193, [b + k >= 257] (the first step's end).
    fn bq_k_carry(&self, b: &mut B, pl: &mut Pl, cy: QubitId) -> (Vec<super::builder::G>, Vec<QubitId>) {
        let g = pl.get_n(BB - 1);
        b.begin();
        // carries c_1 .. c_{BB-1} into g, carry out into cy; k is zero above bit KB-1
        let mut c: Option<QubitId> = None;
        for i in 0..BB {
            let tgt = if i + 1 == BB { cy } else { g[i] };
            let t = self.bq[i];
            let kq = if i < KB { Some(self.k[i]) } else { None };
            match (kq, c) {
                (Some(q), None) => {
                    // carry-in 1: c_1 = t | q
                    b.x(t);
                    b.x(q);
                    b.and_c(t, q, tgt);
                    b.x(tgt);
                    b.x(q);
                    b.x(t);
                }
                (None, Some(cq)) => b.and_c(t, cq, tgt),
                (Some(q), Some(cq)) => {
                    // MAJ(t, q, c) = c ^ (t ^ c)(q ^ c)
                    b.cx(cq, t);
                    b.cx(cq, q);
                    b.and_c(t, q, tgt);
                    b.cx(cq, q);
                    b.cx(cq, t);
                    // tgt = (t ^ c)(q ^ c); add c to make it MAJ
                    b.cx(cq, tgt);
                }
                (None, None) => {}
            }
            c = Some(tgt);
        }
        (b.end(), g)
    }
}

impl FhOne {
    /// Forward traversal: all slots, emitting directly. Returns V's lane map at the start of every slot.
    pub fn forward(&mut self, b: &mut B, lay: &LayOne) -> Vec<Vec<QubitId>> {
        let mut maps = Vec::with_capacity(lay.s);
        for sigma in 0..lay.s {
            maps.push(self.v.clone());
            self.slot(b, lay, sigma);
        }
        maps
    }
    /// Exact inverse of `forward` (slot recordings played inverted, last slot first).
    pub fn inverse(&mut self, b: &mut B, lay: &LayOne, maps: &[Vec<QubitId>]) {
        for sigma in (0..lay.s).rev() {
            self.v = maps[sigma].clone();
            b.begin();
            self.slot(b, lay, sigma);
            let rec = b.end();
            b.play(&rec, true);
            self.v = maps[sigma].clone();
        }
    }
}
