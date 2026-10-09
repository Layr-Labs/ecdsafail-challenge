//! froghop-double: bit-serial 4-phase extended Euclid on exact-packed registers (W = 258), two hops per Euclid step.
//! Design notes: memory/FROGHOP_DOUBLE.md.
//!
//! D and V each hold a value (LSB at lane 0, growing up) and a cofactor (LSB at lane W-1, growing down). V is
//! rotated up by pi relative to D. One shared boundary register b (bits of the current dividend during AL, of the
//! divisor afterwards; stored as b - 1 in 8 bits) gives every per-shot mask; ladders mask only inside classical
//! per-slot windows.
//!
//! Slot order: S0 frozen counter; S2 value ladder P1 (mask [pi <= lane <= b + [DV] pi]); S3 turn: probe, b update,
//! probe erase; S4 DV push / DV0 bit 0, AL->DV and DV0->CO moves; S1 CO pop (shots that were CO at slot start);
//! S5 RT0 swap, RT0->AL / DONE; S6 cofactor ladder P2 (COEF, mask lane >= b + pi); S7 CO->RT; S8 discriminator
//! ladder P3; S9 rotation and pi update.
//!
//! Scratch: one pool of POOL_D qubits, all |0> between slots, handed out per step (`Pl`).

use super::arith::{and_lits, cshift, cswap_regs, dec, down_m, inc, rot2_up, up_m, Dm};
use super::builder::B;
use super::mask::{mdown, mup, onehot_scan, top_carry, Lad, Mscr, Src};
use crate::circuit::QubitId;

pub const WD: usize = 258;
pub const PIB: usize = 5;
pub const DEPB: usize = 5;
/// b (1..=256) is stored as b - 1 in BB bits
pub const BB: usize = 8;
pub const CNTB: usize = 8;
pub const POOL_D: usize = 17;
/// P3 compares only lanes within this depth below the lowest shot boundary of the slot
pub const P3DEPTH: usize = 20;

#[derive(Clone)]
pub struct LayDouble {
    pub w: usize,
    pub s: usize,
    /// per slot: Lv jw p1lo lc p2hi pb0 pb1 pe0 pe1
    pub rows: Vec<[usize; 9]>,
    pub smax: usize,
}

impl LayDouble {
    pub fn from_text(txt: &str, smax: usize) -> LayDouble {
        let mut lines = txt.lines();
        let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        let rows: Vec<[usize; 9]> = lines
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]]
            })
            .collect();
        assert_eq!(rows.len(), hdr[1]);
        LayDouble { w: hdr[0], s: hdr[1], rows, smax }
    }
}

/// Scratch hand-out for one slot (LIFO). Every qubit goes back |0>.
struct Pl {
    free: Vec<QubitId>,
}

impl Pl {
    fn new(pool: &[QubitId]) -> Pl {
        let mut free = pool.to_vec();
        free.reverse();
        Pl { free }
    }
    fn get(&mut self) -> QubitId {
        self.free.pop().expect("Froghop v2 scratch pool exhausted")
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
    /// claim specific (currently free) qubits again
    fn take(&mut self, qs: &[QubitId]) {
        for q in qs {
            let i = self.free.iter().position(|x| x == q).expect("take of a busy scratch qubit");
            self.free.remove(i);
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

pub struct FhDouble {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    pub pi: Vec<QubitId>,
    pub fa: QubitId,
    pub fv: QubitId,
    pub fc: QubitId,
    /// RT has no qubit: fr = !fa & !fv & !fc & !fn
    pub fnn: QubitId,
    pub stk: Vec<QubitId>,
    pub dep: Vec<QubitId>,
    /// b - 1
    pub bq: Vec<QubitId>,
    /// swap parity (starts at whatever the caller put there, e.g. the reflection bit)
    pub par: QubitId,
    pub pool: Vec<QubitId>,
    /// clean logical-AND carry qubits for the ladders' ordinary lanes (|0> between ladder passes)
    pub gp: Vec<QubitId>,
    pub marks: Vec<(&'static str, usize)>,
}

impl FhDouble {
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, lay: &LayDouble, par: QubitId) -> FhDouble {
        let mut q = || b.alloc();
        let (fa, fv, fc, fnn) = (q(), q(), q(), q());
        let pi = b.alloc_n(PIB);
        let stk = b.alloc_n(lay.smax);
        let dep = b.alloc_n(DEPB);
        let bq = b.alloc_n(BB);
        let pool = b.alloc_n(POOL_D);
        let gp = b.alloc_n(super::GPOOL);
        FhDouble { d, v, pi, fa, fv, fc, fnn, stk, dep, bq, par, pool, gp, marks: vec![] }
    }

    /// every qubit the traversal allocated (not D, V or par)
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.pool.clone();
        v.extend(&self.gp);
        v.extend(&self.pi);
        v.extend([self.fa, self.fv, self.fc, self.fnn]);
        v.extend(&self.stk);
        v.extend(&self.dep);
        v.extend(&self.bq);
        v
    }

    pub fn cnt(&self) -> &[QubitId] {
        &self.stk[0..CNTB]
    }

    /// Initial state: D = (R = p, cd = 1), V = (rv = x' already in V lanes [1, 257), cv = 0), b = 256, pi = 1, AL.
    pub fn init(&mut self, b: &mut B) {
        let w = WD;
        let pp = super::refmodel_double::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[i]);
            }
        }
        b.x(self.d[w - 1]);
        for &q in &self.bq {
            b.x(q); // b - 1 = 255
        }
        b.x(self.pi[0]);
        b.x(self.fa);
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
        let carry = self.pi[PIB - 1]; // carry out of the low PIB bits
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

    fn negdep(&self) -> Vec<(QubitId, bool)> {
        self.dep.iter().map(|&q| (q, true)).collect()
    }

    pub fn slot(&mut self, b: &mut B, lay: &LayDouble, sigma: usize) {
        let w = WD;
        let row = lay.rows[sigma];
        let (lv, jw, p1lo, lc, p2hi, pb0, pb1, pe0, pe1) =
            (row[0], row[1], row[2], row[3], row[4], row[5], row[6].min(w), row[7], row[8].min(w));
        let mut pl = Pl::new(&self.pool);
        // pi moves by exactly +-1 on every shot in every slot and is 1 at slot 0, so pi == 0 (DV0, the RT0 swap and
        // the DONE transition) only happens on odd slots: z0 and everything it controls are skipped on even slots
        let odd = sigma % 2 == 1;
        let (fa, fv, fc, fnn) = (self.fa, self.fv, self.fc, self.fnn);
        let not_frv = [(fa, true), (fv, true), (fc, true), (fnn, true)];
        let negdep = self.negdep();
        let negpi: Vec<(QubitId, bool)> = self.pi.iter().map(|&q| (q, true)).collect();
        let cnt: Vec<QubitId> = self.cnt().to_vec();

        // S0 frozen counter
        self.marks.push(("S0", b.ops.len()));
        {
            let anc = pl.get_n(CNTB - 1);
            inc(b, fnn, &cnt, &anc);
            pl.put_n(&anc);
        }

        // S2 value ladder P1 over lanes [0, lv): xd = DIV bit, tt = AL turn
        self.marks.push(("S2", b.ops.len()));
        let xd = pl.get();
        let tt = pl.get();
        if lv > 0 {
            self.bq_pi(b, &mut pl, Some(fv), false, false);
            let c0 = pl.get();
            let mf = pl.get_n(3);
            let pa = pl.get_n(PIB - 1);
            let pre = pl.get_n(BB - 1);
            let t: Vec<QubitId> = self.d[0..lv].to_vec();
            let s: Vec<QubitId> = self.v[0..lv].to_vec();
            let mut srcs = vec![Src { lo: 0, hi: jw.min(lv), v: self.pi.clone(), a: 0, d: 1, pre: pa.clone(), late: false }];
            if p1lo < lv {
                srcs.push(Src { lo: p1lo, hi: lv, v: self.bq.clone(), a: -2, d: 1, pre: pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &ms, g: &self.gp };
            let ru = mup(b, &ld);
            let rd = mdown(b, &ld, Some(xd));
            b.play(&ru, false);
            let ct = top_carry(&ld); // [rv<<pi > R]
            b.x(ct);
            b.and_c(fv, ct, xd); // DIV bit
            b.x(ct);
            b.and_c(fa, ct, tt); // AL turn
            b.play(&rd, false);
            pl.put_n(&pre);
            pl.put_n(&pa);
            pl.put_n(&mf);
            pl.put(c0);
            self.bq_pi(b, &mut pl, Some(fv), false, true);
        }

        // S3 turn: dl = tt & !V[b]; b <- b - pi + 1 - dl; erase dl with D[b + pi - 1]
        self.marks.push(("S3", b.ops.len()));
        let dl = pl.get();
        // probe decoders run over (b - 1, tt) with tt as the top bit, so the one-hot is already gated by the turn
        let mut btt = self.bq.clone();
        btt.push(tt);
        let ttoff = 1isize << BB;
        if pb1 > pb0 {
            let pre = pl.get_n(BB);
            let vref = self.v.clone();
            onehot_scan(b, &btt, &pre, pb0, pb1, ttoff - 1, |b, j, o| {
                b.x(vref[j]);
                b.ccx(o, vref[j], dl);
                b.x(vref[j]);
            });
            pl.put_n(&pre);
        }
        self.marks.push(("S3 bupd", b.ops.len()));
        {
            self.bq_pi(b, &mut pl, Some(tt), true, false);
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
            self.marks.push(("S3 erase", b.ops.len()));
            self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 = e
            let pre = pl.get_n(BB);
            let dref = self.d.clone();
            onehot_scan(b, &btt, &pre, pe0, pe1, ttoff, |b, j, o| {
                b.ccx(o, dref[j], dl);
            });
            pl.put_n(&pre);
            self.bq_pi(b, &mut pl, None, false, true);
        }
        pl.put(dl);

        // S4 DV push / DV0 bit 0 into be; moves AL->DV (tt), DV0->CO (dv0); erase tt, dv0; xd is then |0>
        self.marks.push(("S4", b.ops.len()));
        let z0 = pl.get();
        if odd {
            and_into(b, &mut pl, &negpi, z0, false); // z0 = [pi == 0], until S9
        }
        let be = pl.get();
        {
            let dv0 = pl.get();
            if odd {
                b.and_c(fv, z0, dv0);
            }
            let upq = pl.get();
            b.cx(fv, upq);
            if odd {
                b.cx(dv0, upq); // push = fv & !z0
            }
            cshift(b, upq, &self.stk, true);
            b.cswap(upq, xd, self.stk[0]);
            let anc = pl.get_n(DEPB - 1);
            inc(b, upq, &self.dep, &anc);
            pl.put_n(&anc);
            if odd {
                b.cx(dv0, upq);
            }
            b.cx(fv, upq);
            pl.put(upq);
            if odd {
                b.cswap(dv0, xd, be);
                b.cx(dv0, fv);
                b.cx(dv0, fc);
            }
            b.cx(tt, fa);
            b.cx(tt, fv);
            if odd {
                b.and_u(fc, z0, dv0);
            }
            pl.put(dv0);
            // tt = DV with an empty stack (post)
            let nz = pl.get();
            and_into(b, &mut pl, &negdep, nz, false);
            b.and_u(fv, nz, tt);
            and_into(b, &mut pl, &negdep, nz, true);
            pl.put(nz);
        }
        pl.put(tt);
        pl.put(xd);

        // S1 CO pop for shots that were CO at slot start (fc & !z0); ce = such a shot with an empty stack after it
        self.marks.push(("S1", b.ops.len()));
        let po = pl.get();
        let ce = pl.get();
        {
            let co = pl.get();
            if odd {
                b.x(z0);
                b.and_c(fc, z0, co);
                b.x(z0);
            } else {
                b.cx(fc, co);
            }
            let nz = pl.get();
            and_into(b, &mut pl, &negdep, nz, false);
            b.x(nz);
            b.and_c(co, nz, po);
            b.x(nz);
            and_into(b, &mut pl, &negdep, nz, true);
            b.cswap(po, be, self.stk[0]);
            cshift(b, po, &self.stk, false);
            let anc = pl.get_n(DEPB - 1);
            dec(b, po, &self.dep, &anc);
            pl.put_n(&anc);
            and_into(b, &mut pl, &negdep, nz, false);
            b.and_c(co, nz, ce);
            and_into(b, &mut pl, &negdep, nz, true);
            pl.put(nz);
            if odd {
                b.x(z0);
                b.and_u(fc, z0, co);
                b.x(z0);
            } else {
                b.cx(fc, co);
            }
            pl.put(co);
        }

        // S5 RT0: swap; RT0 -> AL, or DONE when b == 1
        self.marks.push(("S5", b.ops.len()));
        if odd {
            let rt0 = pl.get();
            let mut l5 = not_frv.to_vec();
            l5.push((z0, false));
            and_into(b, &mut pl, &l5, rt0, false); // RT at pi = 0
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&q| (q, true)).collect();
            let b1 = pl.get();
            and_into(b, &mut pl, &bz, b1, false);
            let dn = pl.get();
            b.and_c(rt0, b1, dn);
            cswap_regs(b, rt0, &self.d, &self.v);
            b.cx(rt0, self.par);
            b.cx(dn, fnn);
            b.cx(rt0, fa);
            b.cx(dn, fa);
            b.and_u(rt0, b1, dn);
            pl.put(dn);
            and_into(b, &mut pl, &bz, b1, true);
            pl.put(b1);
            // rt0 = (fa & z0) ^ (fn & z0 & [cnt == 0])
            b.ccx(fa, z0, rt0);
            let clits: Vec<(QubitId, bool)> = cnt.iter().map(|&q| (q, true)).collect();
            let c1 = pl.get();
            and_into(b, &mut pl, &clits, c1, false);
            let e2 = pl.get();
            b.and_c(fnn, z0, e2);
            b.ccx(e2, c1, rt0);
            b.and_u(fnn, z0, e2);
            pl.put(e2);
            and_into(b, &mut pl, &clits, c1, true);
            pl.put(c1);
            pl.put(rt0);
        }

        // S6 cofactor ladder P2 (COEF), mask lane >= b + pi, ladder lane l <-> phys W-1-l over phys [lc, W)
        self.marks.push(("S6", b.ops.len()));
        self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 until the end of S8
        if lc < w {
            let n = w - lc;
            let c0 = pl.get();
            let mf = pl.get_n(3);
            let pre = pl.get_n(BB - 1);
            let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (0..n).map(|l| self.d[w - 1 - l]).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq.clone(), a: w as isize - 1, d: -1,
                                pre: pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &self.gp };
            let ru = mup(b, &ld);
            let rd = mdown(b, &ld, Some(be));
            b.play(&rd, true);
            // ladder scratch is |0> here (c0 holds a carry): lend it out for the top logic
            pl.put_n(&pre);
            pl.put_n(&mf);
            let ct = top_carry(&ld); // [cd<<pi > cv']; cmp = !ct
            // be ^= (po | DV0) & cmp, DV0 = fc & z0 now
            let e2 = pl.get();
            b.x(ct);
            b.ccx(po, ct, be);
            if odd {
                b.and_c(fc, z0, e2);
                b.ccx(e2, ct, be);
                b.and_u(fc, z0, e2);
            }
            b.x(ct);
            // po ^= (fc & !z0) & !(nz & ct)
            let nz = pl.get();
            and_into(b, &mut pl, &negdep, nz, false);
            let h = pl.get();
            b.and_c(nz, ct, h);
            b.x(h);
            if odd {
                b.x(z0);
                b.and_c(fc, z0, e2);
                b.ccx(e2, h, po);
                b.and_u(fc, z0, e2);
                b.x(z0);
            } else {
                b.ccx(fc, h, po);
            }
            b.x(h);
            b.and_u(nz, ct, h);
            pl.put(h);
            and_into(b, &mut pl, &negdep, nz, true);
            pl.put(nz);
            pl.put(e2);
            pl.take(&mf);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        }
        pl.put(po);
        pl.put(be);

        // S7 CO -> RT for ce
        self.marks.push(("S7", b.ops.len()));
        b.cx(ce, fc); // fr is implicit

        // S8 discriminator P3: z = [cv >= cd << (pi_pre + 1)] (= model's pi_post + 2); erase ce = RT_post & !z
        self.marks.push(("S8", b.ops.len()));
        if lc < w {
            // truncated compare: only ladder lanes >= cut (P3DEPTH below the lowest shot boundary); the operands'
            // highest differing lane is <= 25 below a shot's boundary in 6e7 sampled comparisons (tail x0.5/lane)
            let cut = if p2hi > lc { (w - p2hi).saturating_sub(P3DEPTH) } else { 0 };
            let n = w - lc - cut;
            let c0 = pl.get();
            let mf = pl.get_n(3);
            let pre = pl.get_n(BB - 1);
            let zl = pl.get();
            let t: Vec<QubitId> = (cut..cut + n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (cut..cut + n).map(|l| if l < 1 { zl } else { self.d[w - l] }).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                // late: the shot's boundary lane W - b - pi stays in the compare with T there (rv's MSB, always 1)
                // flipped to the 0 it stands for, so cd << 1 may use it (q = 1 CO->RT needs it when W = 258)
                srcs.push(Src { lo: w - p2hi - cut, hi: w - lc - cut, v: self.bq.clone(), a: w as isize - 1 - cut as isize,
                                d: -1, pre: pre.clone(), late: true });
            }
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &self.gp };
            let ru = mup(b, &ld);
            b.play(&ru, false);
            let ct = top_carry(&ld); // [cd<<(pi+1) > cv] = !z
            pl.put_n(&pre);
            pl.put_n(&mf);
            let fq = pl.get();
            and_into(b, &mut pl, &not_frv, fq, false);
            b.ccx(fq, ct, ce);
            and_into(b, &mut pl, &not_frv, fq, true);
            pl.put(fq);
            pl.take(&mf);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put(zl);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        } else {
            and_into(b, &mut pl, &not_frv, ce, false); // degenerate: no cofactor lanes (never with a real schedule)
        }
        pl.put(ce);
        self.bq_pi(b, &mut pl, None, false, true);

        // S9 rotation and pi update from the post phase
        self.marks.push(("S9", b.ops.len()));
        if odd {
            and_into(b, &mut pl, &negpi, z0, true);
        }
        pl.put(z0);
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        // up = AL | CO (post), or DONE with pi even
        let upq = pl.get();
        b.cx(fa, upq);
        b.cx(fc, upq);
        b.x(self.pi[0]);
        b.ccx(fnn, self.pi[0], upq);
        b.x(self.pi[0]);
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
        b.ccx(fnn, self.pi[0], upq); // DONE shots flipped pi's parity: post pi0 = !pre pi0
        b.cx(fc, upq);
        b.cx(fa, upq);
        pl.put(upq);
        assert_eq!(pl.free.len(), self.pool.len(), "scratch leak");
    }

    pub fn forward(&mut self, b: &mut B, lay: &LayDouble) -> Vec<Vec<QubitId>> {
        let mut maps = Vec::with_capacity(lay.s);
        for sigma in 0..lay.s {
            maps.push(self.v.clone());
            self.slot(b, lay, sigma);
        }
        maps
    }

    pub fn inverse(&mut self, b: &mut B, lay: &LayDouble, maps: &[Vec<QubitId>]) {
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
