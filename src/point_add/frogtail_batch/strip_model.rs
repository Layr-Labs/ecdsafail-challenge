//! frogstrip integer model (register level): frogtail's SZ walk with one +-1 quotient digit per tick and the strip
//! (trailing zeros of A.v after a step's last digit) done by a rot4 barrel on ring A, k = min(nu(A.v), 3).
//!
//! Counter j: j >= 1 digits left in the step, j <= -1 minus the strips since the step's last digit (j = 0 never
//! holds at a tick start). Tick t:
//!   step end (t >= 2, e = [j <= -1] & A.v odd): swap A <-> B, parity ^= 1, j <- -j (= the next gap g).
//!   absorption (t >= TABS, f = [j <= -1] & B.v odd & A.v's low lanes zero): the same step end, then A = (0, 1),
//!     B.v = -2 [A.v = -1]; frozen afterwards (j = 3, B.v even: no digit, no decrement, no strip).
//!   digit (a = A.v odd & [j >= 1]): neg = A.v1 ^ B.v1 ^ [j = 1]; A.v += (-1)^neg B.v; B.c -= (-1)^neg A.c.
//!   halve: A.v /= 2, A.c *= 2, j -= 1 where B.v is odd.
//!   strip (j <= 0 after the halve): k = min(nu(A.v), 3); A.v >>= k, A.c <<= k, j -= k, E -= k.
//! E = Smax - (strips so far) is the per-shot exponent correction: x^-1 = (-1)^S C 2^m 2^E 2^-(T + Smax).

use super::frogdrop_sched::{p, N};

pub fn neg(x: N) -> N {
    (!x).wrapping_add(N::from(1u64))
}
pub fn is_neg(x: N) -> bool {
    x.bit(383)
}
/// exact two's complement width
pub fn wx(x: N) -> usize {
    if is_neg(x) {
        (!x).bit_len() + 1
    } else {
        x.bit_len() + 1
    }
}
pub fn sar(x: N, k: usize) -> N {
    if k == 0 {
        return x;
    }
    let s = x >> k;
    if is_neg(x) {
        s | !(N::MAX >> k)
    } else {
        s
    }
}
pub fn nu(x: N) -> usize {
    if x == N::ZERO {
        1000
    } else {
        x.trailing_zeros()
    }
}

/// frogstrip schedule: ring width W (both rings), ticks T, first absorption tick, boundary c[1..=T+1], compressed
/// widths of the swap/adds (kv, kc) and of the strip (ksv, ksc) for t in 1..=T.
#[derive(Clone, Debug)]
pub struct SSched {
    pub w: usize,
    pub t: usize,
    pub tabs: usize,
    pub c: Vec<usize>,
    pub kv: Vec<usize>,
    pub kc: Vec<usize>,
    pub ksv: Vec<usize>,
    pub ksc: Vec<usize>,
    /// compressed widths after tick t's halve (frame t + 1, every shot): the erase's extra carry lanes
    pub kev: Vec<usize>,
    pub kec: Vec<usize>,
}

impl SSched {
    /// "W T TABS" then c[1..=T+1]; then (lsc text) T, then kv kc ksv ksc for t = 1..=T.
    pub fn from_text(s: &str, lsc: Option<&str>) -> SSched {
        let nums = |s: &str| -> Vec<usize> {
            s.lines()
                .filter(|l| !l.trim_start().starts_with('#'))
                .flat_map(|l| l.split_whitespace().map(|w| w.parse::<usize>().unwrap()).collect::<Vec<_>>())
                .collect()
        };
        let v = nums(s);
        let (w, t, tabs) = (v[0], v[1], v[2]);
        let mut c = vec![0];
        c.extend(&v[3..]);
        assert_eq!(c.len(), t + 2, "schedule needs c[1..=T+1]");
        let kv = c.clone();
        let kc: Vec<usize> = c.iter().map(|&x| w.saturating_sub(x)).collect();
        // strip widths: the barrel segment is the cofactor's ksc lanes, 3 of its sign lanes below them, and the
        // value's ksv lanes (strip of tick t in frame t + 1)
        let ksv: Vec<usize> = c.clone();
        let ksc: Vec<usize> = c.iter().map(|&x| w.saturating_sub(x).saturating_sub(3)).collect();
        let kev: Vec<usize> = (0..c.len()).map(|i| c[(i + 1).min(c.len() - 1)]).collect();
        let kec: Vec<usize> = kev.iter().map(|&x| w - x).collect();
        let mut sch = SSched { w, t, tabs, c, kv, kc, ksv, ksc, kev, kec };
        if let Some(l) = lsc {
            let u = nums(l);
            if u[0] == t {
                for tt in 1..=t {
                    let r = &u[6 * tt - 5..6 * tt + 1];
                    let ct = sch.c[tt + 1];
                    assert!(2 <= r[0] && r[0] <= sch.c[tt] && 2 <= r[1] && r[1] <= w - sch.c[tt], "lsc t{tt}");
                    assert!(2 <= r[2] && r[2] <= ct && 2 <= r[3] && r[3] + 3 <= w - ct, "strip lsc t{tt}");
                    assert!(2 <= r[4] && r[4] <= ct && 2 <= r[5] && r[5] <= w - ct, "erase lsc t{tt}");
                    sch.kv[tt] = r[0];
                    sch.kc[tt] = r[1];
                    sch.ksv[tt] = r[2];
                    sch.ksc[tt] = r[3];
                    sch.kev[tt] = r[4];
                    sch.kec[tt] = r[5];
                }
            }
        }
        sch
    }
}

pub const ZL_S: usize = 22;
/// tick policy: 0 = frogstrip (step end, strip and erase every tick); 1 = two-tick cycle (step ends on odd ticks,
/// strips and erases on even ticks; a strip never leaves exactly one zero)
pub static POLICY: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
pub fn policy() -> usize {
    POLICY.load(std::sync::atomic::Ordering::Relaxed)
}
/// gap cap: g <= QB - 1 (the erase's word holds the marker and g digits)
pub const GCAP: i64 = super::frogtail::QB as i64 - 1;
/// exponent counter bits: E'' = H0 - T + EOFF - S, unsigned (S in [H0 - T + EOFF - 63, H0 - T + EOFF])
pub const EB: usize = 6;
pub const EOFF: i64 = 14;

/// per-tick envelope maxima (index t = tick)
#[derive(Clone)]
pub struct Env {
    pub vin: Vec<u16>,
    pub cin: Vec<u16>,
    pub vpost: Vec<u16>,
    pub cpost: Vec<u16>,
    pub kvs: Vec<u16>,
    pub kcs: Vec<u16>,
    pub kva: Vec<u16>,
    pub kca: Vec<u16>,
    pub ksv: Vec<u16>,
    pub ksc: Vec<u16>,
    pub khv: Vec<u16>,
    pub khc: Vec<u16>,
}
impl Env {
    pub fn new(n: usize) -> Env {
        let z = vec![0u16; n];
        Env {
            vin: z.clone(),
            cin: z.clone(),
            vpost: z.clone(),
            cpost: z.clone(),
            kvs: z.clone(),
            kcs: z.clone(),
            kva: z.clone(),
            kca: z.clone(),
            ksv: z.clone(),
            ksc: z.clone(),
            khv: z.clone(),
            khc: z,
        }
    }
    pub fn merge(&mut self, o: &Env) {
        for (a, b) in [
            (&mut self.vin, &o.vin),
            (&mut self.cin, &o.cin),
            (&mut self.vpost, &o.vpost),
            (&mut self.cpost, &o.cpost),
            (&mut self.kvs, &o.kvs),
            (&mut self.kcs, &o.kcs),
            (&mut self.kva, &o.kva),
            (&mut self.kca, &o.kca),
            (&mut self.ksv, &o.ksv),
            (&mut self.ksc, &o.ksc),
            (&mut self.khv, &o.khv),
            (&mut self.khc, &o.khc),
        ] {
            for i in 0..a.len() {
                a[i] = a[i].max(b[i]);
            }
        }
    }
}
fn up(v: &mut [u16], t: usize, x: usize) {
    if t < v.len() && v[t] < x as u16 {
        v[t] = x as u16;
    }
}

#[derive(Clone, Debug)]
pub struct SM {
    pub av: N,
    pub ac: N,
    pub bv: N,
    pub bc: N,
    pub j: i64,
    pub par: u64,
    /// strips so far
    pub s: i64,
    /// halvings so far
    pub h: i64,
    /// tick whose digit made A.v = 0 (0 = not yet)
    pub done: usize,
    /// absorption tick (0 = not yet)
    pub tabs: usize,
    pub gmax: i64,
    pub idle: u32,
    /// digit word of the current step: bit i = neg ^ [last digit] of the step's i-th digit (the circuit's d = A.v1 ^
    /// B.v1), and the step's digit count
    pub dw: u64,
    pub nd: u32,
    pub bad: Option<String>,
}

impl SM {
    pub fn new(x: N) -> SM {
        SM {
            av: p(),
            ac: N::from(1u64),
            bv: x,
            bc: N::ZERO,
            j: 1,
            par: 0,
            s: 0,
            h: 0,
            done: 0,
            tabs: 0,
            gmax: 1,
            idle: 0,
            dw: 0,
            nd: 0,
            bad: None,
        }
    }
    pub fn absorbed(&self) -> bool {
        self.tabs != 0
    }
    fn fail(&mut self, why: String) {
        if self.bad.is_none() {
            self.bad = Some(why);
        }
    }
    fn fits(&mut self, sch: Option<&SSched>, c: usize, what: &str, t: usize) {
        if let Some(s) = sch {
            if wx(self.av) > c || wx(self.bv) > c || wx(self.ac) > s.w - c || wx(self.bc) > s.w - c {
                self.fail(format!("t{t}: {what} widths"));
            }
        }
    }
    fn rec_in(&self, env: &mut Option<&mut Env>, t: usize) {
        if let Some(e) = env {
            up(&mut e.vin, t, wx(self.av).max(wx(self.bv)));
            up(&mut e.cin, t, wx(self.ac).max(wx(self.bc)));
        }
    }
    fn rec_post(&self, env: &mut Option<&mut Env>, t: usize) {
        if let Some(e) = env {
            up(&mut e.vpost, t, wx(self.av).max(wx(self.bv)));
            up(&mut e.cpost, t, wx(self.ac).max(wx(self.bc)));
        }
    }

    /// step end (ordinary or absorbing) at the start of tick t (t = T + 1: the closing step)
    pub fn step_end(&mut self, t: usize, sch: Option<&SSched>, tabs: usize, env: &mut Option<&mut Env>) {
        if t < 2 {
            return;
        }
        let e = self.j <= -1 && self.av.bit(0);
        let zl = sch.map(|s| s.c[t].min(ZL_S)).unwrap_or(ZL_S);
        let f = t >= tabs
            && self.j <= -1
            && self.bv.bit(0)
            && (self.av & ((N::from(1u64) << zl) - N::from(1u64))) == N::ZERO;
        if f && self.av != N::ZERO {
            self.fail(format!("t{t}: absorption flag with A.v != 0"));
        }
        if self.av == N::ZERO && !self.absorbed() && !f {
            self.fail(format!("t{t}: finished shot not absorbed"));
        }
        if e || f {
            if let Some(s) = sch {
                if t <= s.t
                    && (wx(self.av).max(wx(self.bv)) > s.kv[t] || wx(self.ac).max(wx(self.bc)) > s.kc[t])
                {
                    self.fail(format!("t{t}: lsc swap widths"));
                }
            }
            if let Some(en) = env {
                up(&mut en.kvs, t, wx(self.av).max(wx(self.bv)));
                up(&mut en.kcs, t, wx(self.ac).max(wx(self.bc)));
            }
            let g = -self.j;
            if e {
                self.gmax = self.gmax.max(g);
                if g > GCAP {
                    self.fail(format!("t{t}: g {g}"));
                }
            }
            if self.nd != 0 {
                self.fail(format!("t{t}: digit word not erased"));
            }
            std::mem::swap(&mut self.av, &mut self.bv);
            std::mem::swap(&mut self.ac, &mut self.bc);
            self.par ^= 1;
            self.j = g;
        }
        if f {
            let s = self.av != N::from(1u64);
            self.av = N::ZERO;
            self.ac = N::from(1u64);
            self.bv = if s { neg(N::from(2u64)) } else { N::ZERO };
            self.tabs = t;
            self.j = 3;
        }
    }

    /// Radix-4 tick (policy 2, model only, no schedule checks): step end, two +-1 digits each followed by a halve
    /// (the second only where j >= 1 after the first), erase at j in {0, -1}, strip k <= 3 never leaving one zero.
    fn tick_r4(&mut self, t: usize, tabs: usize, mut env: Option<&mut Env>) {
        self.rec_in(&mut env, t);
        self.step_end(t, None, tabs, &mut env);
        self.rec_in(&mut env, t);
        for _sub in 0..2 {
            let a = self.av.bit(0) && self.j >= 1;
            if a {
                if let Some(en) = env.as_deref_mut() {
                    up(&mut en.kva, t, wx(self.av).max(wx(self.bv)));
                    up(&mut en.kca, t, wx(self.ac).max(wx(self.bc)));
                }
                let d = self.av.bit(1) ^ self.bv.bit(1);
                let ng = d ^ (self.j == 1);
                if ng {
                    self.av = self.av.wrapping_sub(self.bv);
                    self.bc = self.bc.wrapping_add(self.ac);
                } else {
                    self.av = self.av.wrapping_add(self.bv);
                    self.bc = self.bc.wrapping_sub(self.ac);
                }
                if let Some(en) = env.as_deref_mut() {
                    up(&mut en.kva, t, wx(self.av).max(wx(self.bv)));
                    up(&mut en.kca, t, wx(self.ac).max(wx(self.bc)));
                }
                self.rec_in(&mut env, t);
                if self.av == N::ZERO && self.done == 0 {
                    self.done = t;
                }
            } else if !self.absorbed() && self.av != N::ZERO {
                self.idle += 1;
            }
            if self.av.bit(0) {
                self.fail(format!("t{t}: A.v odd before a halve"));
                return;
            }
            self.av = sar(self.av, 1);
            self.ac <<= 1;
            if self.bv.bit(0) {
                self.j -= 1;
                self.h += 1;
            }
        }
        self.rec_post(&mut env, t);
        if let Some(en) = env.as_deref_mut() {
            up(&mut en.khv, t, wx(self.av).max(wx(self.bv)));
            up(&mut en.khc, t, wx(self.ac).max(wx(self.bc)));
        }
        if self.j <= 0 {
            let mut k = nu(self.av).min(3);
            if nu(self.av) == k + 1 {
                k -= 1;
            }
            if k >= 1 {
                if let Some(en) = env.as_deref_mut() {
                    up(&mut en.ksv, t, wx(self.av));
                    up(&mut en.ksc, t, (wx(self.ac) + k).saturating_sub(3));
                }
            }
            self.av = sar(self.av, k);
            self.ac <<= k;
            self.j -= k as i64;
            self.s += k as i64;
            self.h += k as i64;
            if self.j < -(GCAP + 5) {
                self.fail(format!("t{t}: j {}", self.j));
            }
            self.rec_post(&mut env, t);
        }
    }

    pub fn tick(&mut self, t: usize, sch: Option<&SSched>, tabs: usize, mut env: Option<&mut Env>) {
        let c = sch.map(|s| s.c[t]).unwrap_or(0);
        let pol = policy();
        if pol == 2 {
            return self.tick_r4(t, tabs, env);
        }
        self.rec_in(&mut env, t);
        if pol == 1 && t % 2 == 0 && t >= 2 && self.j <= -1 && self.av.bit(0) {
            self.fail(format!("t{t}: even step end"));
        }
        if pol == 0 || t % 2 == 1 {
            self.step_end(t, sch, tabs, &mut env);
        }
        self.rec_in(&mut env, t);
        self.fits(sch, c, "pre-add", t);
        let a = self.av.bit(0) && self.j >= 1;
        if a {
            let lsc_add = |m: &SM| match sch {
                Some(s) => wx(m.av).max(wx(m.bv)) <= s.kv[t] && wx(m.ac).max(wx(m.bc)) <= s.kc[t],
                None => true,
            };
            if !lsc_add(self) {
                self.fail(format!("t{t}: lsc add widths"));
            }
            if let Some(en) = env.as_deref_mut() {
                up(&mut en.kva, t, wx(self.av).max(wx(self.bv)));
                up(&mut en.kca, t, wx(self.ac).max(wx(self.bc)));
            }
            let d = self.av.bit(1) ^ self.bv.bit(1);
            let ng = d ^ (self.j == 1);
            if ng {
                self.av = self.av.wrapping_sub(self.bv);
                self.bc = self.bc.wrapping_add(self.ac);
            } else {
                self.av = self.av.wrapping_add(self.bv);
                self.bc = self.bc.wrapping_sub(self.ac);
            }
            self.dw |= (d as u64) << self.nd;
            self.nd += 1;
            if !lsc_add(self) {
                self.fail(format!("t{t}: lsc add widths"));
            }
            if let Some(en) = env.as_deref_mut() {
                up(&mut en.kva, t, wx(self.av).max(wx(self.bv)));
                up(&mut en.kca, t, wx(self.ac).max(wx(self.bc)));
            }
            self.rec_in(&mut env, t);
            self.fits(sch, c, "post-add", t);
            if self.av == N::ZERO && self.done == 0 {
                self.done = t;
            }
        } else if !self.absorbed() && self.av != N::ZERO {
            self.idle += 1;
        }
        if self.bad.is_none() && self.av.bit(0) {
            panic!("A.v odd before the halve");
        }
        let cn = sch.map(|s| s.c[t + 1]).unwrap_or(0);
        self.av = sar(self.av, 1);
        self.ac <<= 1;
        if self.bv.bit(0) {
            self.j -= 1;
            self.h += 1;
        }
        self.rec_post(&mut env, t);
        self.fits(sch, cn, "post-halve", t);
        if let Some(en) = env.as_deref_mut() {
            up(&mut en.khv, t, wx(self.av).max(wx(self.bv)));
            up(&mut en.khc, t, wx(self.ac).max(wx(self.bc)));
        }
        if let Some(s) = sch {
            if t <= s.t && (wx(self.av).max(wx(self.bv)) > s.kev[t] || wx(self.ac).max(wx(self.bc)) > s.kec[t]) {
                self.fail(format!("t{t}: lsc erase widths"));
            }
        }
        if (pol == 0 && self.j == 0) || (pol == 1 && t % 2 == 0 && (self.j == 0 || self.j == -1)) {
            // digit completion: the circuit erases the digit word here
            self.dw = 0;
            self.nd = 0;
        }
        if self.j <= 0 && (pol == 0 || t % 2 == 0) {
            let mut k = nu(self.av).min(3);
            if pol == 1 && nu(self.av) == k + 1 {
                k -= 1;
            }
            if k >= 1 {
                // the barrel segment: A.v in ksv lanes, A.c << k in the cofactor's ksc + 3 lanes
                if let Some(s) = sch {
                    if t <= s.t && (wx(self.av) > s.ksv[t] || wx(self.ac) + k > s.ksc[t] + 3) {
                        self.fail(format!("t{t}: lsc strip widths"));
                    }
                }
                if let Some(en) = env.as_deref_mut() {
                    up(&mut en.ksv, t, wx(self.av));
                    up(&mut en.ksc, t, (wx(self.ac) + k).saturating_sub(3));
                }
            }
            self.av = sar(self.av, k);
            self.ac <<= k;
            self.j -= k as i64;
            self.s += k as i64;
            self.h += k as i64;
            if self.j < -(GCAP + 3) {
                self.fail(format!("t{t}: j {}", self.j));
            }
            self.rec_post(&mut env, t);
        }
    }

    /// x^-1 = (-1)^sgn C_T 2^-(T + S) with C_T = B.c 2^m (m = ticks since the absorption), after close.
    pub fn result(&self, t_end: usize) -> (N, usize, i64, bool) {
        let m = nu(self.ac);
        let sgn = is_neg(self.bv) ^ (self.par == 1) ^ true;
        let _ = t_end;
        (self.bc, m, self.s, sgn)
    }
}

/// Run one walk with the schedule (checks) to the closing step; returns the model.
pub fn run_walk(x: N, sch: &SSched) -> SM {
    let mut m = SM::new(x);
    for t in 1..=sch.t {
        m.tick(t, Some(sch), sch.tabs, None);
        if m.bad.is_some() {
            return m;
        }
    }
    m.step_end(sch.t + 1, Some(sch), sch.tabs, &mut None);
    if !m.absorbed() && m.bad.is_none() {
        m.fail("end: not absorbed".into());
    }
    m
}
