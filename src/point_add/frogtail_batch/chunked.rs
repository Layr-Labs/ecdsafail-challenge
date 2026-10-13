//! Controlled adds using a reusable clean carry bank and measured boundaries.
//! Adapted from gnuchev / jieyilong SkyCof's skycof_mm chunked add construction
//! (submission 4455a38, b29e771). Full-width comparisons: no new truncations.
use super::builder::B;
use crate::circuit::{BitId, QubitId as Q};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AddRole { Value, Cofactor }
/// Exact production-support facts available at the global low lane of a
/// controlled add.  They change only the lane-zero gate realization; every
/// higher carry and every chunk boundary keeps the generic construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LowSupport {
    Generic,
    /// The source low bit is one on the complete supported input subspace.
    SourceOne,
    /// A set source low bit implies that the add control is set.
    SourceImpliesControl,
    /// On the supported call boundary, a cleared add control implies that
    /// source lanes 0..4 are all zero.  Consequently every low-prefix sum
    /// factor `source[i] xor carry[i]` implies the add control.  Carry
    /// formation itself remains generic above lane zero.
    SourceLow4ImpliesControl,
}

impl LowSupport {
    fn at(self, lane: usize) -> LowSupport {
        match self {
            LowSupport::SourceLow4ImpliesControl if lane < 4 => self,
            LowSupport::SourceLow4ImpliesControl => LowSupport::Generic,
            x if lane == 0 => x,
            _ => LowSupport::Generic,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PairKey {
    pub division: usize,
    pub tick: usize,
    pub role: AddRole,
}
#[derive(Clone, Copy, Debug)]
pub enum Pair { Forward(PairKey), Inverse(PairKey) }
#[derive(Clone, Debug)]
pub struct Debt { pub position: usize, pub bit: BitId }

#[derive(Clone)]
pub struct Call {
    pub a: Vec<Q>,
    pub t: Vec<Q>,
    pub ctl: Q,
    pub cout: Option<Q>,
    pub cin: Option<Q>,
    pub pool: Vec<Q>,
    pub sizes: Vec<usize>,
    pub pair: Option<Pair>,
    pub low_support: LowSupport,
}

pub fn plan(n: usize, room: usize, flag: bool) -> Option<Vec<usize>> {
    for count in 1..=n {
        let Some(last_cap) = (room + 1).checked_sub(flag as usize + count - 1) else {
            break;
        };
        if last_cap == 0 || (0..count - 1).any(|j| room <= j) {
            break;
        }
        let caps: Vec<_> = (0..count - 1).map(|j| room - j).collect();
        if caps.iter().sum::<usize>() + last_cap < n {
            continue;
        }
        let last = last_cap.min(n - count + 1);
        let mut rem = n - last;
        let mut sizes = vec![];
        for (j, &cap) in caps.iter().enumerate() {
            let take = cap.min(rem - (count - 2 - j));
            sizes.push(take);
            rem -= take;
        }
        assert_eq!(rem, 0);
        sizes.push(last);
        return Some(sizes);
    }
    None
}

pub fn try_add(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cout: Option<Q>, pool: &[Q]) -> bool {
    try_add_paired(b, a, t, ctl, cout, pool, None)
}

pub fn try_add_paired(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cout: Option<Q>, pool: &[Q], pair: Option<Pair>) -> bool {
    try_add_paired_support(b, a, t, ctl, cout, pool, pair, LowSupport::Generic)
}

pub fn try_add_paired_support(
    b: &mut B,
    a: &[Q],
    t: &[Q],
    ctl: Q,
    cout: Option<Q>,
    pool: &[Q],
    pair: Option<Pair>,
    low_support: LowSupport,
) -> bool {
    // A paired inverse still needs the carry hooks when a larger bank permits
    // one full-width chunk. The ordinary full-bank adder has no receipt hooks.
    let paired_inverse = matches!(pair, Some(Pair::Inverse(_)));
    if !cout.is_some() && pool.len() >= t.len() - 1 && !paired_inverse {
        return false;
    }
    let Some(sizes) = plan(t.len(), pool.len(), cout.is_some()) else {
        return false;
    };
    if sizes.len() == 1 && !paired_inverse {
        return false;
    }
    b.chunk_add(Call {
        a: a.to_vec(),
        t: t.to_vec(),
        ctl,
        cout,
        cin: None,
        pool: pool.to_vec(),
        sizes,
        pair,
        low_support,
    });
    true
}

struct Pool {
    free: Vec<Q>,
}
impl Pool {
    fn new(q: &[Q]) -> Self {
        Self { free: q.to_vec() }
    }
    fn get(&mut self) -> Q {
        self.free.pop().expect("chunk carry bank exhausted")
    }
    fn put(&mut self, q: Q) {
        assert!(!self.free.contains(&q));
        self.free.push(q);
    }
}

/// Compute MAJ(a,t,ci). With ci, leaves t ^= ci and restores a.
fn carry(b: &mut B, a: Q, t: Q, ci: Option<Q>, pool: &mut Pool, low: LowSupport) -> Q {
    let co = pool.get();
    if let Some(c) = ci {
        b.cx(c, a);
        b.cx(c, t);
        b.and_c(a, t, co);
        b.cx(c, a);
        b.cx(c, co);
    } else {
        match low {
            LowSupport::SourceOne => b.cx(t, co),
            LowSupport::Generic | LowSupport::SourceImpliesControl | LowSupport::SourceLow4ImpliesControl =>
                b.and_c(a, t, co),
        }
    }
    co
}
fn erase(b: &mut B, a: Q, t: Q, ci: Option<Q>, co: Q, pool: &mut Pool, low: LowSupport) {
    if let Some(c) = ci {
        b.cx(c, co);
        b.cx(c, a);
        b.and_u(a, t, co);
        b.cx(c, a);
    } else {
        match low {
            LowSupport::SourceOne => b.cx(t, co),
            LowSupport::Generic | LowSupport::SourceImpliesControl | LowSupport::SourceLow4ImpliesControl =>
                b.and_u(a, t, co),
        }
    }
    pool.put(co);
}
fn sum(b: &mut B, a: Q, t: Q, ci: Option<Q>, ctl: Q, modified: bool, low: LowSupport) {
    if modified {
        b.cx(ci.unwrap(), t);
    }
    if let Some(c) = ci {
        b.cx(c, a);
        match low {
            LowSupport::SourceLow4ImpliesControl => b.cx(a, t),
            _ => b.ccx(ctl, a, t),
        }
        b.cx(c, a);
    } else {
        match low {
            LowSupport::SourceOne => b.cx(ctl, t),
            LowSupport::SourceImpliesControl | LowSupport::SourceLow4ImpliesControl => b.cx(a, t),
            LowSupport::Generic => b.ccx(ctl, a, t),
        }
    }
}

fn add_chunk(
    b: &mut B,
    a: &[Q],
    t: &[Q],
    ci: Option<Q>,
    ctl: Q,
    keep: bool,
    cout: Option<Q>,
    pool: &mut Pool,
    lo: usize,
    debts: &mut Vec<Debt>,
    spec_low: LowSupport,
) -> Option<Q> {
    let n = a.len();
    let m = if keep || cout.is_some() { n } else { n - 1 };
    let mut c = vec![ci];
    for i in 0..m {
        let low = spec_low.at(lo + i);
        let q = carry(b, a[i], t[i], c[i], pool, low);
        if let Some(j) = debts.iter().position(|d| d.position == lo + i + 1) {
            let d = debts.remove(j);
            b.z_if(q, d.bit);
        }
        c.push(Some(q));
    }
    if m < n {
        let low = spec_low.at(lo + n - 1);
        sum(b, a[n - 1], t[n - 1], c[n - 1], ctl, false, low);
    }
    if let Some(flag) = cout {
        b.ccx(ctl, c[n].unwrap(), flag);
    }
    let retained = if keep { c[n] } else { None };
    for i in (0..m).rev() {
        if !(keep && i == n - 1) {
            let low = spec_low.at(lo + i);
            erase(b, a[i], t[i], c[i], c[i + 1].unwrap(), pool, low);
        }
        let low = spec_low.at(lo + i);
        sum(b, a[i], t[i], c[i], ctl, c[i].is_some(), low);
    }
    retained
}

/// A phase on the carry, with a and t restored. The top MAJ phase is Clifford.
fn carry_phase(b: &mut B, a: &[Q], t: &[Q], ci: Option<Q>, pool: &mut Pool, low_support: LowSupport) {
    let n = a.len();
    let mut c = vec![ci];
    for i in 0..n - 1 {
        let low = if ci.is_none() { low_support.at(i) } else { LowSupport::Generic };
        let co = carry(b, a[i], t[i], c[i], pool, low);
        c.push(Some(co));
    }
    b.cz(a[n - 1], t[n - 1]);
    if let Some(last) = c[n - 1] {
        b.cz(a[n - 1], last);
        b.cz(t[n - 1], last);
    }
    for i in (0..n - 1).rev() {
        let low = if ci.is_none() { low_support.at(i) } else { LowSupport::Generic };
        erase(b, a[i], t[i], c[i], c[i + 1].unwrap(), pool, low);
        if let Some(prev) = c[i] {
            b.cx(prev, t[i]);
        }
    }
}

pub fn apply(b: &mut B, spec: &Call, inverse: bool) {
    let n = spec.t.len();
    assert_eq!(n, spec.a.len());
    let paired = spec.pair.is_some();
    let mut debts = match spec.pair {
        Some(Pair::Inverse(key)) => {
            assert!(inverse, "paired debt must bind actual inverse emission");
            b.take_chunk_debts(key, n, spec.cout.is_some(), spec.cin.is_some())
        },
        Some(Pair::Forward(_)) => { assert!(!inverse); vec![] },
        None => vec![],
    };
    let mut saved = vec![];
    if inverse {
        for &q in &spec.t {
            if paired { b.cx(spec.ctl, q); } else { b.x(q); }
        }
    }
    let mut pool = Pool::new(&spec.pool);
    let mut bounds = vec![];
    let (mut lo, mut ci) = (0, spec.cin);
    for (j, &size) in spec.sizes.iter().enumerate() {
        let hi = lo + size;
        let last = j + 1 == spec.sizes.len();
        let co = add_chunk(
            b,
            &spec.a[lo..hi],
            &spec.t[lo..hi],
            ci,
            spec.ctl,
            !last,
            if last { spec.cout } else { None },
            &mut pool,
            lo,
            &mut debts,
            spec.low_support,
        );
        if !last {
            bounds.push((lo, hi, co.unwrap(), ci));
            ci = co;
        }
        lo = hi;
    }
    assert_eq!(lo, n);
    assert!(debts.is_empty(), "inverse did not regenerate every old carry");
    for &(lo, hi, co, prev) in bounds.iter().rev() {
        if let Some(Pair::Forward(_)) = spec.pair {
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(co, bit);
            pool.put(co);
            saved.push(Debt { position: hi, bit });
            continue;
        }
        b.measure_and_push(co);
        pool.put(co);
        // ctl=1: compare ~sum+a+cin. ctl=0: compare original_t+a+cin.
        for &q in &spec.t[lo..hi] {
            b.cx(spec.ctl, q);
        }
        let low = if prev.is_none() { spec.low_support.at(lo) } else { LowSupport::Generic };
        carry_phase(b, &spec.a[lo..hi], &spec.t[lo..hi], prev, &mut pool, low);
        for &q in &spec.t[lo..hi] {
            b.cx(spec.ctl, q);
        }
        b.pop_classical();
    }
    assert_eq!(pool.free.len(), spec.pool.len());
    if let Some(Pair::Forward(key)) = spec.pair {
        b.save_chunk_debts(key, n, spec.cout.is_some(), spec.cin.is_some(), saved);
    }
    if inverse {
        for &q in &spec.t {
            if paired { b.cx(spec.ctl, q); } else { b.x(q); }
        }
    }
}
