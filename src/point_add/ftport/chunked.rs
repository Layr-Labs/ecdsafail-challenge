//! Controlled adds using a reusable clean carry bank and measured boundaries.
//! Adapted from gnuchev / jieyilong SkyCof's skycof_mm chunked add construction
//! (submission 4455a38, b29e771). Full-width comparisons: no new truncations.
use super::builder::B;
use crate::circuit::{BitId, QubitId as Q};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AddRole { Value, Cofactor,
    /// G-coordinate forced value add, lanes 2..n with incoming F1.
    /// A distinct semantic pair shape; never matches a full-word receipt.
    ValueHi2,
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
    /// Lane LILY-A: receipts to repay in an unpaired inverse (positions in this add's own lane numbering).
    pub debts: Vec<Debt>,
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

/// A paired forward pass may repay each boundary's space immediately after
/// the following chunk has consumed it.  Reserve one lane for that incoming
/// boundary in every chunk; the inverse's old-carry hooks repay the HMR debts.
fn rolling_plan(n: usize, room: usize) -> Vec<usize> {
    assert!(room >= 2 && n >= 2);
    let mut left = n;
    let mut sizes = Vec::new();
    while left != 0 {
        let take = left.min(room - 1);
        sizes.push(take);
        left -= take;
    }
    sizes
}

pub fn try_add(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cout: Option<Q>, pool: &[Q]) -> bool {
    try_add_paired(b, a, t, ctl, cout, pool, None)
}

pub fn try_add_paired(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cout: Option<Q>, pool: &[Q], pair: Option<Pair>) -> bool {
    try_add_paired_cin(b, a, t, ctl, cout, None, pool, pair)
}

/// Same arithmetic/receipt contract, with an immutable incoming carry owner.
#[allow(clippy::too_many_arguments)]
pub fn try_add_paired_cin(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cout: Option<Q>, cin: Option<Q>, pool: &[Q], pair: Option<Pair>) -> bool {
    assert_eq!(a.len(), t.len());
    assert!(!t.is_empty());
    if let Some(q) = cin {
        assert!(!a.contains(&q) && !t.contains(&q) && !pool.contains(&q));
    }
    // A paired inverse still needs the carry hooks when a larger bank permits
    // one full-width chunk. The ordinary full-bank adder has no receipt hooks.
    let paired_inverse = matches!(pair, Some(Pair::Inverse(_)));
    if cin.is_none() && !cout.is_some() && pool.len() >= t.len() - 1 && !paired_inverse {
        return false;
    }
    let sizes = match plan(t.len(), pool.len(), cout.is_some()) {
        Some(sizes)=>sizes,
        None if matches!(pair, Some(Pair::Forward(_))) && cout.is_none() && pool.len() >= 2
            => rolling_plan(t.len(), pool.len()),
        None if (paired_inverse || cin.is_some()) && cout.is_none() && !pool.is_empty()=>vec![],
        // Lane LILY-A: a paired inverse with no carry lane at all (never reached by builds that held one).
        None if paired_inverse && cout.is_none() && cin.is_none() && pool.is_empty() && t.len() >= 2 => vec![],
        None=>return false,
    };
    if cin.is_none() && sizes.len() == 1 && !paired_inverse {
        return false;
    }
    b.chunk_add(Call {
        a: a.to_vec(),
        t: t.to_vec(),
        ctl,
        cout,
        cin,
        pool: pool.to_vec(),
        sizes,
        pair,
        debts: vec![],
    });
    true
}

/// Lane LILY-A: t += ctl a with incoming carry `cin`, recorded; when played inverted it repays `debts` (receipts of a
/// forward add whose carries at these positions equal this add's carries) exactly like a paired inverse.
pub fn add_with_debts(b: &mut B, a: &[Q], t: &[Q], ctl: Q, cin: Q, pool: &[Q], debts: Vec<Debt>) {
    assert_eq!(a.len(), t.len());
    assert!(!a.contains(&cin) && !t.contains(&cin) && !pool.contains(&cin) && !pool.is_empty() && t.len() >= 2);
    let sizes = plan(t.len(), pool.len(), false).unwrap_or_default();
    b.chunk_add(Call { a: a.to_vec(), t: t.to_vec(), ctl, cout: None, cin: Some(cin), pool: pool.to_vec(), sizes, pair: None, debts });
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
fn carry(b: &mut B, a: Q, t: Q, ci: Option<Q>, pool: &mut Pool) -> Q {
    let co = pool.get();
    if let Some(c) = ci {
        b.cx(c, a);
        b.cx(c, t);
        b.and_c(a, t, co);
        b.cx(c, a);
        b.cx(c, co);
    } else {
        b.and_c(a, t, co);
    }
    co
}
fn erase(b: &mut B, a: Q, t: Q, ci: Option<Q>, co: Q, pool: &mut Pool) {
    if let Some(c) = ci {
        b.cx(c, co);
        b.cx(c, a);
        b.and_u(a, t, co);
        b.cx(c, a);
    } else {
        b.and_u(a, t, co);
    }
    pool.put(co);
}
fn sum(b: &mut B, a: Q, t: Q, ci: Option<Q>, ctl: Q, modified: bool) {
    if modified {
        b.cx(ci.unwrap(), t);
    }
    if let Some(c) = ci {
        b.cx(c, a);
        b.ccx(ctl, a, t);
        b.cx(c, a);
    } else {
        b.ccx(ctl, a, t);
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
) -> Option<Q> {
    let n = a.len();
    let m = if keep || cout.is_some() { n } else { n - 1 };
    let mut c = vec![ci];
    for i in 0..m {
        let q = carry(b, a[i], t[i], c[i], pool);
        if let Some(j) = debts.iter().position(|d| d.position == lo + i + 1) {
            let d = debts.remove(j);
            b.z_if(q, d.bit);
        }
        c.push(Some(q));
    }
    if m < n {
        sum(b, a[n - 1], t[n - 1], c[n - 1], ctl, false);
    }
    if let Some(flag) = cout {
        b.ccx(ctl, c[n].unwrap(), flag);
    }
    let retained = if keep { c[n] } else { None };
    for i in (0..m).rev() {
        if !(keep && i == n - 1) {
            erase(b, a[i], t[i], c[i], c[i + 1].unwrap(), pool);
        }
        sum(b, a[i], t[i], c[i], ctl, c[i].is_some());
    }
    retained
}

/// A phase on the carry, with a and t restored. The top MAJ phase is Clifford.
fn carry_phase(b: &mut B, a: &[Q], t: &[Q], ci: Option<Q>, pool: &mut Pool) {
    let n = a.len();
    let mut c = vec![ci];
    for i in 0..n - 1 {
        let co = carry(b, a[i], t[i], c[i], pool);
        c.push(Some(co));
    }
    b.cz(a[n - 1], t[n - 1]);
    if let Some(last) = c[n - 1] {
        b.cz(a[n - 1], last);
        b.cz(t[n - 1], last);
    }
    for i in (0..n - 1).rev() {
        erase(b, a[i], t[i], c[i], c[i + 1].unwrap(), pool);
        if let Some(prev) = c[i] {
            b.cx(prev, t[i]);
        }
    }
}

fn old_carry_phase(b:&mut B,position:usize,wire:Q,debts:&mut Vec<Debt>) {
    if let Some(j)=debts.iter().position(|d|d.position==position) {
        let debt=debts.remove(j);b.z_if(wire,debt.bit);
    }
}

/// For a paired inverse with no whole-word plan, hold a triangular sequence
/// of low chunk boundaries and use the inherited in-place ripple above it.
/// The estimate is used only to choose an exact circuit shape.
fn mixed_prefix(n: usize, room: usize) -> Vec<usize> {
    if room < 2 || n <= room + 2 { return vec![]; }
    let base = room.min(n - 1) as f64 + 2.0 * (n - room.min(n - 1) - 1) as f64;
    let mut best_cost = base;
    let mut best_len = 0;
    let mut sizes = Vec::new();
    let (mut lo, mut phase) = (0usize, 0.0);
    for j in 0..room {
        let take = (room - j).min(n - 1 - lo);
        if take == 0 { break; }
        sizes.push(take);
        lo += take;
        phase += 0.5 * (take - 1) as f64;
        let cost = lo as f64 + phase + 2.0 * (n - lo - 1) as f64;
        if cost < best_cost {
            best_cost = cost;
            best_len = sizes.len();
        }
        if lo == n - 1 { break; }
    }
    sizes.truncate(best_len);
    sizes
}

fn inverse_mixed(b: &mut B, spec: &Call, mut debts: Vec<Debt>, sizes: &[usize], inverse: bool) {
    use super::arith::{down_m, Dm};
    assert!(spec.cout.is_none());
    let (a, t, ctl) = (&spec.a, &spec.t, spec.ctl);
    let n = t.len();
    if inverse { for &q in t { b.cx(ctl, q); } }
    let mut pool = Pool::new(&spec.pool);
    let mut bounds = Vec::new();
    let (mut lo, mut ci) = (0usize, spec.cin);
    for &size in sizes {
        let hi = lo + size;
        let co = add_chunk(b, &a[lo..hi], &t[lo..hi], ci, ctl, true, None,
            &mut pool, lo, &mut debts).expect("mixed chunk boundary");
        bounds.push((lo, hi, co, ci));
        ci = Some(co);
        lo = hi;
    }
    assert!(lo < n);
    let th = &t[lo..n - 1];
    let sh = &a[lo..n - 1];
    for i in lo..n - 1 {
        let incoming = if i == lo { ci.unwrap() } else { a[i - 1] };
        b.cx(a[i], t[i]);
        b.cx(a[i], incoming);
        b.ccx(incoming, t[i], a[i]);
        old_carry_phase(b, i + 1, a[i], &mut debts);
    }
    assert!(debts.is_empty(), "mixed inverse missed an old carry debt");
    let ct = if th.is_empty() { ci.unwrap() } else { a[n - 2] };
    b.cx(ct, a[n - 1]);
    b.ccx(ctl, a[n - 1], t[n - 1]);
    b.cx(ct, a[n - 1]);
    if !th.is_empty() {
        let down = down_m(b, th, sh, ci.unwrap(), Dm::Cond(ctl), false);
        b.play(&down, false);
    }
    for &(start, end, co, prev) in bounds.iter().rev() {
        b.measure_and_push(co);
        pool.put(co);
        for &q in &t[start..end] { b.cx(ctl, q); }
        carry_phase(b, &a[start..end], &t[start..end], prev, &mut pool);
        for &q in &t[start..end] { b.cx(ctl, q); }
        b.pop_classical();
    }
    assert_eq!(pool.free.len(), spec.pool.len());
    if inverse { for &q in t { b.cx(ctl, q); } }
}
/// Exact paired inverse when the clean bank cannot form a chunk plan.
/// The output flag is excluded; cin is preserved. Normalization regenerates each OLD
/// forward carry; hooks precede any later MAJ mutation of its physical wire.
/// Lane LILY-A: paired inverse add with no carry lane: Takahashi-Tani-Kunihiro ripple (t += ctl a, carries of a + t
/// uncontrolled, as in `inverse_hybrid`). Right after the carry pass wire a[i] holds a_i ^ c_i and before the ladder
/// a_i, so a debt at position i is repaid by one classically controlled Z on a[i] at each of the two points
/// (gnuchev's 856 hook): (-1)^(m a_i) (-1)^(m (a_i ^ c_i)) = (-1)^(m c_i).
fn inverse_ttk(b:&mut B,spec:&Call,debts:Vec<Debt>,inverse:bool) {
    assert!(spec.cout.is_none() && spec.cin.is_none() && spec.pool.is_empty());
    let(a,t,ctl)=(&spec.a,&spec.t,spec.ctl);let n=t.len();assert!(n>=2);
    let mut hook: Vec<(usize, BitId)> = vec![];
    for d in &debts { assert!(d.position >= 1 && d.position < n, "ttk inverse debt outside 1..n"); hook.push((d.position, d.bit)); }
    if inverse {for &q in t {b.cx(ctl,q);}}
    for &(i, m) in &hook { b.z_if(a[i], m); }
    for i in 1..n { b.cx(a[i], t[i]); }
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    for &(i, m) in &hook { b.z_if(a[i], m); }
    for i in (1..n).rev() {
        b.ccx(ctl, a[i], t[i]);
        b.ccx(t[i - 1], a[i - 1], a[i]);
    }
    for i in 1..n - 1 { b.cx(a[i], a[i + 1]); }
    b.ccx(ctl, a[0], t[0]);
    for i in 1..n { b.cx(a[i], t[i]); }
    if inverse {for &q in t {b.cx(ctl,q);}}
}

fn inverse_hybrid(b:&mut B,spec:&Call,mut debts:Vec<Debt>,inverse:bool) {
    use super::arith::{down_m,Dm};
    if spec.pool.is_empty() { inverse_ttk(b, spec, debts, inverse); return; }
    assert!(spec.cout.is_none());
    let(a,t,ctl)=(&spec.a,&spec.t,spec.ctl);let n=t.len();
    let pn=spec.pool.len().min(n-1);assert!(pn>=1 && n>=2);
    let prefix = if inverse { mixed_prefix(n, pn) } else { vec![] };
    if !prefix.is_empty() {
        inverse_mixed(b, spec, debts, &prefix, inverse);
        return;
    }
    let c=&spec.pool;
    if inverse {for &q in t {b.cx(ctl,q);}}
    for i in 0..pn {
        let prev = if i==0 { spec.cin } else { Some(c[i-1]) };
        if let Some(ci)=prev {b.cx(ci,a[i]);b.cx(ci,t[i]);b.and_c(a[i],t[i],c[i]);b.cx(ci,c[i]);}
        else {b.and_c(a[i],t[i],c[i]);}
        old_carry_phase(b,i+1,c[i],&mut debts);
    }
    let(th,sh)=(&t[pn..n-1],&a[pn..n-1]);
    for i in pn..n-1 {
        let incoming=if i==pn{c[pn-1]}else{a[i-1]};
        b.cx(a[i],t[i]);b.cx(a[i],incoming);b.ccx(incoming,t[i],a[i]);
        old_carry_phase(b,i+1,a[i],&mut debts);
    }
    assert!(debts.is_empty(),"hybrid inverse missed an old carry debt");
    let ct=if th.is_empty(){c[pn-1]}else{a[n-2]};
    b.cx(ct,a[n-1]);b.ccx(ctl,a[n-1],t[n-1]);b.cx(ct,a[n-1]);
    if !th.is_empty(){let down=down_m(b,th,sh,c[pn-1],Dm::Cond(ctl),false);b.play(&down,false);}
    for i in (0..pn).rev(){
        let prev = if i==0 { spec.cin } else { Some(c[i-1]) };
        if let Some(ci)=prev {b.cx(ci,c[i]);b.and_u(a[i],t[i],c[i]);b.cx(ci,t[i]);b.ccx(ctl,a[i],t[i]);b.cx(ci,a[i]);}
        else {b.and_u(a[i],t[i],c[i]);b.ccx(ctl,a[i],t[i]);}
    }
    if inverse {for &q in t {b.cx(ctl,q);}}
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
        None => { if !spec.debts.is_empty() { assert!(inverse, "explicit receipts bind the inverse emission"); } spec.debts.clone() },
    };
    if spec.sizes.is_empty() {
        assert!(matches!(spec.pair,Some(Pair::Inverse(_))) || spec.cin.is_some());
        assert!(plan(n,spec.pool.len(),false).is_none(),"hybrid sentinel replaces only an infeasible plan");
        inverse_hybrid(b,spec,debts,inverse);
        if let Some(Pair::Forward(key))=spec.pair {
            assert!(!inverse);
            b.save_chunk_debts(key,n,spec.cout.is_some(),spec.cin.is_some(),vec![]);
        }
        return;
    }
    let rolling = matches!(spec.pair, Some(Pair::Forward(_)))
        && spec.cout.is_none()
        && plan(n, spec.pool.len(), false).is_none();
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
        );
        if rolling && j > 0 {
            let old = ci.expect("rolling boundary");
            let bit = b.fresh_bits(1)[0];
            b.hmr_to(old, bit);
            pool.put(old);
            saved.push(Debt { position: lo, bit });
        }
        if !last {
            if !rolling { bounds.push((lo, hi, co.unwrap(), ci)); }
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
        carry_phase(b, &spec.a[lo..hi], &spec.t[lo..hi], prev, &mut pool);
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
