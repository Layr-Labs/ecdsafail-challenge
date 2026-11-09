//! Exact parity resynthesis on at most six remaining literals.
use crate::circuit::QubitId;
use std::{borrow::Cow, cell::RefCell, collections::HashMap};
type Terms = [Vec<(QubitId, bool)>];
#[derive(Clone, Copy, PartialEq, Eq)]
struct Term {
    mask: u8,
    value: u8,
}
const ONE: Term = Term { mask: 0, value: 0 };
const PLANES: [u64; 6] = [
    0xaaaaaaaaaaaaaaaa,
    0xcccccccccccccccc,
    0xf0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00,
    0xffff0000ffff0000,
    0xffffffff00000000,
];
fn full(n: u8) -> u64 {
    if n == 6 {
        u64::MAX
    } else {
        (1u64 << (1 << n)) - 1
    }
}
fn truth(t: Term, n: u8) -> u64 {
    let mut out = full(n);
    let mut set = t.mask;
    while set != 0 {
        let i = set.trailing_zeros() as usize;
        set &= set - 1;
        out &= if t.value & (1 << i) != 0 {
            PLANES[i]
        } else {
            !PLANES[i]
        };
    }
    out
}
fn cost(v: &[Term], extra: usize) -> (usize, usize) {
    let mut total = 0;
    for t in v {
        total += match t.mask.count_ones() as usize + extra {
            0 | 1 => 0,
            2 => 1,
            n => 4 * n - 8,
        };
    }
    (total, v.len())
}
fn tag(mut cover: Vec<Term>, bit: u8, on: bool) -> Vec<Term> {
    for t in &mut cover {
        t.mask |= bit;
        if on {
            t.value |= bit;
        }
    }
    cover
}
fn join(mut a: Vec<Term>, b: Vec<Term>) -> Vec<Term> {
    a.extend(b);
    a
}
type Memo = HashMap<(u8, u64, usize), Vec<Term>>;
fn best(n: u8, f: u64, extra: usize, memo: &mut Memo) -> Vec<Term> {
    if f == 0 {
        return vec![];
    }
    if f == full(n) {
        return vec![ONE];
    }
    if let Some(hit) = memo.get(&(n, f, extra)) {
        return hit.clone();
    }
    let bit = 1u8 << (n - 1);
    let low = f & full(n - 1);
    let high = f >> bit;
    let result = if low == high {
        best(n - 1, low, extra, memo)
    } else {
        let diff = best(n - 1, low ^ high, extra + 1, memo);
        let sh = join(
            tag(best(n - 1, low, extra + 1, memo), bit, false),
            tag(best(n - 1, high, extra + 1, memo), bit, true),
        );
        let pd = join(best(n - 1, low, extra, memo), tag(diff.clone(), bit, true));
        let nd = join(best(n - 1, high, extra, memo), tag(diff, bit, false));
        [sh, pd, nd]
            .into_iter()
            .min_by_key(|v| cost(v, extra))
            .unwrap()
    };
    memo.insert((n, f, extra), result.clone());
    result
}
thread_local! {static CACHE:RefCell<Memo>=RefCell::new(Memo::new());}
fn cached(n: u8, f: u64, base: usize) -> Vec<Term> {
    CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        let key = (n, f, base);
        if let Some(hit) = cache.get(&key) {
            return hit.clone();
        }
        let v = best(n, f, base, &mut Memo::new());
        assert_eq!(v.iter().fold(0, |s, &t| s ^ truth(t, n)), f);
        if cache.len() >= 8192 {
            cache.clear();
        }
        cache.insert(key, v.clone());
        v
    })
}
pub(super) fn reduce<'a>(input: &'a Terms, extra: usize) -> Cow<'a, Terms> {
    if input.len() < 2 || input.len() > 64 {
        return Cow::Borrowed(input);
    }
    let common: Vec<_> = input[0]
        .iter()
        .copied()
        .filter(|v| input[1..].iter().all(|c| c.contains(v)))
        .collect();
    let mut wires = Vec::with_capacity(6);
    let mut original = Vec::with_capacity(input.len());
    for cube in input {
        let mut t = ONE;
        for &(q, negative) in cube {
            if common.contains(&(q, negative)) {
                continue;
            }
            let i = if let Some(i) = wires.iter().position(|&x| x == q) {
                i
            } else {
                if wires.len() == 6 {
                    return Cow::Borrowed(input);
                }
                wires.push(q);
                wires.len() - 1
            };
            let bit = 1u8 << i;
            if t.mask & bit != 0 {
                return Cow::Borrowed(input);
            }
            t.mask |= bit;
            if !negative {
                t.value |= bit;
            }
        }
        original.push(t);
    }
    let n = wires.len() as u8;
    let f = original.iter().fold(0, |s, &t| s ^ truth(t, n));
    let base = common.len() + extra;
    let new = cached(n, f, base);
    if cost(&new, base) >= cost(&original, base) {
        return Cow::Borrowed(input);
    }
    let out = new
        .into_iter()
        .map(|c| {
            let mut term = common.clone();
            for (i, &q) in wires.iter().enumerate() {
                if c.mask & (1 << i) != 0 {
                    term.push((q, c.value & (1 << i) == 0));
                }
            }
            term
        })
        .collect();
    Cow::Owned(out)
}
