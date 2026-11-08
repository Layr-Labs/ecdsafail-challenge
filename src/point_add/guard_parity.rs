//! Exact XOR covers of the seven-bit Y interval and five-bit sum threshold.
//! Every caller toggles one destination by the parity of the matching terms.
use std::cell::RefCell;
use std::collections::HashMap;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Cube {
    pub mask: u16,
    pub value: u16,
}
const ONE: Cube = Cube { mask: 0, value: 0 };
fn literal_sum(cubes: &[Cube]) -> usize {
    cubes.iter().map(|c| c.mask.count_ones() as usize).sum()
}
fn smaller(a: Vec<Cube>, b: Vec<Cube>) -> Vec<Cube> {
    if (a.len(), literal_sum(&a)) <= (b.len(), literal_sum(&b)) {
        a
    } else {
        b
    }
}
fn join(mut a: Vec<Cube>, b: &[Cube]) -> Vec<Cube> {
    a.extend_from_slice(b);
    a
}
fn range(lo: u16, hi: u16, start: u16, size: u16, mask: u16) -> [Vec<Cube>; 2] {
    let prefix = Cube {
        mask,
        value: start & mask,
    };
    if start >= hi || start + size <= lo {
        return [vec![], vec![prefix]];
    }
    if lo <= start && start + size <= hi {
        return [vec![prefix], vec![]];
    }
    let half = size / 2;
    let [yes_l, no_l] = range(lo, hi, start, half, mask | half);
    let [yes_r, no_r] = range(lo, hi, start + half, half, mask | half);
    let yes = join(yes_l, &yes_r);
    let no = join(no_l, &no_r);
    [
        smaller(yes.clone(), join(vec![prefix], &no)),
        smaller(no, join(vec![prefix], &yes)),
    ]
}
fn disjoint(lo: u16, hi: u16, width: usize) -> Vec<Cube> {
    let full = (1u16 << width) - 1;
    let mut pos = lo;
    let mut out = Vec::new();
    while pos < hi {
        let mut step = if pos == 0 {
            1u16 << width
        } else {
            1u16 << pos.trailing_zeros()
        };
        while pos + step > hi {
            step /= 2;
        }
        let mask = full & !(step - 1);
        out.push(Cube {
            mask,
            value: pos & mask,
        });
        pos += step;
    }
    out
}
fn toggle(v: &mut Vec<Cube>, c: Cube) {
    if let Some(i) = v.iter().position(|&q| q == c) {
        v.swap_remove(i);
    } else {
        v.push(c);
    }
}
fn product(y: &[Cube], sum: &[Cube]) -> Vec<Cube> {
    let mut result = Vec::new();
    for &a in y {
        for &b in sum {
            toggle(
                &mut result,
                Cube {
                    mask: a.mask | (b.mask << 7),
                    value: a.value | (b.value << 7),
                },
            );
        }
    }
    result
}
fn prices(v: &[Cube]) -> [usize; 8] {
    std::array::from_fn(|extra| {
        v.iter()
            .map(|c| match c.mask.count_ones() as usize + extra {
                0 | 1 => 0,
                2 => 1,
                n => 4 * n - 8,
            })
            .sum()
    })
}
pub(super) fn template(lo: u16, hi: u16, bound: u16, positive: bool) -> Vec<Cube> {
    assert!(lo < hi && hi <= 128 && bound <= 32);
    let yo = disjoint(lo, hi, 7);
    let mut best = if positive {
        product(&yo, &disjoint(0, bound, 5))
    } else {
        let mut v = join(disjoint(0, lo, 7), &disjoint(hi, 128, 7));
        v.extend(product(&yo, &disjoint(bound, 32, 5)));
        v
    };
    let mut cost = prices(&best);
    let [yes_y, mut no_y] = range(lo, hi, 0, 128, 0);
    toggle(&mut no_y, ONE);
    let [yes_s, mut no_s] = range(0, bound, 0, 32, 0);
    toggle(&mut no_s, ONE);
    for y in [&yes_y, &no_y] {
        for sum in [&yes_s, &no_s] {
            let mut candidate = product(y, sum);
            if !positive {
                toggle(&mut candidate, ONE);
            }
            let next = prices(&candidate);
            if next.iter().zip(&cost).all(|(a, b)| a <= b)
                && (next != cost || candidate.len() < best.len())
            {
                cost = next;
                best = candidate;
            }
        }
    }
    best
}
type Key = (u16, u16, u16, bool);
thread_local! {static CACHE:RefCell<HashMap<Key,Vec<Cube>>>=RefCell::new(HashMap::new());}
pub(super) fn terms<T: Copy>(
    lo: u16,
    hi: u16,
    bound: u16,
    positive: bool,
    y: &[T],
    sum: &[T],
) -> Vec<Vec<(T, bool)>> {
    assert_eq!((y.len(), sum.len()), (7, 5));
    let key = (lo, hi, bound, positive);
    CACHE.with(|map| {
        let mut map = map.borrow_mut();
        let cubes = map
            .entry(key)
            .or_insert_with(|| template(lo, hi, bound, positive));
        cubes
            .iter()
            .map(|c| {
                let mut bits = c.mask;
                let mut term = Vec::with_capacity(bits.count_ones() as usize);
                while bits != 0 {
                    let i = bits.trailing_zeros() as usize;
                    bits &= bits - 1;
                    term.push((
                        if i < 7 { y[i] } else { sum[i - 7] },
                        c.value & (1 << i) == 0,
                    ));
                }
                term
            })
            .collect()
    })
}
