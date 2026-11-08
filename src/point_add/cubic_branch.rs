//! Factor a six-wire cubic permutation into two *dependent* reversible
//! product updates and a final affine map. Recognized maps are cached by
//! their complete basis truth table. Verify every native emitted region
//! over every assignment before accepting it.
use super::*;
#[derive(Clone, Copy, Default)]
struct Two {
    p: [Product; 2],
    signs: [u8; 2],
    rows: [u8; MAX],
    c: u8,
}
#[derive(Clone, Copy, Default)]
struct Entry {
    truth: [u64; MAX],
    n: u8,
    sol: Option<Two>,
}
struct Table {
    cache: Vec<Entry>,
    linear: [u64; 64],
}
impl Table {
    fn new() -> Self {
        let mut linear = [0u64; 64];
        for mask in 0usize..64 {
            for r in 0usize..64 {
                if (mask & r).count_ones() & 1 != 0 {
                    linear[mask] |= 1u64 << r;
                }
            }
        }
        Self {
            cache: vec![Entry::default(); 8192],
            linear,
        }
    }
    fn solve(&mut self, chart: &Chart) -> Option<Two> {
        let n = chart.n;
        let mut key = 0x33c789c090bfa847u64;
        for (j, &word) in chart.value[..n].iter().enumerate() {
            key = key.rotate_left(17)
                ^ (word
                    .wrapping_mul(0x9e3779b97f4a7c15)
                    .rotate_left(3 * j as u32));
        }
        let at = (key ^ (key >> 31)) as usize & (self.cache.len() - 1);
        let e = self.cache[at];
        if e.n as usize == n && e.truth == chart.value {
            return e.sol;
        }
        let sol = self.fresh(chart);
        self.cache[at] = Entry {
            truth: chart.value,
            n: n as u8,
            sol,
        };
        sol
    }
    fn fresh(&self, chart: &Chart) -> Option<Two> {
        let n = chart.n;
        let mut total = [0u64; MAX];
        let mut non = [0; MAX];
        let mut cub = 0;
        for i in 0..n {
            total[i] = mobius(chart.value[i]);
            non[i] = total[i] & !LO;
            let high = non[i] & !QUAD;
            if high & !degree(3) != 0 {
                return None;
            }
            cub |= high;
        }
        if cub == 0 {
            return None;
        }
        let mut basis = non;
        if reduce(&mut basis, n) != 2 {
            return None;
        }
        let span = [basis[0], basis[1], basis[0] ^ basis[1]];
        let mut pure = 0;
        let mut qs = [0; 2];
        let mut qc = 0;
        for v in span {
            if v & !QUAD == 0 {
                pure = v
            } else if qc < 2 {
                qs[qc] = v;
                qc += 1
            } else {
                return None;
            }
        }
        if pure == 0 || qc != 2 {
            return None;
        }
        let Some(p) = factor(pure, n) else {
            return None;
        };
        let common_cubic = qs[0] & !QUAD;
        for &qshape in &qs {
            let (mut dp, mut dq, mut base, mut basec) = (0u8, 0u8, [0u8; MAX], 0u8);
            for i in 0..n {
                let f = non[i];
                if f == pure || f == pure ^ qshape {
                    dp |= 1 << i
                }
                if f == qshape || f == pure ^ qshape {
                    dq |= 1 << i
                }
                basec |= ((total[i] & 1) as u8) << i;
                for j in 0..n {
                    base[i] |= (((total[i] >> (1 << j)) & 1) as u8) << j;
                }
            }
            for pf in 0u8..4 {
                let signed =
                    |m: u8, b: u8| self.linear[m as usize] ^ if b != 0 { u64::MAX } else { 0 };
                let pw = signed(p.f, pf & 1) & signed(p.g, pf >> 1);
                let pa = mobius(pw);
                debug_assert_eq!(pa & !LO, pure);
                let mut pal = 0u8;
                for j in 0..n {
                    pal |= (((pa >> (1 << j)) & 1) as u8) << j;
                }
                for h in 1u8..(1u8 << n) {
                    let ph = mobius(pw & self.linear[h as usize]);
                    if ph & !LO & !QUAD != common_cubic {
                        continue;
                    }
                    for hc in 0..=1u8 {
                        let wanted = (qshape ^ ph ^ (if hc != 0 { pa } else { 0 })) & QUAD;
                        let Some(basis_p) = factor(wanted, n) else {
                            continue;
                        };
                        let mut pair = [basis_p.f, basis_p.g, basis_p.f ^ basis_p.g];
                        if !pair.contains(&h) {
                            continue;
                        }
                        pair.sort_unstable();
                        for &f in &pair {
                            for &g in &pair {
                                if f == g {
                                    continue;
                                }
                                let (alpha, beta) = if h == g {
                                    (1u8, 0u8)
                                } else if h == f {
                                    (0, 1)
                                } else {
                                    (1, 1)
                                };
                                for sf in 0u8..4 {
                                    let rf = sf & 1;
                                    let sg = sf >> 1;
                                    if ((alpha & sg) ^ (beta & rf) ^ (alpha & beta)) != hc {
                                        continue;
                                    }
                                    let u = signed(f, rf);
                                    let v = signed(g, sg);
                                    let qw = (u ^ (if alpha != 0 { pw } else { 0 }))
                                        & (v ^ (if beta != 0 { pw } else { 0 }));
                                    let qa = mobius(qw);
                                    if qa & !LO != qshape {
                                        continue;
                                    }
                                    let mut qal = 0u8;
                                    for j in 0..n {
                                        qal |= (((qa >> (1 << j)) & 1) as u8) << j;
                                    }
                                    let mut l = base;
                                    let mut off = basec;
                                    for i in 0..n {
                                        if dp >> i & 1 != 0 {
                                            l[i] ^= pal;
                                            off ^= ((pa & 1) as u8) << i;
                                        }
                                        if dq >> i & 1 != 0 {
                                            l[i] ^= qal;
                                            off ^= ((qa & 1) as u8) << i;
                                        }
                                    }
                                    let Some(inv) = inverse(l, n) else { continue };
                                    let mut d1 = 0u8;
                                    let mut d2 = 0u8;
                                    for i in 0..n {
                                        d1 |= u8::from(parity(inv[i] & dp)) << i;
                                        d2 |= u8::from(parity(inv[i] & dq)) << i;
                                    }
                                    if parity(d1 & p.f)
                                        || parity(d1 & p.g)
                                        || parity(d2 & f)
                                        || parity(d2 & g)
                                        || u8::from(parity(d1 & f)) != alpha
                                        || u8::from(parity(d1 & g)) != beta
                                    {
                                        continue;
                                    }
                                    return Some(Two {
                                        p: [
                                            Product {
                                                f: p.f,
                                                g: p.g,
                                                d: d1,
                                            },
                                            Product { f, g, d: d2 },
                                        ],
                                        signs: [pf, sf],
                                        rows: l,
                                        c: off,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }
}
fn signed_product(p: Product, sign: u8, n: usize, out: &mut Vec<Small>) {
    let start = out.len();
    product(p, n, out);
    if sign == 0 {
        return;
    }
    let at = start
        + out[start..]
            .iter()
            .position(|g| matches!(g, Small::CCX(_, _, _)))
            .unwrap();
    let center = out[at];
    let Small::CCX(a, b, _) = center else {
        unreachable!()
    };
    let mut seq = [center; 5];
    let mut k = 0;
    if sign & 1 != 0 {
        seq[k] = Small::X(a);
        k += 1;
    }
    if sign & 2 != 0 {
        seq[k] = Small::X(b);
        k += 1;
    }
    seq[k] = center;
    k += 1;
    if sign & 2 != 0 {
        seq[k] = Small::X(b);
        k += 1;
    }
    if sign & 1 != 0 {
        seq[k] = Small::X(a);
        k += 1;
    }
    out.splice(at..=at, seq[..k].iter().copied());
}
impl Synthesis {
    fn cubic_realize(&mut self, chart: &Chart, p: Two) {
        self.raw.clear();
        for i in 0..2 {
            signed_product(p.p[i], p.signs[i], chart.n, &mut self.raw);
        }
        instructions_for(p.rows, p.c, chart.n, &mut self.raw);
        self.simple.clear();
        simplify_linear(&self.raw, chart.n, &mut self.scratch, &mut self.simple);
        self.native.clear();
        for &g in &self.simple {
            self.native.push(native(g, &chart.wires));
        }
        let mut proof = Chart::new();
        for &w in &chart.wires[..chart.n] {
            proof.idx(w).unwrap();
        }
        for &g in &self.native {
            proof
                .step(g)
                .expect("cubic output uses wires outside original region");
        }
        assert_eq!(
            proof.value[..chart.n],
            chart.value[..chart.n],
            "cubic synthesized native output fails truth table"
        );
    }
}

#[path = "connected.rs"]
mod connected;
pub(super) use connected::Real as Joint;

pub(super) fn joint(ops: &mut Vec<Op>) -> Joint {
    connected::apply(ops)
}
