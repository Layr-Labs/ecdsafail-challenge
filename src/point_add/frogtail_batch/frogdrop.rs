// Rotation helper from Frogtail-917 / 897d06a.
use super::builder::B;
use crate::circuit::QubitId;
pub fn crot_up(b: &mut B, c: QubitId, v: &[QubitId], r: usize) {
    let n = v.len();
    let r = r % n;
    if r == 0 {
        return;
    }
    let g = gcd(n, r);
    for s in 0..g {
        let len = n / g;
        // cycle s -> s + r -> ...: content at lane x moves to x + r; walk the cycle backwards with swaps
        let cyc: Vec<usize> = (0..len).map(|k| (s + k * r) % n).collect();
        for k in (1..len).rev() {
            b.cswap(c, v[cyc[k]], v[cyc[k - 1]]);
        }
    }
}
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}
