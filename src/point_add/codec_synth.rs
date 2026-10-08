//! Synthesized promised-domain compressor, certificate synth4.json.
//! Public research challenge ecdsa.fail, GCD Skywalk architecture.
use super::*;

fn rank(rows: &[u8]) -> usize {
    let mut basis = [0u8; 6];
    let mut r = 0;
    for &row in rows {
        let mut x = row;
        for i in (0..6).rev() {
            if x >> i & 1 != 0 {
                if basis[i] == 0 {
                    basis[i] = x;
                    r += 1;
                    break;
                }
                x ^= basis[i];
            }
        }
    }
    r
}

/// Clifford-only matrix, implemented by reversing its row reduction.
fn linear(c: &mut Builder, q: &[QubitId; 6], matrix: &[u8; 6], inverse: bool) {
    let mut rows = *matrix;
    let mut operations = Vec::new();
    for col in 0..6 {
        let p = (col..6).find(|&i| rows[i] >> col & 1 != 0).unwrap();
        if p != col {
            rows.swap(p, col);
            operations.push((true, p, col));
        }
        for i in 0..6 {
            if i != col && rows[i] >> col & 1 != 0 {
                rows[i] ^= rows[col];
                operations.push((false, col, i));
            }
        }
    }
    assert_eq!(rows, [1, 2, 4, 8, 16, 32]);
    if !inverse {
        operations.reverse();
    }
    for (swap, a, b) in operations {
        if swap {
            c.swap(q[a], q[b]);
        } else {
            c.cx(q[a], q[b]);
        }
    }
}

/// Exactly one CCX: conjugate x ^= d*(affine_u(x)&affine_v(x)).
fn generalized(c: &mut Builder, q: &[QubitId; 6], u: u8, v: u8, d: u8) {
    assert_eq!((u & d).count_ones() % 2, 0);
    assert_eq!((v & d).count_ones() % 2, 0);
    let mut rows = vec![u & 63, v & 63];
    assert_eq!(rank(&rows), 2);
    let target = (0..6).find(|&i| d >> i & 1 != 0).unwrap();
    rows.push(1 << target);
    assert_eq!(rank(&rows), 3);
    for x in 1..64 {
        if (x & d).count_ones() % 2 == 0 && rank(&[rows.clone(), vec![x]].concat()) > rows.len() {
            rows.push(x);
        }
    }
    let matrix: [u8; 6] = rows.try_into().unwrap();
    linear(c, q, &matrix, false);
    if u & 64 != 0 {
        c.x(q[0]);
    }
    if v & 64 != 0 {
        c.x(q[1]);
    }
    c.ccx(q[0], q[1], q[2]);
    if u & 64 != 0 {
        c.x(q[0]);
    }
    if v & 64 != 0 {
        c.x(q[1]);
    }
    linear(c, q, &matrix, true);
}

const PREFIX: [(u8, u8, u8); 3] = [(120, 68, 40), (8, 25, 53), (73, 87, 6)];

/// Three CCX, no temporary quantum wire. Returns 5 persistent coordinates.
pub(super) fn pack(c: &mut Builder, q: [QubitId; 6]) -> [QubitId; 5] {
    for (u, v, d) in PREFIX {
        generalized(c, &q, u, v, d);
    }
    // The final synthesized CCX has (u,v,d)=(10,1,14); on support its
    // predicate equals q3. Fan out that known target into d's other slots.
    c.cx(q[3], q[1]);
    c.cx(q[3], q[2]);
    let m = c.alloc_bit();
    c.hmr(q[3], m);
    c.cz_if(q[1], q[0], m);
    c.free_bit(m);
    c.free(q[3]);
    [q[0], q[1], q[2], q[4], q[5]]
}

/// Four CCX, one restored raw wire; quantum inverse on all 27 valid states.
pub(super) fn unpack(c: &mut Builder, p: [QubitId; 5]) -> [QubitId; 6] {
    let e = c.alloc_qubit();
    let q = [p[0], p[1], p[2], e, p[3], p[4]];
    c.ccx(q[1], q[0], q[3]);
    c.cx(q[3], q[1]);
    c.cx(q[3], q[2]);
    for &(u, v, d) in PREFIX.iter().rev() {
        generalized(c, &q, u, v, d);
    }
    q
}

/// One additional CCX creates an empty affine plane for the inherited
/// five-trit outer pack. Certificate: bridge.json, exhaustive 32-word map.
pub(super) fn pack_compatible_bridge(c: &mut Builder, q: [QubitId; 6]) -> [QubitId; 5] {
    let p = pack(c, q);
    c.cx(p[1], p[3]);
    c.ccx(p[0], p[2], p[1]);
    c.cx(p[1], p[3]);
    c.cx(p[0], p[3]);
    [p[1], p[0], p[2], p[3], p[4]]
}

pub(super) fn unpack_compatible_bridge(c: &mut Builder, outer: [QubitId; 5]) -> [QubitId; 6] {
    let p = [outer[1], outer[0], outer[2], outer[3], outer[4]];
    c.cx(p[0], p[3]);
    c.cx(p[1], p[3]);
    c.ccx(p[0], p[2], p[1]);
    c.cx(p[1], p[3]);
    unpack(c, p)
}

// Compatible certificate synth4-compatible-fixed.json. Full unitary final
// relation is 1+x2+x3+x4=0, and outer affine forms are (27,77,99).
const COMPAT_PREFIX: [(u8, u8, u8); 3] = [(120, 68, 40), (72, 19, 17), (72, 78, 38)];

/// Three CCX, inherited outer pack5-compatible output, no extra bridge.
pub(super) fn pack_compatible(c: &mut Builder, q: [QubitId; 6]) -> [QubitId; 5] {
    pack_compatible_shared(c, q, None)
}

/// v025 A-2 (ported from c1-001/two-tick-001): when the walk already holds the product
/// `h2 * typ3` (the first nonlinear predicate of this pack, produced for free from the
/// previous tick's retained first carry), the first synthesized CCX is replaced by
/// Clifford gates plus an HMR of that product with a Clifford-only phase repair.
pub(super) fn pack_compatible_shared(
    c: &mut Builder,
    q: [QubitId; 6],
    shared: Option<QubitId>,
) -> [QubitId; 5] {
    if let Some(product) = shared {
        // product = h2 * typ3. The first predicate is product XOR u,
        // u=1+l2+h3+l3; displacement d=40 preserves u. After displacement
        // product=h2*u, so its measurement repair is Clifford-only.
        for i in [3, 4, 5] {
            c.cx(q[i], product);
        }
        c.x(product);
        c.cx(product, q[3]);
        c.cx(product, q[5]);
        c.x(product);
        for i in [5, 4, 3] {
            c.cx(q[i], product);
        }
        c.cx(q[3], q[5]);
        c.cx(q[4], q[5]);
        c.x(q[5]);
        let m = c.alloc_bit();
        c.hmr(product, m);
        c.cz_if(q[2], q[5], m);
        c.free_bit(m);
        c.free(product);
        c.x(q[5]);
        c.cx(q[4], q[5]);
        c.cx(q[3], q[5]);
        for &(u, v, d) in &COMPAT_PREFIX[1..] {
            generalized(c, &q, u, v, d);
        }
    } else {
        for (u, v, d) in COMPAT_PREFIX {
            generalized(c, &q, u, v, d);
        }
    }
    // Move the final affine relation to q3. The last CCX's transformed
    // displacement is bits 0,1,3 and its predicate is q4&q2.
    c.cx(q[2], q[3]);
    c.cx(q[4], q[3]);
    c.x(q[3]);
    c.cx(q[3], q[0]);
    c.cx(q[3], q[1]);
    let m = c.alloc_bit();
    c.hmr(q[3], m);
    c.cz_if(q[4], q[2], m);
    c.free_bit(m);
    c.free(q[3]);
    // On the final relation, outer_forms reduce to (1+p0+p1+p2,
    // p0+p3,1+p0+p1+p4), an empty three-control cube on all27 states.
    let p = [q[0], q[1], q[2], q[4], q[5]];
    c.cx(p[0], p[2]);
    c.cx(p[1], p[2]);
    c.x(p[2]);
    c.cx(p[0], p[3]);
    c.cx(p[0], p[4]);
    c.cx(p[1], p[4]);
    c.x(p[4]);
    [p[2], p[0], p[1], p[3], p[4]]
}

pub(super) fn unpack_compatible_retained(
    c: &mut Builder,
    outer: [QubitId; 5],
    retain: bool,
) -> ([QubitId; 6], Option<QubitId>) {
    let p = [outer[1], outer[2], outer[0], outer[3], outer[4]];
    c.cx(p[0], p[2]);
    c.cx(p[1], p[2]);
    c.x(p[2]);
    c.cx(p[0], p[3]);
    c.cx(p[0], p[4]);
    c.cx(p[1], p[4]);
    c.x(p[4]);
    let e = c.alloc_qubit();
    let q = [p[0], p[1], p[2], e, p[3], p[4]];
    c.ccx(q[4], q[2], q[3]);
    c.cx(q[3], q[0]);
    c.cx(q[3], q[1]);
    c.x(q[3]);
    c.cx(q[4], q[3]);
    c.cx(q[2], q[3]);
    for &(u, v, d) in COMPAT_PREFIX[1..].iter().rev() {
        generalized(c, &q, u, v, d);
    }
    let product = if retain {
        let z = c.alloc_qubit();
        // Last inverse displacement: f=(1+l2+h3+l3)*(1+h2).
        c.cx(q[4], q[3]);
        c.cx(q[5], q[3]);
        c.x(q[3]);
        c.x(q[2]);
        c.ccx(q[3], q[2], z);
        c.x(q[2]);
        c.x(q[3]);
        c.cx(q[5], q[3]);
        c.cx(q[4], q[3]);
        c.cx(z, q[3]);
        c.cx(z, q[5]);
        // f XOR u = h2*u = h2*typ3 on the valid trit support.
        c.x(z);
        for i in [3, 4, 5] {
            c.cx(q[i], z);
        }
        Some(z)
    } else {
        let (u, v, d) = COMPAT_PREFIX[0];
        generalized(c, &q, u, v, d);
        None
    };
    (q, product)
}

pub(super) fn unpack_compatible(c: &mut Builder, outer: [QubitId; 5]) -> [QubitId; 6] {
    unpack_compatible_retained(c, outer, false).0
}
