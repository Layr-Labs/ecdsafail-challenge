//! Reversible cut interface from signed Skywalk rails to positive Kaliski
//! values.  This is the first half of the packed-tail seam; physical bucket
//! packing follows after the values are positive.

use super::adder;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::lowroom;

pub struct PositiveFrame {
    neg_u: Q,
}

pub struct BucketFrame {
    header: Vec<Q>,
    released: Vec<Q>,
    pairings: Vec<(Q, Q, usize)>,
}

const BUCKET_STARTS: [usize; 4] = [1, 74, 106, 138];
const BUCKET_HIGH: [usize; 4] = [73, 105, 137, 167];
const BUCKET_BASE_U: usize = 73;
const BUCKET_BASE_S: usize = 120;
const BUCKET_TAIL: usize = 95;

fn fredkin(c: &mut Builder, ctl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctl, a, b);
    c.cx(b, a);
}

fn or_into(c: &mut Builder, bits: &[Q], out: Q) {
    assert!(!bits.is_empty());
    if bits.len() == 1 {
        c.cx(bits[0], out);
        return;
    }
    c.x_all(bits);
    c.x(out);
    if bits.len() == 2 {
        c.ccx(bits[0], bits[1], out);
    } else {
        let work = c.alloc_qubits(bits.len() - 2);
        c.ccx(bits[0], bits[1], work[0]);
        for i in 1..work.len() {
            c.ccx(work[i - 1], bits[i + 1], work[i]);
        }
        c.ccx(*work.last().unwrap(), *bits.last().unwrap(), out);
        for i in (1..work.len()).rev() {
            c.ccx(work[i - 1], bits[i + 1], work[i]);
        }
        c.ccx(bits[0], bits[1], work[0]);
        c.free_vec(&work);
    }
    c.x_all(bits);
}

fn bucket_flags(c: &mut Builder, value: &[Q], flags: &[Q]) {
    assert_eq!(value.len(), BUCKET_HIGH[3]);
    assert_eq!(flags.len(), 3);
    or_into(c, &value[BUCKET_STARTS[3] - 1..], flags[2]);
    let mut mid = value[BUCKET_STARTS[2] - 1..BUCKET_STARTS[3] - 1].to_vec();
    mid.push(flags[2]);
    or_into(c, &mid, flags[1]);
    let mut low = value[BUCKET_STARTS[1] - 1..BUCKET_STARTS[2] - 1].to_vec();
    low.push(flags[1]);
    or_into(c, &low, flags[0]);
}

fn bucket_flags_inv(c: &mut Builder, value: &[Q], flags: &[Q]) {
    let mut low = value[BUCKET_STARTS[1] - 1..BUCKET_STARTS[2] - 1].to_vec();
    low.push(flags[1]);
    or_into(c, &low, flags[0]);
    let mut mid = value[BUCKET_STARTS[2] - 1..BUCKET_STARTS[3] - 1].to_vec();
    mid.push(flags[2]);
    or_into(c, &mid, flags[1]);
    or_into(c, &value[BUCKET_STARTS[3] - 1..], flags[2]);
}

fn slot_bucket(slot: usize) -> usize {
    let bit = BUCKET_BASE_U + slot;
    BUCKET_HIGH
        .iter()
        .position(|&hi| hi > bit)
        .expect("bucket tail slot")
}

fn coefficient_header(c: &mut Builder, coefficient: &[Q]) -> Vec<Q> {
    // At cut160 coefficient width is at most136.  Segment-0 bucket caps are
    // 215,184,152,120, so buckets0/1 are unreachable and b1 is public1.
    // b0=[bitlen(coefficient)<=120] is the zero test of bits120..135.
    let header = c.alloc_qubits(2);
    c.x(header[1]);
    let any_high = c.alloc_qubit();
    or_into(c, &coefficient[120..], any_high);
    c.x(header[0]);
    c.cx(any_high, header[0]);
    or_into(c, &coefficient[120..], any_high);
    c.free(any_high);
    header
}

fn coefficient_header_clear(c: &mut Builder, coefficient: &[Q], header: &[Q]) {
    let any_high = c.alloc_qubit();
    or_into(c, &coefficient[120..], any_high);
    c.cx(any_high, header[0]);
    c.x(header[0]);
    or_into(c, &coefficient[120..], any_high);
    c.free(any_high);
    c.x(header[1]);
}

/// Pack one positive `(value, coefficient)` pair into the first four-bucket
/// arena used after tick 160.  Future coefficient lanes 136..215 are virtual
/// zeroes hosted directly in redundant value positions; they are never
/// allocated as a second source word.
pub fn bucket_pack(c: &mut Builder, value: &[Q], coefficient: &[Q]) -> BucketFrame {
    assert_eq!(value.len(), 167);
    assert_eq!(coefficient.len(), 136);
    let header = coefficient_header(c, coefficient);
    let mut released = Vec::new();
    let mut pairings = Vec::new();
    let mut used_value = std::collections::BTreeSet::new();
    let mut used_coefficient = std::collections::BTreeSet::new();
    used_value.extend(value[..BUCKET_BASE_U].iter().map(|q| q.0));
    used_coefficient.extend(coefficient[..BUCKET_BASE_S].iter().map(|q| q.0));
    for slot in 0..BUCKET_TAIL {
        let ui = BUCKET_BASE_U + slot;
        let sj = BUCKET_BASE_S + (BUCKET_TAIL - 1 - slot);
        let uq = value.get(ui).copied();
        let sq = coefficient.get(sj).copied();
        match (uq, sq) {
            (Some(uq), Some(sq)) => {
                let bucket = slot_bucket(slot);
                // With the cut160 input widths every physical overlap belongs
                // to the bucket3 extension; header b0 is exactly [bucket=3].
                assert_eq!(bucket, 3);
                let ctl = header[0];
                c.x(ctl);
                fredkin(c, ctl, uq, sq);
                c.x(ctl);
                used_value.insert(uq.0);
                released.push(sq);
                pairings.push((uq, sq, bucket));
            }
            (Some(uq), None) => {
                used_value.insert(uq.0);
            }
            (None, Some(sq)) => {
                used_coefficient.insert(sq.0);
            }
            (None, None) => panic!("empty bucket tail slot {slot}"),
        }
    }
    for &q in value {
        if !used_value.contains(&q.0) && !released.contains(&q) {
            released.push(q);
        }
    }
    for &q in coefficient {
        if !used_coefficient.contains(&q.0) && !released.contains(&q) {
            released.push(q);
        }
    }
    for &q in &released {
        c.free(q);
    }
    BucketFrame {
        header,
        released,
        pairings,
    }
}

pub fn bucket_unpack(c: &mut Builder, value: &[Q], coefficient: &[Q], frame: BucketFrame) {
    for &q in &frame.released {
        c.reacquire(q);
    }
    for &(uq, sq, bucket) in frame.pairings.iter().rev() {
        assert_eq!(bucket, 3);
        let ctl = frame.header[0];
        c.x(ctl);
        fredkin(c, ctl, uq, sq);
        c.x(ctl);
    }
    // The pairings restored the original coefficient word; erase its
    // canonical binary header without a retained initial-bucket receipt.
    coefficient_header_clear(c, coefficient, &frame.header);
    c.free_vec(&frame.header);
}

fn route_u_first(c: &mut Builder, rails: &Rails, typ: Q) {
    // typ=1: R1 is +/-u and R2 is +(u+v).
    // typ=0: R2 is +/-u and R1 is +(u+v).
    c.x(typ);
    for (&a, &b) in rails.r1.iter().zip(&rails.r2) {
        fredkin(c, typ, a, b);
    }
    c.x(typ);
}

fn negate_if(c: &mut Builder, value: &[Q], neg: Q, dirty: &[Q]) {
    assert!(
        dirty.len() > value.len(),
        "signed seam needs value width + 1 dirty passengers"
    );
    c.cx_all(neg, value);
    lowroom::cinc_dirty(c, neg, value, &dirty[..value.len() + 1]);
}

/// Convert the reachable signed-rail frame into `(u,v)`, both positive and
/// held in `rails.r1, rails.r2`.  `passenger` is arbitrary dirty data and is
/// restored.  The returned receipt is required by [`from_positive`].
pub fn to_positive(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    passenger: &[Q],
    cap: usize,
) -> PositiveFrame {
    assert_eq!(rails.r1.len(), rails.r2.len());
    route_u_first(c, rails, typ);
    let neg_u = c.alloc_qubit();
    c.cx(*rails.r1.last().unwrap(), neg_u);
    negate_if(c, &rails.r1, neg_u, passenger);
    adder::sub(c, None, &rails.r1, &rails.r2, None, Some(cap));
    PositiveFrame { neg_u }
}

/// Exact inverse of [`to_positive`].
pub fn from_positive(
    c: &mut Builder,
    rails: &mut Rails,
    typ: Q,
    passenger: &[Q],
    cap: usize,
    frame: PositiveFrame,
) {
    adder::add(c, None, &rails.r1, &rails.r2, None, Some(cap));
    negate_if(c, &rails.r1, frame.neg_u, passenger);
    c.cx(*rails.r1.last().unwrap(), frame.neg_u);
    c.release_clean(frame.neg_u);
    route_u_first(c, rails, typ);
}
