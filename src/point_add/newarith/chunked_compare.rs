//! Exact fresh-carry comparison, opt-in with MIDQ_CHUNK_COMPARE=1.
//! See chunked_compare_proof.md for the phase proof and resource formulas.

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

const QCAP: usize = 1019;

#[derive(Clone, Copy)]
enum Carry<'a> {
    Constant(bool),
    Wire(&'a QReg),
}

#[derive(Clone, Copy)]
enum Endpoint<'a> {
    Xor(&'a QReg),
    Phase,
}

fn copy_carry(c: &mut Circuit, carry: Carry<'_>, target: &QReg) {
    match carry {
        Carry::Constant(false) => {}
        Carry::Constant(true) => c.x(target),
        Carry::Wire(q) => c.cx(q, target),
    }
}

fn phase_carry(c: &mut Circuit, carry: Carry<'_>) {
    match carry {
        Carry::Constant(false) => {}
        Carry::Constant(true) => {
            // A constant-one endpoint has a genuine (conditioned) global sign.
            c.b.push_op(crate::circuit::Op::empty());
        }
        Carry::Wire(q) => c.z(q),
    }
}

// a,b are restored immediately, so repeated and noncontiguous input slots work.
fn fresh_maj(c: &mut Circuit, a: &QReg, b: &QReg, cin: Carry<'_>, t: &QReg, complement_b: bool) {
    if a.id() == b.id() {
        if complement_b {
            copy_carry(c, cin, t);
        } else {
            c.cx(a, t);
        }
        return;
    }
    if complement_b {
        c.x(b);
    }
    match cin {
        Carry::Constant(one) => {
            c.ccx(a, b, t);
            if one {
                c.cx(a, t);
                c.cx(b, t);
            }
        }
        Carry::Wire(q) => {
            c.cx(q, a);
            c.cx(q, b);
            c.ccx(a, b, t);
            c.cx(q, t);
            c.cx(q, b);
            c.cx(q, a);
        }
    }
    if complement_b {
        c.x(b);
    }
}

fn phase_maj(c: &mut Circuit, a: &QReg, b: &QReg, cin: Carry<'_>, complement_b: bool) {
    if a.id() == b.id() {
        if complement_b {
            phase_carry(c, cin);
        } else {
            c.z(a);
        }
        return;
    }
    if complement_b {
        c.x(b);
    }
    c.cz(a, b);
    match cin {
        Carry::Constant(false) => {}
        Carry::Constant(true) => {
            c.z(a);
            c.z(b);
        }
        Carry::Wire(q) => {
            c.cz(a, q);
            c.cz(b, q);
        }
    }
    if complement_b {
        c.x(b);
    }
}

fn clear_maj(c: &mut Circuit, a: &QReg, b: &QReg, cin: Carry<'_>, t: &QReg, complement_b: bool) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.with_condition(m, |c| phase_maj(c, a, b, cin, complement_b));
    c.free_bit(m);
}

fn chain(
    c: &mut Circuit,
    a: &[&QReg],
    b: &[&QReg],
    cin: Carry<'_>,
    complement_b: bool,
) -> Vec<QReg> {
    let mut carries = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let q = c.alloc_qreg("chunk.carry");
        let prev = if i == 0 {
            cin
        } else {
            Carry::Wire(&carries[i - 1])
        };
        fresh_maj(c, a[i], b[i], prev, &q, complement_b);
        carries.push(q);
    }
    carries
}

fn clear_chain(
    c: &mut Circuit,
    a: &[&QReg],
    b: &[&QReg],
    cin: Carry<'_>,
    mut carries: Vec<QReg>,
    complement_b: bool,
) {
    while let Some(q) = carries.pop() {
        let i = carries.len();
        let prev = carries.last().map_or(cin, Carry::Wire);
        clear_maj(c, a[i], b[i], prev, &q, complement_b);
        c.zero_and_free(q);
    }
}

fn scratch_qubits(n: usize, k: usize) -> usize {
    if n == 0 {
        return 0;
    }
    let chunks = n.div_ceil(k);
    let tail = n - (chunks - 1) * k;
    let last_peak = chunks - 1 + tail;
    if chunks == 1 {
        last_peak
    } else {
        last_peak.max(chunks - 2 + k)
    }
}

fn select_chunk(n: usize, headroom: usize, preferred: usize) -> Option<usize> {
    (1..=n.min(preferred))
        .filter(|&k| scratch_qubits(n, k) <= headroom)
        .min_by_key(|&k| ((n.div_ceil(k) - 1) * (k - 1), scratch_qubits(n, k), k))
}

fn configured_chunk(c: &mut Circuit, n: usize) -> Option<usize> {
    if std::env::var("MIDQ_CHUNK_COMPARE").ok().as_deref() != Some("1") {
        return None;
    }
    let cap = std::env::var("MIDQ_CHUNK_COMPARE_QCAP")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(QCAP)
        .min(QCAP);
    let preferred = std::env::var("MIDQ_CHUNK_COMPARE_SIZE")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(32);
    c.flush_pending_frees();
    if std::env::var("MIDQ_VARIABLE_CHUNKS").ok().as_deref() == Some("1") {
        return crate::point_add::clean_chunk_plan::plan(n,
            cap.saturating_sub(c.b.active_qubits as usize)).map(|_| 1);
    }
    select_chunk(n, cap.saturating_sub(c.b.active_qubits as usize), preferred)
}

fn validate(a: &[&QReg], b: &[&QReg], out: Option<&QReg>) {
    assert_eq!(a.len(), b.len(), "comparison widths differ");
    if let Some(out) = out {
        assert!(
            a.iter().chain(b).all(|q| q.id() != out.id()),
            "comparison output must not alias an operand"
        );
    }
}

fn emit(
    c: &mut Circuit,
    a: &[&QReg],
    b: &[&QReg],
    initial: bool,
    complement_b: bool,
    endpoint: Endpoint<'_>,
    k: usize,
    conditional_replay: bool,
) {
    validate(
        a,
        b,
        match endpoint {
            Endpoint::Xor(q) => Some(q),
            Endpoint::Phase => None,
        },
    );
    assert!(k > 0);
    let n = a.len();
    let initial = Carry::Constant(initial);
    if n == 0 {
        match endpoint {
            Endpoint::Xor(q) => copy_carry(c, initial, q),
            Endpoint::Phase => phase_carry(c, initial),
        }
        return;
    }
    let section = c.push_section("p.cmp.chunk");
    let mut boundaries = Vec::new();
    let cap = std::env::var("MIDQ_CHUNK_COMPARE_QCAP").ok()
        .and_then(|v| v.parse::<usize>().ok()).unwrap_or(QCAP).min(QCAP);
    let variable = std::env::var("MIDQ_VARIABLE_CHUNKS").ok().as_deref() == Some("1");
    let sizes = if variable {
        crate::point_add::clean_chunk_plan::plan(n,
            cap.saturating_sub(c.b.active_qubits as usize)).expect("comparison fits")
    } else {
        (0..n).step_by(k).map(|s| (n - s).min(k)).collect()
    };
    let mut boundary_ranges = Vec::new();
    let mut next = 0;
    for size in sizes {
        let start = next;
        let end = start + size;
        next = end;
        let prev = boundaries.last().map_or(initial, Carry::Wire);
        if end == n && matches!(endpoint, Endpoint::Phase) {
            let carries = chain(
                c,
                &a[start..end - 1],
                &b[start..end - 1],
                prev,
                complement_b,
            );
            phase_maj(
                c,
                a[end - 1],
                b[end - 1],
                carries.last().map_or(prev, Carry::Wire),
                complement_b,
            );
            clear_chain(
                c,
                &a[start..end - 1],
                &b[start..end - 1],
                prev,
                carries,
                complement_b,
            );
            continue;
        }
        let mut carries = chain(c, &a[start..end], &b[start..end], prev, complement_b);
        if end == n {
            let last = carries.last().unwrap();
            match endpoint {
                Endpoint::Xor(q) => c.cx(last, q),
                Endpoint::Phase => c.z(last),
            }
            clear_chain(
                c,
                &a[start..end],
                &b[start..end],
                prev,
                carries,
                complement_b,
            );
        } else {
            let boundary = carries.pop().unwrap();
            clear_chain(
                c,
                &a[start..end - 1],
                &b[start..end - 1],
                prev,
                carries,
                complement_b,
            );
            boundaries.push(boundary);
            boundary_ranges.push((start, end));
        }
    }
    while let Some(boundary) = boundaries.pop() {
        let (start, end) = boundary_ranges.pop().unwrap();
        let prev = boundaries.last().map_or(initial, Carry::Wire);
        let m = c.alloc_bit();
        c.hmr(&boundary, m);
        // The measured slot is already clean and can join the replay pool.
        c.zero_and_free(boundary);
        let replay = |c: &mut Circuit| {
            let carries = chain(
                c,
                &a[start..end - 1],
                &b[start..end - 1],
                prev,
                complement_b,
            );
            // Only the prefix carries need replay: the final majority is
            // itself a Clifford phase oracle on the original last input pair.
            let phase = |c: &mut Circuit| {
                phase_maj(
                    c,
                    a[end - 1],
                    b[end - 1],
                    carries.last().map_or(prev, Carry::Wire),
                    complement_b,
                )
            };
            if conditional_replay {
                phase(c);
            } else {
                c.with_condition(m, phase);
            }
            clear_chain(
                c,
                &a[start..end - 1],
                &b[start..end - 1],
                prev,
                carries,
                complement_b,
            );
        };
        if conditional_replay {
            c.with_condition(m, replay);
        } else {
            replay(c);
        }
        c.free_bit(m);
    }
    c.pop_section(&section);
}

pub(crate) fn try_compare(c: &mut Circuit, v: &[&QReg], u: &[&QReg], out: &QReg) -> bool {
    let Some(k) = configured_chunk(c, v.len()) else {
        return false;
    };
    validate(u, v, Some(out));
    emit(c, u, v, false, true, Endpoint::Xor(out), k, true);
    true
}

pub(crate) fn try_clear_compare(c: &mut Circuit, v: &[&QReg], u: &[&QReg], out: &QReg) -> bool {
    let Some(k) = configured_chunk(c, v.len()) else {
        return false;
    };
    validate(u, v, Some(out));
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.with_condition(m, |c| emit(c, u, v, false, true, Endpoint::Phase, k, true));
    c.free_bit(m);
    true
}

#[path = "chunked_compare_selftest.rs"]
mod selftest;
pub(crate) use selftest::run as selftest;
