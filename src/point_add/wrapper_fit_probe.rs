//! Isolated 999Q fit probe for the non-GCD point-addition wrapper.
//!
//! This does not stand in for either GCD traversal.  It emits the real
//! coordinate, square, and field-product implementations used by SKY-COF at
//! the liveness contracts presented by a terminal GCD endpoint.  The output is
//! therefore a source-level integration receipt for the wrapper, not a point
//! addition candidate and never an `ops.bin` submission.

use super::builder::Builder;
use super::classical::{coord_add3x, coord_rsub, coord_sub};
use super::skycof::pointadd;
use super::skycof_mm as mm;
use super::square::sub_square;
use super::N;

#[derive(Clone, Copy, Debug)]
struct Price {
    peak: u32,
    native: usize,
    expected: f64,
}

fn totals(b: &Builder) -> (usize, f64) {
    b.report_totals()
        .expect("wrapper probe requires HEO_PHASE_REPORT")
}

fn delta(b: &Builder, before: (usize, f64)) -> Price {
    let after = totals(b);
    Price {
        peak: b.peak_total(),
        native: after.0 - before.0,
        expected: after.1 - before.1,
    }
}

/// Price one product and its independently emitted inverse in a single
/// allocator.  `receipt` remains arbitrary and live throughout.  When
/// `signed` is true, the product sign is a distinct live endpoint bit, matching
/// the conservative compact-endpoint contract used in the integration ledger.
fn product_pair(cap: usize, receipt: usize, signed: bool, k: usize) -> (Price, Price) {
    let mut b = Builder::new();
    let a = b.alloc_qubits(N);
    let factor = b.alloc_qubits(N);
    let _receipt = b.alloc_qubits(receipt);
    let sign = signed.then(|| b.alloc_qubit());
    let room = cap
        .checked_sub(3 * N + receipt + usize::from(signed))
        .expect("product liveness exceeds cap");
    assert!(room >= 8);
    let guard = pointadd::knob("SKYCOF_WRAPPER_GUARD")
        .map(|v| v.parse().expect("SKYCOF_WRAPPER_GUARD integer"))
        .unwrap_or(25usize);
    let cmpw = pointadd::knob("SKYCOF_WRAPPER_CMPW")
        .map(|v| v.parse().expect("SKYCOF_WRAPPER_CMPW integer"))
        .unwrap_or(24usize);
    let cfg = mm::Cfg::windowed(mm::Field::secp(), guard, cmpw, room);

    b.set_phase("wrapper_product_fwd");
    let before = totals(&b);
    let out = mm::mul_fwd(&mut b, mm::Field::secp(), cfg, &a, &factor, k, sign);
    let fwd = delta(&b, before);

    b.set_phase("wrapper_product_inv");
    let before = totals(&b);
    let out = mm::mul_inv(&mut b, mm::Field::secp(), cfg, &a, &factor, k, sign, out);
    let inv = delta(&b, before);
    b.free_vec(&out);
    assert_eq!(
        b.active_qubits() as usize,
        2 * N + receipt + usize::from(signed)
    );
    (fwd, inv)
}

fn wrapper_shell() -> (Price, Price, [Price; 5]) {
    let mut b = Builder::new();
    let x = b.alloc_qubits(N);
    let y = b.alloc_qubits(N);
    let ox = b.alloc_bits(N);
    let oy = b.alloc_bits(N);
    let mut coords = [Price {
        peak: 0,
        native: 0,
        expected: 0.0,
    }; 5];

    b.set_phase("wrapper_coord_x_sub");
    let t = totals(&b);
    coord_sub(&mut b, &x, &ox);
    coords[0] = delta(&b, t);

    b.set_phase("wrapper_coord_y_sub");
    let t = totals(&b);
    coord_sub(&mut b, &y, &oy);
    coords[1] = delta(&b, t);

    b.set_phase("wrapper_coord_add3x");
    let t = totals(&b);
    coord_add3x(&mut b, &x, &ox);
    coords[2] = delta(&b, t);

    b.set_phase("wrapper_square");
    let t = totals(&b);
    sub_square(&mut b, &x, &y);
    let square = delta(&b, t);

    b.set_phase("wrapper_coord_y_sub_final");
    let t = totals(&b);
    coord_sub(&mut b, &y, &oy);
    coords[3] = delta(&b, t);

    b.set_phase("wrapper_coord_rsub_final");
    let t = totals(&b);
    coord_rsub(&mut b, &x, &ox);
    coords[4] = delta(&b, t);

    let all = totals(&b);
    let total = Price {
        peak: b.peak_total(),
        native: all.0,
        expected: all.1,
    };
    (total, square, coords)
}

pub fn run() {
    let cap = pointadd::params().walk.cap;
    assert!(
        cap <= 999,
        "wrapper fit probe must run at cap <= 999 (got {cap})"
    );
    let scale = pointadd::params().walk.r;
    let receipt = pointadd::knob("SKYCOF_WRAPPER_RECEIPT")
        .map(|v| v.parse().expect("SKYCOF_WRAPPER_RECEIPT integer"))
        // The directly integrable SKY-COF endpoint retains H[194] and the
        // seven-bit park odometer.  A transcript-free endpoint can override
        // this to 20 and recover the larger product carry room.
        .unwrap_or(201usize);
    let (shell, square, coords) = wrapper_shell();
    let (scaled_fwd, scaled_inv) = product_pair(cap, receipt, true, scale);
    let (plain_fwd, plain_inv) = product_pair(cap, 0, false, 0);

    // The point-addition wrapper has two scaled forwards and one scaled
    // inverse, plus two unscaled forwards and one unscaled inverse.
    let products_expected = 2.0 * scaled_fwd.expected
        + scaled_inv.expected
        + 2.0 * plain_fwd.expected
        + plain_inv.expected;
    let products_native =
        2 * scaled_fwd.native + scaled_inv.native + 2 * plain_fwd.native + plain_inv.native;
    let wrapper_expected = products_expected + shell.expected;
    let wrapper_native = products_native + shell.native;
    let peak = shell
        .peak
        .max(scaled_fwd.peak)
        .max(scaled_inv.peak)
        .max(plain_fwd.peak)
        .max(plain_inv.peak);

    eprintln!(
        "WRAPPER_FIT_COMPONENT shell_Q={} shell_native={} shell_expected={:.3} square_Q={} square_native={} square_expected={:.3}",
        shell.peak, shell.native, shell.expected, square.peak, square.native, square.expected
    );
    for (i, p) in coords.iter().enumerate() {
        eprintln!(
            "WRAPPER_FIT_COORD index={} Q={} native={} expected={:.3}",
            i + 1,
            p.peak,
            p.native,
            p.expected
        );
    }
    eprintln!(
        "WRAPPER_FIT_PRODUCT kind=scaled scale={} receipt={} sign=1 room={} Q={} fwd_native={} fwd_expected={:.3} inv_native={} inv_expected={:.3}",
        scale,
        receipt,
        cap - 3 * N - receipt - 1,
        scaled_fwd.peak.max(scaled_inv.peak),
        scaled_fwd.native,
        scaled_fwd.expected,
        scaled_inv.native,
        scaled_inv.expected
    );
    eprintln!(
        "WRAPPER_FIT_PRODUCT kind=plain scale=0 receipt=0 sign=0 room={} Q={} fwd_native={} fwd_expected={:.3} inv_native={} inv_expected={:.3}",
        cap - 3 * N,
        plain_fwd.peak.max(plain_inv.peak),
        plain_fwd.native,
        plain_fwd.expected,
        plain_inv.native,
        plain_inv.expected
    );
    eprintln!(
        "WRAPPER_FIT_PASS cap={} Q={} scale={} receipt={} products_native={} products_expected={:.3} shell_native={} shell_expected={:.3} nongcd_native={} nongcd_expected={:.3} gcd_included=false point_add_complete=false",
        cap,
        peak,
        scale,
        receipt,
        products_native,
        products_expected,
        shell.native,
        shell.expected,
        wrapper_native,
        wrapper_expected
    );
}
