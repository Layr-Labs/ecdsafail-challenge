//! Emitted resource ledger with persistent beta, cached-position endpoints,
//! and the validated uncached framed helper as its reference.
use super::*;
use crate::circuit::OperationType;

fn emit(i: usize, cached: bool, inverse: bool, kind: &str) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    let (wa, wb, wca, wcb, _) = reg_widths(i);
    let n = trailmix_ab_width(wa.max(wb));
    let m = trailmix_cacb_width(wca.max(wcb));
    let mut c = Circuit::new();
    let _passenger = c.alloc_qreg_bits("cache.ledger.external", 256);
    let _sign = c.alloc_qreg("cache.ledger.sign");
    let carry = c.alloc_qreg("cache.ledger.carry");
    let mut a = c.alloc_qreg_bits("cache.ledger.A", n);
    let mut b = c.alloc_qreg_bits("cache.ledger.B", n);
    let ca = c.alloc_qreg_bits("cache.ledger.ca", m);
    let cb = c.alloc_qreg_bits("cache.ledger.cb", m);
    let q = c.alloc_qreg_bits("cache.ledger.q", 32);
    let counter = c.alloc_qreg_bits("cache.ledger.counter", 8);
    let parity = c.alloc_qreg("cache.ledger.parity");
    let srot = c.alloc_qreg_bits("cache.ledger.srot", 5);
    let offset = c.alloc_qreg("cache.ledger.offset");
    let phi = c.alloc_qreg_bits("cache.ledger.phi", 5);
    let role = c.alloc_qreg("cache.ledger.R");
    let mut cache = None;
    if kind == "step" {
        if cached {
            cache = Some(Cache::placeholder(&mut c, if inverse { i + 1 } else { i }));
        }
        if let Some(p) = cache.as_mut() {
            step_cached(
                &mut c,
                &mut a,
                &mut b,
                &ca,
                &cb,
                &q,
                &counter,
                &parity,
                &srot,
                &offset,
                Some(&carry),
                &phi,
                &role,
                p,
                i,
                inverse,
            );
        } else {
            d_alignment_iteration::step(
                &mut c,
                &mut a,
                &mut b,
                &ca,
                &cb,
                &q,
                &counter,
                &parity,
                &srot,
                &offset,
                Some(&carry),
                &phi,
                &role,
                i,
                inverse,
            );
        }
    } else if kind == "cut" {
        if inverse {
            if cached {
                cache = Some(Cache::begin_raw(&mut c, &a, &b, MIDQ_PZ_CUT, false));
            }
            d_alignment_iteration::enter(&mut c, &b, &ca, &cb, &q, &phi, &role);
        } else {
            if cached {
                cache = Some(Cache::placeholder(&mut c, MIDQ_PZ_CUT));
            }
            d_alignment_iteration::exit(&mut c, &b, &ca, &cb, &q, &phi, &role);
            for bit in phi {
                c.zero_and_free(bit);
            }
            c.zero_and_free(role);
            if let Some(p) = cache.take() {
                p.close_raw(&mut c, &a, &b, false);
            }
        }
    } else if cached {
        assert_eq!(i, 0);
        if kind == "initial" {
            cache = Some(Cache::begin_raw(&mut c, &a, &b, 0, true));
        } else {
            assert_eq!(kind, "final");
            Cache::placeholder(&mut c, 0).close_raw(&mut c, &a, &b, true);
        }
    }
    c.flush_pending_frees();
    let raw =
        c.b.ops
            .iter()
            .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
            .count();
    let expected = d_alignment_ledger::expectations(&c.b.ops);
    let error = expected
        .as_ref()
        .err()
        .map_or("null".to_string(), |e| format!("{e:?}"));
    let expected = expected.map_or("null".into(), |v| format!("{}", v.iter().sum::<f64>()));
    let variant = if cached { "cached" } else { "uncached" };
    let direction = if inverse { "inverse" } else { "forward" };
    println!("D_POSITION_CACHE_LEDGER {{\"step\":{i},\"kind\":\"{kind}\",\"variant\":\"{variant}\",\"direction\":\"{direction}\",\"AB\":{n},\"cofactor\":{m},\"q\":32,\"passenger\":256,\"floor\":{},\"next_floor\":{},\"peak\":{},\"output_floor\":{},\"raw_T\":{raw},\"unoptimized_expected_T\":{expected},\"expectation_error\":{error}}}",floor(i),floor(i+1),c.b.peak_qubits,c.b.active_qubits);
    // Keep the supplied/produced cache data live through the resource snapshot.
    let _ = cache;
}

pub(super) fn run() {
    assert_eq!(qretain::fixed_width(), Some(32));
    assert_eq!(env_usize("HYBRID_QCAP", 0), 1100);
    assert_eq!(
        std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref(),
        Some("1")
    );
    std::env::set_var("POINT_ADD_COUNT_ONLY", "0");
    let selected = std::env::var("MIDQ_D_POSITION_CACHE_LEDGER_STEPS").ok();
    let steps: Vec<usize> = selected.map_or_else(
        || (0..MIDQ_PZ_CUT).collect(),
        |s| s.split(',').map(|v| v.parse().unwrap()).collect(),
    );
    for i in steps {
        assert!(i < MIDQ_PZ_CUT);
        for inverse in [false, true] {
            for cached in [false, true] {
                emit(i, cached, inverse, "step");
            }
        }
    }
    for cached in [false, true] {
        for inverse in [false, true] {
            emit(MIDQ_PZ_CUT - 1, cached, inverse, "cut");
        }
        emit(0, cached, false, "initial");
        emit(0, cached, true, "final");
    }
    eprintln!("D_POSITION_CACHE_LEDGER COMPLETE persistent_beta_during_arithmetic=true initial_final_queries_charged=true expected_before_compiler=true production_driver=false");
}
