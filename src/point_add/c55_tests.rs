//! Construction-only census of the pinned schedule with the ninth pool wire withheld.
use super::builder::B;
use super::frogdrop_col::{self, ColScr, Fd, C55_STAGE};
use super::frogdrop_sched::{from_text};
use super::pointadd_frogdrop::{self, CNTB, KP, N, NQ, QB, SW, TAIL, SCHED_FROGDROP};
use super::payload::NP;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn panic_text(e: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = e.downcast_ref::<String>() { return s.clone(); }
    if let Some(s) = e.downcast_ref::<&str>() { return s.to_string(); }
    "non-string panic".to_string()
}

#[test]
#[ignore = "C55 construction-only census; run one explicit filter"]
fn c55_k3_pool8_census() {
    super::bake_knobs();
    assert!(frogdrop_col::c55_pool8() || std::env::var_os("C55_K3_BASELINE").is_some());
    let (cols, b0, last) = pointadd_frogdrop::col_pars(&from_text(SCHED_FROGDROP));
    std::panic::set_hook(Box::new(|info| {
        if let Some(loc) = info.location() { eprintln!("C55_K3_AT {}:{}", loc.file(), loc.line()); }
        if std::env::var_os("C55_K3_TRACE").is_some() {
            eprintln!("C55_K3_BACKTRACE {}", std::backtrace::Backtrace::force_capture());
        }
    }));
    let mut failures = 0usize;
    for (idx, cp) in cols.iter().enumerate() {
        if let Some(only) = std::env::var("C55_K3_COL").ok().and_then(|v| v.parse::<usize>().ok()) {
            if idx != only { continue; }
        }
        for payload in [false, true] {
            if let Ok(want) = std::env::var("C55_K3_PAYLOAD") {
                if payload != (want == "1") { continue; }
            }
            C55_STAGE.with(|s| s.set(0));
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                let mut b = B::new();
                let fd_ring = b.alloc_n(N);
                let fd_q = b.alloc_n(NQ);
                let fd_cnt = fd_q[NQ-CNTB..].to_vec();
                let mut fd = Fd { ring: fd_ring, q: fd_q, sy: b.alloc_n(SW), sx: b.alloc_n(SW),
                                  ph: b.alloc(), cnt: fd_cnt };
                let pool = b.alloc_n(frogdrop_col::pool_size(KP, QB, SW));
                let p = b.alloc_n(NP);
                let dirty = p.clone();
                let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, KP, QB, TAIL, cp.sz.1 > 255);
                let pl = if payload { Some(pointadd_frogdrop::pl_col(&p, &fd, &pool)) } else { None };
                frogdrop_col::column_pl(&mut b, &mut fd, cp, &sc, pl.as_ref());
            }));
            if let Err(e) = outcome {
                failures += 1;
                let stage = C55_STAGE.with(|s| s.get());
                let msg = panic_text(e);
                eprintln!("C55_K3_FAIL col={} kind=HR:{}|HT:{}|SW:{} session=all stage={} payload={} lanes={} detail={}",
                          idx, cp.hr, cp.ht, cp.sw, stage, payload, frogdrop_col::pool_size(KP, QB, SW), msg);
            }
        }
        if idx % 20 == 19 { eprintln!("C55_K3_PROGRESS columns={} failures={}", idx+1, failures); }
    }
    eprintln!("C55_K3_SUMMARY columns={} windows={} failures={} b0={} last={}",
              cols.len(), cols.len()*2, failures, b0.is_some(), last.nomap);
}
