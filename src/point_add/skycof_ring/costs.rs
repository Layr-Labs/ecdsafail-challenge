//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=costs`): expected Toffoli per forward tick of the public
//! walk (k2 decoder) and of the ring walk, each at its own source cap (overrides: `SKYCOF_COST_PUBCAP`,
//! `SKYCOF_CAP` for the ring), with a 256-wire passenger. Prints per-tick rows and cumulative tails.
use super::selftest::expected_ccx;
use crate::point_add::builder::Builder;
use crate::point_add::N;

pub fn run() {
    // public walk (k2) per tick, via the walk's snapshot recorder
    let pp = crate::point_add::skycof::pointadd::params();
    let penv = crate::point_add::skycof::pointadd::envelope();
    let mut wp = pp.walk;
    if let Some(v) = crate::point_add::skycof::pointadd::knob("SKYCOF_COST_PUBCAP") {
        wp.cap = v.parse().unwrap();
    }
    crate::point_add::skycof::walk::SNAPS.with(|s| *s.borrow_mut() = Some(Vec::new()));
    let mut b = Builder::new();
    let d = b.alloc_qubits(N);
    let _pass = b.alloc_qubits(N);
    let _pk = crate::point_add::skycof::walk::forward(&mut b, &wp, penv, &d);
    let tail = b.take_ops();
    let snaps = crate::point_add::skycof::walk::SNAPS.with(|s| s.borrow_mut().take().unwrap());
    let mut pubt = vec![0f64; wp.r];
    for (tag, ops, _) in &snaps {
        if let Some(t) = tag.strip_prefix('F') {
            let t: usize = t.parse().unwrap();
            pubt[t] = expected_ccx(ops);
        }
    }
    let pub_tail_extra = expected_ccx(&tail);
    eprintln!("COSTS public cap={} peak={} total fwd={:.0} (+ final disposal {:.0})", wp.cap, b.peak_total(), pubt.iter().sum::<f64>(), pub_tail_extra);
    // ring walk per tick
    let renv = super::pointadd::envelope().clone();
    let mut c = Builder::new();
    let d = c.alloc_qubits(renv.n - 1);
    let _pass = c.alloc_qubits(N);
    let mut marks: Vec<usize> = Vec::new();
    let _pk = super::rwalk::forward_hooked(&mut c, &renv, &d, &mut |cb, _t, _r, _h, _o, _s| marks.push(cb.op_count()));
    let ops = c.take_ops();
    let mut ringt = vec![0f64; renv.r];
    let mut prev = 0usize;
    for (t, &m) in marks.iter().enumerate() {
        ringt[t] = expected_ccx(&ops[prev..m]);
        prev = m;
    }
    eprintln!("COSTS ring cap={:?} peak={} total fwd={:.0}", renv.cap, c.peak_total(), ringt.iter().sum::<f64>());
    for t in (0..renv.r).step_by(10) {
        let e = (t + 10).min(renv.r);
        let ps: f64 = pubt[t..e.min(pubt.len())].iter().sum::<f64>() / (e - t) as f64;
        let rs: f64 = ringt[t..e].iter().sum::<f64>() / (e - t) as f64;
        eprintln!("COSTS ticks {t:3}..{e:3}: public {ps:7.0}  ring {rs:7.0} per tick");
    }
    for t1 in [180usize, 200, 220, 240, 260, 280, 300] {
        let p: f64 = pubt[..t1].iter().sum();
        let r: f64 = ringt[t1..].iter().sum();
        eprintln!("COSTS hybrid T1={t1}: public[0,{t1}) {p:.0} + ring[{t1},{}) {r:.0} = {:.0} per traversal", renv.r, p + r);
    }
}
