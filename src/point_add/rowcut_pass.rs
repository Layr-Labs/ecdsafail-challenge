//! Row cuts: CCX rows whose AND equals a CNOT form of other wires (or a constant) on every state that reaches
//! them, applied by op index right after the K3a measurement absorption and before the cond pass. Switch
//! `SL_ROWCUT`:
//!   unset or "0"  the gate list byte for byte;
//!   "1"           every row in rowcut_data.txt;
//!   "3,7,12"      only the rows with those ids.
//! `SL_ROWCUT_FAULT=id` (diagnostic only): that row is applied with its constant flipped (a deliberate fault).
//! Row line: `id site c1 c2 t cc cst supp` with cc the CCX's own c_condition id or `-`, cst 0|1, supp `w1,w2,..` or `-`.
//! The CCX at `site` (asserted: kind, target, unordered controls, c_condition) is replaced by CX(w -> t) for each w in
//! supp and an X on t if cst, each with the CCX's own c_condition (push-region conditions apply as before). A row with
//! no support and cst 0 deletes the CCX. Rows are applied in descending site order, so every index refers to the
//! unedited stream. No qubit, measurement or reset is added or removed.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT};

struct Row { id: u64, site: usize, c1: u64, c2: u64, t: u64, cc: Option<u64>, cst: bool, supp: Vec<u64> }

pub fn run(mut ops: Vec<Op>) -> Vec<Op> {
    let sw = std::env::var("SL_ROWCUT").unwrap_or_default();
    if sw.is_empty() || sw == "0" { return ops; }
    let fault: Option<u64> = std::env::var("SL_ROWCUT_FAULT").ok().and_then(|v| v.parse().ok());
    let pick: Option<Vec<u64>> = if sw == "1" { None } else {
        Some(sw.split(',').map(|x| x.trim().parse().expect("SL_ROWCUT: row id")).collect())
    };
    let text = include_str!("rowcut_data.txt");
    let mut rows: Vec<Row> = Vec::new();
    for l in text.lines() {
        let l = l.trim();
        if l.is_empty() || l.starts_with('#') { continue; }
        let f: Vec<&str> = l.split_whitespace().collect();
        assert!(f.len() == 8, "rowcut: bad line {l:?}");
        let r = Row {
            id: f[0].parse().unwrap(), site: f[1].parse().unwrap(), c1: f[2].parse().unwrap(), c2: f[3].parse().unwrap(),
            t: f[4].parse().unwrap(), cc: if f[5] == "-" { None } else { Some(f[5].parse().unwrap()) },
            cst: f[6] == "1", supp: if f[7] == "-" { vec![] } else { f[7].split(',').map(|x| x.parse().unwrap()).collect() },
        };
        if pick.as_ref().map_or(true, |p| p.contains(&r.id)) { rows.push(r); }
    }
    if let Some(p) = &pick { assert!(rows.len() == p.len(), "rowcut: {} of {} picked ids found", rows.len(), p.len()); }
    rows.sort_by(|a, b| b.site.cmp(&a.site));
    for w in rows.windows(2) { assert!(w[0].site != w[1].site, "rowcut: two rows at site {}", w[0].site); }
    let (mut n_drop, mut n_cx) = (0usize, 0usize);
    for r in &rows {
        let o = ops[r.site];
        let cc = if o.c_condition == NO_BIT { None } else { Some(o.c_condition.0) };
        assert!(o.kind == K::CCX && o.q_target.0 == r.t && cc == r.cc
            && ((o.q_control1.0 == r.c1 && o.q_control2.0 == r.c2) || (o.q_control1.0 == r.c2 && o.q_control2.0 == r.c1)),
            "rowcut: row {} does not match the CCX at {}", r.id, r.site);
        let cst = r.cst ^ (fault == Some(r.id));
        let mut rep: Vec<Op> = Vec::new();
        for &w in &r.supp {
            assert!(w != r.t);
            let mut x = Op::empty(); x.kind = K::CX; x.q_control1 = QubitId(w); x.q_target = QubitId(r.t);
            x.c_condition = o.c_condition; x.validate(); rep.push(x);
        }
        if cst {
            let mut x = Op::empty(); x.kind = K::X; x.q_target = QubitId(r.t); x.c_condition = o.c_condition;
            x.validate(); rep.push(x);
        }
        if rep.is_empty() { n_drop += 1; } else { n_cx += 1; }
        ops.splice(r.site..r.site + 1, rep);
    }
    let _ = BitId(0);
    eprintln!("SL_ROWCUT rows={} deleted={} as_cx={} fault={:?}", rows.len(), n_drop, n_cx, fault);
    ops
}
