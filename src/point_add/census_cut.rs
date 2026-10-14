//! Census cuts: Toffolis whose replaced control pattern occurred on no correct shot of a random-input census, applied by op index on
//! the stream after the row cuts. Row line: `site kind c2 c1 t cc action`, kind ccx|ccz, cc the op's c_condition id or
//! `-`, action `del` (the AND never fires), `cx:w` (the AND equals control w) or `cz:a,b` (the CCZ's three-way AND
//! equals the AND of a and b). The op at `site` is asserted (kind, wires, condition); replacements keep its condition.
//! Block line: `B push pop bit z neg`: the PUSH(bit) .. POP block at [push, pop] restores every wire it touches and
//! flips the phase by the parity of the wires `z` (`w1,w2,..` or `-`) plus `neg` (0|1); it becomes Z gates (and a Neg)
//! under `bit`. Edits apply in descending order and may not overlap, so every index refers to the unedited stream.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

/// Expected executed Toffoli of a gate list: each CCX / CCZ weighted 2^-k for the k classical conditions it runs under.
pub fn static_t(ops: &[Op]) -> f64 {
    let (mut d, mut w) = (0i32, 0.0);
    for o in ops {
        match o.kind {
            K::PushCondition => d += 1,
            K::PopCondition => d -= 1,
            K::CCX | K::CCZ => w += 0.5f64.powi(d + (o.c_condition != NO_BIT) as i32),
            _ => {}
        }
    }
    w
}

pub fn rows() -> Vec<(usize, Vec<&'static str>)> {
    include_str!("census_cut_data.txt").lines()
        .map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            let (n, at) = if f[0] == "B" { (6, 1) } else { (7, 0) };
            assert!(f.len() == n, "census_cut: bad line {l:?}");
            (f[at].parse().unwrap(), f)
        })
        .collect()
}

pub fn run(ops: Vec<Op>) -> Vec<Op> { run_rows(ops, rows()) }

pub fn run_rows(mut ops: Vec<Op>, mut rows: Vec<(usize, Vec<&str>)>) -> Vec<Op> {
    let w0 = static_t(&ops);
    rows.sort_by(|a, b| b.0.cmp(&a.0));
    let w = |s: &str| -> u64 { s.parse().unwrap() };
    let (mut n_del, mut n_red, mut n_blk) = (0usize, 0usize, 0usize);
    let mut floor = usize::MAX;
    for (site, f) in &rows {
        let mut x = Op::empty();
        if f[0] == "B" {
            let (push, pop, bit) = (*site, w(f[2]) as usize, w(f[3]));
            assert!(pop < floor, "census_cut: edits overlap at {push}");
            floor = push;
            assert!(ops[push].kind == K::PushCondition && ops[push].c_condition.0 == bit && ops[pop].kind == K::PopCondition,
                "census_cut: block at {push} does not match the stream");
            let mut d = 0i64;
            for o in &ops[push..=pop] { if o.kind == K::PushCondition { d += 1; } if o.kind == K::PopCondition { d -= 1; assert!(d > 0 || std::ptr::eq(o, &ops[pop]), "census_cut: block {push} closes early"); } }
            assert!(d == 0, "census_cut: block {push} unbalanced");
            x.c_condition = ops[push].c_condition;
            let mut rep = Vec::new();
            if f[4] != "-" { for z in f[4].split(',') { let mut y = x; y.kind = K::Z; y.q_target = QubitId(w(z)); y.validate(); rep.push(y); } }
            if f[5] == "1" { let mut y = x; y.kind = K::Neg; y.validate(); rep.push(y); }
            n_blk += 1;
            ops.splice(push..=pop, rep);
            continue;
        }
        assert!(*site < floor, "census_cut: edits overlap at {site}");
        floor = *site;
        let o = ops[*site];
        let kind = if f[1] == "ccx" { K::CCX } else { K::CCZ };
        let cc = if o.c_condition == NO_BIT { "-".to_string() } else { o.c_condition.0.to_string() };
        assert!(o.kind == kind && o.q_control2.0 == w(f[2]) && o.q_control1.0 == w(f[3]) && o.q_target.0 == w(f[4]) && cc == f[5],
            "census_cut: row at {site} does not match the stream");
        x.c_condition = o.c_condition;
        let rep = match f[6].split_once(':') {
            None if f[6] == "del" => { n_del += 1; vec![] }
            Some(("cx", a)) if kind == K::CCX => { x.kind = K::CX; x.q_control1 = QubitId(w(a)); x.q_target = o.q_target; vec![x] }
            Some(("cz", ab)) if kind == K::CCZ => {
                let (a, b) = ab.split_once(',').unwrap();
                x.kind = K::CZ; x.q_control1 = QubitId(w(a)); x.q_target = QubitId(w(b)); vec![x]
            }
            _ => panic!("census_cut: bad action {:?}", f[6]),
        };
        if !rep.is_empty() { n_red += 1; for r in &rep { r.validate(); } }
        ops.splice(*site..*site + 1, rep);
    }
    let w1 = static_t(&ops);
    eprintln!("CENSUS_CUT rows={} deleted={} reduced={} blocks={} static expected Toffoli {w0:.1} -> {w1:.1} ({:.1})", rows.len(), n_del, n_red, n_blk, w1 - w0);
    ops
}
