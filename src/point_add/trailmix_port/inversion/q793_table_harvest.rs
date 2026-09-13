//! W5 phase-1 diagnostic: harvest every dirty-table truth function that passes
//! through `metadata_muxlease::swap_terms` during a source-default Q793 build.
//! Pure observation: with `LOWQ_Q793_TABLE_HARVEST` unset the hook is a single
//! env-check and the emitted op stream is bit-identical to the default build.
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("LOWQ_Q793_TABLE_HARVEST").ok().as_deref() == Some("1"))
}

/// The tree's own emitter cost model, mirrored from
/// `metadata_muxlease::swap_terms::cost` and `arith::mcx::mcx_dirty_ladder`:
/// k positive controls cost 0 (k<=1, X/CX) / 1 (k=2) / 4k-8 (k>=3) Toffoli.
/// `truth_swap` adds exactly one external control (`left`) to every monomial,
/// so a monomial of popcount p is scored at k = p + 1, matching `cost()`.
fn mcx_t(k: usize) -> usize {
    match k {
        0 | 1 => 0,
        2 => 1,
        _ => 4 * k - 8,
    }
}

#[derive(Default)]
struct Entry {
    width: usize,
    polarity: usize,
    terms: Vec<usize>,
    unit_t: usize,
    unit_ops: usize,
    calls: u64,
    total_t: u64,
    sites: Vec<(u64, u64)>,
}

struct Registry {
    map: HashMap<(usize, Vec<bool>), Entry>,
    site_names: HashMap<u64, String>,
    order: Vec<(usize, Vec<bool>)>,
}

fn registry() -> &'static Mutex<Registry> {
    static REG: OnceLock<Mutex<Registry>> = OnceLock::new();
    REG.get_or_init(|| {
        Mutex::new(Registry {
            map: HashMap::new(),
            site_names: HashMap::new(),
            order: Vec::new(),
        })
    })
}

fn fnv64(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Observation-only hook called from `metadata_muxlease::swap_terms` after the
/// (polarity, terms) selection. Never called unless `enabled()` was true, so
/// the default build pays nothing and emits identical ops.
pub fn record(truth: &[bool], width: usize, polarity: usize, terms: &[usize]) {
    debug_assert!(enabled());
    let unit_t: usize = terms.iter().map(|&m| mcx_t(m.count_ones() as usize + 1)).sum();
    let unit_ops: usize = 2 * polarity.count_ones() as usize
        + 2
        + terms
            .iter()
            .map(|&m| mcx_t(m.count_ones() as usize + 1).max(1))
            .sum::<usize>();
    let site = fnv64(std::backtrace::Backtrace::force_capture().to_string().as_bytes());
    let key = (width, truth.to_vec());
    let mut reg = registry().lock().unwrap();
    if !reg.map.contains_key(&key) {
        reg.order.push(key.clone());
    }
    let entry = reg.map.entry(key).or_insert_with(|| Entry {
        width,
        polarity,
        terms: terms.to_vec(),
        ..Entry::default()
    });
    entry.unit_t = unit_t;
    entry.unit_ops = unit_ops;
    entry.polarity = polarity;
    entry.calls += 1;
    entry.total_t += unit_t as u64;
    match entry.sites.iter_mut().find(|(h, _)| *h == site) {
        Some((_, n)) => *n += 1,
        None => {
            entry.sites.push((site, 1));
            if !reg.site_names.contains_key(&site) {
                let raw = std::backtrace::Backtrace::force_capture().to_string();
                let frames: Vec<&str> = raw
                    .lines()
                    .filter(|l| l.contains("trailmix_port"))
                    .take(4)
                    .collect();
                reg.site_names.insert(site, frames.join(" | "));
            }
        }
    }
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Regenerate the source-default Q793 stream count-only and dump the harvest.
pub fn run() {
    assert!(
        super::q793_lifecycle_r03::candidate_configuration(),
        "table-harvest requires source-default Q793 configuration"
    );
    std::env::set_var("LOWQ_Q793_TABLE_HARVEST", "1");
    assert!(enabled());
    std::env::set_var("POINT_ADD_COUNT_ONLY", "1");
    let b = super::super::build_builder();
    assert!(b.count_only && b.ops.is_empty());
    let ops = b.current_ops_len();
    let structural_t =
        b.counted_kind_ops[crate::circuit::OperationType::CCX as usize]
            + b.counted_kind_ops[crate::circuit::OperationType::CCZ as usize];
    let reg = registry().lock().unwrap();
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("research/w5");
    std::fs::create_dir_all(&dir).expect("create research/w5");
    let mut functions = 0usize;
    let mut configs = 0usize;
    let mut calls_total = 0u64;
    let mut in_scope_t = 0u64;
    let mut by_width: HashMap<usize, (usize, u64)> = HashMap::new();
    {
        let mut out = String::new();
        for (id, key) in reg.order.iter().enumerate() {
            let e = &reg.map[key];
            let truth_bits: String = key
                .1
                .iter()
                .map(|&v| if v { '1' } else { '0' })
                .collect();
            let terms: String = e
                .terms
                .iter()
                .map(|m| m.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let sites: String = e
                .sites
                .iter()
                .map(|(h, n)| format!("{{\"h\":\"{h:016x}\",\"calls\":{n}}}"))
                .collect::<Vec<_>>()
                .join(",");
            out.push_str(&format!(
                "{{\"id\":{id},\"width\":{},\"truth\":\"{truth_bits}\",\"polarity\":{},\"terms\":[{}],\"unit_t\":{},\"unit_ops\":{},\"calls\":{},\"total_t\":{},\"sites\":[{}]}}\n",
                e.width, e.polarity, terms, e.unit_t, e.unit_ops, e.calls, e.total_t, sites
            ));
            functions += 1;
            if (4..=6).contains(&e.width) {
                configs += 1;
                in_scope_t += e.total_t;
            }
            calls_total += e.calls;
            let w = by_width.entry(e.width).or_default();
            w.0 += 1;
            w.1 += e.total_t;
        }
        std::fs::write(dir.join("table_harvest.jsonl"), out).expect("write table_harvest.jsonl");
        let mut sites_out = String::new();
        for (h, name) in &reg.site_names {
            sites_out.push_str(&format!("{{\"h\":\"{h:016x}\",\"frames\":\"{}\"}}\n", json_escape(name)));
        }
        std::fs::write(dir.join("table_harvest_sites.jsonl"), sites_out).expect("write sites");
    }
    let mut widths: Vec<String> = by_width
        .iter()
        .map(|(w, (f, t))| format!("w{w}:f={f},T={t}"))
        .collect();
    widths.sort();
    eprintln!(
        "TABLE_HARVEST_PASS functions={functions} configs_4_5_6={configs} calls={calls_total} in_scope_t={in_scope_t} ops={ops} structural_T={structural_t} peak={} widths=[{}]; diagnostic, no op change when unset",
        b.peak_qubits,
        widths.join(";")
    );
}
