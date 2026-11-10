mod common;
mod sim;
mod stats;
mod decoder;
mod schedule;
mod opt;
use common::*;
use std::io::Read;

struct Target(Vec<u64>);
impl schedule::RecordTarget for Target {
    fn read_prior(&mut self, i: usize) -> [u16; 4] { let r = self.0[i]; [r as u16, (r >> 16) as u16, (r >> 32) as u16, (r >> 48) as u16] }
    fn append(&mut self, row: [u16; 4]) { self.0.push(rec(row[0], row[1] as usize, row[2] as usize, row[3] as usize)); }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let threads = std::env::var("QOPT_THREADS").ok().and_then(|x| x.parse().ok()).unwrap_or(44usize);
    match a.get(1).map(|s| s.as_str()) {
        // decode PLAN_RAW OUT.u16le  (decompressed gate stream on stdin)
        Some("decode") => {
            let mut plan = Vec::new(); std::fs::File::open(&a[2]).unwrap().read_to_end(&mut plan).unwrap();
            let mut out = Target(Vec::new());
            let n = schedule::expand(std::io::BufReader::with_capacity(1 << 24, std::io::stdin().lock()), &plan, &mut out).expect("decode");
            eprintln!("decoded {} ops", n);
            save_trace(&a[3], &out.0);
        }
        // stats TRACE SPANS|- INPUTS OUTDIR BATCHES
        Some("stats") => stats::run(&a[2], &a[3], &a[4], &a[5], a[6].parse().unwrap(), threads),
        // verify TRACE INPUTS BATCHES
        Some("verify") => {
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let p = stats::replay(&t, &lay, &shots, a[4].parse().unwrap(), threads, false);
            println!("ops {} qubits {} avg_toffoli {:.3} failing_shots {} of {} result {}", t.len(), lay.nq, p.tof_total as f64 / (p.batches * 64) as f64,
                p.bad_shots, p.batches * 64, p.fail.clone().unwrap_or_else(|| "PASS".into()));
            if p.fail.is_some() { std::process::exit(1); }
        }
        // dump TRACE FLAGS START END
        Some("dump") => {
            let t = load_trace(&a[2]); let flags = std::fs::read(&a[3]).unwrap();
            let (s, e): (usize, usize) = (a[4].parse().unwrap(), a[5].parse().unwrap());
            let mut j = t[..s].iter().filter(|&&r| kind(r) == K_CCX).count();
            for i in s..e.min(t.len()) {
                let r = t[i]; let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
                let f = |v: usize| if v == NONE { "-".to_string() } else { v.to_string() };
                match k {
                    K_CCX => { println!("{} CCX {} {} -> {}  [{:07b}]", i, x, y, z, flags[j]); j += 1; }
                    K_CX => println!("{} CX {} -> {} if {}", i, x, y, f(z)),
                    K_CZ => println!("{} CZ {} {} if {}", i, x, y, f(z)),
                    K_X => println!("{} X {} if {}", i, x, f(y)),
                    K_Z => println!("{} Z {} if {}", i, x, f(y)),
                    K_HMR => println!("{} HMR {} -> bit {}", i, x, y),
                    K_BINV => println!("{} BINV {} if {}", i, x, f(y)),
                    K_BST0 => println!("{} BST0 {} if {}", i, x, f(y)),
                    K_BST1 => println!("{} BST1 {} if {}", i, x, f(y)),
                    K_PUSH => println!("{} PUSH {}", i, x),
                    K_POP => println!("{} POP", i),
                    _ => println!("{} K{} {} {} {}", i, k, x, y, z),
                }
            }
        }
        // children TRACE ANALYSIS_DIR SPANS PARENT_ID : per-child summary (ops, ccx, never-fired, first-fire range)
        Some("children") => {
            let t = load_trace(&a[2]);
            let flags = std::fs::read(format!("{}/ccx_flags.bin", a[3])).unwrap();
            let fb = std::fs::read(format!("{}/ccx_first.bin", a[3])).unwrap();
            let first: Vec<u32> = fb.chunks_exact(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect();
            let mut pc: Vec<u32> = Vec::with_capacity(t.len() + 1); pc.push(0);
            let mut j = 0u32; for &r in t.iter() { if kind(r) == K_CCX { j += 1; } pc.push(j); }
            let parents: Vec<&str> = a[5].split(',').collect();
            let text = std::fs::read_to_string(&a[4]).unwrap();
            for line in text.lines() {
                let f: Vec<&str> = line.split('\t').collect();
                if f.len() < 6 || !(parents.contains(&f[1]) || parents.contains(&f[0])) { continue; }
                let (s, e): (usize, usize) = (f[2].parse().unwrap(), f[3].parse().unwrap());
                let (ja, jb) = (pc[s] as usize, pc[e] as usize);
                let never = (ja..jb).filter(|&i| flags[i] & 4 == 0).count();
                let late = (ja..jb).filter(|&i| first[i] != u32::MAX && first[i] >= 1000).count();
                let ctrl: std::collections::BTreeSet<usize> = (ja..jb).filter(|&i| flags[i] & 4 == 0).map(|_| 0).collect(); let _ = ctrl;
                println!("{}\t{}\t{}\t{}\tops={}\tccx={}\tnever={}\tfirst>=1000={}", f[0], f[1], f[4], f[2], e - s, jb - ja, never, late);
            }
        }
        // prune TRACE ANALYSIS_DIR|- LATE W OUT_PREFIX : roots (optional) + exact cancellation; writes mask, runs, pruned trace
        Some("prune") => {
            let t = load_trace(&a[2]); let n = t.len();
            let mut mask = opt::mask_new(n);
            if a[3] != "-" {
                let flags = std::fs::read(format!("{}/ccx_flags.bin", a[3])).unwrap();
                let fb = std::fs::read(format!("{}/ccx_first.bin", a[3])).unwrap();
                let first: Vec<u32> = fb.chunks_exact(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect();
                opt::roots(&t, &flags, &first, a[4].parse().unwrap(), a[5].parse().unwrap(), &mut mask);
            }
            if std::env::var("QOPT_MODE").ok().as_deref() == Some("2") { opt::cancel2(&t, &mut mask); } else { opt::cancel(&t, &mut mask); }
            let (mut dc, mut dall) = (0u64, 0u64);
            for i in 0..n { if opt::mget(&mask, i) { dall += 1; if kind(t[i]) == K_CCX { dc += 1; } } }
            eprintln!("deleted ops {} of {}; deleted Toffolis {}", dall, n, dc);
            opt::mask_save(&format!("{}.mask", a[6]), &mask);
            let runs = opt::encode(&mask, n);
            eprintln!("run-length mask: {} bytes", runs.len());
            save_bytes(&format!("{}.runs", a[6]), &runs);
            save_trace(&format!("{}.u16le", a[6]), &opt::apply(&t, &mask));
        }
        _ => { eprintln!("usage: qopt decode|stats|verify ..."); std::process::exit(2); }
    }
}
