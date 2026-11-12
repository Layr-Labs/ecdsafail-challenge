mod common;
mod sim;
mod stats;
mod decoder;
mod schedule;
mod opt;
mod gvn;
mod feat;
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
        Some("feat") => feat::run(&a[2], &a[3], &a[4], &a[5], a[6].parse().unwrap(), threads),
        // cmpc A.u16le B.u16le [BATCHES] : are two component bodies equal on random inputs (all wires, phase, measured bits)?
        Some("cmpc") => {
            let (x, y) = (load_trace(&a[2]), load_trace(&a[3]));
            let (lx, ly) = (layout(&x), layout(&y)); let (nq, nb) = (lx.nq.max(ly.nq), lx.nb.max(ly.nb));
            let batches: u64 = a.get(4).and_then(|v| v.parse().ok()).unwrap_or(64);
            let cnt = |t: &[u64]| t.iter().filter(|&&r| kind(r) == K_CCX).count();
            let mut bad = 0u64; let (mut ta, mut tb) = (0u64, 0u64);
            for bt in 0..batches {
                let mut s = 0x1234_5678_9ABC_DEF1u64 ^ (bt << 32);
                let mut rnd = || { s = s.wrapping_add(0x9E3779B97F4A7C15); let mut z = s; z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9); z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB); z ^ (z >> 31) };
                let mut p = sim::Sim::new(nq, nb, 77 + bt); let mut q = sim::Sim::new(nq, nb, 77 + bt);
                for i in 0..nq { let v = rnd(); p.q[i] = v; q.q[i] = v; }
                for i in 0..nb { let v = rnd(); p.b[i] = v; q.b[i] = v; }
                p.run(&x, None); q.run(&y, None);
                let mut d = p.phase ^ q.phase;
                for i in 0..nq { d |= p.q[i] ^ q.q[i]; }
                for i in 0..nb { d |= p.b[i] ^ q.b[i]; }
                bad += d.count_ones() as u64; ta += p.tof; tb += q.tof;
            }
            let n = (batches * 64) as f64;
            println!("A: ops {} ccx {} executed {:.3}   B: ops {} ccx {} executed {:.3}   differing shots {} of {}   {}", x.len(), cnt(&x), ta as f64 / n, y.len(), cnt(&y), tb as f64 / n,
                bad, batches * 64, if bad == 0 { "EQUAL on all sampled inputs" } else { "DIFFERENT" });
            if bad != 0 { std::process::exit(1); }
        }
        // show A.u16le : print a component as text
        Some("show") => { let t = load_trace(&a[2]); let f = |v: usize| if v == NONE { "-".to_string() } else { v.to_string() };
            for (i, &r) in t.iter().enumerate() { let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
                let nm = match k { K_CCX => "CCX", K_CX => "CX", K_CZ => "CZ", K_X => "X", K_Z => "Z", K_HMR => "HMR", K_PUSH => "PUSH", K_POP => "POP", K_BINV => "BINV", K_BST0 => "BST0", K_BST1 => "BST1", _ => "OTHER" };
                println!("{}\t{}\t{}\t{}\t{}", i, nm, f(x), f(y), f(z)); } }
        Some("stats") => stats::run(&a[2], &a[3], &a[4], &a[5], a[6].parse().unwrap(), threads),
        // verify TRACE INPUTS BATCHES
        // life TRACE INPUTS NBUCKETS h1,h2,..   helper lifetimes from one 64-shot replay
        Some("life") => {
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let nb: usize = a[4].parse().unwrap();
            let hs: Vec<usize> = a[5].split(',').map(|x| x.parse().unwrap()).collect();
            let mut hidx = vec![usize::MAX; lay.nq]; for (i, &h) in hs.iter().enumerate() { hidx[h] = i; }
            #[derive(Clone, Default)] struct Iv { start: usize, nw: u32, fk: u16, fa: usize, fb: usize, va: u32, vb: u32, uc: u32, ux: u32, same: bool }
            #[derive(Clone, Default)] struct Acc { n: u64, nw: u64, uc: u64, ux: u64, span: u64, maxspan: u64, wmax: u64 }
            let mut iv: Vec<Option<Iv>> = vec![None; hs.len()];
            let mut ver = vec![0u32; lay.nq]; let mut last = vec![0usize; lay.nq];
            let mut acc: std::collections::BTreeMap<(usize, usize, &'static str), Acc> = Default::default();
            let mut idle = vec![[0u64; 3]; hs.len()];
            let n = t.len();
            let mut sim = sim::Sim::new(lay.nq, lay.nb, 0xC0FFEE); sim.load(&lay, &shots, 0);
            sim.run_each(&t, |i, r, q| {
                let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
                let (tgt, c1, c2) = match k { K_CCX => (z, x, y), K_CX => (y, x, NONE), K_X => (x, NONE, NONE), K_HMR => (x, NONE, NONE), K_CZ => (NONE, x, y), K_Z => (NONE, x, NONE), _ => (NONE, NONE, NONE) };
                for c in [c1, c2] { if c != NONE { last[c] = i + 1; let hi = hidx[c]; if hi != usize::MAX { match iv[hi].as_mut() { Some(v) => { if k == K_CCX { v.uc += 1 } else { v.ux += 1 } } None => idle[hi][if k == K_CCX { 0 } else { 1 }] += 1 } } } }
                if tgt != NONE {
                    last[tgt] = i + 1;
                    let hi = hidx[tgt];
                    if hi != usize::MAX {
                        let zero = q[tgt] == 0;
                        if iv[hi].is_none() { if zero { idle[hi][2] += 1; } else { iv[hi] = Some(Iv { start: i, nw: 0, fk: k, fa: c1, fb: c2, va: if c1 != NONE { ver[c1] } else { 0 }, vb: if c2 != NONE { ver[c2] } else { 0 }, uc: 0, ux: 0, same: false }); } }
                        if let Some(v) = iv[hi].as_mut() {
                            v.nw += 1;
                            v.same = k == v.fk && ((c1 == v.fa && c2 == v.fb) || (c1 == v.fb && c2 == v.fa));
                            if zero {
                                let v = iv[hi].take().unwrap();
                                let unch = (v.fa == NONE || ver[v.fa] == v.va) && (v.fb == NONE || ver[v.fb] == v.vb);
                                let and = v.fk == K_CCX;
                                let class = if k == K_HMR { if v.nw == 2 { if and { if unch { "and..hmr" } else { "and..hmr(ctrl changed)" } } else { "cx/x..hmr" } } else if v.nw <= 8 { "3-8 writes..hmr" } else { "many writes..hmr" } }
                                    else if v.nw == 2 && v.same { if and { if unch { "and..and" } else { "and..and(ctrl changed)" } } else { "cx/x pair" } }
                                    else if v.nw <= 8 { "3-8 writes" } else { "many writes" };
                                let span = (i + 1 - v.start) as u64;
                                let e = acc.entry((v.start / (n / nb + 1), hs[hi], class)).or_default();
                                e.n += 1; e.nw += v.nw as u64; e.uc += v.uc as u64; e.ux += v.ux as u64; e.span += span; e.maxspan = e.maxspan.max(span);
                                if span < 100_000 { let w = last.iter().filter(|&&l| l > v.start).count() as u64; e.wmax = e.wmax.max(w); } else { e.wmax = e.wmax.max(9999); }
                            }
                        }
                    }
                    ver[tgt] = ver[tgt].wrapping_add(1);
                }
            });
            println!("bucket\thelper\tclass\tintervals\twrites\tuses_ccx\tuses_cx\tspan_ops\tmax_span\twires_max");
            for (k, e) in &acc { println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", k.0, k.1, k.2, e.n, e.nw, e.uc, e.ux, e.span, e.maxspan, e.wmax); }
            for (hi, h) in hs.iter().enumerate() { println!("# helper {} while zero: ccx-control {} cx/cz/z-control {} writes leaving it zero {}; open at end {}", h, idle[hi][0], idle[hi][1], idle[hi][2], iv[hi].is_some()); }
        }
        // occ TRACE INPUTS NBUCKETS h1,h2,..   how many of the given wires are non-zero (in any of 64 shots) at each op
        Some("occ") => {
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let nb: usize = a[4].parse().unwrap();
            let hs: Vec<usize> = a[5].split(',').map(|x| x.parse().unwrap()).collect();
            let n = t.len(); let w = hs.len() + 1;
            let mut ops = vec![0u64; nb * w]; let mut ccx = vec![0u64; nb * w];
            let mut sets: std::collections::HashMap<u32, (u64, u64)> = Default::default();
            let mut sim = sim::Sim::new(lay.nq, lay.nb, 0xC0FFEE); sim.load(&lay, &shots, 0);
            sim.run_each(&t, |i, r, q| {
                let mut c = 0usize; let mut mask = 0u32;
                for (j, &h) in hs.iter().enumerate() { if q[h] != 0 { c += 1; mask |= 1 << j; } }
                let b = i / (n / nb + 1);
                ops[b * w + c] += 1;
                let e = sets.entry(mask).or_default(); e.0 += 1;
                if kind(r) == K_CCX { ccx[b * w + c] += 1; e.1 += 1; }
            });
            println!("bucket\tkind\t{}", (0..w).map(|c| format!("occ{}", c)).collect::<Vec<_>>().join("\t"));
            for b in 0..nb { println!("{}\tops\t{}", b, (0..w).map(|c| ops[b * w + c].to_string()).collect::<Vec<_>>().join("\t")); println!("{}\tccx\t{}", b, (0..w).map(|c| ccx[b * w + c].to_string()).collect::<Vec<_>>().join("\t")); }
            let mut v: Vec<_> = sets.into_iter().collect(); v.sort_by_key(|e| std::cmp::Reverse(e.1 .0));
            for (mask, (o, c)) in v.iter().take(60) { println!("# set {} ops {} ccx {}", hs.iter().enumerate().filter(|(j, _)| mask >> j & 1 == 1).map(|(_, h)| h.to_string()).collect::<Vec<_>>().join(","), o, c); }
        }
        // ivl TRACE INPUTS h1,h2,.. OUT   every non-zero interval of the given wires (64-shot replay), with a flag saying whether
        // the value is recomputable at every use (all writers' controls unchanged since the write) = can be hosted on a dirty wire
        Some("ivl") => {
            use std::io::Write;
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let hs: Vec<usize> = a[4].split(',').map(|x| x.parse().unwrap()).collect();
            let mut out = std::io::BufWriter::new(std::fs::File::create(&a[5]).unwrap());
            let mut hidx = vec![usize::MAX; lay.nq]; for (i, &h) in hs.iter().enumerate() { hidx[h] = i; }
            #[derive(Clone, Default)] struct Iv { start: usize, nw: u32, wr: Vec<(usize, u32)>, uc: u32, ux: u32, uz: u32, elig: bool, tcost: u64, ccxw: u32 }
            let mut iv: Vec<Option<Iv>> = vec![None; hs.len()];
            let mut ver = vec![0u32; lay.nq];
            let mut ccx_before = 0u64;
            let mut sim = sim::Sim::new(lay.nq, lay.nb, 0xC0FFEE); sim.load(&lay, &shots, 0);
            sim.run_each(&t, |i, r, q| {
                let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
                if k == K_CCX { ccx_before += 1; }
                let (tgt, c1, c2) = match k { K_CCX => (z, x, y), K_CX => (y, x, NONE), K_X => (x, NONE, NONE), K_HMR => (x, NONE, NONE), K_CZ => (NONE, x, y), K_Z => (NONE, x, NONE), _ => (NONE, NONE, NONE) };
                let conditioned = match k { K_CX | K_CZ => z != NONE, K_X | K_Z => y != NONE, _ => false };
                for c in [c1, c2] { if c != NONE { let hi = hidx[c]; if hi != usize::MAX { if let Some(v) = iv[hi].as_mut() {
                    if k == K_CCX { v.uc += 1 } else if k == K_CX { v.ux += 1 } else { v.uz += 1 }
                    if v.elig { if v.wr.iter().any(|&(w, vv)| ver[w] != vv) { v.elig = false; } else if k == K_CCX { v.tcost += v.ccxw as u64; } }
                    // the other operand of this use must not be one of the writers' controls being a helper itself: fine either way
                } } } }
                if tgt != NONE {
                    let hi = hidx[tgt];
                    if hi != usize::MAX {
                        let zero = q[tgt] == 0;
                        if iv[hi].is_none() && !zero { iv[hi] = Some(Iv { start: i, elig: true, ..Default::default() }); }
                        if let Some(v) = iv[hi].as_mut() {
                            v.nw += 1;
                            if k == K_HMR { /* measured reset */ } else {
                                if conditioned || v.wr.len() >= 24 { v.elig = false; }
                                for c in [c1, c2] { if c != NONE { v.wr.push((c, ver[c])); if hidx[c] != usize::MAX { /* written from another helper: allowed, tracked by version */ } } }
                                if k == K_CCX { v.ccxw += 1; }
                            }
                            if zero {
                                let v = iv[hi].take().unwrap();
                                let el = v.elig && !v.wr.iter().any(|&(w, vv)| ver[w] != vv);
                                writeln!(out, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", hs[hi], v.start, i, v.nw, v.ccxw, v.uc, v.ux, v.uz, el as u8, (k == K_HMR) as u8, v.tcost, ccx_before).unwrap();
                            }
                        }
                    }
                    ver[tgt] = ver[tgt].wrapping_add(1);
                }
            });
            for (hi, v) in iv.iter().enumerate() { if let Some(v) = v { writeln!(out, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t0\t0\t0\t{}", hs[hi], v.start, t.len(), v.nw, v.ccxw, v.uc, v.ux, v.uz, ccx_before).unwrap(); } }
        }
        // zwin TRACE INPUTS BATCHES MINLEN OUT   windows in which a wire is zero in every replayed shot and is not touched at all
        // (no read, no write) for at least MINLEN ops. Replays BATCHES x 64 shots one after another and intersects.
        Some("zwin") => {
            use std::io::Write;
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let batches: usize = a[4].parse().unwrap(); let minlen: usize = a[5].parse().unwrap();
            let n = t.len();
            // candidate windows from untouched gaps
            let mut last = vec![0usize; lay.nq]; let mut wins: Vec<(usize, usize, usize)> = Vec::new();
            for (i, &r) in t.iter().enumerate() {
                let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
                let ws: [usize; 3] = match k { K_CCX => [x, y, z], K_CX | K_CZ => [x, y, NONE], K_X | K_Z | K_HMR => [x, NONE, NONE], _ => [NONE, NONE, NONE] };
                for w in ws { if w != NONE { if i - last[w] >= minlen { wins.push((last[w], i, w)); } last[w] = i + 1; } }
            }
            for w in 0..lay.nq { if n - last[w] >= minlen { wins.push((last[w], n, w)); } }
            if let Ok(qf) = std::env::var("QFILE") {
                // keep only gaps that overlap a query interval [a,b) (tab separated, sorted by a); helper wires in QSKIP are dropped
                let mut qs: Vec<(usize, usize)> = std::fs::read_to_string(qf).unwrap().lines().map(|l| { let mut p = l.split('\t'); (p.next().unwrap().parse().unwrap(), p.next().unwrap().parse().unwrap()) }).collect();
                qs.sort(); let mut pm = Vec::with_capacity(qs.len()); let mut mx = 0usize; for q in &qs { mx = mx.max(q.1); pm.push(mx); }
                let skip: Vec<usize> = std::env::var("QSKIP").unwrap_or_default().split(',').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect();
                wins.retain(|w| { if skip.contains(&w.2) { return false; } let i = qs.partition_point(|q| q.0 < w.1); i > 0 && pm[i - 1] > w.0 });
            }
            wins.sort();
            eprintln!("untouched gaps >= {}: {}", minlen, wins.len());
            let mut zero = vec![true; wins.len()];
            let pts: Vec<u64> = wins.iter().map(|w| w.0 as u64).collect();
            for b in 0..batches {
                let mut sim = sim::Sim::new(lay.nq, lay.nb, 0xC0FFEE ^ ((b as u64) << 20)); sim.load(&lay, &shots, b);
                sim.run_hooked(&t, &pts, |p, q| { if q[wins[p].2] != 0 { zero[p] = false; } });
            }
            let mut out = std::io::BufWriter::new(std::fs::File::create(&a[6]).unwrap());
            for (p, w) in wins.iter().enumerate() { writeln!(out, "{}\t{}\t{}\t{}", w.2, w.0, w.1, zero[p] as u8).unwrap(); }
        }
        // hpat TRACE INPUTS BATCHES POINTS h1,h2,..   joint values of the given wires at the given op indices over all shots
        Some("hpat") => {
            let t = load_trace(&a[2]); let lay = layout(&t); let shots = sim::load_shots(&a[3]);
            let batches: usize = a[4].parse().unwrap();
            let pts: Vec<u64> = std::fs::read_to_string(&a[5]).unwrap().lines().map(|l| l.trim().parse().unwrap()).collect();
            let hs: Vec<usize> = a[6].split(',').map(|x| x.parse().unwrap()).collect();
            let np = pts.len(); let nh = hs.len(); let w = 1usize << nh;
            let mut seen = vec![0u32; np * w];
            for b in 0..batches {
                let mut sim = sim::Sim::new(lay.nq, lay.nb, 0xC0FFEE ^ ((b as u64) << 20)); sim.load(&lay, &shots, b);
                sim.run_hooked(&t, &pts, |p, q| { for s in 0..64 { let mut v = 0usize; for (j, &h) in hs.iter().enumerate() { v |= ((q[h] >> s & 1) as usize) << j; } seen[p * w + v] += 1; } });
            }
            for p in 0..np { let pats: Vec<String> = (0..w).filter(|&v| seen[p * w + v] > 0).map(|v| format!("{:0width$b}:{}", v, seen[p * w + v], width = nh)).collect(); println!("{}\t{}\t{}", pts[p], pats.len(), pats.join(" ")); }
        }
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
            let mode = std::env::var("QOPT_MODE").unwrap_or_default();
            let mut patches: Vec<opt::Patch> = Vec::new();
            if mode == "33" { opt::cancel3(&t, &mut mask, false); patches = opt::cancel3(&t, &mut mask, true); }
            else if mode == "23" { opt::cancel2(&t, &mut mask); patches = opt::cancel3(&t, &mut mask, true); }
            else if mode == "3" || mode == "3n" { patches = opt::cancel3(&t, &mut mask, mode == "3"); }
            else if mode == "2" { opt::cancel2(&t, &mut mask); } else { opt::cancel(&t, &mut mask); }
            let (mut dc, mut dall) = (0u64, 0u64);
            for i in 0..n { if opt::mget(&mask, i) { dall += 1; if kind(t[i]) == K_CCX { dc += 1; } } }
            eprintln!("deleted ops {} of {}; deleted Toffolis {}", dall, n, dc);
            opt::mask_save(&format!("{}.mask", a[6]), &mask);
            let runs = opt::encode(&mask, n);
            eprintln!("run-length mask: {} bytes", runs.len());
            save_bytes(&format!("{}.runs", a[6]), &runs);
            if mode == "3" || mode == "3n" || mode == "23" || mode == "33" {
                let pb = opt::encode_patches(&mask, n, &patches);
                eprintln!("patches: {} ({} bytes)", patches.len(), pb.len());
                save_bytes(&format!("{}.patch", a[6]), &pb);
                let out = opt::apply2(&t, &mask, &patches);
                eprintln!("ops out {}", out.len());
                save_trace(&format!("{}.u16le", a[6]), &out);
            } else { save_trace(&format!("{}.u16le", a[6]), &opt::apply(&t, &mask)); }
        }
        // gvn IN.u16le OUT.u16le
        Some("mt") => { let t = load_trace(&a[2]); let out = gvn::measured_targets(&t); save_trace(&a[3], &out); }
        Some("gvn") => { let t = load_trace(&a[2]); let out = gvn::run(&t); save_trace(&a[3], &out); }
        _ => { eprintln!("usage: qopt decode|stats|verify ..."); std::process::exit(2); }
    }
}
