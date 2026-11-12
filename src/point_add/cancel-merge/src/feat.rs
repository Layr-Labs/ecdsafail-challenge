// Feature extraction for later offline optimisation work on a small machine.
// feat TRACE SPANS INPUTS OUTDIR BATCHES
// Writes: shapes.tsv (every distinct span body up to wire renaming), by_name_shapes.tsv, small_instances.bin,
// motifs_top.txt (bodies of the most expensive small shapes with wire and gate facts), gaps.tsv (long idle
// windows per qubit with the value held), state_samples.bin (+ clean_count.tsv), chunks.tsv.
use crate::common::*;
use crate::sim::*;
use crate::stats::replay;
use std::collections::HashMap;
use std::fmt::Write as FW;
use std::time::Instant;

fn envu(k: &str, d: usize) -> usize { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) }

/// Which operand slots are qubits (1), bits (2) or neither (0), by kind.
#[inline(always)] fn slots(k: u16) -> [u8; 3] {
    match k {
        K_CCX => [1, 1, 1], K_CX | K_CZ => [1, 1, 2], K_X | K_Z => [1, 2, 0], K_HMR => [1, 2, 0],
        K_BINV | K_BST0 | K_BST1 => [2, 2, 0], K_PUSH => [2, 0, 0], _ => [0, 0, 0],
    }
}

struct Stamp { qs: Vec<u32>, ql: Vec<u16>, bs: Vec<u32>, bl: Vec<u16>, ep: u32 }
impl Stamp { fn new() -> Self { Stamp { qs: vec![0; 65536], ql: vec![0; 65536], bs: vec![0; 65536], bl: vec![0; 65536], ep: 0 } } }

/// Canonical 128-bit hash of a span body (qubits and bits renamed by first appearance) and its qubit count.
fn shape_hash(t: &[u64], st: &mut Stamp) -> (u128, u16) {
    st.ep += 1; let ep = st.ep;
    let (mut nq, mut nb) = (0u16, 0u16);
    let (mut h1, mut h2) = (0x9E3779B97F4A7C15u64, 0xC2B2AE3D27D4EB4Fu64);
    for &r in t {
        let k = kind(r); let s = slots(k); let v = [fa(r), fb(r), fc(r)];
        let mut c = k as u64;
        for j in 0..3 {
            let x = if v[j] == NONE { 0xFFFF } else { match s[j] {
                1 => { if st.qs[v[j]] != ep { st.qs[v[j]] = ep; st.ql[v[j]] = nq; nq += 1; } st.ql[v[j]] as usize }
                2 => { if st.bs[v[j]] != ep { st.bs[v[j]] = ep; st.bl[v[j]] = nb; nb += 1; } st.bl[v[j]] as usize }
                _ => v[j],
            } };
            c |= (x as u64) << (16 * (j + 1));
        }
        h1 = (h1 ^ c).wrapping_mul(0x100000001B3).rotate_left(29) ^ (c >> 7);
        h2 = (h2.rotate_left(17) ^ c).wrapping_mul(0xFF51AFD7ED558CCD);
    }
    (((h1 as u128) << 64) | h2 as u128, nq)
}

/// Global qubit ids of a span in local order (same numbering as shape_hash).
fn wires(t: &[u64], qs: &mut [u32], ep: &mut u32, out: &mut Vec<u16>) {
    *ep += 1; out.clear();
    for &r in t {
        let s = slots(kind(r)); let v = [fa(r), fb(r), fc(r)];
        for j in 0..3 { if s[j] == 1 && v[j] != NONE && qs[v[j]] != *ep { qs[v[j]] = *ep; out.push(v[j] as u16); } }
    }
}

struct Shape { name: u32, inst: u64, ops: u64, ccx: u64, exec: u64, nq: u16, first: usize, small: bool, woff: usize, coff: usize }

pub fn run(trace: &str, spans: &str, inputs: &str, outdir: &str, batches: usize, threads: usize) {
    std::fs::create_dir_all(outdir).unwrap();
    let small_max = envu("FEAT_SMALL", 2048); let gap_min = envu("FEAT_GAP", 500_000);
    let sample = envu("FEAT_SAMPLE", 250_000); let topk = envu("FEAT_TOP", 3000); let chunk = envu("FEAT_CHUNK", 1_000_000);
    let t0 = Instant::now();
    let t = load_trace(trace); let n = t.len(); let lay = layout(&t); let nq = lay.nq;
    let shots = load_shots(inputs);
    eprintln!("loaded {} ops, {} qubits ({:.0}s)", n, nq, t0.elapsed().as_secs_f64());
    let prof = replay(&t, &lay, &shots, batches, threads, true);
    let nshots = (batches * 64) as f64;
    // prefix sums
    let mut pc: Vec<u32> = Vec::with_capacity(n + 1); pc.push(0);
    let mut j = 0u32; for &r in t.iter() { if kind(r) == K_CCX { j += 1; } pc.push(j); }
    let nccx = j as usize;
    let mut pe: Vec<u64> = Vec::with_capacity(nccx + 1); pe.push(0);
    let mut e = 0u64; for i in 0..nccx { e += prof.exec[i] as u64; pe.push(e); }
    // spans
    let text = std::fs::read_to_string(spans).expect("spans");
    let mut sa: Vec<usize> = Vec::new(); let mut sb: Vec<usize> = Vec::new(); let mut sn: Vec<u32> = Vec::new();
    let mut nameid: HashMap<String, u32> = HashMap::new(); let mut namev: Vec<String> = Vec::new();
    for line in text.lines() {
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 6 || f[0] == "id" { continue; }
        let (a, b): (usize, usize) = (f[2].parse().unwrap(), f[3].parse().unwrap());
        if b > n || b <= a { continue; }
        let nm = *nameid.entry(f[4].to_string()).or_insert_with(|| { namev.push(f[4].to_string()); (namev.len() - 1) as u32 });
        sa.push(a); sb.push(b); sn.push(nm);
    }
    drop(text);
    let ns = sa.len();
    eprintln!("spans {} names {} ({:.0}s)", ns, namev.len(), t0.elapsed().as_secs_f64());
    // ---- shape hashes, in parallel ----
    let hashes: Vec<(u128, u16)> = {
        let mut out = vec![(0u128, 0u16); ns];
        let parts: Vec<Vec<(usize, (u128, u16))>> = std::thread::scope(|sc| {
            let (t, sa, sb) = (&t, &sa, &sb);
            let hs: Vec<_> = (0..threads).map(|th| sc.spawn(move || {
                let mut st = Stamp::new(); let mut v = Vec::new();
                let mut i = th; while i < ns { v.push((i, shape_hash(&t[sa[i]..sb[i]], &mut st))); i += threads; }
                v
            })).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        for p in parts { for (i, h) in p { out[i] = h; } }
        out
    };
    eprintln!("hashed ({:.0}s)", t0.elapsed().as_secs_f64());
    let mut sid: HashMap<u128, u32> = HashMap::new(); let mut shapes: Vec<Shape> = Vec::new(); let mut span_shape = vec![0u32; ns];
    for i in 0..ns {
        let (h, q) = hashes[i]; let (a, b) = (sa[i], sb[i]);
        let id = *sid.entry(h).or_insert_with(|| { shapes.push(Shape { name: sn[i], inst: 0, ops: 0, ccx: 0, exec: 0, nq: q, first: i, small: b - a <= small_max && b - a >= 4, woff: 0, coff: 0 }); (shapes.len() - 1) as u32 });
        let s = &mut shapes[id as usize];
        s.inst += 1; s.ops += (b - a) as u64; s.ccx += (pc[b] - pc[a]) as u64; s.exec += pe[pc[b] as usize] - pe[pc[a] as usize];
        span_shape[i] = id;
    }
    let (mut wtot, mut ctot) = (0usize, 0usize);
    for s in shapes.iter_mut() { if s.small { s.woff = wtot; wtot += s.nq as usize; s.coff = ctot; ctot += (pc[sb[s.first]] - pc[sa[s.first]]) as usize; } }
    eprintln!("shapes {} (small {}), small wires {}, small ccx {}", shapes.len(), shapes.iter().filter(|s| s.small).count(), wtot, ctot);
    // ---- static per-qubit gaps and chunk table ----
    let mut last = vec![0usize; nq]; let mut gaps: Vec<(u16, usize, usize)> = Vec::new();
    let nch = n.div_ceil(chunk); let mut ch = vec![[0u64; 8]; nch]; // ccx cx x hmr cz z cond other
    let mut seen = vec![u32::MAX; nq]; let mut chq = vec![0u32; nch];
    for (i, &r) in t.iter().enumerate() {
        let k = kind(r); let s = slots(k); let v = [fa(r), fb(r), fc(r)]; let c = i / chunk;
        let col = match k { K_CCX => 0, K_CX => 1, K_X => 2, K_HMR => 3, K_CZ => 4, K_Z => 5, K_PUSH | K_POP => 6, _ => 7 };
        ch[c][col] += 1;
        for j in 0..3 { if s[j] == 1 && v[j] != NONE { let q = v[j];
            if i - last[q] >= gap_min { gaps.push((q as u16, last[q], i)); }
            last[q] = i + 1;
            if seen[q] != c as u32 { seen[q] = c as u32; chq[c] += 1; }
        } }
    }
    for q in 0..nq { if n - last[q] >= gap_min { gaps.push((q as u16, last[q], n)); } }
    eprintln!("gaps >= {} ops: {} ({:.0}s)", gap_min, gaps.len(), t0.elapsed().as_secs_f64());
    // ---- events ----
    // kind 0 = small instance start, 1 = small instance end, 2 = gap end, 3 = sample
    let mut ev: Vec<(u64, u8, u32)> = Vec::new();
    let mut small_spans: Vec<u32> = Vec::new();
    for i in 0..ns { if shapes[span_shape[i] as usize].small { small_spans.push(i as u32); ev.push((sa[i] as u64, 0, i as u32)); ev.push((sb[i] as u64, 1, i as u32)); } }
    for (g, x) in gaps.iter().enumerate() { ev.push((x.2 as u64, 2, g as u32)); }
    let nsamp = n / sample + 1; for s in 0..nsamp { ev.push(((s * sample).min(n) as u64, 3, s as u32)); }
    ev.sort_unstable();
    let pts: Vec<u64> = ev.iter().map(|x| x.0).collect();
    eprintln!("events {} (small instances {}) ({:.0}s)", ev.len(), small_spans.len(), t0.elapsed().as_secs_f64());
    // ---- hooked replay ----
    let th = threads.min(batches).max(1);
    let res: Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> = std::thread::scope(|sc| {
        let (t, lay, shots, ev, pts, sa, sb, shapes, span_shape, gaps) = (&t, &lay, &shots, &ev, &pts, &sa, &sb, &shapes, &span_shape, &gaps);
        let hs: Vec<_> = (0..th).map(|x| sc.spawn(move || {
            let mut wf = vec![0u8; wtot]; let mut gf = vec![0u8; gaps.len()]; let mut sf = vec![0u8; nsamp * nq];
            let mut qs = vec![0u32; 65536]; let mut ep = 0u32; let mut w: Vec<u16> = Vec::new();
            let mut b = x;
            while b < batches {
                let mut sim = Sim::new(lay.nq, lay.nb, 0xC0FFEE ^ ((b as u64) << 20));
                sim.load(lay, shots, b);
                sim.run_hooked(t, pts, |p, q| {
                    let (_, k, id) = ev[p]; let id = id as usize;
                    match k {
                        0 | 1 => {
                            let s = &shapes[span_shape[id] as usize];
                            wires(&t[sa[id]..sb[id]], &mut qs, &mut ep, &mut w);
                            let sh = if k == 0 { 0 } else { 2 };
                            for (l, &g) in w.iter().enumerate() { let v = q[g as usize]; wf[s.woff + l] |= (((v != 0) as u8) | (((v != !0) as u8) << 1)) << sh; }
                        }
                        2 => { let v = q[gaps[id].0 as usize]; gf[id] |= ((v != 0) as u8) | (((v != !0) as u8) << 1); }
                        _ => { for g in 0..nq { let v = q[g]; sf[id * nq + g] |= ((v != 0) as u8) | (((v != !0) as u8) << 1); } }
                    }
                });
                b += th;
            }
            (wf, gf, sf)
        })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut wf = vec![0u8; wtot]; let mut gf = vec![0u8; gaps.len()]; let mut sf = vec![0u8; nsamp * nq];
    for (a, b, c) in res { for i in 0..wtot { wf[i] |= a[i]; } for i in 0..gf.len() { gf[i] |= b[i]; } for i in 0..sf.len() { sf[i] |= c[i]; } }
    eprintln!("hooked replay done ({:.0}s)", t0.elapsed().as_secs_f64());
    // ---- per-gate facts of small shapes ----
    let mut cfl = vec![0u8; ctot]; let mut cex = vec![0u64; ctot];
    for &i in small_spans.iter() { let i = i as usize; let s = &shapes[span_shape[i] as usize];
        let (ja, jb) = (pc[sa[i]] as usize, pc[sb[i]] as usize);
        for j in ja..jb { cfl[s.coff + j - ja] |= prof.flags[j]; cex[s.coff + j - ja] += prof.exec[j] as u64; } }
    let st = |f: u8| match f & 3 { 1 => "1", 2 => "0", 3 => "m", _ => "?" };
    // ---- outputs ----
    let mut o = String::from("shape\thash\tname\tinstances\tops_each\tccx_each\tqubits\ttof_per_shot_total\tccx_total\tsmall\tfirst_start\tfirst_end\n");
    let mut order: Vec<usize> = (0..shapes.len()).collect(); order.sort_by(|&a, &b| shapes[b].exec.cmp(&shapes[a].exec));
    for &i in order.iter() { let s = &shapes[i];
        writeln!(o, "{}\t{:032x}\t{}\t{}\t{}\t{}\t{}\t{:.2}\t{}\t{}\t{}\t{}", i, hashes[s.first].0, namev[s.name as usize], s.inst, s.ops / s.inst, s.ccx / s.inst, s.nq,
            s.exec as f64 / nshots, s.ccx, s.small as u8, sa[s.first], sb[s.first]).unwrap(); }
    std::fs::write(format!("{}/shapes.tsv", outdir), &o).unwrap();
    let mut by: HashMap<u32, (u64, std::collections::HashSet<u32>, u64, u64, u64)> = HashMap::new();
    for i in 0..ns { let e = by.entry(sn[i]).or_insert((0, Default::default(), 0, 0, 0)); e.0 += 1; e.1.insert(span_shape[i]);
        e.2 += (sb[i] - sa[i]) as u64; e.3 += (pc[sb[i]] - pc[sa[i]]) as u64; e.4 += pe[pc[sb[i]] as usize] - pe[pc[sa[i]] as usize]; }
    let mut rows: Vec<_> = by.into_iter().collect(); rows.sort_by(|a, b| b.1 .4.cmp(&a.1 .4));
    let mut o = String::from("name\tinstances\tdistinct_shapes\tops_incl\tccx_incl\ttof_per_shot_incl\n");
    for (nm, (c, set, ops, ccx, ex)) in rows.iter() { writeln!(o, "{}\t{}\t{}\t{}\t{}\t{:.1}", namev[*nm as usize], c, set.len(), ops, ccx, *ex as f64 / nshots).unwrap(); }
    std::fs::write(format!("{}/by_name_shapes.tsv", outdir), &o).unwrap();
    let mut bin: Vec<u8> = Vec::with_capacity(small_spans.len() * 16);
    for &i in small_spans.iter() { let i = i as usize; bin.extend_from_slice(&(sa[i] as u64).to_le_bytes()); bin.extend_from_slice(&((sb[i] - sa[i]) as u32).to_le_bytes()); bin.extend_from_slice(&span_shape[i].to_le_bytes()); }
    save_bytes(&format!("{}/small_instances.bin", outdir), &bin);
    // top small shapes with bodies
    let mut o = String::new(); let mut done = 0usize; let mut qs = vec![0u32; 65536]; let mut ep = 0u32; let mut w: Vec<u16> = Vec::new();
    let f = |v: usize| if v == NONE { "-".to_string() } else { v.to_string() };
    for &i in order.iter() { let s = &shapes[i]; if !s.small || s.exec == 0 { continue; } if done == topk { break; } done += 1;
        let (a, b) = (sa[s.first], sb[s.first]);
        writeln!(o, "## shape {} name {} instances {} ops {} ccx {} qubits {} tof_per_shot_total {:.2} first_start {}", i, namev[s.name as usize], s.inst, b - a, pc[b] - pc[a], s.nq, s.exec as f64 / nshots, a).unwrap();
        wires(&t[a..b], &mut qs, &mut ep, &mut w);
        let mut l = String::from("wires local:global(in,out) ");
        for (x, &g) in w.iter().enumerate() { let v = wf[s.woff + x]; write!(l, "{}:{}({},{}) ", x, g, st(v), st(v >> 2)).unwrap(); }
        writeln!(o, "{}", l).unwrap();
        let mut loc: HashMap<usize, usize> = HashMap::new(); for (x, &g) in w.iter().enumerate() { loc.insert(g as usize, x); }
        let lq = |v: usize| if v == NONE { "-".to_string() } else { format!("q{}", loc[&v]) };
        let mut cj = 0usize;
        for &r in &t[a..b] { let (k, x, y, z) = (kind(r), fa(r), fb(r), fc(r));
            match k {
                K_CCX => { writeln!(o, "CCX {} {} {} flags={:07b} tof_per_inst={:.3}", lq(x), lq(y), lq(z), cfl[s.coff + cj], cex[s.coff + cj] as f64 / nshots / s.inst as f64).unwrap(); cj += 1; }
                K_CX => writeln!(o, "CX {} {} if b{}", lq(x), lq(y), f(z)).unwrap(),
                K_CZ => writeln!(o, "CZ {} {} if b{}", lq(x), lq(y), f(z)).unwrap(),
                K_X => writeln!(o, "X {} if b{}", lq(x), f(y)).unwrap(),
                K_Z => writeln!(o, "Z {} if b{}", lq(x), f(y)).unwrap(),
                K_HMR => writeln!(o, "HMR {} b{}", lq(x), y).unwrap(),
                K_PUSH => writeln!(o, "PUSH b{}", x).unwrap(), K_POP => writeln!(o, "POP").unwrap(),
                _ => writeln!(o, "K{} {} {} {}", k, f(x), f(y), f(z)).unwrap(),
            } }
    }
    std::fs::write(format!("{}/motifs_top.txt", outdir), &o).unwrap();
    // ---- individual components: canonical body of each of the most expensive distinct shapes, any size up to comp_max ----
    {
        let compk = envu("FEAT_COMP", 4000); let comp_max = envu("FEAT_COMP_MAX", 4_000_000);
        std::fs::create_dir_all(format!("{}/components", outdir)).unwrap();
        let total: u64 = pe[nccx];
        let mut idx = String::from("rank\tfile\tshape\tname\tinstances\tops_each\tccx_each\tqubits\ttof_per_shot_each\ttof_per_shot_total\tshare_of_circuit\thas_facts\tfirst_start\n");
        let mut stp = Stamp::new(); let mut rank = 0usize; let mut seq = 0usize; let per = envu("FEAT_PER_NAME", 30);
        let mut per_name: HashMap<u32, usize> = HashMap::new();
        for &i in order.iter() { let s = &shapes[i]; let (a, b) = (sa[s.first], sb[s.first]);
            if s.exec == 0 || b - a > comp_max || b - a < 4 { continue; }
            let cnt = per_name.entry(s.name).or_insert(0usize);
            if seq >= compk && *cnt >= per { continue; }
            seq += 1; *cnt += 1; rank += 1;
            stp.ep += 1; let ep = stp.ep; let (mut cq, mut cb) = (0u16, 0u16);
            let mut body: Vec<u8> = Vec::with_capacity((b - a) * 8);
            for &r in &t[a..b] { let k = kind(r); let sl = slots(k); let v = [fa(r), fb(r), fc(r)]; let mut out = [k, 0u16, 0, 0];
                for j in 0..3 { out[j + 1] = if v[j] == NONE { 0xFFFF } else { match sl[j] {
                    1 => { if stp.qs[v[j]] != ep { stp.qs[v[j]] = ep; stp.ql[v[j]] = cq; cq += 1; } stp.ql[v[j]] }
                    2 => { if stp.bs[v[j]] != ep { stp.bs[v[j]] = ep; stp.bl[v[j]] = cb; cb += 1; } stp.bl[v[j]] }
                    _ => v[j] as u16 } }; }
                for x in out { body.extend_from_slice(&x.to_le_bytes()); } }
            let nm: String = namev[s.name as usize].chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
            std::fs::create_dir_all(format!("{}/components/{}", outdir, nm)).unwrap();
            let file = format!("{}/c{:05}_s{}.u16le", nm, rank, i);
            std::fs::write(format!("{}/components/{}", outdir, file), &body).unwrap();
            writeln!(idx, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{:.2}\t{:.5}%\t{}\t{}", rank, file, i, namev[s.name as usize], s.inst, b - a, pc[b] - pc[a], s.nq,
                s.exec as f64 / nshots / s.inst as f64, s.exec as f64 / nshots, s.exec as f64 * 100.0 / total as f64, s.small as u8, a).unwrap();
        }
        std::fs::write(format!("{}/components/index.tsv", outdir), &idx).unwrap();
    }
    let mut o = String::from("qubit\tstart\tend\tlength\tvalue\n");
    for (g, x) in gaps.iter().enumerate() { writeln!(o, "{}\t{}\t{}\t{}\t{}", x.0, x.1, x.2, x.2 - x.1, st(gf[g])).unwrap(); }
    std::fs::write(format!("{}/gaps.tsv", outdir), &o).unwrap();
    save_bytes(&format!("{}/state_samples.bin", outdir), &sf);
    let mut o = String::from("op\tqubits_always0\tqubits_always1\tqubits_mixed\n");
    for s in 0..nsamp { let mut c = [0u32; 4]; for g in 0..nq { c[(sf[s * nq + g] & 3) as usize] += 1; }
        writeln!(o, "{}\t{}\t{}\t{}", (s * sample).min(n), c[2], c[1], c[3]).unwrap(); }
    std::fs::write(format!("{}/clean_count.tsv", outdir), &o).unwrap();
    let mut o = String::from("chunk_start\tccx\tcx\tx\thmr\tcz\tz\tpushpop\tother\ttof_per_shot\tqubits_touched\n");
    for c in 0..nch { let (a, b) = (c * chunk, ((c + 1) * chunk).min(n)); let x = ch[c];
        writeln!(o, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.1}\t{}", a, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], (pe[pc[b] as usize] - pe[pc[a] as usize]) as f64 / nshots, chq[c]).unwrap(); }
    std::fs::write(format!("{}/chunks.tsv", outdir), &o).unwrap();
    std::fs::write(format!("{}/meta.tsv", outdir), format!("trace\t{}\nops\t{}\nqubits\t{}\nccx\t{}\nshots\t{}\ncheck\t{}\navg_toffoli\t{:.3}\nsmall_max\t{}\ngap_min\t{}\nsample_every\t{}\nsamples\t{}\nchunk\t{}\nshapes\t{}\nspans\t{}\n",
        trace, n, nq, nccx, batches * 64, prof.fail.clone().unwrap_or_else(|| "PASS".into()), prof.tof_total as f64 / nshots, small_max, gap_min, sample, nsamp, chunk, shapes.len(), ns)).unwrap();
    eprintln!("FEAT_DONE ({:.0}s)", t0.elapsed().as_secs_f64());
}
