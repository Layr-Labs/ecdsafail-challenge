// Replay-based profile of a trace: per-Toffoli behaviour flags, per-stage (span) tables, per-qubit table.
use crate::common::*;
use crate::sim::*;
use std::collections::HashMap;
use std::fmt::Write as FW;
use std::time::Instant;

pub struct Profile { pub flags: Vec<u8>, pub exec: Vec<u16>, pub first: Vec<u32>, pub batches: usize, pub fail: Option<String>, pub tof_total: u64, pub bad_shots: u64 }

/// Replays `batches` batches of 64 shots on `threads` threads. With `record`, keeps per-Toffoli flags and executed counts.
pub fn replay(t: &[u64], lay: &Layout, shots: &Shots, batches: usize, threads: usize, record: bool) -> Profile {
    assert!(batches * 64 <= shots.n, "not enough shots");
    let nccx = t.iter().filter(|&&r| kind(r) == K_CCX).count();
    let threads = threads.min(batches).max(1);
    let t0 = Instant::now();
    assert!(!record || batches.div_ceil(threads) < 1023, "too many batches per thread for u16 first-fire index");
    let results: Vec<(Vec<u8>, Vec<u16>, Vec<u16>, Option<String>, u64, u64)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads).map(|th| sc.spawn(move || {
            let mut flags = if record { vec![0u8; nccx] } else { Vec::new() };
            let mut exec = if record { vec![0u16; nccx] } else { Vec::new() };
            let mut first = if record { vec![0xFFFFu16; nccx] } else { Vec::new() };
            let mut fail = None; let mut tof = 0u64; let mut bad = 0u64;
            let mut b = th; let mut lb = 0usize;
            while b < batches {
                let mut sim = Sim::new(lay.nq, lay.nb, 0xC0FFEE ^ ((b as u64) << 20));
                sim.load(lay, shots, b);
                sim.run(t, if record { Some(Rec { flags: &mut flags, exec: &mut exec, first: &mut first, local_batch: lb }) } else { None });
                tof += sim.tof;
                let m = sim.fail_mask(lay, shots, b);
                bad += m.count_ones() as u64;
                if fail.is_none() { fail = sim.check(lay, shots, b); }
                b += threads; lb += 1;
            }
            (flags, exec, first, fail, tof, bad)
        })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut flags = if record { vec![0u8; nccx] } else { Vec::new() };
    let mut exec = if record { vec![0u16; nccx] } else { Vec::new() };
    let mut first = if record { vec![u32::MAX; nccx] } else { Vec::new() };
    let mut fail = None; let mut tof_total = 0u64; let mut bad_shots = 0u64;
    for (th, (f, e, fi, fl, tf, bad)) in results.into_iter().enumerate() {
        if record { for i in 0..nccx {
            flags[i] |= f[i]; exec[i] = exec[i].saturating_add(e[i]);
            if fi[i] != 0xFFFF { let (lb, bit) = ((fi[i] / 64) as usize, (fi[i] % 64) as usize); let g = ((th + lb * threads) * 64 + bit) as u32; if g < first[i] { first[i] = g; } }
        } }
        if fail.is_none() { fail = fl; }
        tof_total += tf; bad_shots += bad;
    }
    eprintln!("failing shots: {} of {}", bad_shots, batches * 64);
    eprintln!("replay: {} batches ({} shots) on {} threads in {:.1}s; avg Toffoli/shot {:.3}; check {}",
        batches, batches * 64, threads, t0.elapsed().as_secs_f64(), tof_total as f64 / (batches * 64) as f64,
        fail.clone().unwrap_or_else(|| "PASS".into()));
    Profile { flags, exec, first, batches, fail, tof_total, bad_shots }
}

#[derive(Default, Clone, Copy)]
struct M { ops: u64, ccx: u64, exec: u64, nofire: u64, uncomp: u64, comp: u64, ctrl1: u64, condl: u64 }
impl M {
    fn sub(&mut self, o: &M) { self.ops -= o.ops; self.ccx -= o.ccx; self.exec -= o.exec; self.nofire -= o.nofire;
        self.uncomp -= o.uncomp; self.comp -= o.comp; self.ctrl1 -= o.ctrl1; self.condl -= o.condl; }
    fn add(&mut self, o: &M) { self.ops += o.ops; self.ccx += o.ccx; self.exec += o.exec; self.nofire += o.nofire;
        self.uncomp += o.uncomp; self.comp += o.comp; self.ctrl1 += o.ctrl1; self.condl += o.condl; }
}

pub fn run(trace: &str, spans: &str, inputs: &str, outdir: &str, batches: usize, threads: usize) {
    std::fs::create_dir_all(outdir).unwrap();
    let t0 = Instant::now();
    let t = load_trace(trace);
    let lay = layout(&t);
    eprintln!("loaded {} ops in {:.1}s; qubits {} bits {} regs {:?}", t.len(), t0.elapsed().as_secs_f64(), lay.nq, lay.nb,
        lay.regs.iter().map(|r| r.len()).collect::<Vec<_>>());
    let shots = load_shots(inputs);
    let prof = replay(&t, &lay, &shots, batches, threads, true);
    save_bytes(&format!("{}/ccx_flags.bin", outdir), &prof.flags);
    {
        let bytes: Vec<u8> = prof.first.iter().flat_map(|x| x.to_le_bytes()).collect();
        save_bytes(&format!("{}/ccx_first.bin", outdir), &bytes);
        // learning curve: how many gates first fire at shot s
        let ns = batches * 64;
        let mut novel = vec![0u64; ns]; let mut never = 0u64;
        for &f in prof.first.iter() { if f == u32::MAX { never += 1; } else { novel[f as usize] += 1; } }
        let mut s = String::from("shots_seen\tgates_not_yet_fired\tnew_gates_in_window\tshots_with_new_gate_in_window\twindow\n");
        let mut unseen: u64 = never + novel.iter().sum::<u64>();
        let mut w0 = 0usize;
        while w0 < ns {
            let w1 = (w0 + (w0 / 4).max(16)).min(ns);
            let newg: u64 = novel[w0..w1].iter().sum(); let sh = novel[w0..w1].iter().filter(|&&x| x > 0).count();
            writeln!(s, "{}\t{}\t{}\t{}\t{}", w0, unseen, newg, sh, w1 - w0).unwrap();
            unseen -= newg; w0 = w1;
        }
        writeln!(s, "{}\t{}\t0\t0\t0", ns, unseen).unwrap();
        std::fs::write(format!("{}/learning_curve.tsv", outdir), &s).unwrap();
    }
    let nshots = (batches * 64) as f64;

    // ---- static tables ----
    let mut hist = [0u64; 20]; let mut cond_ops = [0u64; 20];
    let mut depth = 0usize; let mut maxdepth = 0usize; let mut ccx_in_cond = 0u64;
    let nq = lay.nq;
    let mut qt = vec![[0u64; 6]; nq]; // ccx target, ccx control, cx target, cx control, hmr, other
    let mut first = vec![u64::MAX; nq]; let mut last = vec![0u64; nq];
    let mut adj_dup = 0u64; let mut prev = 0u64;
    for (i, &r) in t.iter().enumerate() {
        let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
        hist[k as usize] += 1;
        let mut touch = |q: usize, col: usize| { qt[q][col] += 1; if first[q] == u64::MAX { first[q] = i as u64; } last[q] = i as u64; };
        match k {
            K_CCX => { touch(a, 1); touch(b, 1); touch(c, 0); if depth > 0 { ccx_in_cond += 1; } if r == prev { adj_dup += 1; } }
            K_CX => { touch(a, 3); touch(b, 2); if c != NONE { cond_ops[k as usize] += 1; } }
            K_CZ => { touch(a, 5); touch(b, 5); if c != NONE { cond_ops[k as usize] += 1; } }
            K_X | K_Z => { touch(a, 5); if b != NONE { cond_ops[k as usize] += 1; } }
            K_HMR => { touch(a, 4); }
            K_BINV | K_BST0 | K_BST1 => { if b != NONE { cond_ops[k as usize] += 1; } }
            K_PUSH => { depth += 1; maxdepth = maxdepth.max(depth); }
            K_POP => { depth -= 1; }
            _ => {}
        }
        prev = r;
    }
    // ---- prefix sums over ops ----
    let n = t.len();
    let mut pc: Vec<u32> = Vec::with_capacity(n + 1); // CCX ordinal prefix
    pc.push(0);
    let mut j = 0u32;
    for &r in t.iter() { if kind(r) == K_CCX { j += 1; } pc.push(j); }
    let nccx = j as usize;
    let cls = |f: u8| -> (bool, bool, bool, bool, bool) {
        let ex = f & F_EXEC != 0;
        (ex && f & F_FIRE == 0,                 // never fires
         ex && f & F_TPOST == 0,                // target always 0 afterwards (uncompute-like)
         ex && f & F_TPRE == 0,                 // target always 0 before (compute-like)
         ex && (f & F_A0 == 0 || f & F_B0 == 0),// a control is always 1
         f & F_COND0 != 0)                      // classically conditioned
    };
    let mut p_exec: Vec<u64> = Vec::with_capacity(nccx + 1); p_exec.push(0);
    let mut p_cls: Vec<[u32; 5]> = Vec::with_capacity(nccx + 1); p_cls.push([0; 5]);
    let mut tot = [0u64; 5]; let mut acc = [0u32; 5]; let mut e = 0u64;
    let mut combo: HashMap<u8, u64> = HashMap::new();
    for i in 0..nccx {
        e += prof.exec[i] as u64; p_exec.push(e);
        let c = cls(prof.flags[i]);
        let cs = [c.0, c.1, c.2, c.3, c.4];
        for x in 0..5 { if cs[x] { acc[x] += 1; tot[x] += 1; } }
        p_cls.push(acc);
        *combo.entry(prof.flags[i]).or_insert(0) += 1;
    }
    let measure = |a: usize, b: usize| -> M {
        let (ja, jb) = (pc[a] as usize, pc[b] as usize);
        let (x, y) = (p_cls[ja], p_cls[jb]);
        M { ops: (b - a) as u64, ccx: (jb - ja) as u64, exec: p_exec[jb] - p_exec[ja], nofire: (y[0] - x[0]) as u64,
            uncomp: (y[1] - x[1]) as u64, comp: (y[2] - x[2]) as u64, ctrl1: (y[3] - x[3]) as u64, condl: (y[4] - x[4]) as u64 }
    };
    // ---- summary ----
    let mut s = String::new();
    writeln!(s, "trace\t{}", trace).unwrap();
    writeln!(s, "ops\t{}\nqubits\t{}\nbits\t{}\nccx\t{}\nshots\t{}\ncheck\t{}", n, lay.nq, lay.nb, nccx, batches * 64,
        prof.fail.clone().unwrap_or_else(|| "PASS".into())).unwrap();
    writeln!(s, "avg_executed_toffoli_per_shot\t{:.3}", prof.tof_total as f64 / nshots).unwrap();
    let names = ["", "Register", "AppendQ", "BitInvert", "BitStore0", "BitStore1", "X", "Z", "CX", "CZ", "", "", "Hmr", "CCX", "", "Push", "Pop", "", "AppendB", ""];
    for k in 0..20 { if hist[k] > 0 { writeln!(s, "kind_{}\t{}\tclassically_conditioned\t{}", names[k], hist[k], cond_ops[k]).unwrap(); } }
    writeln!(s, "max_condition_depth\t{}\nccx_inside_condition_blocks\t{}\nadjacent_identical_ccx_pairs\t{}", maxdepth, ccx_in_cond, adj_dup).unwrap();
    let lbl = ["ccx_never_fires", "ccx_target_always0_after", "ccx_target_always0_before", "ccx_a_control_always1", "ccx_sometimes_skipped_by_condition"];
    for x in 0..5 { writeln!(s, "{}\t{}\t{:.3}%", lbl[x], tot[x], tot[x] as f64 * 100.0 / nccx as f64).unwrap(); }
    let mut cv: Vec<_> = combo.into_iter().collect(); cv.sort_by(|a, b| b.1.cmp(&a.1));
    writeln!(s, "# flag combinations (bits: 1 exec, 2 cond-skipped, 4 fires, 8 tgt1-before, 16 tgt1-after, 32 a-sometimes0, 64 b-sometimes0)").unwrap();
    for (f, c) in cv.iter().take(40) { writeln!(s, "flags_{:07b}\t{}\t{:.3}%", f, c, *c as f64 * 100.0 / nccx as f64).unwrap(); }
    std::fs::write(format!("{}/summary.tsv", outdir), &s).unwrap();
    eprint!("{}", s);
    // ---- per qubit ----
    let mut isreg = vec![String::new(); nq];
    for (ri, r) in lay.regs.iter().enumerate() { for (i, &(isb, id)) in r.iter().enumerate() { if !isb { isreg[id] = format!("reg{}[{}]", ri, i); } } }
    let mut s = String::from("qubit\trole\tccx_target\tccx_control\tcx_target\tcx_control\thmr\tother\tfirst_op\tlast_op\n");
    for q in 0..nq { writeln!(s, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", q, isreg[q], qt[q][0], qt[q][1], qt[q][2], qt[q][3], qt[q][4], qt[q][5], first[q], last[q]).unwrap(); }
    std::fs::write(format!("{}/qubits.tsv", outdir), &s).unwrap();
    // ---- spans ----
    if spans == "-" { return; }
    let text = std::fs::read_to_string(spans).expect("spans");
    struct Sp { id: u64, parent: u64, a: usize, b: usize, name: u32, flag: u32 }
    let mut sp: Vec<Sp> = Vec::new(); let mut nameid: HashMap<String, u32> = HashMap::new(); let mut namev: Vec<String> = Vec::new();
    for line in text.lines() {
        if line.is_empty() || line.starts_with('#') { continue; }
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 6 || f[0] == "id" { continue; }
        let nm = *nameid.entry(f[4].to_string()).or_insert_with(|| { namev.push(f[4].to_string()); (namev.len() - 1) as u32 });
        sp.push(Sp { id: f[0].parse().unwrap(), parent: f[1].parse().unwrap(), a: f[2].parse().unwrap(), b: f[3].parse().unwrap(), name: nm, flag: f[5].parse().unwrap_or(0) });
    }
    drop(text);
    let idx: HashMap<u64, usize> = sp.iter().enumerate().map(|(i, s)| (s.id, i)).collect();
    let incl: Vec<M> = sp.iter().map(|s| measure(s.a, s.b.min(n))).collect();
    let mut selfm = incl.clone();
    for (i, s) in sp.iter().enumerate() { if let Some(&p) = idx.get(&s.parent) { if p != i { let m = incl[i]; selfm[p].sub(&m); } } }
    let mut depthv = vec![u32::MAX; sp.len()];
    fn dep(i: usize, sp: &Vec<Sp>, idx: &HashMap<u64, usize>, d: &mut Vec<u32>) -> u32 {
        if d[i] != u32::MAX { return d[i]; }
        let v = match idx.get(&sp[i].parent) { Some(&p) if p != i => dep(p, sp, idx, d) + 1, _ => 0 };
        d[i] = v; v
    }
    for i in 0..sp.len() { dep(i, &sp, &idx, &mut depthv); }
    // by name (+flag)
    let mut by: HashMap<(u32, u32), (u64, M, M)> = HashMap::new();
    for (i, s) in sp.iter().enumerate() { let e = by.entry((s.name, s.flag)).or_insert((0, M::default(), M::default())); e.0 += 1; e.1.add(&incl[i]); e.2.add(&selfm[i]); }
    let mut rows: Vec<_> = by.into_iter().collect(); rows.sort_by(|a, b| b.1 .2.exec.cmp(&a.1 .2.exec));
    let mut s = String::from("name\tflag\tinstances\tops_incl\tccx_incl\ttof_per_shot_incl\tops_self\tccx_self\ttof_per_shot_self\tself_never_fires\tself_tgt0_after\tself_tgt0_before\tself_ctrl_always1\tself_conditional\n");
    for ((nm, fl), (cnt, mi, ms)) in rows.iter() {
        writeln!(s, "{}\t{}\t{}\t{}\t{}\t{:.1}\t{}\t{}\t{:.1}\t{}\t{}\t{}\t{}\t{}", namev[*nm as usize], fl, cnt, mi.ops, mi.ccx, mi.exec as f64 / nshots,
            ms.ops, ms.ccx, ms.exec as f64 / nshots, ms.nofire, ms.uncomp, ms.comp, ms.ctrl1, ms.condl).unwrap();
    }
    std::fs::write(format!("{}/by_name.tsv", outdir), &s).unwrap();
    // tree of big spans
    let mut s = String::from("id\tparent\tdepth\tstart\tend\tname\tflag\tops\tccx\ttof_per_shot\tnever_fires\ttgt0_after\ttgt0_before\tctrl_always1\tconditional\n");
    for (i, x) in sp.iter().enumerate() {
        if depthv[i] <= 2 || incl[i].ops >= 2_000_000 {
            let m = incl[i];
            writeln!(s, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.1}\t{}\t{}\t{}\t{}\t{}", x.id, x.parent, depthv[i], x.a, x.b, namev[x.name as usize], x.flag, m.ops, m.ccx,
                m.exec as f64 / nshots, m.nofire, m.uncomp, m.comp, m.ctrl1, m.condl).unwrap();
        }
    }
    std::fs::write(format!("{}/tree.tsv", outdir), &s).unwrap();
    eprintln!("spans {} names {}; wrote tables to {} ({:.1}s total)", sp.len(), namev.len(), outdir, t0.elapsed().as_secs_f64());
}
