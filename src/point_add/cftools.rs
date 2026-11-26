//! cf1 local tools (q631 / cf, 2026-11-19; local research, never submitted): survey of the forward upper walk ranges
//! that cf631.rs replaces.  Nothing here is called by the builder.
use super::*;
use std::io::Write;

/// positions in the hybrid-spliced assembled list (before the relabelling) of every placed piece:
/// (start, end, kind 0 his / 1 item / 2 scan / 3 hybrid region, index, segment)
pub fn pieces_hyb(pk: &Pack, sh: &Shift) -> Vec<(u64, u64, u8, u32, u16)> {
    let hl = i1::hook_lens(pk);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut pcs: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
    for (k, p) in pk.his.iter().enumerate() { let s = at(p.out); pcs.push((s, s + (p.to - p.from), 0, k as u32, p.seg as u16)); }
    for (k, it) in pk.items.iter().enumerate() { let s = at(it.out); let e = at(it.out + it.n); assert!(e - s == hl[k].unwrap_or(it.n)); pcs.push((s, e, 1, k as u32, pk.seg_of(it.out) as u16)); }
    for (k, sp) in pk.scans.iter().enumerate() { pcs.push((at(sp.out), at(sp.end), 2, k as u32, pk.seg_of(sp.out) as u16)); }
    let lay = hybrid::layout();
    let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
    for &(s, e, k, i, sg) in pcs.iter() {
        let mut parts = vec![(s, e)];
        for r in hybrid::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
        for (a, b) in parts { if b > a { np.push((hybrid::map_pos(a), hybrid::map_pos(b), k, i, sg)); } }
    }
    for (i, (r, l)) in hybrid::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 3, i as u32, r.seg as u16)); }
    np.sort();
    np
}

/// cfdump: the hybrid-spliced assembled list (= the list cf631::splice works on) as raw rows (u16le x 4) + a text meta
/// file (layout, segment maps, pieces, relabelling table re-bound by hybrid::splice).  Heavy (~19 GB RSS).
pub fn dump(dir: &str) {
    let t0 = std::time::Instant::now();
    let (pk, sh, out, n, rt) = assemble::<Row>(true);
    eprintln!("[{:?}] assembled (hybrid on): n {}", t0.elapsed(), n);
    {
        let mut f = std::io::BufWriter::with_capacity(1 << 24, std::fs::File::create(format!("{dir}/asm_on.rows")).unwrap());
        let mut buf: Vec<u8> = Vec::with_capacity(8 << 20);
        for c in out[..n].chunks(1 << 20) { buf.clear(); for r in c { for v in r { buf.extend_from_slice(&v.to_le_bytes()); } } f.write_all(&buf).unwrap(); }
        f.flush().unwrap();
    }
    eprintln!("[{:?}] rows written", t0.elapsed());
    let mut m = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/asm_on.meta")).unwrap());
    writeln!(m, "n {}", n).unwrap();
    for (i, l) in hybrid::layout().iter().enumerate() { writeln!(m, "hyb {} {} {} {} {}", i, l.0, l.1, l.2, l.3).unwrap(); }
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut prev = 0u64;
    for (k, s) in pk.segs.iter().enumerate() {
        let (a, b) = (at(prev), at(s.end)); prev = s.end;
        let mp = |p: u64| -> i64 { if hybrid::REGIONS.iter().any(|r| p > r.start && p < r.end) { -1 } else { hybrid::map_pos(p) as i64 } };
        writeln!(m, "seg {} {} {} {}", k, mp(a), mp(b), s.map.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")).unwrap();
    }
    for p in pieces_hyb(&pk, &sh).iter() {
        if p.2 == 0 { let h = &pk.his[p.3 as usize]; writeln!(m, "piece {} {} {} {} {} his_from {} his_to {} sub {:?}", p.0, p.1, p.2, p.3, p.4, h.from, h.to, h.sub).unwrap(); }
        else { writeln!(m, "piece {} {} {} {} {}", p.0, p.1, p.2, p.3, p.4).unwrap(); }
    }
    let t = rt.expect("relabel table");
    writeln!(m, "rel_n {} rel_hash {:016x} h0 {} entries {}", t.n, t.hash, t.h0, t.ent.len()).unwrap();
    for e in t.ent.iter() { writeln!(m, "rel {} {} {}", e.0, e.1, e.2).unwrap(); }
    m.flush().unwrap();
    eprintln!("[{:?}] meta written", t0.elapsed());
}

/// Check A list (cfcheck): build_slots_hc(false, true, cf) exactly (assemble with the hybrid splice, the cf631 splice when
/// `cf`, relabelling, nonce rows) + in ITS positions: every placed piece (kind 0 his / 1 item / 2 scan / 3 hybrid region /
/// 4 cf631 region), segment ranges, relabelling frames, segment inverse maps, and (cf only) the REFERENCE rows of the two
/// replaced ranges (his records, renamed by the frame in force there) with the final positions of the generated blocks.
pub struct CfBuild { pub rows: Vec<Row>, pub pieces: Vec<(u64, u64, u8, u32, u16)>, pub segs: Vec<(u64, u64)>, pub frames: Vec<(u64, u16)>, pub h0: u16,
    pub inv: Vec<Vec<u16>>, pub refs: Vec<(u64, u64, Vec<Row>)>, pub log: String }
pub fn census_list(cf: bool) -> CfBuild {
    let (pk, sh, mut out, n, rt) = assemble_c::<Row>(true, false);
    let mut log = format!("{}\n", hybrid::LOG.lock().unwrap());
    let mut pcs = pieces_hyb(&pk, &sh);
    let at = |o: u64| (o as i64 + sh.at(o)) as u64;
    let mut segs: Vec<(u64, u64)> = Vec::new(); let mut prev = 0u64;
    let mp = |p: u64| -> u64 { let mut q = p; for r in hybrid::REGIONS.iter() { if q > r.start && q < r.end { q = r.end; } } hybrid::map_pos(q) };
    for s in pk.segs.iter() { segs.push((mp(at(prev)), mp(at(s.end)))); prev = s.end; }
    // the reference rows of the replaced ranges (hybrid-spliced list, before the relabelling)
    let mut refs_raw: Vec<Vec<Row>> = Vec::new();
    let (n, rt) = if cf {
        for r in cf631::REGIONS.iter() { refs_raw.push(out[r.start as usize..r.end as usize].to_vec()); }
        let (n2, rt2) = cf631::splice(&pk, &mut out, n, rt);
        log.push_str(&format!("{}\n", cf631::LOG.lock().unwrap()));
        let lay = cf631::layout();
        let mut np: Vec<(u64, u64, u8, u32, u16)> = Vec::new();
        for &(s, e, k, i, sg) in pcs.iter() {
            let mut parts = vec![(s, e)];
            for r in cf631::REGIONS.iter() { let mut nx = Vec::new(); for &(a, b) in parts.iter() { if b <= r.start || a >= r.end { nx.push((a, b)); continue; } if a < r.start { nx.push((a, r.start)); } if b > r.end { nx.push((r.end, b)); } } parts = nx; }
            for (a, b) in parts { if b > a { np.push((cf631::map_pos(a), cf631::map_pos(b), k, i, sg)); } }
        }
        for (i, (r, l)) in cf631::REGIONS.iter().zip(lay.iter()).enumerate() { np.push((l.2, l.2 + l.3, 4, i as u32, r.seg as u16)); }
        np.sort(); pcs = np;
        let mpc = |p: u64| -> u64 { let mut q = p; for r in cf631::REGIONS.iter() { if q > r.start && q < r.end { q = r.end; } } cf631::map_pos(q) };
        for s in segs.iter_mut() { *s = (mpc(s.0), mpc(s.1)); }
        (n2, rt2)
    } else { (n, rt) };
    let t = rt.as_ref().expect("relabel table");
    let fin = |p: u64| p + hybtools::moves_before(t, p);
    for p in pcs.iter_mut() { p.0 = fin(p.0); p.1 = fin(p.1); }
    for s in segs.iter_mut() { *s = (fin(s.0), fin(s.1)); }
    pcs.sort();
    let frames: Vec<(u64, u16)> = t.ent.iter().map(|e| (fin(e.0), e.1)).collect();
    let mut refs = Vec::new();
    if cf { for (i, l) in cf631::layout().iter().enumerate() {
        let h = hybrid::frame_at(t, l.2); assert!(h == hybrid::frame_at(t, l.2 + l.3 - 1));
        let rows: Vec<Row> = refs_raw[i].iter().map(|r| i1::sigma(*r, h)).collect();
        refs.push((fin(l.2), fin(l.2 + l.3), rows)); log.push_str(&format!("cf region {}: final positions [{}, {}), hidden lane {}, reference rows {}\n", i, fin(l.2), fin(l.2 + l.3), h, refs_raw[i].len())); } }
    let inv: Vec<Vec<u16>> = pk.segs.iter().map(|s| s.inv.clone()).collect();
    let h0 = t.h0;
    let n = i1::apply(&mut out, n, t);
    for i in 0..TAIL { out[n + i] = nonce_row(i, NONCE); }
    out.truncate(n + TAIL);
    CfBuild { rows: out, pieces: pcs, segs, frames, h0, inv, refs, log }
}

/// cfgen (LIGHT, no circuit build): the generator alone.  (1) Identity frame (own wire i -> qubit i, walk[388] = 630), base
/// 10098: SHA3-256 of the ops8 records (u16le kind, then fields, 65535 = none; CCX controls in both orders) = the delivered
/// whole-walk hash?  (2) For segments 2 and 18 (this tree's maps after the W4 patch): counts by kind, Toffolis, lanes named,
/// whether H0's lane or lane 498 is named, HMR bits.
pub fn gen_report() {
    use sha3::{Digest, Sha3_256};
    let t0 = std::time::Instant::now();
    {
        let walk: [crate::circuit::QubitId; 389] = std::array::from_fn(|i| crate::circuit::QubitId(if i < 388 { i as u64 } else { 630 }));
        let pass: [crate::circuit::QubitId; 242] = std::array::from_fn(|k| crate::circuit::QubitId(388 + k as u64));
        let fr = upperwalk_forward631::Frame::new(walk, pass);
        let (mut h1, mut h2) = (Sha3_256::new(), Sha3_256::new()); let mut n = 0u64; let mut buf1: Vec<u8> = Vec::with_capacity(1 << 23); let mut buf2: Vec<u8> = Vec::with_capacity(1 << 23);
        let cost = upperwalk_forward631::forward(&fr, crate::circuit::BitId(10098), |op| { let r = op_to_row(&op);
            let (a, b) = match r[0] { 13 => ([13, r[2], r[1], r[3]], [13, r[1], r[2], r[3]]), _ => (r, r) };
            for v in a { buf1.extend_from_slice(&v.to_le_bytes()); } for v in b { buf2.extend_from_slice(&v.to_le_bytes()); } n += 1;
            if buf1.len() >= 1 << 23 { h1.update(&buf1); h2.update(&buf2); buf1.clear(); buf2.clear(); } });
        h1.update(&buf1); h2.update(&buf2);
        println!("identity frame: {} records (cost: gates {} toffolis {} max capture words {}); SHA3-256 ops8 [13, control1, control2, t]: {:x}; [13, control2, control1, t]: {:x}; [{:?}]",
            n, cost.gates, cost.toffolis, cost.max_capture_words, h1.finalize(), h2.finalize(), t0.elapsed());
    }
    let mut pk = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).expect("pack tables"));
    walkpack::apply(&mut pk); i1::w4_apply(&mut pk);
    for r in cf631::REGIONS.iter() {
        let m = &pk.segs[r.seg].map; let mut kinds = [0u64; 20]; let mut named = vec![0u64; 633]; let mut bits: Vec<u16> = Vec::new();
        let cnt = cf631::gen(m, r.base, &mut |row| { kinds[row[0] as usize] += 1; for j in 1..=qubits(row[0]) { named[row[j] as usize] += 1; } if row[0] == 12 { bits.push(row[2]); } });
        let nl = named.iter().filter(|&&c| c > 0).count();
        let h0 = m[641]; let unnamed: Vec<String> = (0..633).filter(|&l| named[l] == 0).map(|l| format!("{}(id {})", l, pk.segs[r.seg].inv[l] as i32)).collect();
        println!("seg {}: {} rows: X {} CX {} CCX {} HMR {} other {}; lanes named {} (unnamed: {:?}); H0 (id 641) lane {} named {}; lane 498 named {}; lane 632 named {} (holds id {}); HMR bits {:?}..{:?} ({}) [{:?}]",
            r.seg, cnt, kinds[6], kinds[8], kinds[13], kinds[12], cnt - kinds[6] - kinds[8] - kinds[13] - kinds[12], nl, unnamed, h0, named[h0 as usize], named[498], named[632], pk.segs[r.seg].inv[632], bits.first(), bits.last(), bits.len(), t0.elapsed());
    }
}
