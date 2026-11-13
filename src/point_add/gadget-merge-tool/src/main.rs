// gmerge apply IN OUT   : apply gadget_merge to a flat little-endian [u16;4] gate list
// gmerge selftest       : exhaustive equivalence checks of the rewrite on small random circuits
include!("../../gadget_merge.rs");
use std::io::{Read, Write};
type Row = [u16; 4];
fn sim(rows: &[Row], mut s: u32) -> u32 {
    for r in rows { match r[0] { 13 => { if (s >> r[1]) & (s >> r[2]) & 1 == 1 { s ^= 1 << r[3]; } } 8 => { if (s >> r[1]) & 1 == 1 { s ^= 1 << r[2]; } } 6 => { s ^= 1 << r[1]; } _ => panic!() } }
    s
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a[1].as_str() {
        "apply" => {
            let mut f = std::fs::File::open(&a[2]).unwrap();
            let n = (f.metadata().unwrap().len() / 8) as usize;
            let mut rows: Vec<Row> = vec![[0u16; 4]; n];
            let bytes = unsafe { std::slice::from_raw_parts_mut(rows.as_mut_ptr() as *mut u8, n * 8) };
            f.read_exact(bytes).unwrap();
            let c0 = rows.iter().filter(|r| r[0] == 13).count();
            let (chains, removed) = gadget_merge(&mut rows, |r| *r, |r| r);
            let c1 = rows.iter().filter(|r| r[0] == 13).count();
            eprintln!("chains {} toffolis removed {} | ops {} -> {} | static ccx {} -> {}", chains, removed, n, rows.len(), c0, c1);
            assert_eq!(c0 - c1, removed as usize);
            let mut o = std::io::BufWriter::with_capacity(1 << 24, std::fs::File::create(&a[3]).unwrap());
            let bytes = unsafe { std::slice::from_raw_parts(rows.as_ptr() as *const u8, rows.len() * 8) };
            o.write_all(bytes).unwrap();
        }
        "selftest" => {
            // xorshift rng
            let mut x = 0x9E3779B97F4A7C15u64;
            let mut rnd = |m: u64| -> u64 { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x % m };
            let nw = 9u16; // wires 0..8
            let (mut tested, mut fired, mut chains_tot) = (0u64, 0u64, 0u64);
            for it in 0..1_500_000u64 {
                // build a random chain-like circuit: U1 T U1 (T Ui T Ui)* with random wires, plus random junk around it
                let mut rows: Vec<Row> = Vec::new();
                let junk = |rows: &mut Vec<Row>, rnd: &mut dyn FnMut(u64) -> u64| { for _ in 0..rnd(3) { let k = rnd(3); let (p, q, t) = (rnd(nw as u64) as u16, rnd(nw as u64) as u16, rnd(nw as u64) as u16);
                    if k == 0 && p != q && p != t && q != t { rows.push([13, p, q, t]); } else if k == 1 && p != q { rows.push([8, p, q, 65535]); } else if k == 2 { rows.push([6, p, 65535, 65535]); } } };
                junk(&mut rows, &mut rnd);
                let (c1, c2, d) = (rnd(nw as u64) as u16, rnd(nw as u64) as u16, rnd(nw as u64) as u16);
                if c1 == c2 || c1 == d || c2 == d { continue; }
                let t = [13, c1, c2, d];
                let mk = |rnd: &mut dyn FnMut(u64) -> u64| -> Option<Row> { let (xx, tg) = (rnd(nw as u64) as u16, rnd(nw as u64) as u16); if xx == d || tg == d || xx == tg { return None; } Some(if rnd(2) == 0 { [13, d, xx, tg] } else { [13, xx, d, tg] }) };
                let Some(u1) = mk(&mut rnd) else { continue };
                if rnd(4) == 0 { rows.push(t); }
                rows.push(u1); rows.push(t); rows.push(u1);
                let units = 1 + rnd(3);
                for _ in 0..units {
                    // bias towards mergeable units: reuse target or x of u1
                    let ui = if rnd(4) != 0 { let x1 = if u1[1] == d { u1[2] } else { u1[1] }; let t1 = u1[3];
                        if rnd(2) == 0 { let xx = rnd(nw as u64) as u16; if xx == d || xx == t1 { continue; } [13, d, xx, t1] } else { let tg = rnd(nw as u64) as u16; if tg == d || tg == x1 { continue; } [13, x1, d, tg] } }
                        else { match mk(&mut rnd) { Some(u) => u, None => continue } };
                    rows.push(t); rows.push(ui); rows.push(t); rows.push(ui);
                }
                if rnd(3) == 0 { rows.push(t); }
                // sometimes append a mirror chain: T1 U T1 (U Ti U Ti)* with T_i sharing a control with T
                if rnd(2) == 0 {
                    let uu = u1; rows.push(t); rows.push(uu); rows.push(t);
                    for _ in 0..(1 + rnd(3)) {
                        let bi = rnd(nw as u64) as u16; let sh = if rnd(2) == 0 { c1 } else { c2 };
                        if bi == sh || bi == d { continue; }
                        let ti = if rnd(2) == 0 { [13, sh, bi, d] } else { [13, bi, sh, d] };
                        rows.push(uu); rows.push(ti); rows.push(uu); rows.push(ti);
                    }
                    if rnd(3) == 0 { rows.push(uu); }
                }
                junk(&mut rows, &mut rnd);
                let mut new = rows.clone();
                let (ch, rem) = gadget_merge(&mut new, |r| *r, |r| r);
                tested += 1; if ch > 0 { fired += 1; chains_tot += ch; }
                let c0 = rows.iter().filter(|r| r[0] == 13).count(); let c1n = new.iter().filter(|r| r[0] == 13).count();
                assert_eq!(c0 - c1n, rem as usize);
                for s in 0..(1u32 << nw) { if sim(&rows, s) != sim(&new, s) { panic!("MISMATCH it {} state {:b}\n old {:?}\n new {:?}", it, s, rows, new); } }
            }
            println!("selftest: {} circuits, {} with a rewrite ({} chains), all {} basis states equal on each", tested, fired, chains_tot, 1u32 << nw);
        }
        _ => panic!("usage"),
    }
}
