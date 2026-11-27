//! w4 lane patch for the his pieces ((internal)/(internal)). A child module of a q633a-style `point_add`.
//! Text table, one command per line (applied in this order: all `split`, then all `sub`, then all `map`):
//!   split X            split the his piece that contains input position X (from < X < to) at X
//!   sub FROM F T       add the substitution F -> T (logical ids) to the his piece whose `from` is FROM
//!                      (an existing substitution of F in that piece is replaced)
//!   resub FROM F T     replace the target of the existing substitution F -> * of piece FROM by T
//!   map S ID LANE      set segment S's map of logical ID to LANE (-1 = unmapped)
//! Lines starting with '#' are comments.  The segment inverse maps are rebuilt and checked (injective, lanes < 633).
use super::*;

pub fn apply(pk: &mut Pack, text: &str) {
    let mut splits: Vec<u64> = Vec::new(); let mut subs: Vec<(u64, u16, u16, bool)> = Vec::new(); let mut maps: Vec<(usize, usize, i64)> = Vec::new();
    for line in text.lines() { let l = line.trim(); if l.is_empty() || l.starts_with('#') { continue; }
        let f: Vec<&str> = l.split_whitespace().collect();
        match f[0] {
            "split" => splits.push(f[1].parse().unwrap()),
            "sub" => subs.push((f[1].parse().unwrap(), f[2].parse().unwrap(), f[3].parse().unwrap(), false)),
            "resub" => subs.push((f[1].parse().unwrap(), f[2].parse().unwrap(), f[3].parse().unwrap(), true)),
            "map" => maps.push((f[1].parse().unwrap(), f[2].parse().unwrap(), f[3].parse().unwrap())),
            _ => panic!("w4patch: bad line {}", l),
        } }
    splits.sort(); splits.dedup();
    for x in splits { let k = pk.his.partition_point(|p| p.to <= x); assert!(k < pk.his.len() && pk.his[k].from <= x, "w4patch: split {} outside the pieces", x);
        if pk.his[k].from == x { continue; }
        let p = &pk.his[k]; let (from, to, out, sub, seg) = (p.from, p.to, p.out, p.sub.clone(), p.seg);
        pk.his[k] = HisPiece { from, to: x, out, sub: sub.clone(), seg };
        pk.his.insert(k + 1, HisPiece { from: x, to, out: out + (x - from), sub, seg }); }
    for (fr, a, b, re) in subs { let k = pk.his.partition_point(|p| p.to <= fr); assert!(k < pk.his.len() && pk.his[k].from == fr, "w4patch: no piece starts at {}", fr);
        let s = &mut pk.his[k].sub;
        // a NEW target must not be a target already (the copy reader inverts the table); `resub` keeps the piece's own sharing pattern
        if !re { assert!(!s.iter().any(|e| e.1 == b && e.0 != a), "w4patch: new substitution {} -> {} reuses a target in piece {}", a, b, fr); }
        if let Some(e) = s.iter_mut().find(|e| e.0 == a) { e.1 = b; } else { assert!(!re, "w4patch: resub of a missing substitution {} in piece {}", a, fr); s.push((a, b)); } }
    let mut touched = vec![false; pk.segs.len()];
    for (s, id, lane) in maps { pk.segs[s].map[id] = if lane < 0 { NONE } else { lane as u16 }; touched[s] = true; }
    for (s, sg) in pk.segs.iter_mut().enumerate() { if !touched[s] { continue; } let mut inv = vec![NONE; 633];
        for (id, &l) in sg.map.iter().enumerate() { if l != NONE { assert!((l as usize) < 633 && inv[l as usize] == NONE, "w4patch: lane map of segment {} not injective at lane {}", s, l); inv[l as usize] = id as u16; } }
        sg.inv = inv; }
}
