//! (internal) (internal) (internal) ((internal)): analysis modes and the loop-enable redesign for ITEM 12 / ITEM 2.
//! Child module of a COPY of the 633 tree's point_add (next to w2.rs / w2rw.rs, which it reuses).
use super::*;
use super::w2::*;



/// f-controlled Fredkin chain starting at i: CX(s,x) CCX(f,x,s) CX(s,x) repeated with one s; returns (slot, elements, end index)
pub fn chain_at(rows: &[Row], i: usize, f: u16) -> Option<(u16, Vec<u16>, usize)> {
    let mut xs = Vec::new(); let mut j = i; let mut s = NONE;
    while j + 2 < rows.len() { let (a, b, c) = (rows[j], rows[j + 1], rows[j + 2]);
        if a[0] != 8 || a[3] != NONE || c != a || b[0] != 13 { break; }
        let (sl, x) = (a[1], a[2]); if s != NONE && sl != s { break; }
        if !(b[3] == sl && ((b[1] == f && b[2] == x) || (b[2] == f && b[1] == x))) { break; }
        s = sl; xs.push(x); j += 3; }
    if xs.len() >= 4 { Some((s, xs, j)) } else { None }
}
pub fn touches(r: &Row, w: u16) -> bool { (1..=qubits(r[0])).any(|j| r[j] == w) }
fn targets(r: &Row, w: u16) -> bool { let nq = qubits(r[0]); nq > 0 && matches!(r[0], 6 | 8 | 13) && r[nq] == w }




