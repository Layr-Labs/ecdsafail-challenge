// Gadget merging (exact). Rows are [kind, a, b, c]; kind 13 = CCX(a, b -> c), kind 8 = CX(a -> b), 65535 = none.
//
// A dirty-borrow toggle gadget computes a triply-controlled NOT through a borrowed wire d in any state:
//     U T U,  T = CCX(c1, c2 -> d),  U = CCX(d, x -> t)   gives   t ^= c1&c2&x   and   d ^= c1&c2
// (and  T U T U  gives the same with d restored). The generator often emits several such gadgets in a row on the
// same T. A contiguous chain
//     U1 T U1   T U2 T U2   T U3 T U3  ...                                   (3 + 4m Toffolis)
// is replaced by one gadget wrapped in CX gates                               (3 Toffolis, 2m CX):
//   type A, same target t, different x:   t ^= p&x1 ^ p&x2 ^ ... = p&(x1^x2^...)   with p = c1&c2
//           CX(x2->x1) .. CX(xm->x1)   U1 T U1   CX(x2->x1) .. CX(xm->x1)
//   type B, same x, different targets:    every ti ^= p&x
//           CX(t1->t2) .. CX(t1->tm)   U1 T U1   CX(t1->t2) .. CX(t1->tm)
// The odd number of T gates in the chain (1 + 2m) and the single T of the replacement leave d ^= p in both.
// The mirror image, with U fixed and T varying, is merged the same way:
//     T1 U T1   U T2 U T2   U T3 U T3  ...     gives   t ^= (d ^ p1 ^ p2 ^ ...)&x   with d restored
//   type C, T_i = CCX(a, b_i -> d) sharing the control a:   p1 ^ p2 ^ ... = a&(b1 ^ b2 ^ ...)
//           CX(b2->b1) .. CX(bm->b1)   T1 U T1   CX(b2->b1) .. CX(bm->b1)
// Side conditions (checked below): all rows are unconditioned CCX and adjacent, so they run in one condition context;
// every U has d as a control, its other control x and its target t are not wires of T's target d, t is not a control
// of T; type A also needs x1 not to be a control of T (x1 is modified while T runs) and x_i != x1; type B needs
// t_i != t1 and t_i not in {c1, c2, d, x}. Every identity is a permutation of basis states, so there is no phase.
// Returns (chains rewritten, Toffolis removed).
pub fn gadget_merge<T: Copy>(v: &mut Vec<T>, row: impl Fn(&T) -> [u16; 4], make: impl Fn([u16; 4]) -> T) -> (u64, u64) {
    let n = v.len();
    let (mut r, mut w) = (0usize, 0usize);
    let (mut chains, mut removed) = (0u64, 0u64);
    // other control and target of a U gate for toggle wire d; None if the row is not a valid U for T = (c1, c2 -> d)
    let parse = |u: [u16; 4], t: [u16; 4]| -> Option<(u16, u16)> {
        if u[0] != 13 || t[0] != 13 { return None; }
        let (c1, c2, d) = (t[1], t[2], t[3]);
        let x = if u[1] == d { u[2] } else if u[2] == d { u[1] } else { return None; };
        let tg = u[3];
        if x == d || tg == d || tg == c1 || tg == c2 || tg == x || c1 == d || c2 == d { return None; }
        Some((x, tg))
    };
    let mut ext: Vec<u16> = Vec::new();
    while r < n {
        if r + 6 < n {
            let u1 = row(&v[r]);
            if u1[0] == 13 {
                let t = row(&v[r + 1]);
                if t[0] == 13 && row(&v[r + 2]) == u1 {
                    if let Some((x1, t1)) = parse(u1, t) {
                        let (c1, c2) = (t[1], t[2]);
                        ext.clear();
                        let mut kind = 0u8; // 1 = type A, 2 = type B
                        let mut j = r + 3;
                        while j + 3 < n {
                            if row(&v[j]) != t || row(&v[j + 2]) != t { break; }
                            let ui = row(&v[j + 1]);
                            if row(&v[j + 3]) != ui { break; }
                            let Some((xi, ti)) = parse(ui, t) else { break };
                            let a_ok = ti == t1 && xi != x1 && x1 != c1 && x1 != c2;
                            let b_ok = xi == x1 && ti != t1;
                            if kind == 0 { kind = if a_ok { 1 } else if b_ok { 2 } else { 0 }; if kind == 0 { break; } }
                            else if (kind == 1 && !a_ok) || (kind == 2 && !b_ok) { break; }
                            ext.push(if kind == 1 { xi } else { ti });
                            j += 4;
                        }
                        if !ext.is_empty() {
                            let m = ext.len();
                            debug_assert!(w + 2 * m + 3 <= j);
                            let (tr, ur) = (v[r + 1], v[r]);
                            for &e in ext.iter() { v[w] = make(if kind == 1 { [8, e, x1, 65535] } else { [8, t1, e, 65535] }); w += 1; }
                            v[w] = ur; v[w + 1] = tr; v[w + 2] = ur; w += 3;
                            for &e in ext.iter() { v[w] = make(if kind == 1 { [8, e, x1, 65535] } else { [8, t1, e, 65535] }); w += 1; }
                            chains += 1; removed += 4 * m as u64; // each merged unit T Ui T Ui disappears
                            r = j;
                            continue;
                        }
                    }
                }
            }
        }
        if r + 6 < n {
            let t1 = row(&v[r]);
            if t1[0] == 13 {
                let u = row(&v[r + 1]);
                if u[0] == 13 && row(&v[r + 2]) == t1 {
                    if let Some((x, tg)) = parse(u, t1) {
                        let d = t1[3];
                        ext.clear();
                        let (mut a, mut b1) = (65535u16, 65535u16);
                        let mut j = r + 3;
                        while j + 3 < n {
                            if row(&v[j]) != u || row(&v[j + 2]) != u { break; }
                            let ti = row(&v[j + 1]);
                            if row(&v[j + 3]) != ti || ti[0] != 13 || ti[3] != d || ti == t1 { break; }
                            if parse(u, ti).is_none() { break; }
                            // shared control a, differing controls b1 (of T1) and bi (of Ti)
                            let (sa, sb1, bi) = if ti[1] == t1[1] { (t1[1], t1[2], ti[2]) } else if ti[2] == t1[2] { (t1[2], t1[1], ti[1]) }
                                else if ti[1] == t1[2] { (t1[2], t1[1], ti[2]) } else if ti[2] == t1[1] { (t1[1], t1[2], ti[1]) } else { break };
                            if a == 65535 { a = sa; b1 = sb1; } else if sa != a { break; }
                            // b1 is modified while T1 U T1 runs: it must not be read or written by U; bi is only read
                            if bi == b1 || bi == a || b1 == a || b1 == x || b1 == tg || b1 == d || bi == d || bi == tg { break; }
                            ext.push(bi);
                            j += 4;
                        }
                        if !ext.is_empty() {
                            let m = ext.len();
                            debug_assert!(w + 2 * m + 3 <= j);
                            let (ur, tr) = (v[r + 1], v[r]);
                            for &e in ext.iter() { v[w] = make([8, e, b1, 65535]); w += 1; }
                            v[w] = tr; v[w + 1] = ur; v[w + 2] = tr; w += 3;
                            for &e in ext.iter() { v[w] = make([8, e, b1, 65535]); w += 1; }
                            chains += 1; removed += 4 * m as u64;
                            r = j;
                            continue;
                        }
                    }
                }
            }
        }
        v[w] = v[r]; w += 1; r += 1;
    }
    v.truncate(w);
    (chains, removed)
}
