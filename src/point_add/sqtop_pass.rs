//! sqtop (switch `SL_SQTOP`; unset or "0" = the gate list byte for byte): the square's
//! inverse-row top carries, built only under the bit that reads them.
//!
//! Shape (every inverse row of the square's triangles whose result top is a known constant, `terminal_step_known`
//! with a previous carry). Wires: the row's top carry C = MAJ at position n-3, built from the folded operands A, S
//! and the carry below it P; the terminal position's addend A2 and accumulator S2; the top T.
//!
//! ```text
//!   k    CCX(A, S -> C)            u    CX(C -> A2)              unfold
//!   k+1  CX(P -> C)                u+1  CX(A2 -> S2)             sum bit of position n-2
//!   k+2  CX(C -> A2)    fold       u+2  CX(P -> C)               unwind
//!   k+3  CX(C -> S2)    fold       u+3  HMR(C -> M)
//!   k+4  HMR(T -> B)    top        u+4  CZ(A, S) if M
//!   R    X(T), Z(T)?B, Z(C)?B, Z(W)?B, CZ(A2, S2)?B (the top's repair)   u+5  R(C)
//! ```
//!
//! S2 is the next inverse row's top: after u+1 it is only written (complement-frame X / CX) until that row measures it
//! (HMR(S2 -> B2) at h) and repairs the kick under B2. So C is read by phases under B and by the value of S2, which
//! only a measurement reads. The rewrite (all exact, every shot, every outcome):
//!   G  S2 is measured where its sum would be written (HMR(S2 -> b2), a fresh bit); the sum and every later write of
//!      the run become phase twins under b2 (CX(x -> S2) -> Z(x)?b2, X(S2) -> NEG?b2); the late HMR at h is deleted and
//!      every op that read B2 there reads b2 (y33's argument with a measured end: the kick of the early measurement
//!      plus the twins is b2 AND the late value).
//!   T  the fold CX(C -> S2) is deleted: the top repair CZ(A2', S2 ^ C) becomes CZ(A2', S2) CZ(A2', C) (A2' = A2 ^ C),
//!      and the fold's twin Z(C)?b2 is paid as Z(P)?b2 CZ(A, S)?b2, because C = P ^ A S (C is 0 before k).
//!   C  C is then read only under the top bit beta, so the CCX and both CX(P -> C) run under beta and the unwind's
//!      fix runs inside PUSH(beta). beta is the early bit b2 of the row above (chain), or for a chain head the top's
//!      own HMR moved to just before k into a fresh bit (T is untouched between, so no random word moves).
//! Saving: one CCX at weight 1/2 per site with a link (w1 -0.5).
//!
//! Modes: "1" full (G + T + C); "g" G only (with the head moves): the same random words in the same order as "1"
//! (no measurement is added, moved or dropped between them), so "1" vs "g" is a word-aligned exactness test.
//! "galign" = "g" with an idle HMR (S2 is 0 there) kept at each late place; "balign" = the base with an idle HMR of
//! T right after each accepted site's top HMR: those two draw the same words in the same order (diagnostic only).
//! `SL_SQTOP_FAULT=z,N | c,N | r,N` (diagnostic only, mode "1"): at accepted site N drop the Z(P)?b2 twin, the
//! CZ(A2', C)?beta term, or the link's run twins.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

struct Site {
    k: usize,
    a: QubitId,
    s: QubitId,
    c: QubitId,
    p: QubitId,
    a2: QubitId,
    s2: QubitId,
    t: QubitId,
    b: BitId,
    cz: usize,
    u: usize,
}

struct Link {
    run: Vec<usize>,
    h: usize,
    win: Vec<usize>,
    wend: usize,
}

fn mk(kind: K, c1: QubitId, t: QubitId, cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = kind;
    o.q_control1 = c1;
    o.q_target = t;
    o.c_condition = cc;
    o
}

fn hmr(t: QubitId, b: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::Hmr;
    o.q_target = t;
    o.c_target = b;
    o
}

fn writes_bit(o: &Op) -> bool {
    matches!(o.kind, K::Hmr | K::BitStore0 | K::BitStore1 | K::BitInvert)
}

fn touches(o: &Op, q: QubitId) -> bool {
    o.q_control1 == q || o.q_control2 == q || o.q_target == q
}

/// The ops that read bit `b` after index `h`, up to its next plain overwrite (and that overwrite's index, or the
/// stream length); None if a write that reads it (BINV, a conditional write) comes first.
fn window(ops: &[Op], depth: &[u32], h: usize, b: BitId) -> Option<(Vec<usize>, usize)> {
    let mut v = Vec::new();
    for (i, o) in ops.iter().enumerate().skip(h + 1) {
        let w = writes_bit(o) && o.c_target == b;
        if o.c_condition == b {
            if w {
                return None;
            }
            v.push(i);
        }
        if w {
            if o.kind == K::BitInvert || depth[i] != 0 || o.c_condition != NO_BIT {
                return None;
            }
            return Some((v, i));
        }
    }
    Some((v, ops.len()))
}

fn mode() -> String {
    std::env::var("SL_SQTOP").unwrap_or_default()
}

fn fault() -> Option<(char, usize)> {
    let v = std::env::var("SL_SQTOP_FAULT").ok()?;
    let (a, b) = v.split_once(',')?;
    Some((a.trim().chars().next()?, b.trim().parse().ok()?))
}

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let m = mode();
    if m.is_empty() || m == "0" {
        return ops;
    }
    assert!(matches!(m.as_str(), "1" | "g" | "galign" | "balign"), "SL_SQTOP: unknown mode {m:?}");
    let full = m == "1";
    let flt = if full { fault() } else { None };
    let n = ops.len();
    let mut depth = vec![0u32; n + 1];
    let mut d = 0u32;
    let mut maxbit = 0u64;
    for (i, o) in ops.iter().enumerate() {
        depth[i] = d;
        match o.kind {
            K::PushCondition => d += 1,
            K::PopCondition => d -= 1,
            _ => {}
        }
        for b in [o.c_target, o.c_condition] {
            if b != NO_BIT {
                maxbit = maxbit.max(b.0);
            }
        }
    }
    depth[n] = d;
    let plain = |i: usize| depth[i] == 0 && ops[i].c_condition == NO_BIT;
    let is_cx = |i: usize, c: QubitId, t: QubitId| i < n && ops[i].kind == K::CX && ops[i].q_control1 == c && ops[i].q_target == t && plain(i);
    // last op touching each wire, for "C is 0 before k" (a plain R or HMR of C, or C never touched)
    let mut last: HashMap<u64, usize> = HashMap::new();
    let mut sites: Vec<Site> = Vec::new();
    let mut shapes = [0usize; 4];
    for k in 0..n {
        let o = ops[k];
        if o.kind == K::CCX && plain(k) && k + 16 < n {
            if let Some(st) = match_site(&ops, &depth, k, &is_cx) {
                let fresh = match last.get(&st.c.0) {
                    None => true,
                    Some(&j) => matches!(ops[j].kind, K::R | K::Hmr) && ops[j].q_target == st.c && depth[j] == 0 && ops[j].c_condition == NO_BIT,
                };
                if fresh {
                    sites.push(st);
                } else {
                    shapes[0] += 1;
                }
            }
        }
        for q in [o.q_control1, o.q_control2, o.q_target] {
            if q != NO_QUBIT {
                last.insert(q.0, k);
            }
        }
    }
    // links: S2 after its sum only written (plain X / CX into it) until a plain HMR of S2
    let mut links: Vec<Option<Link>> = Vec::with_capacity(sites.len());
    for st in &sites {
        let mut run = Vec::new();
        let mut h = None;
        let mut i = st.u + 2;
        while i < n && i < st.u + 400_000 {
            let o = &ops[i];
            if touches(o, st.s2) {
                if o.kind == K::X && o.q_target == st.s2 && plain(i) {
                    run.push(i);
                } else if o.kind == K::CX && o.q_target == st.s2 && o.q_control1 != st.s2 && plain(i) {
                    run.push(i);
                } else if o.kind == K::Hmr && o.q_target == st.s2 && plain(i) {
                    h = Some(i);
                    break;
                } else {
                    break;
                }
            }
            i += 1;
        }
        links.push(h.and_then(|h| window(&ops, &depth, h, ops[h].c_target).map(|(win, wend)| Link { run, h, win, wend })));
    }
    // accept in stream order: beta from a link whose late HMR is this site's top HMR, else a head move
    let mut late: HashMap<usize, BitId> = HashMap::new();
    let mut next = maxbit + 1;
    let mut fresh_bit = || {
        let b = BitId(next);
        next += 1;
        b
    };
    struct Acc {
        site: usize,
        beta: BitId,
        b2: BitId,
        head: Option<Vec<usize>>,
        hend: usize,
    }
    let mut acc: Vec<Acc> = Vec::new();
    let (mut heads, mut chained) = (0usize, 0usize);
    for (si, st) in sites.iter().enumerate() {
        let Some(lk) = &links[si] else { continue };
        let _ = lk;
        let (beta, head, hend) = if let Some(&b) = late.get(&(st.k + 4)) {
            chained += 1;
            (b, None, 0)
        } else {
            let Some((win, hend)) = window(&ops, &depth, st.k + 4, st.b) else { continue };
            heads += 1;
            (fresh_bit(), Some(win), hend)
        };
        let b2 = fresh_bit();
        late.insert(links[si].as_ref().unwrap().h, b2);
        acc.push(Acc { site: si, beta, b2, head, hend });
    }
    // edits: in-place condition changes first, then replacements
    let mut out_ops = ops.clone();
    let mut rep: HashMap<usize, Vec<Op>> = HashMap::new();
    let dummy = if m == "galign" || m == "balign" { Some(fresh_bit()) } else { None };
    for (ai, a) in acc.iter().enumerate() {
        let st = &sites[a.site];
        let lk = links[a.site].as_ref().unwrap();
        if m == "balign" {
            // the base with an idle measurement of T (0 right after its HMR) where "g" measures S2
            rep.insert(st.k + 4, vec![ops[st.k + 4], hmr(st.t, dummy.unwrap())]);
            continue;
        }
        if let Some(win) = &a.head {
            for &i in win {
                out_ops[i].c_condition = a.beta;
            }
        }
        for &i in &lk.win {
            out_ops[i].c_condition = a.b2;
        }
        if full {
            out_ops[st.k].c_condition = a.beta;
            out_ops[st.k + 1].c_condition = a.beta;
            out_ops[st.u + 2].c_condition = a.beta;
        }
        let _ = ai;
    }
    if m != "balign" {
        for (ai, a) in acc.iter().enumerate() {
            let st = &sites[a.site];
            let lk = links[a.site].as_ref().unwrap();
            let f = |c: char| flt == Some((c, ai));
            // head move: the top measured just before k into beta (T untouched between, no HMR/R between)
            if a.head.is_some() {
                rep.insert(st.k, vec![hmr(st.t, a.beta), out_ops[st.k]]);
                rep.insert(st.k + 4, vec![]);
            }
            if full {
                rep.insert(st.k + 3, vec![]);
                if !f('c') {
                    rep.insert(st.cz, vec![out_ops[st.cz], mk(K::CZ, st.a2, st.c, a.beta)]);
                }
                let mut fix = Vec::new();
                let mut push = Op::empty();
                push.kind = K::PushCondition;
                push.c_condition = a.beta;
                let mut pop = Op::empty();
                pop.kind = K::PopCondition;
                fix.push(push);
                fix.push(out_ops[st.u + 4]);
                fix.push(pop);
                rep.insert(st.u + 4, fix);
                let mut tw = Vec::new();
                if !f('z') {
                    tw.push(mk(K::Z, NO_QUBIT, st.p, a.b2));
                }
                tw.push(mk(K::CZ, st.a, st.s, a.b2));
                tw.push(out_ops[st.u + 5]);
                rep.insert(st.u + 5, tw);
            }
            // G: early measurement of S2 where its sum was written; the sum and the run become twins under b2
            rep.insert(st.u + 1, vec![hmr(st.s2, a.b2), mk(K::Z, NO_QUBIT, st.a2, a.b2)]);
            if !f('r') {
                for &i in &lk.run {
                    let o = ops[i];
                    let tw = if o.kind == K::X {
                        let mut g = Op::empty();
                        g.kind = K::Neg;
                        g.c_condition = a.b2;
                        g
                    } else {
                        mk(K::Z, NO_QUBIT, o.q_control1, a.b2)
                    };
                    rep.insert(i, vec![tw]);
                }
            } else {
                for &i in &lk.run {
                    rep.insert(i, vec![]);
                }
            }
            let late_op = if m == "galign" { vec![hmr(st.s2, dummy.unwrap())] } else { vec![] };
            assert!(!rep.contains_key(&lk.h) || rep[&lk.h].is_empty(), "sqtop: late HMR edited twice");
            rep.insert(lk.h, late_op);
        }
    }
    if std::env::var("SL_SQTOP_DUMP").is_ok_and(|v| v == "1") {
        // check slices: for each accepted site, input indices and the output index where each input index starts
        let mut start = vec![0usize; n + 1];
        let mut c = 0usize;
        for i in 0..n {
            start[i] = c;
            c += rep.get(&i).map_or(1, |r| r.len());
        }
        start[n] = c;
        let mut s = String::from("site	head	k	cz	u	h	wend	hend	beta	b2	c	nrun	ok	ou6	oh	owend	ohend
");
        for (ai, a) in acc.iter().enumerate() {
            let st = &sites[a.site];
            let lk = links[a.site].as_ref().unwrap();
            s += &format!(
                "{ai}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}	{}
",
                a.head.is_some() as u8, st.k, st.cz, st.u, lk.h, lk.wend, a.hend, a.beta.0, a.b2.0, st.c.0, lk.run.len(),
                start[st.k], start[st.u + 6], start[lk.h], start[lk.wend.min(n)], start[a.hend.min(n)]
            );
        }
        std::fs::write("sqtop_sites.tsv", s).expect("sqtop: write sqtop_sites.tsv");
    }
    let mut out = Vec::with_capacity(n + 8 * acc.len());
    for (i, o) in out_ops.iter().enumerate() {
        match rep.get(&i) {
            Some(r) => out.extend_from_slice(r),
            None => out.push(*o),
        }
    }
    for o in &out {
        o.validate();
    }
    eprintln!(
        "SQTOP mode={m} sites={} dirty_c={} links={} accepted={} heads={heads} chained={chained} dw1_est={:.1} ops {n} -> {}",
        sites.len(),
        shapes[0],
        links.iter().filter(|l| l.is_some()).count(),
        acc.len(),
        if full { -0.5 * acc.len() as f64 } else { 0.0 },
        out.len()
    );
    out
}

/// The site shape at CCX k (see the module doc), or None.
fn match_site(ops: &[Op], depth: &[u32], k: usize, is_cx: &dyn Fn(usize, QubitId, QubitId) -> bool) -> Option<Site> {
    let plain = |i: usize| depth[i] == 0 && ops[i].c_condition == NO_BIT;
    let x = ops[k];
    let (a, s, c) = (x.q_control2, x.q_control1, x.q_target);
    let o1 = ops[k + 1];
    if !(o1.kind == K::CX && o1.q_target == c && plain(k + 1)) {
        return None;
    }
    let p = o1.q_control1;
    let o2 = ops[k + 2];
    if !(o2.kind == K::CX && o2.q_control1 == c && plain(k + 2)) {
        return None;
    }
    let a2 = o2.q_target;
    let o3 = ops[k + 3];
    if !(o3.kind == K::CX && o3.q_control1 == c && plain(k + 3)) {
        return None;
    }
    let s2 = o3.q_target;
    let o4 = ops[k + 4];
    if !(o4.kind == K::Hmr && plain(k + 4)) {
        return None;
    }
    let (t, b) = (o4.q_target, o4.c_target);
    let ws = [a, s, c, p, a2, s2, t];
    for i in 0..ws.len() {
        for j in 0..i {
            if ws[i] == ws[j] {
                return None;
            }
        }
    }
    // the top's repair block, up to the unfold CX(C -> A2)
    let mut i = k + 5;
    let mut cz = None;
    while i < k + 12 {
        let o = ops[i];
        if is_cx(i, c, a2) {
            break;
        }
        if depth[i] != 0 {
            return None;
        }
        let ok = match o.kind {
            K::X => o.q_target == t && o.c_condition == NO_BIT,
            K::Z => o.c_condition == b && (o.q_target == t || o.q_target == c || !ws.contains(&o.q_target)),
            K::CZ => {
                o.c_condition == b
                    && cz.is_none()
                    && ((o.q_control1 == a2 && o.q_target == s2) || (o.q_control1 == s2 && o.q_target == a2))
            }
            _ => false,
        };
        if !ok {
            return None;
        }
        if o.kind == K::CZ {
            cz = Some(i);
        }
        i += 1;
    }
    let cz = cz?;
    let u = i;
    if !is_cx(u, c, a2) || !is_cx(u + 1, a2, s2) || !is_cx(u + 2, p, c) {
        return None;
    }
    let o = ops[u + 3];
    if !(o.kind == K::Hmr && o.q_target == c && plain(u + 3)) {
        return None;
    }
    let mb = o.c_target;
    let o = ops[u + 4];
    if !(o.kind == K::CZ && o.c_condition == mb && depth[u + 4] == 0
        && ((o.q_control1 == a && o.q_target == s) || (o.q_control1 == s && o.q_target == a)))
    {
        return None;
    }
    let o = ops[u + 5];
    if !(o.kind == K::R && o.q_target == c && plain(u + 5)) {
        return None;
    }
    if !is_cx(u + 6, p, a) || !is_cx(u + 7, a, s) {
        return None;
    }
    Some(Site { k, a, s, c, p, a2, s2, t, b, cz, u })
}
