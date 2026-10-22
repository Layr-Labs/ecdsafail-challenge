// ======================================================================================================================
// round17 a2-build (M3): lever A on the rails. The A decision (e <= 7 with the per-rail (3,1) record: one e >= 4 event
// per same-rail triple {6g + r, 6g + r + 2, 6g + r + 4}), the record (2-bit field per triple, codes 1, 2, 3 by
// position), the k-letter erase with k3, the switch. Tick 0 (e <= 3, main's tick-0 machinery) and the last tick (the
// walk caps it at e <= 3: main's terminal kernels and endpoint) stay main's.
// ======================================================================================================================
/// Lever A's walk is this tree's build (ticks 1 ..= R - 2 run A ticks); LFA2=0 restores main's walk (research only).
pub(crate) const A2_DEFAULT: bool = true;
pub(super) fn a2_on() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| match std::env::var("LFA2") {
        Ok(v) => v == "1",
        Err(_) => A2_DEFAULT,
    })
}
/// Tick t runs as an A tick (k3 exists).
pub(super) fn a2_tick(t: usize) -> bool { a2_on() && t >= 1 && t + 1 < rounds() }
/// The A fold's digit cap on tick t (LFA2_EMAX, default 7).
pub(super) fn a2_emax(_t: usize) -> usize {
    static V: OnceLock<usize> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_EMAX").ok().and_then(|v| v.parse().ok()).unwrap_or(7))
}
fn a2_tid(t: usize) -> usize { (t / 6) * 2 + t % 2 }
fn a2_pos(t: usize) -> usize { (t % 6) / 2 + 1 }
thread_local! {
    /// The record's fields by triple id: [f0, f1] (None once consumed by the reverse).
    static A2_REC: std::cell::RefCell<std::collections::HashMap<usize, [Option<QubitId>; 2]>> = std::cell::RefCell::new(std::collections::HashMap::new());
}
/// The field of tick t's triple; at its first tick (forward) the two wires are allocated.
fn a2_field_open(c: &mut Builder, t: usize) -> [QubitId; 2] {
    let id = a2_tid(t);
    let f = A2_REC.with(|r| r.borrow().get(&id).copied());
    match f {
        Some([Some(a), Some(b)]) => [a, b],
        None => {
            // a triple opens at its first A tick: position 1, or position 2 for rail 0's first triple (tick 0 is not
            // an A tick; its f0 stays 0)
            assert!(a2_pos(t) == 1 || t == 2, "a2: tick {t} opens its triple's field but is not its first A tick");
            let w = [c.alloc_qubit(), c.alloc_qubit()];
            A2_REC.with(|r| r.borrow_mut().insert(id, [Some(w[0]), Some(w[1])]));
            w
        }
        _ => panic!("a2: tick {t}'s field is partly consumed"),
    }
}
fn a2_field(t: usize) -> [Option<QubitId>; 2] {
    A2_REC.with(|r| r.borrow().get(&a2_tid(t)).copied()).unwrap_or_else(|| panic!("a2: tick {t} has no record field"))
}
/// spent(t): an e >= 4 event at an earlier position of t's triple, as a linear form of the field (written at
/// positions < pos(t) only): pos 1: 0; pos 2: f0; pos 3: f0 ^ f1.
fn a2_spent(t: usize) -> Lin {
    // position 1, or rail 0's first triple at position 2 (its position-1 tick is tick 0: never an event)
    if a2_pos(t) == 1 || t == 2 {
        return Lin::k(false);
    }
    let f = a2_field(t);
    match a2_pos(t) {
        1 => Lin::k(false),
        2 => Lin::of(&[f[0].expect("a2: f0")]),
        _ => Lin::of(&[f[0].expect("a2: f0"), f[1].expect("a2: f1")]),
    }
}
/// [f == code(pos t)] as two literal forms (code 1 = (1,0), 2 = (0,1), 3 = (1,1)). A slot the reverse already
/// consumed (f1 after its position 2) reads as the constant 0.
fn a2_code_forms(t: usize) -> (Lin, Lin) {
    let f = a2_field(t);
    let lit = |q: Option<QubitId>, want: bool| match q {
        Some(w) => Lin { w: vec![w], one: !want },
        None => Lin::k(!want),
    };
    match a2_pos(t) {
        1 => (lit(f[0], true), lit(f[1], false)),
        2 => (lit(f[0], false), lit(f[1], true)),
        _ => (lit(f[0], true), lit(f[1], true)),
    }
}
/// a & b of two literal forms onto a fresh wire (1 AND, or a CNOT copy when one side is the constant 1).
fn a2_and_forms(c: &mut Builder, a: &Lin, b: &Lin) -> QubitId {
    match (a.w.is_empty(), b.w.is_empty()) {
        (false, false) => lin_and(c, a, b),
        (true, true) => {
            let q = c.alloc_qubit();
            if a.one && b.one { c.x(q); }
            q
        }
        _ => {
            let (k, v) = if a.w.is_empty() { (a, b) } else { (b, a) };
            let q = c.alloc_qubit();
            if k.one { lin_xor_into(c, v, q); }
            q
        }
    }
}
/// The phase (-1)^(a & b) of two literal forms under the condition bit m.
fn a2_cz_forms_if(c: &mut Builder, a: &Lin, b: &Lin, m: crate::circuit::BitId) {
    match (a.w.is_empty(), b.w.is_empty()) {
        (false, false) => {
            let (ha, hb) = lin_pair_on(c, a, b);
            c.cz_if(ha, hb, m);
            lin_pair_off(c, a, b);
        }
        (true, true) => assert!(!(a.one && b.one), "a2: a constant 1 code"),
        _ => {
            let (k, v) = if a.w.is_empty() { (a, b) } else { (b, a) };
            if k.one {
                let h = v.w[0];
                lin_on(c, v, h);
                c.z_if(h, m);
                lin_off(c, v, h);
            }
        }
    }
}
/// Writer: field ^= code(pos t) * k3 (CNOTs).
fn a2_write(c: &mut Builder, t: usize, k3: QubitId) {
    let f = a2_field(t);
    let p = a2_pos(t);
    if p != 2 { c.cx(k3, f[0].unwrap()); }
    if p != 1 { c.cx(k3, f[1].unwrap()); }
}
/// MBU erase of a k3 wire against the field (k3 = [f == code(pos t)] once t's write is in): free.
fn a2_k3_erase_rec(c: &mut Builder, t: usize, k3: QubitId) {
    let (a, b) = a2_code_forms(t);
    let m = c.alloc_bit();
    c.hmr(k3, m);
    c.release_clean(k3);
    a2_cz_forms_if(c, &a, &b, m);
    c.free_bit(m);
}
/// Non-consuming read: k3 = [f == code(pos t)] on a fresh wire (1 AND); erase it with [`a2_k3_erase_rec`].
fn a2_read(c: &mut Builder, t: usize) -> QubitId {
    let (a, b) = a2_code_forms(t);
    a2_and_forms(c, &a, &b)
}
/// Consuming read (reverse rails pass, positions 3, 2, 1 in that order): pos 3: k3 = f0 f1 (1 AND), then the
/// field un-written (f ^= 3 k3); pos 2: k3 is f1 itself; pos 1: k3 is f0 itself (the field leaves with it). The
/// returned wire is erased by the k-letter erase against the rail.
fn a2_consume(c: &mut Builder, t: usize) -> QubitId {
    let id = a2_tid(t);
    let f = a2_field(t);
    match a2_pos(t) {
        3 => {
            let (f0, f1) = (f[0].unwrap(), f[1].unwrap());
            let q = and_new(c, f0, f1);
            c.cx(q, f0);
            c.cx(q, f1);
            q
        }
        2 if t == 2 => {
            // rail 0's first triple: no position-1 A tick, so f0 (always 0) leaves here
            A2_REC.with(|r| r.borrow_mut().remove(&id));
            c.release_clean(f[0].expect("a2: f0"));
            f[1].expect("a2: f1 consumed twice")
        }
        2 => {
            A2_REC.with(|r| r.borrow_mut().get_mut(&id).unwrap()[1] = None);
            f[1].expect("a2: f1 consumed twice")
        }
        _ => {
            // a triple cut by the walk's end (its position-2 tick is not an A tick): f1 was never written
            if let Some(f1) = f[1] {
                assert!(!a2_tick(t + 2), "a2: the field's f1 outlived its position 2");
                c.release_clean(f1);
            }
            A2_REC.with(|r| r.borrow_mut().remove(&id));
            f[0].expect("a2: f0 consumed twice")
        }
    }
}
/// The A width table: LFA2_TABLE (a P2 refit table file) or the embedded build table.
fn a2_table_text() -> String {
    match std::env::var("LFA2_TABLE") {
        Ok(p) => std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("a2: LFA2_TABLE {p}: {e}")),
        Err(_) => include_str!("leapfrog_data/a2_R122_steps.txt").to_string(),
    }
}
/// The A window anchors: LFA2_ANCH, or LFA2_TABLE + ".anch", or the embedded ones.
fn a2_anch_text() -> String {
    let p = std::env::var("LFA2_ANCH").ok().or_else(|| std::env::var("LFA2_TABLE").ok().map(|t| t + ".anch"));
    match p {
        Some(p) => std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("a2: anchors {p}: {e}")),
        None => include_str!("leapfrog_data/a2_R122_anch.txt").to_string(),
    }
}
/// Recipe entries of lever A's walk (after main's recipe): the per-rail spec's window schedule (L = 22 at tick 0,
/// 13 from 1, 17 from 4, 22 from 9, 19 from 81, 17 from 91, 15 from 102, 13 from 107, 11 from 113).
fn a2_recipe() {
    // tick-indexed boundaries of main's recipe moved to A's 122 ticks: the divide's payload-only/fused split by
    // payload fraction (42 -> 37; flat within +-10 T over 33..45), the multiply's re-picked by builder sweep (49:
    // -1,218 T against 67; 45..49 within 100 T), the N2 batch from 116 (sweep 112..116; 117 does not fit), the
    // boundary compare widening by fraction (120 -> 106)
    for (k, v) in [
        ("LF_YP8", "22"),
        ("LF_YP8_LATE", "1:13,4:17,9:22,81:19,91:17,102:15,107:13,113:11"),
        ("LFF_IPK", "1"),
        ("LF_REORDER_DIV", "37"),
        ("LF_REORDER_MUL", "49"),
        ("SL_N2_DFROM", "116"),
        ("SL_N2_MFROM", "116"),
        ("LF_CMP_FROM", "106"),
        // the walk cap of A's build (the multiply's N2-batch reverse ticks bind it)
        ("HEO_PIN_PP_WALK_MAX_QUBITS", "1242"),
    ] {
        match std::env::var(format!("LFA2_SET_{k}")) {
            Ok(o) => std::env::set_var(k, o),
            Err(_) => std::env::set_var(k, v),
        }
    }
}
/// At a walk's end every field is gone.
pub(super) fn a2_rec_empty() -> bool { A2_REC.with(|r| r.borrow().is_empty()) }
/// round17 v4: R1 on A ticks (LFA2_R1, default on): the 8-way barrel has an R1 plan at width w no dearer than its plain one.
fn a2_r1_ok(w: usize) -> bool {
    !std::env::var("LFA2_R1").is_ok_and(|v| v == "0") && w >= 3 && y15::rail8_plan_g(w).is_some_and(|p| { let (g, b) = p.costs(); g <= b })
}
/// [`fast_k_erase_a`] on the R1 reverse target X^ (wires 1 ..= e hold X ^ L): a read of wire i >= 1 is a read of X ^ L,
/// which is X wherever its term is live (the term's letter or a lower zero factor confines it to e >= i), so L is
/// hosted on wires 1 .. min(w, 7) around the erase (Clifford).
fn fast_k_erase_a_g(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId, k3: QubitId, l: Option<&Lin>) {
    let nz = t.len().min(7);
    if let Some(l) = l {
        for i in 1..nz { lin_xor_into(c, l, t[i]); }
    }
    fast_k_erase_a(c, t, k1, k2, k3);
    if let Some(l) = l {
        for i in (1..nz).rev() { lin_xor_into(c, l, t[i]); }
    }
}

/// Forget every field (tests that build several circuits in one process).
#[cfg(test)]
pub(super) fn a2_rec_clear() { A2_REC.with(|r| r.borrow_mut().clear()) }

/// [`zlin_on`] over bits 2..8 (A's deep candidate up to v = 8): t_i <- z_i = t_i ^ b_i ^ dq (i = 2..8).
fn zlin_on_a(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(b[1], t[1]);
    for i in 2..9 {
        c.cx(b[i], t[i]);
        c.cx(t[1], t[i]);
    }
    c.cx(b[top.min(b.len() - 1)], t[top]);
    c.cx(t[1], t[top]);
}
fn zlin_off_a(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(t[1], t[top]);
    c.cx(b[top.min(b.len() - 1)], t[top]);
    for i in 2..9 {
        c.cx(t[1], t[i]);
        c.cx(b[i], t[i]);
    }
    c.cx(b[1], t[1]);
}
/// The A decision at the pause ([`yp8_logic`] with e <= 7 and the record): `spent` = the record's linear form for
/// this tick. outs = Some((out, k1, k2, k3)) writes the choice and shift letters; None applies (-1)^out.
fn yp8_logic_a(c: &mut Builder, t2: &[QubitId], b: &[QubitId], s1: QubitId, ct: QubitId, tick: usize, spent: &Lin, outs: Option<(QubitId, QubitId, QubitId, QubitId)>) {
    let need0 = w1_anchor(tick) <= w1_kt(tick);
    // full-index views: bit 0 (the constant 1 of an odd rail) is a wire only when the window reads it
    let mut tv: Vec<QubitId> = Vec::with_capacity(t2.len() + 1);
    let mut bv: Vec<QubitId> = Vec::with_capacity(b.len() + 1);
    if need0 {
        for v in [&mut tv, &mut bv] {
            let q = c.alloc_qubit();
            c.x(q);
            v.push(q);
        }
    } else {
        tv.push(t2[0]); // placeholders, never read
        bv.push(b[0]);
    }
    tv.extend_from_slice(t2);
    bv.extend_from_slice(b);
    let (t_real, b_real) = (tv.len(), bv.len());
    for v in [&mut tv, &mut bv] {
        while v.len() < 10 {
            let q = c.alloc_qubit();
            c.cx(*v.last().unwrap(), q);
            v.push(q);
        }
    }
    // a source held wider than the target: its wires past the target's width are sign copies
    let bview: Vec<QubitId> = bv[..bv.len().min(tv.len())].to_vec();
    let top = tv.len() - 1;
    let btop = *bview.last().unwrap();
    // window compare Y = [a > 2b]
    let (wa, wb) = (w1_window(&tv, tick), w1_window(&bview, tick));
    w1_conj(c, &tv, &wa);
    w1_conj(c, &bview, &wb);
    let (w, recs) = w1_chain_s(c, &wa, &wb, 1);
    w1_conj(c, &bview, &wb);
    w1_conj(c, &tv, &wa);
    if let Lit::W(q, _) = w {
        assert!(recs.iter().any(|r| r.t == q), "YP8: the compare's result must be an AND wire");
    }
    // hosts: s1's wire <- not flipped = 1 ^ c_top ^ sign(B) ^ s1;  ct's wire <- added = 1 ^ c_top ^ sign(T2)
    c.cx(ct, s1);
    c.cx(btop, s1);
    c.x(s1);
    c.cx(tv[top], ct);
    c.x(ct);
    zlin_on_a(c, &tv, &bview);
    // !Y as an AND operand
    let ny = |c: &mut Builder| {
        if let Lit::W(wq, false) = w {
            c.x(wq);
        }
    };
    let veto = !matches!(w, Lit::One);
    match outs {
        Some((out, k1, k2, k3)) => {
            for i in 2..9 {
                c.x(tv[i]);
            }
            let a1 = and_new(c, tv[2], tv[3]);
            let a2 = and_new(c, a1, tv[4]);
            c.cx(tv[1], out);
            c.x(out);
            c.cx(a2, out);
            // barrel letters: k2 = Dsel & !z2 = !z2 ^ a2 ^ v3;  k1 = Dsel ^ (k2 & z3) = Dsel ^ !z2 ^ a1 ^ v3
            c.cx(tv[2], k2);
            c.cx(a2, k2);
            // A: g = p4 & !spent (= p4 at a triple's first position), p_j = g & !z5 .. !z_j (j = 5..8);
            // inadmissible I = (p4 ^ g) ^ p8 (spent: v >= 5; else v >= 9); k3 = g ^ p8; k2 ^= p6 ^ p8;
            // k1 ^= g ^ p5 ^ p6 ^ p7 (the deep v = 5, 7 cases leave Dsel's k1)
            let nsp = spent.x(&Lin::k(true));
            let g = if spent.w.is_empty() && !spent.one { None } else { Some(lin_and(c, &Lin::of(&[a2]), &nsp)) };
            let gw = g.unwrap_or(a2);
            let p5 = and_new(c, gw, tv[5]);
            let p6 = and_new(c, p5, tv[6]);
            let p7 = and_new(c, p6, tv[7]);
            let p8 = and_new(c, p7, tv[8]);
            if let Some(gq) = g {
                c.cx(gq, out);
            } else {
                c.cx(a2, out);
            }
            c.cx(p8, out);
            c.cx(gw, k3);
            c.cx(p8, k3);
            c.cx(p6, k2);
            c.cx(p8, k2);
            for q in [gw, p5, p6, p7] {
                c.cx(q, k1);
            }
            and_erase(c, p8, p7, tv[8]);
            and_erase(c, p7, p6, tv[7]);
            and_erase(c, p6, p5, tv[6]);
            and_erase(c, p5, gw, tv[5]);
            if let Some(gq) = g {
                lin_and_erase(c, gq, &Lin::of(&[a2]), &nsp);
            }
            and_erase(c, a2, a1, tv[4]);
            let fsw = match w { Lit::W(q, i) if veto && yp8_veto() != 0 => Some((q, i)), _ => None };
            if let Some((wq, winv)) = fsw {
                // YP8_VETO: q' = E & (Y ^ S) (= E & !Y & S where the add did not overflow); v2 = q' & z2
                c.cx(s1, wq);
                if winv { c.x(wq); }
                let q1 = and_new(c, tv[top], wq);
                c.x(tv[2]);
                let v2 = and_new(c, q1, tv[2]);
                if yp8_veto_fault() != 2 { c.cx(v2, out); }
                and_erase(c, v2, q1, tv[2]);
                c.x(tv[2]);
                yp8_veto_pad(c);
                // v = 3 as before, on q'
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct);
                c.cx(tv[2], a1);
                let v3 = and_new(c, q1, r3);
                c.cx(v3, out);
                c.cx(v3, k2);
                c.cx(v3, k1);
                and_erase(c, v3, q1, r3);
                c.cx(tv[2], a1);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                and_erase(c, q1, tv[top], wq);
                if winv { c.x(wq); }
                c.cx(s1, wq);
            } else if veto {
                // q1 = eq & !Y
                let q1 = match w {
                    Lit::W(wq, _) => {
                        ny(c);
                        let q = and_new(c, tv[top], wq);
                        ny(c);
                        q
                    }
                    _ => tv[top],
                };
                // v = 2: z2 & not flipped
                c.x(tv[2]);
                let r2 = and_new(c, tv[2], s1);
                c.x(tv[2]);
                let v2 = and_new(c, q1, r2);
                c.cx(v2, out);
                and_erase(c, v2, q1, r2);
                c.x(tv[2]);
                and_erase(c, r2, tv[2], s1);
                c.x(tv[2]);
                // v = 3: [v = 3] & added  (a1's wire holds [v = 3] = !z2 & z3 meanwhile)
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct);
                c.cx(tv[2], a1);
                let v3 = and_new(c, q1, r3);
                c.cx(v3, out);
                c.cx(v3, k2);
                c.cx(v3, k1);
                and_erase(c, v3, q1, r3);
                c.cx(tv[2], a1);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                if let Lit::W(wq, _) = w {
                    ny(c);
                    and_erase(c, q1, tv[top], wq);
                    ny(c);
                }
            }
            c.cx(tv[2], k1);
            c.cx(a1, k1);
            and_erase(c, a1, tv[2], tv[3]);
            c.cx(tv[1], out); // Dsel on out's wire
            for i in 2..9 {
                c.x(tv[i]);
            }
            c.cx(out, k1);
            c.cx(tv[1], out);
        }
        None => {
            c.x(tv[1]);
            c.z_if(tv[1], NO_BIT); // dq ^ 1
            c.x(tv[1]);
            for i in 2..9 {
                c.x(tv[i]);
            }
            let a1 = and_new(c, tv[2], tv[3]);
            // A: the phase of I = (p4 ^ g) ^ p8 in place of main's p4
            {
                let a2 = and_new(c, a1, tv[4]);
                let nsp = spent.x(&Lin::k(true));
                let g = if spent.w.is_empty() && !spent.one { None } else { Some(lin_and(c, &Lin::of(&[a2]), &nsp)) };
                let gw = g.unwrap_or(a2);
                if let Some(gq) = g {
                    c.z_if(a2, NO_BIT);
                    c.z_if(gq, NO_BIT);
                }
                let p5 = and_new(c, gw, tv[5]);
                let p6 = and_new(c, p5, tv[6]);
                let p7 = and_new(c, p6, tv[7]);
                c.cz(p7, tv[8]);
                and_erase(c, p7, p6, tv[7]);
                and_erase(c, p6, p5, tv[6]);
                and_erase(c, p5, gw, tv[5]);
                if let Some(gq) = g {
                    lin_and_erase(c, gq, &Lin::of(&[a2]), &nsp);
                }
                and_erase(c, a2, a1, tv[4]);
            }
            let fsw = match w { Lit::W(q, i) if veto && yp8_veto() != 0 => Some((q, i)), _ => None };
            if let Some((wq, winv)) = fsw {
                // YP8_VETO: the phase of q' & z2 and q' & r3, q' = E & (Y ^ S)
                c.cx(s1, wq);
                if winv { c.x(wq); }
                let q1 = and_new(c, tv[top], wq);
                c.x(tv[2]);
                if yp8_veto_fault() != 1 { c.cz(q1, tv[2]); }
                yp8_veto_pad(c);
                c.x(tv[2]);
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct); // [v = 3] & added
                c.cz(q1, r3);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                and_erase(c, q1, tv[top], wq);
                if winv { c.x(wq); }
                c.cx(s1, wq);
            } else if veto {
                let q1 = match w {
                    Lit::W(wq, _) => {
                        ny(c);
                        let q = and_new(c, tv[top], wq);
                        ny(c);
                        q
                    }
                    _ => tv[top],
                };
                c.x(tv[2]);
                let r2 = and_new(c, tv[2], s1); // z2 & not flipped
                c.cz(q1, r2);
                and_erase(c, r2, tv[2], s1);
                c.x(tv[2]);
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct); // [v = 3] & added
                c.cz(q1, r3);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                if let Lit::W(wq, _) = w {
                    ny(c);
                    and_erase(c, q1, tv[top], wq);
                    ny(c);
                }
            }
            and_erase(c, a1, tv[2], tv[3]);
            for i in 2..9 {
                c.x(tv[i]);
            }
        }
    }
    zlin_off_a(c, &tv, &bview);
    c.x(ct);
    c.cx(tv[top], ct);
    c.x(s1);
    c.cx(btop, s1);
    c.cx(ct, s1);
    w1_conj(c, &tv, &wa);
    w1_conj(c, &bview, &wb);
    erase_recs(c, recs);
    w1_conj(c, &bview, &wb);
    w1_conj(c, &tv, &wa);
    for (v, real) in [(&mut bv, b_real), (&mut tv, t_real)] {
        while v.len() > real {
            let q = v.pop().unwrap();
            c.cx(*v.last().unwrap(), q);
            c.free(q);
        }
    }
    if need0 {
        for q in [bv[0], tv[0]] {
            c.x(q);
            c.free(q);
        }
    }
}


/// [`yp8_reserve`] for the A decision: 5 more AND wires (g, p5..p8) and views padded to 10 positions.
fn yp8_reserve_a(tl: usize, bl: usize, t: usize, fwd: bool) -> usize {
    yp8_reserve(tl, bl, t, fwd) + 5 + 10usize.saturating_sub((tl + 1).max(6)) + 10usize.saturating_sub((bl + 1).max(6))
}
/// [`yp8_add_halve_forced_choice`] with the A decision (k3 and the record's spent form).
fn yp8_add_halve_forced_choice_a(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>, out: QubitId, k1: QubitId, k2: QubitId, k3: QubitId, tick: usize, spent: &Lin) {
    c.cx_all(sign, b);
    c.cx(b[0], t[0]);
    let low = t.remove(0);
    c.free(low);
    let acc = t.clone();
    let reserve = yp8_reserve_a(acc.len(), b.len(), tick, true);
    rail_add_mid(c, &b[1..], &acc, b[0], reserve, true, None, &mut |c, add, delta, carry| {
        let flip = |c: &mut Builder| {
            for (j, cj) in carry.iter().enumerate() {
                for &q in &add[delta + j] {
                    c.cx(q, acc[delta + j]);
                }
                if let Some(cj) = *cj {
                    c.cx(cj, acc[delta + j]);
                }
            }
        };
        let ct = carry.last().copied().flatten().expect("top carry");
        let q0 = pmark(c);
        flip(c); // the paused part's sums, by CNOTs: acc holds the new target
        c.cx_all(sign, b);
        yp8_logic_a(c, &acc, b, sign, ct, tick, spent, Some((out, k1, k2, k3)));
        c.cx_all(sign, b);
        flip(c);
        pacc(c, "yp8.fwd_logic", q0);
    });
    c.cx_all(sign, b);
}

/// [`yp8_double_sub_forced_erase`] with the A decision's phase.
fn yp8_double_sub_forced_erase_a(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>, m: crate::circuit::BitId, tick: usize, spent: &Lin) {
    c.cx_all(sign, b);
    c.x_all(t);
    let acc = t.clone();
    let reserve = yp8_reserve_a(acc.len(), b.len(), tick, false);
    let n = acc.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    // the logic reads the target's bits 1..4 (positions 0..4 here) and, below the sign, only its window
    let h = w1_anchor(tick).saturating_sub(w1_kt(tick));
    // A: the logic reads the target's bits 1..8 (positions 0..8 here)
    let low = (h >= 1).then(|| (8usize, h - 1));
    if n > 3 && n - 1 + reserve > room {
        // The paused add would be split deeper than the plain one, and the pause is only needed on shots whose
        // outcome is 1: run the plain add on the others.
        assert!(!y28_pending(), "y28: a kept bit's Z would sit under the choice outcome here");
        let nm = c.alloc_bit();
        c.bit_store1(nm);
        c.bit_xor_into(nm, m);
        c.push_condition(nm);
        rail_add(c, &b[1..], &acc, Some(b[0]));
        c.pop_condition();
        c.free_bit(nm);
        c.push_condition(m);
        rail_add_mid(c, &b[1..], &acc, b[0], reserve, false, low, &mut |c, _add, _delta, carry| {
            let ct = carry.last().copied().flatten().expect("top carry");
            let q0 = pmark(c);
            c.x_all(&acc);
            c.cx_all(sign, b);
            yp8_logic_a(c, &acc, b, sign, ct, tick, spent, None);
            c.cx_all(sign, b);
            c.x_all(&acc);
            pacc(c, "yp8.rev_logic", q0);
        });
        c.pop_condition();
    } else {
        rail_add_mid(c, &b[1..], &acc, b[0], reserve, false, low, &mut |c, _add, _delta, carry| {
            let ct = carry.last().copied().flatten().expect("top carry");
            let q0 = pmark(c);
            c.push_condition(m);
            c.x_all(&acc);
            c.cx_all(sign, b);
            yp8_logic_a(c, &acc, b, sign, ct, tick, spent, None);
            c.cx_all(sign, b);
            c.x_all(&acc);
            c.pop_condition();
            pacc(c, "yp8.rev_logic", q0);
        });
    }
    c.x_all(t);
    let u = c.alloc_qubit();
    c.cx(b[0], u);
    c.cx_all(sign, b);
    t.insert(0, u);
}


/// MBU erase of the A shift letters on the reverse tick from x3 (the target before the barrel; x3 = 2^e odd,
/// z_i = !t_i): k1 = z0 ^ k2 t2 ^ k3 t4 ^ k2 k3 t6 (k2, k3 live), then k2 = z0 z1 ^ k3 ^ k3 z4 z5 (k3 live), then
/// k3 = z0 z1 z2 z3. Phase fixes: Clifford except one AND each (k2 k3; z4 z5; z0 z1 and z2 z3 for k3), all under the
/// measurement's condition.
fn fast_k_erase_a(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId, k3: QubitId) {
    // x3 = 2^e odd with e <= w - 2: a term whose indicator needs e beyond the register is identically 0 (skipped)
    let w = t.len();
    let nz = w.min(7);
    for i in 0..nz {
        c.x(t[i]);
    }
    // t[i] holds z_i now; t_i = z_i ^ 1
    let m1 = c.alloc_bit();
    c.hmr(k1, m1);
    c.release_clean(k1);
    c.z_if(t[0], m1);
    for (k, i) in [(k2, 2usize), (k3, 4usize)] {
        if i + 2 <= w {
            c.x(t[i]);
            c.cz_if(k, t[i], m1);
            c.x(t[i]);
        }
    }
    if w >= 8 {
        c.push_condition(m1);
        let kk = and_new(c, k2, k3);
        c.x(t[6]);
        c.cz(kk, t[6]);
        c.x(t[6]);
        and_erase(c, kk, k2, k3);
        c.pop_condition();
    }
    c.free_bit(m1);
    let m2 = c.alloc_bit();
    c.hmr(k2, m2);
    c.release_clean(k2);
    c.cz_if(t[0], t[1], m2);
    if w >= 6 {
        c.z_if(k3, m2);
        c.push_condition(m2);
        let zz = and_new(c, t[4], t[5]);
        c.cz(k3, zz);
        and_erase(c, zz, t[4], t[5]);
        c.pop_condition();
    }
    c.free_bit(m2);
    let m3 = c.alloc_bit();
    c.hmr(k3, m3);
    c.release_clean(k3);
    if w >= 6 {
        c.push_condition(m3);
        let a = and_new(c, t[0], t[1]);
        let b2 = and_new(c, t[2], t[3]);
        c.cz(a, b2);
        and_erase(c, b2, t[2], t[3]);
        and_erase(c, a, t[0], t[1]);
        c.pop_condition();
    }
    c.free_bit(m3);
    for i in (0..nz).rev() {
        c.x(t[i]);
    }
}

/// Reference model of lever A's walk (rsim's tick_core / choose / cap_at for the build spec), for the tests.
#[cfg(test)]
pub(super) mod a2_ref {
    /// 320-bit two's complement (rsim's I).
    #[derive(Clone, Copy, PartialEq, Debug)]
    pub struct I5(pub [u64; 5]);
    impl I5 {
        pub fn add(&self, b: &I5) -> I5 { let mut r = [0u64; 5]; let mut c = false; for i in 0..5 { let (x, c1) = self.0[i].overflowing_add(b.0[i]); let (y, c2) = x.overflowing_add(c as u64); r[i] = y; c = c1 || c2; } I5(r) }
        pub fn sub(&self, b: &I5) -> I5 { let mut r = [0u64; 5]; let mut c = false; for i in 0..5 { let (x, c1) = self.0[i].overflowing_sub(b.0[i]); let (y, c2) = x.overflowing_sub(c as u64); r[i] = y; c = c1 || c2; } I5(r) }
        pub fn neg_p(&self) -> bool { self.0[4] >> 63 == 1 }
        pub fn is_zero(&self) -> bool { self.0.iter().all(|&w| w == 0) }
        pub fn sar(&self, k: u32) -> I5 { let mut r = [0u64; 5]; for i in 0..4 { r[i] = (self.0[i] >> k) | (self.0[i + 1] << (64 - k)); } r[4] = ((self.0[4] as i64) >> k) as u64; I5(r) }
        pub fn bit(&self, i: usize) -> bool { self.0[i / 64] >> (i % 64) & 1 == 1 }
        pub fn ctz(&self) -> usize { for i in 0..5 { if self.0[i] != 0 { return 64 * i + self.0[i].trailing_zeros() as usize; } } 99 }
        /// bits [h, h + l) of the ones'-complement magnitude
        pub fn winv(&self, h: usize, l: usize) -> u128 {
            let m = if self.neg_p() { u64::MAX } else { 0 };
            let mut v: u128 = 0;
            for j in 0..l { let p = h + j; if p < 320 && ((self.0[p / 64] ^ m) >> (p % 64)) & 1 == 1 { v |= 1 << j; } }
            v
        }
    }
    pub fn p() -> I5 { I5([0xFFFF_FFFE_FFFF_FC2F, u64::MAX, u64::MAX, u64::MAX, 0]) }
    /// Letters of one tick: (forced signs (1 = subtract), choice letter s3 (1 = subtract), e).
    #[derive(Clone, Debug, PartialEq)]
    pub struct Tl { pub s: Vec<bool>, pub s3: bool, pub e: usize }
    pub fn lwin(t: usize) -> usize {
        let main = !super::a2_on();
        let sch: &[(usize, usize)] = if main {
            &[(0, 22), (1, 13), (6, 17), (11, 22), (90, 19), (100, 17), (112, 15), (118, 13), (124, 11)]
        } else {
            &[(0, 22), (1, 13), (4, 17), (9, 22), (81, 19), (91, 17), (102, 15), (107, 13), (113, 11)]
        };
        sch.iter().filter(|&&(f, _)| t >= f).last().unwrap().1
    }
    /// The walk on d (in [1, p)) for R ticks with these anchors: letters per tick (main's spec without LFA2).
    pub fn walk(d: &I5, r: usize, anch: &[usize]) -> Vec<Tl> { walk_t0(d, r, anch, None) }
    /// [`walk`] with tick 0's choice letter given (main's circuit decides tick 0 by its own R1-window sign predicate,
    /// which differs from rsim's exact E on about a fifth of the inputs; tick 0 is main's machinery in both walks).
    pub fn walk_t0(d: &I5, r: usize, anch: &[usize], t0s3: Option<bool>) -> Vec<Tl> {
        let main = !super::a2_on();
        let pp = p();
        let r0 = if d.0[0] & 1 == 1 { *d } else { d.sub(&pp) };
        let x = if r0.bit(1) { r0.add(&pp) } else { r0.sub(&pp) };
        let mut rr = [r0, x.sar(1)];
        let fam = |m: u32| -> bool { let r0 = m & 0x15; let r1 = m & 0x2a; r0.count_ones() <= 1 && r1.count_ones() <= 1 };
        let mut pfx: u32 = 0;
        let mut out = Vec::new();
        for t in 0..r {
            let a = t & 1;
            let last = t == r - 1;
            let nf = if last { 0 } else { 2 };
            let b = rr[1 - a];
            let mut tk = rr[a];
            let (mut added, mut flipped) = (false, false);
            let mut ss = Vec::new();
            let bn = b.neg_p();
            for i in 0..nf {
                let s = tk.bit(1) == b.bit(1);
                let xx = if s { tk.add(&b) } else { tk.sub(&b) };
                let tn = tk.neg_p();
                let ad = tn == (bn ^ !s);
                let tnew = xx.sar(1);
                let fl = !ad && tnew.neg_p() != tn;
                if i == nf - 1 { added = ad; flipped = fl; }
                tk = tnew;
                ss.push(!s);
            }
            let sd = tk.bit(1) != b.bit(1);
            let (xd, xf) = if sd { (tk.add(&b), tk.sub(&b)) } else { (tk.sub(&b), tk.add(&b)) };
            let z = xd.is_zero();
            let v = if z { 99 } else { xd.ctz() };
            let e_eq = !z && (tk.neg_p() == (bn ^ !sd));
            if t % 6 == 0 { pfx = 0; }
            let mut cap = if t == 0 || last || main { 3 } else { 7 };
            if cap > 3 && !fam(pfx | 1 << (t % 6)) { cap = 3; }
            let l = lwin(t);
            let h = anch[t.min(anch.len() - 1)].saturating_sub(l - 2);
            let (wa, wb) = (tk.winv(h, l), b.winv(h, l));
            let mut deep = false;
            if v <= cap + 1 {
                deep = if last {
                    if !(e_eq && v == 2) { true } else { wa > (wb << 2) }
                } else if t == 0 {
                    !(e_eq && v == 2)
                } else if !e_eq {
                    true
                } else {
                    match v { 2 => wa > (wb << 1) || flipped, 3 => wa > (wb << 1) || !added, _ => true }
                };
            }
            if let (0, Some(g)) = (t, t0s3) {
                deep = g != sd;
            }
            if deep && v - 1 >= 4 { pfx |= 1 << (t % 6); }
            if t < 1 && std::env::var("LFA2_DBG").is_ok() {
                eprintln!("A2_REFDBG t={t} T2={:x?} B={:x?} sd={sd} v={v} E={e_eq} deep={deep} added={added} flipped={flipped}", tk.0[0], b.0[0]);
            }
            rr[a] = if deep { xd.sar(v as u32) } else { xf.sar(1) };
            out.push(Tl { s: ss, s3: if deep { !sd } else { sd }, e: if deep { v - 1 } else { 0 } });
        }
        out
    }
}

#[cfg(test)]
mod a2_walk_tests {
    use super::*;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};
    fn setup() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
    }
    fn rnd_d(seed: &mut u64) -> U256 {
        let p = super::super::SECP256K1_P;
        loop {
            let mut v = U256::ZERO;
            for i in 0..4 {
                *seed ^= *seed << 13; *seed ^= *seed >> 7; *seed ^= *seed << 17;
                v |= U256::from(*seed) << (64 * i);
            }
            if v != U256::ZERO && v < p { return v; }
        }
    }
    thread_local! { static FIRST_BAD: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) }; }
    thread_local! { static PAR: std::cell::RefCell<[usize; 2]> = const { std::cell::RefCell::new([0, 0]) }; }
    fn to_i5(v: U256) -> a2_ref::I5 { let l = v.as_limbs(); a2_ref::I5([l[0], l[1], l[2], l[3], 0]) }
    /// Rails-only forward walk (all R ticks): the tape letters and the record's k3 against the reference model;
    /// then the reverse walk and the unseed: x restored, every other wire clean, no phase.
    #[test]
    fn a2_walk_letters() {
        setup();
        let r = rounds();
        let anch: Vec<usize> = (0..r).map(w1_anchor).collect();
        let nb: usize = std::env::var("LFA2_WB").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        let fulls: Vec<bool> = if std::env::var("LFA2_WFULL").is_ok() { vec![true] } else { vec![false, true] };
        for full in fulls {
            a2_rec_clear();
            let mut c = Builder::new();
            let x = c.alloc_qubits(N);
            let rails = seed(&mut c, &x);
            let mut wk = Walk { r: rails, tape: Vec::new() };
            // tick 0 on the plain rule, as divide / multiply run it (LF_T0_FREE; LFA2_T0YP8=1 keeps the YP8 rule)
            T0_PLAIN.with(|p| p.set(t0_free(false) && std::env::var("LFA2_T0YP8").is_err()));
            // LFA2_PARITY=a: stop after tick a - 1 and check main's parity relation (parity_wires) on every shot
            let par_at: Option<usize> = std::env::var("LFA2_PARITY").ok().and_then(|v| v.parse().ok());
            for t in 0..par_at.unwrap_or(r) {
                fwd_tick(&mut c, &mut wk, t, None);
            }
            let pw: Vec<QubitId> = par_at.map(|a| parity_wires(&wk, a)).unwrap_or_default();
            let park_chk = std::env::var("LFA2_PARKCHK").is_ok();
            let rails_end = wk.r.clone();
            let tape = wk.tape.clone();
            let rec: std::collections::HashMap<usize, [Option<QubitId>; 2]> = A2_REC.with(|m| m.borrow().clone());
            if full {
                for t in (0..r).rev() {
                    rev_tick(&mut c, &mut wk, t, None);
                }
                assert!(a2_rec_empty(), "a2: record fields left after the reverse walk");
                unseed(&mut c, wk.r, &x);
            }
            let (nq, nbits) = c.i13_dims();
            let ops = c.take_ops();
            let mut h = sha3::Shake256::default();
            h.update(b"a2-walk");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
            let mut seedv = 0x5eed_0000_1234_5678u64;
            // LFA2_DFILE: walk inputs from a file (one hex d per line), cycled over the shots
            let dfile: Vec<U256> = std::env::var("LFA2_DFILE").ok().map(|p| std::fs::read_to_string(p).unwrap().lines().filter_map(|l| U256::from_str_radix(l.trim().trim_start_matches("0x"), 16).ok()).collect()).unwrap_or_default();
            let mut di = 0usize;
            let (mut bad, mut events, mut ticks) = (0usize, 0usize, 0usize);
            for _ in 0..nb {
                sim.clear_for_shot();
                let mut ins = Vec::new();
                for shot in 0..64 {
                    let d = if dfile.is_empty() { rnd_d(&mut seedv) } else { di += 1; dfile[(di - 1) % dfile.len()] };
                    for i in 0..N { if d.bit(i) { *sim.qubit_mut(x[i]) |= 1 << shot; } }
                    ins.push(d);
                }
                sim.apply_iter(ops.iter());
                for (shot, &d) in ins.iter().enumerate() {
                    let rd = |q: QubitId| (sim.qubit(q) >> shot) & 1 == 1;
                    if full {
                        let mut ok = (0..N).all(|i| rd(x[i]) == d.bit(i)) && (sim.phase >> shot) & 1 == 0;
                        ok &= (N..nq).all(|q| (sim.qubits[q] >> shot) & 1 == 0);
                        if !ok {
                            bad += 1;
                            if std::env::var("LFA2_WFULL").is_ok() {
                                let xr = (0..N).all(|i| rd(x[i]) == d.bit(i));
                                eprintln!("A2_WALK_FAIL d={d:#x} x_ok={xr} phase={} anc={}", (sim.phase >> shot) & 1, (N..nq).any(|q| (sim.qubits[q] >> shot) & 1 == 1));
                            }
                        }
                        continue;
                    }
                    if park_chk {
                        // parked: both rails +-1 (bit-0-less registers: every held bit equal)
                        let pk = rails_end.iter().all(|r| r.iter().all(|&q| rd(q) == rd(r[0])));
                        let want = a2_ref::walk_t0(&to_i5(d), r, &anch, Some(rd(tape[0][tape[0].len() - 3])));
                        let _ = want;
                        PAR.with(|p| p.borrow_mut()[pk as usize] += 1);
                        if !pk && std::env::var("LFA2_PARKV").is_ok() { eprintln!("A2_NOPARK d={d:#x}"); }
                        continue;
                    }
                    if par_at.is_some() {
                        let v = pw.iter().fold(false, |a, &q| a ^ rd(q));
                        PAR.with(|p| p.borrow_mut()[v as usize] += 1);
                        continue;
                    }
                    let t0s3 = rd(tape[0][tape[0].len() - 3]);
                    let want = a2_ref::walk_t0(&to_i5(d), r, &anch, Some(t0s3));
                    let mut first_bad: Option<usize> = None;
                    if shot == 0 && std::env::var("LFA2_DBG").is_ok() {
                        let ls: Vec<String> = (0..6).map(|t| format!("{:?}", tape[t].iter().map(|&q| rd(q) as u8).collect::<Vec<u8>>())).collect();
                        eprintln!("A2_DBG d={d:#x} letters {ls:?}");
                        eprintln!("A2_DBG want {:?}", &want[..6]);
                    }
                    for t in 0..r {
                        let lt = &tape[t];
                        let nf = lt.len() - 3;
                        let got_s: Vec<bool> = (0..nf).map(|i| rd(lt[i])).collect();
                        let s3 = rd(lt[nf]);
                        let mut e = usize::from(rd(lt[nf + 1])) + 2 * usize::from(rd(lt[nf + 2]));
                        if a2_tick(t) {
                            let f = rec.get(&a2_tid(t)).expect("a2: field");
                            let fv = usize::from(rd(f[0].unwrap())) + 2 * usize::from(rd(f[1].unwrap()));
                            if fv == a2_pos(t) { e += 4; }
                        }
                        let w = &want[t];
                        ticks += 1;
                        if w.e >= 4 { events += 1; }
                        if (got_s != w.s || s3 != w.s3 || e != w.e) && first_bad.is_none() {
                            first_bad = Some(t);
                            FIRST_BAD.with(|f| f.borrow_mut().push(t));
                        }
                        if got_s != w.s || s3 != w.s3 || e != w.e {
                            if bad < 6 {
                                eprintln!("A2 WALK MISMATCH shot={shot} d={d:#x} t={t} got s={got_s:?} s3={s3} e={e} want {w:?}");
                            }
                            bad += 1;
                        }
                    }
                }
            }
            if par_at.is_some() {
                eprintln!("A2_PARITY at={:?} counts(xor=0,1)={:?}", par_at, PAR.with(|p| *p.borrow()));
                return;
            }
            if park_chk {
                eprintln!("A2_PARKCHK shots={} (not parked, parked)={:?}", nb * 64, PAR.with(|p| *p.borrow()));
                return;
            }
            let fb = FIRST_BAD.with(|f| std::mem::take(&mut *f.borrow_mut()));
            if std::env::var("LFA2_WFULL").is_ok() {
                eprintln!("A2_WALK_FAILS shots={} bad={bad}", nb * 64);
                continue;
            }
            eprintln!("A2_WALK_CHECK full={full} R={r} shots={} ticks={ticks} e>=4 events={events} bad={bad} diverging shots={} first ticks={fb:?}", nb * 64, fb.len());
            assert_eq!(bad, 0, "a2: the A walk disagrees (full={full})");
        }
    }
}

#[cfg(test)]
mod a2_divmul_tests {
    use super::*;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};
    /// The recipe's divide or multiply alone (LFA2_KIND=div|mul, LF_CAP, LFA2_NB batches): y / x or y x, x restored,
    /// clean ancillas, phase; per-batch phase-bad counts.
    #[test]
    fn a2_divmul() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
        // standalone walks: no coordinate seam, so no RT0 / T0ONE (tick 0 back on the plain reverse tick)
        std::env::set_var("SL_RT0", "0");
        std::env::set_var("SL_T0ONE", "0");
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let kind = std::env::var("LFA2_KIND").unwrap_or_else(|_| "div".into());
        let nb: usize = std::env::var("LFA2_NB").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        if kind == "div" { divide(&mut c, &y, &x) } else { multiply(&mut c, &y, &x) }
        let (nq, nbits) = c.i13_dims();
        let peak = c.peak_total();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(b"a2-divmul");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let p = super::super::SECP256K1_P;
        let mut seed = 0x1357_9bdf_2468_ace0u64;
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v % p };
        let (mut wrong, mut phase, mut anc) = (0, 0, 0);
        for _ in 0..nb {
            sim.clear_for_shot();
            let mut ins = Vec::new();
            let fixed: Option<(U256, U256)> = std::env::var("LFA2_DMIN").ok().map(|v| {
                let f: Vec<U256> = v.split(',').map(|h| U256::from_str_radix(h.trim().trim_start_matches("0x"), 16).unwrap()).collect();
                (f[0], f[1])
            });
            for shot in 0..64 {
                let (xv, yv) = fixed.unwrap_or_else(|| (rnd().max(U256::from(1u8)), rnd()));
                for i in 0..N { if xv.bit(i) { *sim.qubit_mut(x[i]) |= 1 << shot; } if yv.bit(i) { *sim.qubit_mut(y[i]) |= 1 << shot; } }
                ins.push((xv, yv));
            }
            sim.apply_iter(ops.iter());
            for (shot, &(xv, yv)) in ins.iter().enumerate() {
                let rd = |r: &[QubitId]| { let mut v = U256::ZERO; for i in 0..N { if (sim.qubit(r[i]) >> shot) & 1 == 1 { v |= U256::from(1u8) << i; } } v };
                let want = if kind == "div" { yv.mul_mod(xv.pow_mod(p - U256::from(2u8), p), p) } else { yv.mul_mod(xv, p) };
                if rd(&x) != xv || rd(&y) % p != want { wrong += 1; }
                if (sim.phase >> shot) & 1 == 1 { phase += 1; }
                let dirty = (0..nq).filter(|&q| !x.iter().chain(y.iter()).any(|w| w.0 as usize == q)).any(|q| (sim.qubits[q] >> shot) & 1 == 1);
                if dirty { anc += 1; }
            }
        }
        eprintln!("A2_DIVMUL {kind} shots={} wrong={wrong} phase_bad_shots={phase} ancilla_bad_shots={anc} peak={peak} rounds={}", nb * 64, rounds());
    }
}

#[cfg(test)]
mod a2_fused_tests {
    use super::*;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};
    /// Fused forward ticks 0..n then fused reverse ticks n-1..0 on (y, y) payload registers (LFA2_FN = n; LFA2_FMODE:
    /// "ff" fused both ways, "fp" fused forward + payload-only then rails-only reverse, "pf" rails-only + payload-only
    /// forward then fused reverse): identity on x, y; clean; no phase.
    #[test]
    fn a2_fused_identity() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let n: usize = std::env::var("LFA2_FN").ok().and_then(|v| v.parse().ok()).unwrap_or(12);
        let mode = std::env::var("LFA2_FMODE").unwrap_or_else(|_| "ff".into());
        let lo: usize = std::env::var("LFA2_FLO").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        a2_rec_clear();
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let z = c.alloc_qubits(N); // an independent second payload register (equal registers make the compares tie)
        let r = seed(&mut c, &x);
        let mut wk = Walk { r, tape: Vec::new() };
        for t in 0..lo { fwd_tick(&mut c, &mut wk, t, None); }
        let mut pay = [y.to_vec(), z.clone()];
        for t in lo..n {
            if mode == "pf" || mode == "pp" {
                fwd_tick(&mut c, &mut wk, t, None);
            } else {
                fwd_tick(&mut c, &mut wk, t, Some(&mut pay));
            }
        }
        if mode == "pf" || mode == "pp" {
            for t in lo..n { let l = wk.tape[t].clone(); pay_fwd_tick(&mut c, t, &l, &mut pay); }
        }
        if mode == "fp" || mode == "pp" {
            for t in (lo..n).rev() { let l = wk.tape[t].clone(); pay_rev_tick(&mut c, t, &l, &mut pay); }
            for t in (lo..n).rev() { rev_tick(&mut c, &mut wk, t, None); }
        } else {
            for t in (lo..n).rev() { rev_tick(&mut c, &mut wk, t, Some(&mut pay)); }
        }
        for t in (0..lo).rev() { rev_tick(&mut c, &mut wk, t, None); }
        unseed(&mut c, wk.r, &x);
        let (nq, nbits) = c.i13_dims();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(b"a2-fused");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let p = super::super::SECP256K1_P;
        let mut seed = 0x2468_1357_aaaa_5555u64;
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v % p };
        let (mut wrong, mut phase, mut anc) = (0, 0, 0);
        let fb: usize = std::env::var("LFA2_FB").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
        for _ in 0..fb {
            sim.clear_for_shot();
            let mut ins = Vec::new();
            for shot in 0..64 {
                let (xv, yv, zv) = (rnd().max(U256::from(1u8)), rnd(), rnd());
                for i in 0..N {
                    if xv.bit(i) { *sim.qubit_mut(x[i]) |= 1 << shot; }
                    if yv.bit(i) { *sim.qubit_mut(y[i]) |= 1 << shot; }
                    if zv.bit(i) { *sim.qubit_mut(z[i]) |= 1 << shot; }
                }
                ins.push((xv, yv, zv));
            }
            sim.apply_iter(ops.iter());
            for (shot, &(xv, yv, zv)) in ins.iter().enumerate() {
                let rd = |r: &[QubitId]| { let mut v = U256::ZERO; for i in 0..N { if (sim.qubit(r[i]) >> shot) & 1 == 1 { v |= U256::from(1u8) << i; } } v };
                if rd(&x) != xv || rd(&y) != yv || rd(&z) != zv { wrong += 1; }
                if (sim.phase >> shot) & 1 == 1 { phase += 1; }
                if (3 * N..nq).any(|q| (sim.qubits[q] >> shot) & 1 == 1) { anc += 1; }
            }
        }
        eprintln!("A2_FUSED mode={mode} lo={lo} n={n} shots={} wrong={wrong} phase_bad_shots={phase} ancilla_bad_shots={anc}", fb * 64);
    }
}

#[cfg(test)]
mod a2_paychain_tests {
    use super::*;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};
    /// Rails-only forward walk on d = LFA2_PD, then payload-only reverse ticks R-2 .. LFA2_PSTOP on (y, z) (both random),
    /// read against the classical inverse maps with the reference walk's letters: the first bad tick.
    #[test]
    fn a2_paychain() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let p = super::super::SECP256K1_P;
        let dv = U256::from_str_radix(std::env::var("LFA2_PD").unwrap().trim_start_matches("0x"), 16).unwrap();
        let stop: usize = std::env::var("LFA2_PSTOP").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let fwd = std::env::var("LFA2_PFWD").is_ok();
        a2_rec_clear();
        let r = rounds();
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let z = c.alloc_qubits(N);
        let rails = seed(&mut c, &x);
        let mut wk = Walk { r: rails, tape: Vec::new() };
        for t in 0..r { fwd_tick(&mut c, &mut wk, t, None); }
        let mut pay = [y.clone(), z.clone()];
        let ticks: Vec<usize> = if fwd { (stop..r - 1).collect() } else { (stop..r - 1).rev().collect() };
        for &t in &ticks {
            let l = wk.tape[t].clone();
            if fwd { pay_fwd_tick(&mut c, t, &l, &mut pay); } else { pay_rev_tick(&mut c, t, &l, &mut pay); }
        }
        let (nq, nbits) = c.i13_dims();
        let ops = c.take_ops();
        let mut h = sha3::Shake256::default();
        h.update(b"a2-paychain");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq, nbits.max(1), &mut xof);
        let anch: Vec<usize> = (0..r).map(w1_anchor).collect();
        let to_i5 = |v: U256| { let l = v.as_limbs(); a2_ref::I5([l[0], l[1], l[2], l[3], 0]) };
        sim.clear_for_shot();
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap() % p;
        let yv = hx(&std::env::var("LFA2_PY").unwrap_or_else(|_| "8f1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdef0fedcba9876543210".into()));
        // LFA2_PZ = "neg" / "same": the multiply's endpoint relation (P1 = -P0 / P0); else an independent value
        let zv = match std::env::var("LFA2_PZ").as_deref() {
            Ok("same") => yv,
            Ok("neg") => (p - yv) % p,
            _ => hx("3c5a7e9b1d2f4a6c8e0b2d4f6a8c0e2b4d6f8a0c2e4b6d8f0a2c4e6b8d0f2a4c"),
        };
        for shot in 0..64 {
            for i in 0..N {
                if dv.bit(i) { *sim.qubit_mut(x[i]) |= 1 << shot; }
                if yv.bit(i) { *sim.qubit_mut(y[i]) |= 1 << shot; }
                if zv.bit(i) { *sim.qubit_mut(z[i]) |= 1 << shot; }
            }
        }
        sim.apply_iter(ops.iter());
        let rd = |r: &[QubitId]| { let mut v = U256::ZERO; for i in 0..N { if sim.qubit(r[i]) & 1 == 1 { v |= U256::from(1u8) << i; } } v };
        // classical maps with the circuit's tick-0 choice (reference walk)
        let t0s3 = sim.qubit(wk.tape[0][wk.tape[0].len() - 3]) & 1 == 1;
        let lt = a2_ref::walk_t0(&to_i5(dv), r, &anch, Some(t0s3));
        let mut pv = [yv, zv];
        let inv2 = |k: usize| U256::from(1u64 << k).pow_mod(p - U256::from(2u8), p);
        for &t in &ticks {
            let (ti, si) = (t % 2, 1 - t % 2);
            let k = 3 + lt[t].e;
            let mut sum = U256::ZERO;
            for (i, &sg) in [lt[t].s[0], lt[t].s[1], lt[t].s3].iter().enumerate() {
                let term = pv[si].mul_mod(U256::from(1u64 << i), p);
                sum = if sg { sum.add_mod(p - term, p) } else { sum.add_mod(term, p) };
            }
            pv[ti] = if fwd {
                pv[ti].add_mod(sum, p).mul_mod(inv2(k), p)
            } else {
                pv[ti].mul_mod(U256::from(1u64 << k), p).add_mod(p - sum, p)
            };
        }
        for &t in &ticks { if t + 6 >= stop.max(1) + 6 && t < stop + 4 { eprintln!("A2_PCL t={t} letters={:?}", lt[t]); } }
        let (g0, g1) = (rd(&pay[0]) % p, rd(&pay[1]) % p);
        eprintln!("A2_PAYCHAIN fwd={fwd} stop={stop} ok0={} ok1={} phase={} events={:?}", g0 == pv[0], g1 == pv[1], sim.phase & 1,
            ticks.iter().filter(|&&t| lt[t].e >= 4).map(|&t| (t, lt[t].e)).collect::<Vec<_>>());
    }
}
