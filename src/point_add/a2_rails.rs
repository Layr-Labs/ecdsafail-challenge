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
/// laneW: tick-indexed tuning constants below were set on the 122-tick walk. Ticks of the late window bands keep their
/// distance from the walk's end; ticks that precede the first shifted band read as tick 80. Identity at R = 122.
pub(super) fn late_t(t: usize) -> usize {
    let s = rounds().saturating_sub(122);
    if t >= 81 + s { t - s } else { t.min(80) }
}
/// laneQ: a tail tick cut to e <= 3 by LFQ_LASTN (not tick 0, not the last tick).
pub(super) fn lfq_e3(t: usize) -> bool { a2_on() && !a2_tick(t) && t >= 1 && t + 1 < rounds() }
/// Tick t runs as an A tick (k3 exists).
pub(super) fn a2_tick(t: usize) -> bool {
    static N: OnceLock<usize> = OnceLock::new();
    let n = *N.get_or_init(|| std::env::var("LFQ_LASTN").ok().and_then(|v| v.parse().ok()).unwrap_or(1));
    a2_on() && t >= 1 && t + n < rounds()
}
/// The A fold's digit cap on tick t (LFA2_EMAX, default 7).
pub(super) fn a2_emax(_t: usize) -> usize {
    static V: OnceLock<usize> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_EMAX").ok().and_then(|v| v.parse().ok()).unwrap_or(7))
}
/// laneW: no record limit, one k3 cell per tick (research pricing of the uncoded dense walk).
pub(super) fn a2_dense() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_DENSE").is_ok_and(|v| v == "1"))
}
thread_local! { static A2_PADS: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) }; }
fn a2_pads_on() -> bool { a2_dense() && std::env::var("LFA2_DENSE_PADS").is_ok_and(|v| v == "1") }
fn a2_pos3(t: usize) -> bool { (t % 6) / 2 == 2 }
/// laneW: S6 barrels on the A ticks (rails from laneS, the payload's ring word). Needs emax <= 5.
pub(super) fn a2_s6() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_S6").is_ok_and(|v| v == "1") && a2_emax(0) <= 5)
}
fn a2_rail_s6(w: usize) -> bool { a2_s6() && super::rail_s6::rail_s6_plan(w).is_some() }
pub(super) fn a2_code() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| std::env::var("LFA2_CODE").is_ok_and(|v| v == "1"))
}
thread_local! {
    /// laneW code: the k2 cell (tape wire) of each A tick that has written and not been popped.
    static A2_CELLS: std::cell::RefCell<std::collections::HashMap<usize, QubitId>> = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Zero placeholders for a read of a partly written or partly popped block.
    static A2_TEMPS: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
}
fn a2_cell_set(t: usize, q: QubitId) { A2_CELLS.with(|m| { m.borrow_mut().insert(t, q); }); }
fn a2_cell(t: usize) -> Option<QubitId> { A2_CELLS.with(|m| m.borrow().get(&t).copied()) }
fn a2_block_tick(t: usize, p: usize) -> usize { t + 2 * p - 2 * a2_pos(t) }
/// (f0, c1) of a position-3 tick, the two factors of the spent form; None where position 1 is not an A tick.
fn a2_sp_pair(t: usize) -> Option<(QubitId, QubitId)> {
    if !a2_code() || a2_pos(t) != 3 { return None; }
    let c1 = a2_cell(t - 4)?;
    Some((a2_field(t)[0].expect("a2 code: f0"), c1))
}
/// End of a forward tick: the letter's k3 goes into the block's cells (positions 2 and 3), its wire leaves.
fn a2_code_commit(c: &mut Builder, t: usize, k3: QubitId) {
    let f = a2_field(t);
    match a2_pos(t) {
        1 => {}
        2 => {
            if let Some(c1) = a2_cell(t - 2) {
                // k3 is on f1's wire. m = k3 f0: toggles c1 (the marker, k2_1 = 0 under f0) and clears f1; m = f0 c1 now.
                let (f0, f1) = (f[0].unwrap(), f[1].unwrap());
                let m = and_new(c, f1, f0);
                c.cx(m, c1);
                c.cx(m, f1);
                and_erase(c, m, f0, c1);
            }
        }
        _ => {
            let (f0, f1) = (f[0].unwrap(), f[1].unwrap());
            let c2 = a2_cell(t - 2).expect("a2 code: c2");
            let c3 = a2_cell(t).expect("a2 code: c3");
            let first = a2_cell(t - 4).is_some();
            let x1 = first.then(|| and_new(c, k3, f0));
            let x2 = and_new(c, k3, f1);
            if let Some(x) = x1 { c.cx(x, c3); }
            c.cx(x2, c2);
            c.cx(k3, f0);
            c.cx(x2, f0);
            if let Some(x) = x1 { c.cx(x, f0); }
            c.cx(k3, f1);
            c.cx(x2, f1);
            // x1 = k3 c3, x2 = k3 !f0 now
            if let Some(x) = x1 { and_erase(c, x, k3, c3); }
            c.x(f0);
            and_erase(c, x2, k3, f0);
            c.x(f0);
            // k3 = f1 (f0 | c2): degree 3, one AND under the measurement
            let m = c.alloc_bit();
            c.hmr(k3, m);
            c.release_clean(k3);
            c.push_condition(m);
            let u = and_new(c, f0, c2);
            let b = Lin::of(&[f0, c2, u]);
            let a = Lin::of(&[f1]);
            let (ha, hb) = lin_pair_on(c, &a, &b);
            c.cz(ha, hb);
            lin_pair_off(c, &a, &b);
            and_erase(c, u, f0, c2);
            c.pop_condition();
            c.free_bit(m);
        }
    }
}
/// The forms of k3_p: k3 = A & (B ^ u), u = a0 & b0.
fn a2_block_forms(c: &mut Builder, t: usize) -> (Lin, Lin, Lin, Lin) {
    let f = a2_field(t);
    let mut wire = |c: &mut Builder, q: Option<QubitId>| -> QubitId {
        q.unwrap_or_else(|| {
            let z = c.alloc_qubit();
            A2_TEMPS.with(|v| v.borrow_mut().push(z));
            z
        })
    };
    let f0 = wire(c, f[0]);
    let f1 = wire(c, f[1]);
    match a2_pos(t) {
        1 => {
            let c3 = wire(c, a2_cell(a2_block_tick(t, 3)));
            // k3_1 = f0 & (1 ^ u), u = f1 & !c3
            (Lin::of(&[f0]), Lin::k(true), Lin::of(&[f1]), Lin { w: vec![c3], one: true })
        }
        2 => {
            let c1 = wire(c, a2_cell(a2_block_tick(t, 1)));
            // k3_2 = (f0 ^ f1) & (f1 ^ c1 ^ u), u = f1 & c1
            (Lin::of(&[f0, f1]), Lin::of(&[f1, c1]), Lin::of(&[f1]), Lin::of(&[c1]))
        }
        _ => {
            let c2 = wire(c, a2_cell(a2_block_tick(t, 2)));
            // k3_3 = f1 & (f0 ^ c2 ^ u), u = f0 & c2
            (Lin::of(&[f1]), Lin::of(&[f0, c2]), Lin::of(&[f0]), Lin::of(&[c2]))
        }
    }
}
/// Random-access read of the block: fresh wires (k3, k2). 3 Toffoli; erase with [`a2_code_read_erase`] (one conditional AND).
pub(super) fn a2_code_read(c: &mut Builder, t: usize) -> (QubitId, QubitId) {
    let (a, b, a0, b0) = a2_block_forms(c, t);
    let u = lin_and(c, &a0, &b0);
    let k3 = lin_and(c, &a, &b.x(&Lin::of(&[u])));
    lin_and_erase(c, u, &a0, &b0);
    a2_code_temps_free(c);
    let cp = a2_cell(t).expect("a2 code: own cell");
    c.x(k3);
    let k2 = and_new(c, cp, k3);
    c.x(k3);
    (k3, k2)
}
pub(super) fn a2_code_read_erase(c: &mut Builder, t: usize, k3: QubitId, k2: QubitId) {
    let cp = a2_cell(t).expect("a2 code: own cell");
    c.x(k3);
    and_erase(c, k2, cp, k3);
    c.x(k3);
    let (a, b, a0, b0) = a2_block_forms(c, t);
    let m = c.alloc_bit();
    c.hmr(k3, m);
    c.release_clean(k3);
    c.push_condition(m);
    let u = lin_and(c, &a0, &b0);
    let bu = b.x(&Lin::of(&[u]));
    let (ha, hb) = lin_pair_on(c, &a, &bu);
    c.cz(ha, hb);
    lin_pair_off(c, &a, &bu);
    lin_and_erase(c, u, &a0, &b0);
    c.pop_condition();
    c.free_bit(m);
    a2_code_temps_free(c);
}
fn a2_code_temps_free(c: &mut Builder) {
    let v = A2_TEMPS.with(|v| std::mem::take(&mut *v.borrow_mut()));
    for z in v { c.release_clean(z); }
}
/// Reverse pop of position 3: k3 on a fresh wire, the block back to its state after position 2.
fn a2_code_pop3(c: &mut Builder, t: usize) -> QubitId {
    let f = a2_field(t);
    let (f0, f1) = (f[0].unwrap(), f[1].unwrap());
    let c2 = a2_cell(t - 2).expect("a2 code: c2");
    let c3 = a2_cell(t).expect("a2 code: c3");
    let first = a2_cell(t - 4).is_some();
    let kn = and_new(c, f0, f1);
    let x1 = first.then(|| and_new(c, kn, c3));
    let x2 = lin_and(c, &Lin::of(&[f1, kn]), &Lin::of(&[c2]));
    c.cx(x2, kn); // kn's wire holds k3 from here on
    let k3 = kn;
    if let Some(x) = x1 { c.cx(x, c3); }
    c.cx(x2, c2);
    c.cx(k3, f0);
    c.cx(x2, f0);
    if let Some(x) = x1 { c.cx(x, f0); }
    c.cx(k3, f1);
    c.cx(x2, f1);
    if let Some(x) = x1 { and_erase(c, x, k3, f0); }
    and_erase(c, x2, k3, f1);
    k3
}
fn a2_tid(t: usize) -> usize { if a2_dense() { t } else { (t / 6) * 2 + t % 2 } }
fn a2_pos(t: usize) -> usize { if a2_dense() { 1 } else { (t % 6) / 2 + 1 } }
thread_local! {
    /// The record's fields by triple id: [f0, f1] (None once consumed by the reverse).
    static A2_REC: std::cell::RefCell<std::collections::HashMap<usize, [Option<QubitId>; 2]>> = std::cell::RefCell::new(std::collections::HashMap::new());
}
/// rec4 F1LAZY (exact): f1 is first written at position 2, so its wire is allocated there instead of at the
/// triple's first tick; until then it is |0> and every reader takes it as the constant 0 (as a consumed slot). The
/// wire is off the live count over the position-1 tick and the tick after it.
const F1LAZY: bool = true;
fn f1lazy() -> bool {
    F1LAZY
}
/// The field of tick t's triple; at its first tick (forward) the two wires are allocated (F1LAZY: f1 at position 2).
fn a2_field_open(c: &mut Builder, t: usize) {
    let id = a2_tid(t);
    if a2_pads_on() {
        if t == 1 {
            let n = (1..rounds() - 1).filter(|&u| a2_pos3(u)).count();
            let v: Vec<QubitId> = (0..n).map(|_| c.alloc_qubit()).collect();
            A2_PADS.with(|p| *p.borrow_mut() = v);
        }
        if a2_pos3(t) {
            let q = A2_PADS.with(|p| p.borrow_mut().pop()).expect("a2: pad pool");
            c.release_clean(q);
        }
    }
    let f = A2_REC.with(|r| r.borrow().get(&id).copied());
    match f {
        Some([Some(_), Some(_)]) => {}
        Some([Some(_), None]) if f1lazy() && a2_pos(t) >= 2 => {
            let b = c.alloc_qubit();
            A2_REC.with(|r| r.borrow_mut().get_mut(&id).unwrap()[1] = Some(b));
        }
        None => {
            // a triple opens at its first A tick: position 1, or position 2 for rail 0's first triple (tick 0 is not
            // an A tick; its f0 stays 0)
            assert!(a2_pos(t) == 1 || t == 2, "a2: tick {t} opens its triple's field but is not its first A tick");
            if f1lazy() && a2_pos(t) == 1 {
                let a = c.alloc_qubit();
                A2_REC.with(|r| r.borrow_mut().insert(id, [Some(a), None]));
            } else {
                let w = [c.alloc_qubit(), c.alloc_qubit()];
                A2_REC.with(|r| r.borrow_mut().insert(id, [Some(w[0]), Some(w[1])]));
            }
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
    if a2_code() { return Lin::k(false); }
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
/// rec4 K3INF (exact): at position 1 (code (1,0)) and position 2 (code (0,1)) the write is one CNOT into a slot that
/// still holds 0 (f0 is opened at position 1; f1 is written first at position 2), so after the write that slot equals
/// k3 on every state. The decision writes k3 into the slot itself: one wire fewer from the decision to the end of the
/// tick (the payload op included), no write and no erase. Some(slot) on such a tick, None otherwise (position 3, or
/// K3INF off).
const K3INF: bool = true;
fn k3inf() -> bool {
    K3INF
}
fn a2_k3_slot(t: usize) -> Option<QubitId> {
    if !k3inf() {
        return None;
    }
    let f = a2_field(t);
    match a2_pos(t) {
        1 => f[0],
        2 => f[1],
        _ => None,
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
    if t+2==rounds() && std::env::var("RAIL_OPT_ALIAS").ok().as_deref()==Some("1") {assert!(a.w==vec![k3] && !a.one && b.w.is_empty() && b.one);return;}
    let m = c.alloc_bit();
    c.hmr(k3, m);
    c.release_clean(k3);
    a2_cz_forms_if(c, &a, &b, m);
    c.free_bit(m);
}
/// Non-consuming read: k3 = [f == code(pos t)] on a fresh wire (1 AND); erase it with [`a2_k3_erase_rec`].
fn a2_read(c: &mut Builder, t: usize) -> QubitId {
    if t+2==rounds() && std::env::var("RAIL_OPT_ALIAS").ok().as_deref()==Some("1") {
        let (a,b)=a2_code_forms(t);assert_eq!(a.w.len(),1);assert!(!a.one && b.w.is_empty() && b.one);
        let q=a.w[0];if false{c.x(q);}return q;
    }
    let (a, b) = a2_code_forms(t);
    a2_and_forms(c, &a, &b)
}
/// Consuming read (reverse rails pass, positions 3, 2, 1 in that order): pos 3: k3 = f0 f1 (1 AND), then the
/// field un-written (f ^= 3 k3); pos 2: k3 is f1 itself; pos 1: k3 is f0 itself (the field leaves with it). The
/// returned wire is erased by the k-letter erase against the rail.
fn a2_consume(c: &mut Builder, t: usize) -> QubitId {
    let id = a2_tid(t);
    if a2_code() {
        let f = a2_field(t);
        let out = match a2_pos(t) {
            3 => a2_code_pop3(c, t),
            2 if t == 2 => {
                A2_REC.with(|r| r.borrow_mut().remove(&id));
                c.release_clean(f[0].expect("a2: f0"));
                f[1].expect("a2: f1 consumed twice")
            }
            2 => {
                let (f0, f1) = (f[0].unwrap(), f[1].unwrap());
                let c1 = a2_cell(t - 2).expect("a2 code: c1");
                let m = and_new(c, f0, c1);
                c.cx(m, c1);
                c.cx(m, f1);
                and_erase(c, m, f0, f1);
                A2_REC.with(|r| r.borrow_mut().get_mut(&id).unwrap()[1] = None);
                f1
            }
            _ => {
                if let Some(f1) = f[1] {
                    assert!(!a2_tick(t + 2), "a2: the field's f1 outlived its position 2");
                    c.release_clean(f1);
                }
                A2_REC.with(|r| r.borrow_mut().remove(&id));
                f[0].expect("a2: f0 consumed twice")
            }
        };
        A2_CELLS.with(|m| { m.borrow_mut().remove(&t); });
        return out;
    }
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
    include_str!("leapfrog_data/a2_R124_steps.txt").to_string()
}
/// The A window anchors: LFA2_ANCH, or LFA2_TABLE + ".anch", or the embedded ones.
fn a2_anch_text() -> String {
    include_str!("leapfrog_data/a2_R124_anch.txt").to_string()
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
        ("LF_REORDER_MUL", "43"),
        ("SL_N2_DFROM", "116"),
        ("SL_N2_MFROM", "116"),
        ("LF_CMP_FROM", "106"),
        // the walk cap of A's build (the multiply's N2-batch reverse ticks bind it); rec4: 1240 with F1LAZY and K3INF
        // (the record wires they take off the live count make plans below 1242 fit; without them 1241 does not)
        ("HEO_PIN_PP_WALK_MAX_QUBITS", "1234"),
    ] {
        match std::env::var(format!("LFA2_SET_{k}")) {
            Ok(o) => std::env::set_var(k, o),
            Err(_) => std::env::set_var(k, v),
        }
    }
}
/// At a walk's end every field is gone.

// ---------------------------------------------------------------------------------------------------------------------
// T3P-1 MAJ: majority pack of the A record. After forward tick 95 the fields of triples 0..31 are closed and dormant
// until the reverse reaches tick 95. N = 63 of their 64 wires (all but triple 31's f1) are packed: x* (triple 31's
// f0) is fanned out into the other 62 (z) and X-measured. On every block of weight <= 31 (half of all values; measured
// 3e-6 of walks fall outside) x* = [wt(z) >= 32], so its phase is a function of z, fixed at the unpack where x* is
// recomputed as bit 5 of popcount(z) (57 Toffoli, every AND measured away). An excluded block restores a wrong field:
// a classical failure of that input. One record wire is off the live count from forward tick 96 to reverse tick 96.
// ---------------------------------------------------------------------------------------------------------------------
const T3P1_MAJ_BAKED: bool = true;
/// Pack after this forward tick, unpack before this reverse tick (every packed triple is closed by then).
const T3P1_MAJ_TICK: usize = 95;
/// Triples 0 .. T3P1_MAJ_TIDS are packed (x* = f0 of the last one; its f1 stays outside the pack).
const T3P1_MAJ_TIDS: usize = 32;
pub(super) fn t3p1_maj_on() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| !a2_dense() && !a2_code() && (T3P1_MAJ_BAKED || std::env::var("T3P1_MAJ").is_ok_and(|v| v == "1")))
}
thread_local! {
    /// The pack's measurement bit while the pack is out (laneT: a stack of (tick, lo, hi, bit)).
    static T3P1_PACK: std::cell::RefCell<Vec<(T3Pack, crate::circuit::BitId)>> = const { std::cell::RefCell::new(Vec::new()) };
}
/// laneT: LFT_PACK = "tick:lo-hi,..." majority packs of closed record triples lo..hi (x* = f0 of triple hi - 1). Without it, the baked T3P1 entry where that is on.
#[derive(Clone, Copy)]
struct T3Pack { t: usize, lo: usize, hi: usize, c1: usize, c2: usize, thr: usize, xf1: bool }
fn t3p1_list() -> Vec<T3Pack> {
    if let Ok(v) = std::env::var("LFT_PACK") {
        return v.split(',').filter(|x| !x.is_empty()).map(|r| {
            let (r, xf1) = match r.strip_suffix("+1") { Some(x) => (x, true), None => (r, false) };
            let (r, thr) = match r.split_once('@') { Some((x, y)) => (x, y.parse().unwrap()), None => (r, 0) };
            let mut it = r.split(':');
            let t: usize = it.next().unwrap().parse().unwrap();
            let (a, b) = it.next().unwrap().split_once('-').unwrap();
            let (c1, c2) = match it.next() { Some(cr) => { let (x, y) = cr.split_once('-').unwrap(); (x.parse().unwrap(), y.parse::<usize>().unwrap() + 1) } None => (0, 0) };
            T3Pack { t, lo: a.parse().unwrap(), hi: b.parse().unwrap(), c1, c2, thr, xf1 }
        }).collect();
    }
    if t3p1_maj_on() { vec![T3Pack { t: T3P1_MAJ_TICK, lo: 0, hi: T3P1_MAJ_TIDS, c1: 0, c2: 0, thr: 0, xf1: false }] } else { Vec::new() }
}
/// z: both field wires of triples lo .. hi - 1, the k2 cells of ticks c1 .. c2 - 1, and (xf1) f1 of triple hi - 1.
fn t3p1_maj_z(p: T3Pack) -> Vec<QubitId> {
    let mut z = A2_REC.with(|r| {
        let r = r.borrow();
        let mut z = Vec::with_capacity(2 * (p.hi - p.lo));
        for id in p.lo..p.hi - 1 {
            let f = r.get(&id).unwrap_or_else(|| panic!("t3p1: triple {id} has no field at the pack"));
            for (s, q) in f.iter().enumerate() {
                z.push(q.unwrap_or_else(|| panic!("t3p1: triple {id} slot {s} is empty at the pack")));
            }
        }
        if p.xf1 { z.push(r.get(&(p.hi - 1)).and_then(|f| f[1]).expect("t3p1: f1 of the last triple")); }
        z
    });
    for t in p.c1..p.c2 { z.push(a2_cell(t).unwrap_or_else(|| panic!("t3p1: tick {t} has no k2 cell"))); }
    z
}
pub(super) fn t3p1_pack_tick(c: &mut Builder, t: usize) {
    for p in t3p1_list() { if p.t == t { t3p1_pack(c, p); } }
}
pub(super) fn t3p1_unpack_tick(c: &mut Builder, t: usize) {
    let top = T3P1_PACK.with(|s| s.borrow().iter().rev().take_while(|e| e.0.t == t).count());
    for _ in 0..top { t3p1_unpack(c); }
}
fn t3p1_pack(c: &mut Builder, p: T3Pack) {
    let z = t3p1_maj_z(p);
    let last = p.hi - 1;
    let xs = A2_REC.with(|r| r.borrow().get(&last).and_then(|f| f[0])).expect("t3p1: x* (f0 of the last packed triple)");
    for &q in &z {
        c.cx(xs, q);
    }
    let m = c.alloc_bit();
    c.hmr(xs, m);
    c.release_clean(xs);
    A2_REC.with(|r| r.borrow_mut().get_mut(&last).unwrap()[0] = None);
    T3P1_PACK.with(|s| s.borrow_mut().push((p, m)));
    if std::env::var("ROOM_TRACE").is_ok_and(|v| v == "1") {
        eprintln!("T3P1_PACK out n={} active={}", z.len() + 1, c.active_qubits());
    }
}
fn t3p1_unpack(c: &mut Builder) {
    let (p, m) = T3P1_PACK.with(|s| s.borrow_mut().pop()).expect("t3p1: unpack without a pack");
    let z = t3p1_maj_z(p);
    let a0 = c.active_qubits();
    let e0 = c.expected_total();
    let xs = c.alloc_qubit();
    let peak = t3p1_threshold_top(c, &z, xs, p.thr);
    c.z_if(xs, m);
    c.free_bit(m);
    for &q in &z {
        c.cx(xs, q);
    }
    let last = p.hi - 1;
    A2_REC.with(|r| r.borrow_mut().get_mut(&last).unwrap()[0] = Some(xs));
    if std::env::var("ROOM_TRACE").is_ok_and(|v| v == "1") {
        eprintln!("T3P1_PACK in n={} active={a0} peak={peak} cost={:.1}", z.len() + 1, c.expected_total() - e0);
    }
}
/// out ^= [wt(z) >= 2^k] with 2^k <= len(z) < 2^(k+1): carry-save reduction of the columns below k (full adders,
/// a half adder's carry when two bits are left; residual column bits are never needed), the column-k bit copied
/// out, every AND measured away. Returns the peak live count.
fn t3p1_threshold_top(c: &mut Builder, z: &[QubitId], out: QubitId, thr: usize) -> u32 {
    let n = z.len();
    let k = (usize::BITS - 1 - n.leading_zeros()) as usize;
    assert!(n >= 2 && (1usize << k) <= n && n < (1usize << (k + 1)));
    enum St { Fa(QubitId, QubitId, QubitId, QubitId), Ha(QubitId, QubitId, QubitId) }
    let mut steps: Vec<St> = Vec::new();
    let mut col: Vec<QubitId> = z.to_vec();
    // laneT: thr != 0: residual column bits, as forms, for the comparison [wt >= thr]
    let mut res: Vec<Lin> = Vec::new();
    for _w in 0..k {
        let mut next = Vec::new();
        while col.len() >= 3 {
            let a = col.pop().unwrap();
            let b = col.pop().unwrap();
            let cc = col.pop().unwrap();
            c.cx(a, b);
            c.cx(a, cc);
            let carry = and_new(c, b, cc);
            c.cx(a, carry);
            c.cx(b, cc);
            c.cx(a, cc);
            steps.push(St::Fa(a, b, cc, carry));
            col.insert(0, cc);
            next.push(carry);
        }
        if col.len() == 2 {
            let a = col.pop().unwrap();
            let b = col.pop().unwrap();
            let carry = and_new(c, a, b);
            steps.push(St::Ha(a, b, carry));
            next.push(carry);
            res.push(Lin::of(&[a, b]));
        } else if col.len() == 1 {
            res.push(Lin::of(&[col[0]]));
        } else {
            res.push(Lin::k(false));
        }
        col = next;
    }
    assert!(col.len() <= 1, "t3p1: column k holds {} bits", col.len());
    if let Some(&b) = col.first() {
        c.cx(b, out);
    }
    // laneT: out ^= [wt mod 2^k >= thr] for thr in (2^(k-1), 2^k), which excludes wt >= 2^k when n < 2^k + 2^(k-1)
    let mut recs: Vec<(QubitId, Lin, Lin)> = Vec::new();
    if thr != 0 && thr != (1 << k) {
        assert!(thr > (1 << (k - 1)) && thr < (1 << k) && n < (1 << k) + (1 << (k - 1)), "t3p1: threshold {thr} for n = {n}");
        let j = thr.trailing_zeros() as usize;
        let mut ge = res[j].clone(); // [wt mod 2^(j + 1) >= thr mod 2^(j + 1)]
        for i in j + 1..k {
            let (a, b) = if thr >> i & 1 == 1 { (res[i].clone(), ge.clone()) } else { (res[i].x(&Lin::k(true)), ge.x(&Lin::k(true))) };
            let q = lin_and(c, &a, &b);
            ge = if thr >> i & 1 == 1 { l_of(q) } else { l_of(q).x(&Lin::k(true)) };
            recs.push((q, a, b));
        }
        lin_xor_into(c, &ge, out);
    }
    let peak = c.active_qubits();
    while let Some((q, a, b)) = recs.pop() {
        lin_and_erase(c, q, &a, &b);
    }
    for s in steps.into_iter().rev() {
        match s {
            St::Fa(a, b, cc, carry) => {
                c.cx(a, cc);
                c.cx(b, cc);
                c.cx(a, carry);
                and_erase(c, carry, b, cc);
                c.cx(a, cc);
                c.cx(a, b);
            }
            St::Ha(a, b, carry) => and_erase(c, carry, a, b),
        }
    }
    peak
}
fn l_of(q: QubitId) -> Lin { Lin::of(&[q]) }
pub(super) fn a2_rec_empty() -> bool { A2_REC.with(|r| r.borrow().is_empty()) }
/// round17 v4: R1 on A ticks (LFA2_R1, default on): the 8-way barrel has an R1 plan at width w no dearer than its plain one.
fn a2_r1_ok(w: usize) -> bool {
    if a2_rail_s6(w) { return !std::env::var("LFA2_R1").is_ok_and(|v| v == "0"); }
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
fn zlin_on_a(c: &mut Builder, t: &[QubitId], b: &[QubitId], vtop: usize) {
    let top = t.len() - 1;
    c.cx(b[1], t[1]);
    for i in 2..=vtop {
        c.cx(b[i], t[i]);
        c.cx(t[1], t[i]);
    }
    c.cx(b[top.min(b.len() - 1)], t[top]);
    c.cx(t[1], t[top]);
}
fn zlin_off_a(c: &mut Builder, t: &[QubitId], b: &[QubitId], vtop: usize) {
    let top = t.len() - 1;
    c.cx(t[1], t[top]);
    c.cx(b[top.min(b.len() - 1)], t[top]);
    for i in 2..=vtop {
        c.cx(t[1], t[i]);
        c.cx(b[i], t[i]);
    }
    c.cx(b[1], t[1]);
}
/// The A decision at the pause ([`yp8_logic`] with e <= 7 and the record): `spent` = the record's linear form for
/// this tick. outs = Some((out, k1, k2, k3)) writes the choice and shift letters; None applies (-1)^out.
fn yp8_logic_a(c: &mut Builder, t2: &[QubitId], b: &[QubitId], s1: QubitId, ct: QubitId, tick: usize, spent: &Lin, outs: Option<(QubitId, QubitId, QubitId, QubitId)>) {
    let rail_opt_entry=c.active_qubits();
    let ((),rail_opt_peak)=c.r3_peak(|c| {
    // laneW code: position 3 is spent when f0 & c1 (one AND, around the decision)
    let sp_pair = a2_sp_pair(tick);
    let sp_wire = sp_pair.map(|(a, b)| and_new(c, a, b));
    let spent_owned = sp_wire.map_or_else(|| spent.clone(), |q| Lin::of(&[q]));
    let spent = &spent_owned;
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
        while v.len() < a2_emax(tick) + 3 {
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
    let vtop_all = a2_emax(tick) + 1;
    zlin_on_a(c, &tv, &bview, vtop_all);
    // !Y as an AND operand
    let ny = |c: &mut Builder| {
        if let Lit::W(wq, false) = w {
            c.x(wq);
        }
    };
    let veto = !matches!(w, Lit::One);
    match outs {
        Some((out, k1, k2, k3)) => {
            for i in 2..=vtop_all {
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
            // laneW: the chain stops at v = emax + 1; v > emax + 1 is inadmissible (flat), so I = (p4 ^ g) ^ p(emax + 1)
            let emax = a2_emax(tick);
            let vtop = emax + 1;
            let mut pc: Vec<QubitId> = vec![gw];
            for i in 5..=vtop {
                let q = and_new(c, *pc.last().unwrap(), tv[i]);
                pc.push(q);
            }
            let ptop = *pc.last().unwrap();
            if let Some(gq) = g {
                c.cx(gq, out);
            } else {
                c.cx(a2, out);
            }
            c.cx(ptop, out);
            c.cx(gw, k3);
            c.cx(ptop, k3);
            if emax >= 6 {
                c.cx(pc[2], k2);
                c.cx(ptop, k2);
            }
            // v = 5 (and v = 7 where admissible) leave Dsel's k1
            c.cx(pc[0], k1);
            c.cx(pc[1], k1);
            if emax >= 6 {
                c.cx(pc[2], k1);
                c.cx(pc[3], k1);
            }
            for i in (5..=vtop).rev() {
                and_erase(c, pc[i - 4], pc[i - 5], tv[i]);
            }
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
            for i in 2..=vtop_all {
                c.x(tv[i]);
            }
            c.cx(out, k1);
            c.cx(tv[1], out);
        }
        None => {
            c.x(tv[1]);
            c.z_if(tv[1], NO_BIT); // dq ^ 1
            c.x(tv[1]);
            for i in 2..=vtop_all {
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
                // laneW: the phase of p(emax + 1) = p(emax) & !z(emax + 1)
                let vtop = a2_emax(tick) + 1;
                let mut pc: Vec<QubitId> = vec![gw];
                for i in 5..vtop {
                    let q = and_new(c, *pc.last().unwrap(), tv[i]);
                    pc.push(q);
                }
                c.cz(*pc.last().unwrap(), tv[vtop]);
                for i in (5..vtop).rev() {
                    and_erase(c, pc[i - 4], pc[i - 5], tv[i]);
                }
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
            for i in 2..=vtop_all {
                c.x(tv[i]);
            }
        }
    }
    zlin_off_a(c, &tv, &bview, vtop_all);
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
    if let (Some(q), Some((a, b))) = (sp_wire, sp_pair) { and_erase(c, q, a, b); }
    });
    assert!(rail_opt_peak as usize<=cells::cap(),"rail_opt reserve: tick{tick} peak{rail_opt_peak}");
    if std::env::var("RAIL_OPT_RESERVE").ok().as_deref()==Some("1") && false {c.z_if(t2[0],NO_BIT);}

}


/// [`yp8_reserve`] for the A decision: 5 more AND wires (g, p5..p8) and views padded to 10 positions.
fn yp8_reserve_a(tl: usize, bl: usize, t: usize, fwd: bool) -> usize {
    let pad = a2_emax(t) + 3;
    let old=yp8_reserve(tl, bl, t, fwd) + (a2_emax(t) - 2) + pad.saturating_sub((tl + 1).max(6)) + pad.saturating_sub((bl + 1).max(6));
    if std::env::var("RAIL_OPT_RESERVE").ok().as_deref()==Some("1") {
        if a2_code() { if a2_pos(t) <= 2 || t == 4 { old - 3 } else { old - 1 } } else { old-(2+usize::from(a2_pos(t)==1||t==2)) }
    } else { old }
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
    let low = (h >= 1).then(|| (a2_emax(tick) + 1, h - 1));
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
    let emax = a2_emax(0);
    if w >= 8 && emax >= 6 {
        c.push_condition(m1);
        let kk = and_new(c, k2, k3);
        c.x(t[6]);
        c.cz(kk, t[6]);
        c.x(t[6]);
        and_erase(c, kk, k2, k3);
        c.pop_condition();
    }
    c.free_bit(m1);
    if emax <= 5 {
        // Q3: k2 ^ k3 = z0 z1 on x3 = 2^e odd with e <= 5, so that wire goes last with a Clifford fix; k3 = (k2 ^ k3) z2 z3 goes
        // first, one AND under its measurement instead of the two of z0 z1 z2 z3.
        if w >= 6 { c.cx(k3, k2); }
        let m3 = c.alloc_bit();
        c.hmr(k3, m3);
        c.release_clean(k3);
        if w >= 6 {
            c.push_condition(m3);
            let b2 = and_new(c, t[2], t[3]);
            c.cz(k2, b2);
            and_erase(c, b2, t[2], t[3]);
            c.pop_condition();
        }
        c.free_bit(m3);
        let m2 = c.alloc_bit();
        c.hmr(k2, m2);
        c.release_clean(k2);
        c.cz_if(t[0], t[1], m2);
        c.free_bit(m2);
        for i in (0..nz).rev() {
            c.x(t[i]);
        }
        return;
    }
    let m2 = c.alloc_bit();
    c.hmr(k2, m2);
    c.release_clean(k2);
    c.cz_if(t[0], t[1], m2);
    if w >= 6 {
        c.z_if(k3, m2);
        if emax >= 6 {
            c.push_condition(m2);
            let zz = and_new(c, t[4], t[5]);
            c.cz(k3, zz);
            and_erase(c, zz, t[4], t[5]);
            c.pop_condition();
        }
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
        let t = if main { t } else { super::late_t(t) };
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
        let fam = |m: u32| -> bool { let r0 = m & 0x15; let r1 = m & 0x2a; super::a2_dense() || if super::a2_code() { r0.count_ones() <= 2 && r1.count_ones() <= 2 } else { r0.count_ones() <= 1 && r1.count_ones() <= 1 } };
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
            let mut cap = if t == 0 || last || main { 3 } else { super::a2_emax(t) };
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
                        if a2_tick(t) && a2_code() {
                            let f = rec.get(&a2_tid(t)).expect("a2: field");
                            let p = a2_pos(t);
                            let cell = |q: usize| -> bool { let u = t + 2 * q - 2 * p; u < r && u > 0 && a2_tick(u) && rd(tape[u][tape[u].len() - 1]) };
                            let (f0, f1) = (f[0].is_some_and(|q| rd(q)), f[1].is_some_and(|q| rd(q)));
                            let (c1, c2, c3) = (cell(1), cell(2), cell(3));
                            let k3 = match p { 1 => f0 && !(f1 && !c3), 2 => (f0 ^ f1) && (f1 || c1), _ => f1 && (f0 || c2) };
                            let k2 = !k3 && [c1, c2, c3][p - 1];
                            e = usize::from(rd(lt[nf + 1])) + 2 * usize::from(k2) + 4 * usize::from(k3);
                        } else if a2_tick(t) {
                            let f = rec.get(&a2_tid(t)).expect("a2: field");
                            // F1LAZY: f1 of a triple cut by the walk's end was never opened
                            let fv = usize::from(rd(f[0].unwrap())) + 2 * usize::from(f[1].is_some_and(|q| rd(q)));
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
