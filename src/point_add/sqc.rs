//! round10/square-chains (research, off by default; SQC_G1M=1): frame-X travel by one-digit REDC, and
//! C = s^2 added DIRECTLY into out (frame X) with chained rows (round-10 G1 junction flip), its affine
//! correction and a top-bits wrap witness. Every ripple here is a "held-carry" ripple: sums are written in
//! the forward pass (so later columns may read them), every carry is held, then all carries are erased
//! top-down by X-measurement with CZ fix-ups (each carry is MAJ of affine forms of live wires).
use super::Builder;
use crate::circuit::{BitId, QubitId};

/// [`c_direct`]'s w read off the live top-bit sum E while E is alive; no W register (false = the parent's gates).
const W_FUSE: bool = true;
pub(super) fn on() -> bool { !std::env::var("SQC_G1M").is_ok_and(|v| v == "0") }
pub(super) fn g() -> usize { std::env::var("SQC_G").ok().and_then(|v| v.parse().ok()).unwrap_or(24) }
pub(super) fn t_top() -> usize { std::env::var("SQC_T").ok().and_then(|v| v.parse().ok()).unwrap_or(21) }

#[derive(Clone, Copy)]
pub(super) enum W { Q(QubitId), T(usize) }
pub(super) struct Rec { pub col: usize, pub x: QubitId, pub o: Option<W>, pub ci: Option<W>, pub neg: bool,
                        pub carry: bool, pub flips: Vec<QubitId>, pub ocomp: bool, pub frame: Option<QubitId> }


thread_local! {static RAIL_OPT_COMPLEMENT:std::cell::Cell<Option<(QubitId,QubitId)>>=const {std::cell::Cell::new(None)};}
fn rail_opt_complement(o:Option<QubitId>,ci:Option<QubitId>)->bool {
    RAIL_OPT_COMPLEMENT.with(|v|v.get().is_some_and(|(a,b)| (o==Some(a)&&ci==Some(b))||(o==Some(b)&&ci==Some(a))))
}
pub(super) fn rail_opt_redc_seed(c:&mut Builder,out:&[QubitId])->usize {
    let ev=c.alloc_qubit();c.cx(out[0],ev);c.x(ev);
    let mut recs=plan_redc(out,g());
    let mut n=0;
    for r in &mut recs {if [4,6,10,32].contains(&r.col) && r.ci.is_none(){assert!(matches!(r.o,Some(W::Q(q)) if q==out[0]));r.ci=Some(W::Q(ev));n+=1;}}
    assert_eq!(n,4);
    RAIL_OPT_COMPLEMENT.with(|v|{assert!(v.get().is_none());v.set(Some((out[0],ev)));});
    let k=emit(c,&recs,true);
    RAIL_OPT_COMPLEMENT.with(|v|v.set(None));
    if std::env::var("FRAME_SEED_FAULT").ok().as_deref()!=Some("1"){c.cx(ev,out[0]);}
    super::leapfrog::rail_opt_accept_seed(c,out,ev);k
}
fn erase_and(c: &mut Builder, t: QubitId, u: QubitId, v: QubitId) {
    let m = c.alloc_bit(); c.hmr(t, m); c.cz_if(u, v, m); c.free_bit(m); c.release_clean(t);
}
fn rw(w: Option<W>, tw: &[Option<QubitId>]) -> Option<QubitId> {
    w.map(|w| match w { W::Q(q) => q, W::T(i) => tw[i].expect("carry wire") })
}
/// AND of the FA inputs: compute into a fresh wire (compute=true) or erase the held carry (compute=false).
/// On entry x holds (value right after this FA) ^ neg.
fn and_io(c: &mut Builder, x: QubitId, o: Option<QubitId>, ci: Option<QubitId>, slot: &mut Option<QubitId>, compute: bool) {
    if rail_opt_complement(o,ci) {
        if compute {let q=c.alloc_qubit();c.x(q);c.cx(x,q);*slot=Some(q);}
        else {let q=slot.take().unwrap();c.cx(x,q);c.x(q);c.release_clean(q);}
        return;
    }
    let mut and = |c: &mut Builder, u: QubitId, v: QubitId, fix: Option<QubitId>| {
        if compute { let q = c.alloc_qubit(); c.ccx(u, v, q); if let Some(f) = fix { c.cx(f, q); } *slot = Some(q); }
        else { let q = slot.take().unwrap(); if let Some(f) = fix { c.cx(f, q); } erase_and(c, q, u, v); }
    };
    match (o, ci) {
        (Some(o), Some(ci)) => { c.cx(o, x); c.cx(ci, o); and(c, x, o, Some(ci)); c.cx(ci, o); c.cx(o, x); }
        (Some(o), None) => { c.cx(o, x); and(c, x, o, None); c.cx(o, x); }
        (None, Some(ci)) => { c.cx(ci, x); and(c, x, ci, None); c.cx(ci, x); }
        (None, None) => {}
    }
}
fn delta(c: &mut Builder, recs: &[Rec], tw: &[Option<QubitId>], i: usize) {
    // XOR into x the sum updates of the later records of the same column (affine prelude)
    let mut k = i + 1;
    while k < recs.len() && recs[k].col == recs[i].col {
        if recs[k].ocomp { c.x(recs[i].x); } // complement contributes a constant to the later sum
        if let Some(o) = rw(recs[k].o, tw) { c.cx(o, recs[i].x); }
        if let Some(q) = rw(recs[k].ci, tw) { c.cx(q, recs[i].x); }
        for &q in &recs[k].flips {c.cx(q,recs[i].x);}
        k += 1;
    }
}
/// Emit a planned held-carry ripple. inverse=false: the forward map; inverse=true: its exact inverse
/// (same AND count: erasures become recomputations and vice versa).
pub(super) fn emit(c: &mut Builder, recs: &[Rec], inverse: bool) -> usize {
    let n = recs.len(); let mut tw: Vec<Option<QubitId>> = vec![None; n]; let mut ands = 0;
    let fa = |c: &mut Builder, r: &Rec, tw: &mut Vec<Option<QubitId>>, i: usize, fwd: bool| {
        let (o, ci) = (rw(r.o, tw), rw(r.ci, tw));
        if r.neg { c.x(r.x); } if let Some(k)=r.frame {c.cx(k,r.x);}
        if r.ocomp { if let Some(o) = o { c.x(o); } }
        if rail_opt_complement(o,ci) {
            assert!(r.flips.is_empty() && !r.ocomp && r.carry);
            if fwd {let q=c.alloc_qubit();c.cx(r.x,q);tw[i]=Some(q);c.x(r.x);}
            else {let q=tw[i].take().unwrap();c.cx(r.x,q);c.x(q);c.release_clean(q);c.x(r.x);}
        } else if fwd {
            if let Some(q) = ci { for &f in &r.flips { c.cx(f, q); } }
            if r.carry {   // x currently holds x_in: make it x_in ^ o ^ ci after computing the carry
                let mut s = None;
                match (o, ci) {
                    (Some(o), Some(q)) => { c.cx(q, r.x); c.cx(q, o); let t = c.alloc_qubit(); c.ccx(r.x, o, t); c.cx(q, t); c.cx(q, o); c.cx(o, r.x); s = Some(t); }
                    (Some(o), None) => { let t = c.alloc_qubit(); c.ccx(r.x, o, t); c.cx(o, r.x); s = Some(t); }
                    (None, Some(q)) => { let t = c.alloc_qubit(); c.ccx(r.x, q, t); c.cx(q, r.x); s = Some(t); }
                    (None, None) => {}
                }
                tw[i] = s;
            } else { if let Some(o) = o { c.cx(o, r.x); } if let Some(q) = ci { c.cx(q, r.x); } }
        } else {
            if r.carry {
                let mut s = tw[i].take();
                match (o, ci) {
                    (Some(o), Some(q)) => { c.cx(o, r.x); c.cx(q, o); let t = s.take().unwrap(); c.cx(q, t); erase_and(c, t, r.x, o); c.cx(q, o); c.cx(q, r.x); }
                    (Some(o), None) => { c.cx(o, r.x); erase_and(c, s.take().unwrap(), r.x, o); }
                    (None, Some(q)) => { c.cx(q, r.x); erase_and(c, s.take().unwrap(), r.x, q); }
                    (None, None) => {}
                }
            } else { if let Some(o) = o { c.cx(o, r.x); } if let Some(q) = ci { c.cx(q, r.x); } }
            if let Some(q) = ci { for &f in r.flips.iter().rev() { c.cx(f, q); } }
        }
        if r.ocomp { if let Some(o) = o { c.x(o); } }
        if r.neg { c.x(r.x); } if let Some(k)=r.frame {c.cx(k,r.x);}
    };
    let hold = |c: &mut Builder, recs: &[Rec], tw: &mut Vec<Option<QubitId>>, i: usize, compute: bool| {
        let r = &recs[i];
        if !r.carry || (r.o.is_none() && r.ci.is_none()) { return; }
        delta(c, recs, tw, i); if r.neg { c.x(r.x); } if let Some(k)=r.frame {c.cx(k,r.x);}
        let (o, ci) = (rw(r.o, tw), rw(r.ci, tw)); let mut slot = tw[i];
        if r.ocomp { if let Some(o) = o { c.x(o); } }
        and_io(c, r.x, o, ci, &mut slot, compute); tw[i] = slot;
        if r.ocomp { if let Some(o) = o { c.x(o); } }
        if r.neg { c.x(r.x); } if let Some(k)=r.frame {c.cx(k,r.x);} delta(c, recs, tw, i);
    };
    if !inverse {
        for i in 0..n { fa(c, &recs[i], &mut tw, i, true); if tw[i].is_some() { ands += 1; } }
        for i in (0..n).rev() {
            hold(c, recs, &mut tw, i, false);
            if let Some(q) = rw(recs[i].ci, &tw) { for &f in recs[i].flips.iter().rev() { c.cx(f, q); } }
        }
    } else {
        for i in 0..n {
            if let Some(q) = rw(recs[i].ci, &tw) { for &f in &recs[i].flips { c.cx(f, q); } }
            hold(c, recs, &mut tw, i, true); if tw[i].is_some() { ands += 1; }
        }
        for i in (0..n).rev() { fa(c, &recs[i], &mut tw, i, false); }
    }
    ands
}

/// REDC plan on reg = [L | H] (256 wires): subtract (f-1)*m, m = the pass's own new low bits.
pub(super) fn plan_redc(reg: &[QubitId], g: usize) -> Vec<Rec> {
    assert_eq!(reg.len(), 256);
    let st: [(bool, usize); 4] = [(true, 4), (false, 6), (true, 10), (true, 32)];
    let merges:Vec<(usize,usize,usize)>=vec![(134,0,1),(138,1,2),(160,2,3)];
    let top = 256.min(161 + g);
    let mut carry: [Option<W>; 4] = [None; 4]; let mut dead = [false; 4]; let mut recs = Vec::new();
    for j in 0..top {
        let mut feed: [Option<W>; 4] = [None; 4]; let mut complement=[false;4];
        for &(col, a, b) in &merges { if col == j { feed[b] = carry[a]; complement[b] = st[a].0!=st[b].0; carry[a] = None; dead[a] = true; } }
        for r in 0..4 {
            if dead[r] { continue; }
            let (neg, s) = st[r];
            let own = (j >= s && j - s < 128).then(|| W::Q(reg[j - s]));
            let o = if feed[r].is_some() { assert!(own.is_none()); feed[r] } else { own };
            if o.is_none() && carry[r].is_none() { continue; }
            let cf = j + 1 < top;
            recs.push(Rec { col: j, x: reg[j], o, ci: carry[r], neg, carry: cf, flips: vec![], ocomp: complement[r], frame: None });
            carry[r] = cf.then(|| W::T(recs.len() - 1));
        }
    }
    recs
}

/// A single-stream ripple over target columns `xs` with per-column operand, carry-in and flips.
pub(super) fn plan_line(xs: &[QubitId], ops: &[Option<QubitId>], flips: &[Vec<QubitId>], cin: Option<QubitId>) -> Vec<Rec> {
    let mut recs: Vec<Rec> = Vec::new(); let mut carry = cin.map(W::Q);
    for (j, &x) in xs.iter().enumerate() {
        let cf = j + 1 < xs.len();
        recs.push(Rec { col: j, x, o: ops[j].map(W::Q), ci: carry, neg: false, carry: cf, flips: flips[j].clone(), ocomp: false, frame: None });
        carry = cf.then(|| W::T(recs.len() - 1));
    }
    recs
}

/// out <- out * 2^-128 mod p (inverse=false) or out <- out * 2^128 (inverse=true), in place (see module doc).
/// After the forward call the frame-X value's limbs are swapped: low limb = out[128..], high = out[..128].
pub(super) fn redc(c: &mut Builder, out: &[QubitId], inverse: bool) -> usize {
    let recs = plan_redc(out, g());
    emit(c, &recs, inverse)
}

/// Rows (i, pos = 2i+1, k = m-1-i) linked end to end into chains (round-10 G1).
pub(super) fn chain_plan(m: usize) -> Vec<Vec<(usize, usize, usize)>> {
    let rows: Vec<(usize, usize, usize)> = (0..m - 1).map(|i| (i, 2 * i + 1, m - 1 - i)).collect();
    let mut chains: Vec<Vec<(usize, usize, usize)>> = Vec::new();
    let mut open: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    for p in 1..2 * m {
        if let Some(&r) = rows.iter().find(|r| r.1 == p) {
            let idx = if let Some(ci) = open.remove(&(p - 1)) { chains[ci].push(r); ci }
                      else { chains.push(vec![r]); chains.len() - 1 };
            open.insert(p + r.2 - 1, idx);
        }
    }
    chains
}

/// Erase e = a + b (an out-of-place sum, no carry-in) while a and b are live, for 0 Toffolis: CNOTs turn each
/// e_i into the carry c_i, then c_39..c_1 are X-measured top-down; c_i = MAJ(a, b, c_{i-1}) (or AND / 0), so every
/// phase fix-up is CZ on live wires (round-10 G5: an out-of-place sum is free to erase while its summands live).
pub(super) fn erase_sum(c: &mut Builder, e: &[QubitId], a: &[Option<QubitId>], b: &[Option<QubitId>]) {
    for i in 0..e.len() { if let Some(x) = a[i] { c.cx(x, e[i]); } if let Some(y) = b[i] { c.cx(y, e[i]); } }
    for i in (1..e.len()).rev() {
        match (a[i - 1], b[i - 1]) {
            (Some(x), Some(y)) => { let m = c.alloc_bit(); c.hmr(e[i], m); c.cz_if(x, y, m); c.cx(x, y); c.cz_if(e[i - 1], y, m); c.cx(x, y); c.free_bit(m); }
            (Some(x), None) | (None, Some(x)) => { let m = c.alloc_bit(); c.hmr(e[i], m); c.cz_if(x, e[i - 1], m); c.free_bit(m); }
            (None, None) => {}                                   // c_i = 0: nothing to erase
        }
    }
}

fn line(c: &mut Builder, xs: &[QubitId], ops: &[Option<QubitId>], cin: Option<QubitId>) -> usize {
    let flips = vec![Vec::new(); xs.len()];
    emit(c, &plan_line(xs, ops, &flips, cin), false)
}
fn sub_line(c: &mut Builder, xs: &[QubitId], ops: &[Option<QubitId>]) -> usize {
    c.x_all(xs); let a = line(c, xs, ops, None); c.x_all(xs); a
}

/// out (frame-X view, 256 wires, value S) -= s^2 mod p, s = 129 wires; s and every scratch wire restored.
pub(super) fn c_direct(c: &mut Builder, outx: &[QubitId], s: &[QubitId]) -> usize {
    let (m, g, t) = (s.len(), g(), t_top());
    assert_eq!(outx.len(), 256); assert_eq!(m, 129);
    let mut ands = 0;
    let ext = c.alloc_qubits(3);
    let reg: Vec<QubitId> = outx.iter().chain(ext.iter()).copied().collect();
    let n = reg.len();
    // wrap witness: Ct = s_top^2 at weight 2^(2(m-t)); A = Ct >> (220 - 2(m-t)), B = S >> 220
    let ct = c.alloc_qubits(2 * t);
    super::square::sqc_leaf(c, &s[m - t..], &ct, false);
    let sh = 220 - 2 * (m - t);
    let a: Vec<QubitId> = ct[sh..].to_vec();
    let wfuse = W_FUSE;
    let w = if wfuse { Vec::new() } else { c.alloc_qubits(3) };
    // top bits w of E = A + B'; the sum is erased for free (erase_sum). erase = Some(r): instead of copying w into
    // W, apply the phase (-1)^(r.w) that X-measuring W left (the caller runs this only under r != 0).
    let topbits = |c: &mut Builder, a: &[QubitId], b: &[QubitId], comp: bool, w: &[QubitId], erase: Option<&[BitId]>| -> usize {
        let e = c.alloc_qubits(a.len() + 2);
        for i in 0..a.len() { c.cx(a[i], e[i]); }
        let ops: Vec<Option<QubitId>> = (0..e.len()).map(|i| (i < b.len()).then(|| b[i])).collect();
        let aops: Vec<Option<QubitId>> = (0..e.len()).map(|i| (i < a.len()).then(|| a[i])).collect();
        if comp { c.x_all(b); }
        let k = line(c, &e, &ops, None);
        match erase { None => for i in 0..3 { c.cx(e[36 + i], w[i]); }, Some(r) => for i in 0..3 { c.z_if(e[36 + i], r[i]); } }
        erase_sum(c, &e, &aops, &ops);
        if comp { c.x_all(b); }
        for &q in &e { c.release_clean(q); }
        k
    };
    if wfuse {
        // W_FUSE: w is read by exactly two ops, the ext add and the witness product, both before the rows and both
        // off the top bits B (they write ext and S's bits below 59). So they read w straight off E = A + ~B while E is
        // alive, and E is then erased for free while its summands live (erase_sum). No W register is ever written: no
        // X-measurement of W, and no 39-AND recomputation of the top bits on its outcome-nonzero shots (7/8 of them).
        // The wrap leaf is uncomputed right away (nothing reads it later), so ct is not held through the rows.
        let b = &reg[220..256];
        let e = c.alloc_qubits(a.len() + 2);
        for i in 0..a.len() { c.cx(a[i], e[i]); }
        let ops: Vec<Option<QubitId>> = (0..e.len()).map(|i| (i < b.len()).then(|| b[i])).collect();
        let aops: Vec<Option<QubitId>> = (0..e.len()).map(|i| (i < a.len()).then(|| a[i])).collect();
        c.x_all(b);
        ands += line(c, &e, &ops, None);                               // E = A + ~B; w = E >> 36 (3 bits)
        let wv = [e[36], e[37], e[38]];
        ands += line(c, &ext, &[Some(wv[0]), Some(wv[1]), Some(wv[2])], None);   // [S|ext] += w 2^256
        ands += witness_product(c, &reg, &wv);
        erase_sum(c, &e, &aops, &ops);
        c.x_all(b);
        for &q in &e { c.release_clean(q); }
        super::square::sqc_leaf(c, &s[m - t..], &ct, true);
        for &q in &ct { c.release_clean(q); }
    } else {
    ands += topbits(c, &a, &reg[220..256], true, &w, None);            // w = floor((A + ~B)/2^36) = ceil((A-B)/2^36)
    ands += line(c, &ext, &[Some(w[0]), Some(w[1]), Some(w[2])], None);   // [S|ext] += w 2^256
    ands+=witness_product(c,&reg,&w);
    }
    c.x_all(&reg);                                               // complement frame: rows ADD s^2
    let chains = chain_plan(m);
    
        ands+=chain_groups::run(c,&reg,s);
    
    // correction: + (~s) + 1 + sum_{i in NT} s_i 2^(i+m)  (exact value -s + .. + 2^m: 2^m X goes to the offset)
    let tops: Vec<usize> = Vec::new();
    let ops: Vec<Option<QubitId>> = (0..n).map(|j| if j < m { Some(s[j]) }
        else if j < 2 * m && !tops.contains(&(j - m)) { Some(s[j - m]) } else { None }).collect();
    let one = c.alloc_qubit(); c.x(one);
    let mut recs = plan_line(&reg, &ops, &vec![Vec::new(); n], Some(one));
    for r in recs.iter_mut().take(m) { r.ocomp = true; }           // ~s on the low m columns
    ands += emit(c, &recs, false);
    c.x(one); c.release_clean(one);
    c.x_all(&reg);
    // erase W by X-measurement: w == floor((A + S_new>>220)/2^36), so the kicked phase (-1)^(r.w) is repaired by
    // recomputing those top bits ONLY when the outcome r != 0 (exact; executed with probability 7/8).
    if wfuse {
        for &q in ext.iter() { c.release_clean(q); }
        return ands;
    }
    let r: Vec<BitId> = (0..3).map(|_| c.alloc_bit()).collect();
    for i in 0..3 { c.hmr(w[i], r[i]); }
    let flag = c.alloc_bit(); c.bit_store0(flag);
    for &ri in &r { c.push_condition(ri); c.bit_store1(flag); c.pop_condition(); }
    c.push_condition(flag);
    ands += topbits(c, &a, &reg[220..256], false, &w, Some(&r));
    c.pop_condition();
    for b in r.into_iter().chain([flag]) { c.free_bit(b); }
    for &q in w.iter().chain(ext.iter()) { c.release_clean(q); }
    super::square::sqc_leaf(c, &s[m - t..], &ct, true);
    for &q in &ct { c.release_clean(q); }
    ands
}

mod chain_groups;


fn witness_product(c:&mut Builder,reg:&[QubitId],w:&[QubitId])->usize{
 let m=c.alloc_qubits(4);c.ccx(w[0],w[1],m[0]);c.ccx(w[0],w[2],m[1]);c.ccx(w[1],w[2],m[2]);c.ccx(m[0],w[2],m[3]);
 let prod=c.alloc_qubits(13);let atoms=[w[0],w[1],m[0],w[2],m[1],m[2],m[3]];
 c.cx(atoms[0],prod[0]);
 c.cx(atoms[1],prod[1]);
 c.cx(atoms[3],prod[2]);
 c.cx(atoms[0],prod[4]);
 c.cx(atoms[1],prod[5]);
 c.cx(atoms[0],prod[6]);
 c.cx(atoms[3],prod[6]);
 c.cx(atoms[0],prod[7]);
 c.cx(atoms[1],prod[7]);
 c.cx(atoms[4],prod[7]);
 c.cx(atoms[0],prod[8]);
 c.cx(atoms[1],prod[8]);
 c.cx(atoms[2],prod[8]);
 c.cx(atoms[3],prod[8]);
 c.cx(atoms[4],prod[8]);
 c.cx(atoms[6],prod[8]);
 c.cx(atoms[0],prod[9]);
 c.cx(atoms[1],prod[9]);
 c.cx(atoms[2],prod[9]);
 c.cx(atoms[3],prod[9]);
 c.cx(atoms[4],prod[9]);
 c.cx(atoms[5],prod[9]);
 c.cx(atoms[6],prod[9]);
 c.cx(atoms[1],prod[10]);
 c.cx(atoms[2],prod[10]);
 c.cx(atoms[3],prod[10]);
 c.cx(atoms[4],prod[10]);
 c.cx(atoms[5],prod[10]);
 c.cx(atoms[6],prod[10]);
 c.cx(atoms[2],prod[11]);
 c.cx(atoms[3],prod[11]);
 c.cx(atoms[4],prod[11]);
 c.cx(atoms[5],prod[11]);
 c.cx(atoms[6],prod[11]);
 c.cx(atoms[4],prod[12]);
 c.cx(atoms[5],prod[12]);
 c.cx(atoms[6],prod[12]);
 let ops:Vec<Option<QubitId>>=(0..59).map(|j|if j<13{Some(prod[j])}else if (32..35).contains(&j){Some(w[j-32])}else{None}).collect();
 let ands=sub_line(c,&reg[..59],&ops)+4;
 c.cx(atoms[0],prod[0]);
 c.cx(atoms[1],prod[1]);
 c.cx(atoms[3],prod[2]);
 c.cx(atoms[0],prod[4]);
 c.cx(atoms[1],prod[5]);
 c.cx(atoms[0],prod[6]);
 c.cx(atoms[3],prod[6]);
 c.cx(atoms[0],prod[7]);
 c.cx(atoms[1],prod[7]);
 c.cx(atoms[4],prod[7]);
 c.cx(atoms[0],prod[8]);
 c.cx(atoms[1],prod[8]);
 c.cx(atoms[2],prod[8]);
 c.cx(atoms[3],prod[8]);
 c.cx(atoms[4],prod[8]);
 c.cx(atoms[6],prod[8]);
 c.cx(atoms[0],prod[9]);
 c.cx(atoms[1],prod[9]);
 c.cx(atoms[2],prod[9]);
 c.cx(atoms[3],prod[9]);
 c.cx(atoms[4],prod[9]);
 c.cx(atoms[5],prod[9]);
 c.cx(atoms[6],prod[9]);
 c.cx(atoms[1],prod[10]);
 c.cx(atoms[2],prod[10]);
 c.cx(atoms[3],prod[10]);
 c.cx(atoms[4],prod[10]);
 c.cx(atoms[5],prod[10]);
 c.cx(atoms[6],prod[10]);
 c.cx(atoms[2],prod[11]);
 c.cx(atoms[3],prod[11]);
 c.cx(atoms[4],prod[11]);
 c.cx(atoms[5],prod[11]);
 c.cx(atoms[6],prod[11]);
 c.cx(atoms[4],prod[12]);
 c.cx(atoms[5],prod[12]);
 c.cx(atoms[6],prod[12]);
 for &q in &prod{c.release_clean(q);}
 erase_and(c,m[3],m[0],w[2]);erase_and(c,m[2],w[1],w[2]);erase_and(c,m[1],w[0],w[2]);erase_and(c,m[0],w[0],w[1]);ands
}

