//! Native differential fixture for ordinary (!C) Q660 column stage 1 and its
//! boundary exchange. Register this file as a test child of `point_add`.
//!
//! Compact entry: E.low6 persists, E.high is in S4, S0..3 and the four
//! scalar roles are zero. The top Y bits of the 257-ring are a positive
//! Y-bit word. The previous Q word fits min(128, 257-Z) bits, including up
//! to 31-S extra high bits. 1<=Y<=128 and 226<=Z+Y<=257. This component
//! bypasses tagged columns, optional pre-swap HT payload narrowing, and
//! DONE counter data. PH and the 258 payload wires are held as passengers.
//!
//! Compact exit: E.low6, all five ordinary S bits, parent ring and raw Q.
//! The omitted high bit is recoverable at Q[64+E.low6]. A synthetically
//! labelled HR/HT input is evidence for this interface, not for reachability.
use super::builder::{B, G};
use super::{byte_cut_swap, frogdrop, mask, outer_size, sum_size::SumSize};
use super::outer_size::Roles;
use super::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType, QubitId};

#[path = "q659_tagged_bridge.rs"]
mod tagged_bridge;

#[derive(Clone)]
struct Ports {
    ring: Vec<QubitId>,
    q: Vec<QubitId>,
    low: [QubitId; 6],
    sum: [QubitId; 5],
    roles: Roles,
    phase: QubitId,
    payload: Vec<QubitId>,
    separate_high: Option<QubitId>,
}

fn with_high(low: &[QubitId; 6], high: QubitId) -> [QubitId; 7] {
    [low[0], low[1], low[2], low[3], low[4], low[5], high]
}

fn eq_toggle(b: &mut B, word: &[QubitId], value: usize, target: QubitId, dirty: &[QubitId]) {
    let controls: Vec<_> = word.iter().enumerate()
        .map(|(k, &q)| (q, (value >> k) & 1 == 0)).collect();
    mask::mc_xor(b, &controls, target, &[], dirty);
}

/// Swap Q[0..Y) with the reversed ring top. During this epoch S4 is E.high.
fn swap_y(b: &mut B, p: &Ports) {
    let address = with_high(&p.low, p.sum[4]);
    let flag = p.roles.cut;
    b.x(flag);
    for i in 0..128 {
        b.cswap(flag, p.q[i], p.ring[256-i]);
        eq_toggle(b, &address, i, flag, &p.ring[..32]);
    }
}

/// The absent raw short-class marker is zero even for a partially swapped HT
/// operand: for E.low=e its index is e+64, whereas Q has at most Y+31 bits.
/// Output Q[127]=h and logical normalized Q_leading=1 under this care.
fn q_frame(b: &mut B, p: &Ports) -> Vec<G> {
    b.begin();
    for (i, &bit) in p.low.iter().enumerate() {
        b.x(bit);
        frogdrop::crot_up(b, bit, &p.q, 1usize << i);
        b.x(bit);
    }
    let h = p.q[127];
    b.x(h);
    for i in 0..63 {
        b.cswap(h, p.q[i], p.q[i+64]);
    }
    b.cx(h, p.q[63]);
    b.x(h);
    b.end()
}

fn ring_down(b: &mut B, p: &Ports, size: &SumSize) -> Vec<G> {
    b.begin();
    for (i, &bit) in size.y.iter().enumerate() {
        b.x(bit);
        frogdrop::crot_up(b, bit, &p.ring, 257-(1usize << i));
        b.x(bit);
    }
    b.end()
}

/// In the aligned ring, the remaining swaps join ring[128-j] to Q[j]
/// for j < min(31-S,127-E). The two running thresholds close exactly.
fn residual(b: &mut B, p: &Ports, size: &SumSize) {
    let r = p.roles;
    let bank = &p.ring[..32];
    b.x(r.cut);
    eq_toggle(b, &p.sum, 31, r.cut, bank);
    b.x(r.toggle);
    eq_toggle(b, &size.y, 127, r.toggle, bank);
    for j in 0..31 {
        b.ccx(r.cut, r.toggle, r.prefix);
        b.cswap(r.prefix, p.ring[128-j], p.q[j]);
        b.ccx(r.cut, r.toggle, r.prefix);
        eq_toggle(b, &p.sum, 30-j, r.cut, bank);
        eq_toggle(b, &size.y, 126-j, r.toggle, bank);
    }
    // E<=95 is the only surviving threshold. S<=-1 is already zero.
    b.x(r.toggle);
    b.ccx(size.y[6], size.y[5], r.toggle);
}

// When DONE is excluded the original narrow activity is PH & !C. At the
// selected address i=256-Z, i is the final lane of the full Z-cut exchange.
// Its former Q bit now lives at ring[Z]. At Z=128 both versions use the
// parent's virtual zero. Every other gathered data bit is restored.
fn previous_ht_narrow(b:&mut B,p:&Ports,size:&SumSize,q_view:&[QubitId],range:(usize,usize)){
    let r=p.roles;
    b.x(r.tag); b.ccx(p.phase,r.tag,r.cut); b.x(r.tag);
    super::direct_payload::narrow_ht(b,size,&p.payload,q_view,range,r.cut,r.toggle,r.prefix,&p.ring[..96]);
    b.x(r.tag); b.ccx(p.phase,r.tag,r.cut); b.x(r.tag);
}

fn compact(b: &mut B, p: &Ports, narrow:Option<(usize,usize)>) -> Vec<G> {
    b.begin();
    swap_y(b, p);
    let frame = q_frame(b, p);
    b.play(&frame, false);
    b.cx(p.q[127], p.sum[4]);
    let size = SumSize { y: with_high(&p.low, p.q[127]), sum: p.sum };
    // The first Y swaps begin at ring[257-Y]. The uppermost bit seen by
    // the proper ordinary bottom probe is ring[256-Y], so the probe's full
    // 32-lane active window and its highest bottom bit survive the swaps.
    let probe = outer_size::stage1_record(b, &size, p.roles, &p.ring, (97,256), &p.q[..127]);
    b.play(&probe, false);
    let ring_frame = ring_down(b, p, &size);
    b.play(&ring_frame, false);
    residual(b, p, &size);
    b.play(&ring_frame, true);
    if let Some(range)=narrow{
        let post_swap_q:Vec<_>=(0..128).map(|i|p.ring[256-i]).collect();
        previous_ht_narrow(b,p,&size,&post_swap_q,range);
    }
    b.play(&frame, true);
    b.end()
}

fn reference(b: &mut B, p: &Ports, narrow:Option<(usize,usize)>) -> Vec<G> {
    let size = SumSize { y: with_high(&p.low, p.separate_high.unwrap()), sum: p.sum };
    let probe = outer_size::stage1_record(b, &size, p.roles, &p.ring, (97,256), &p.q);
    let exchange = byte_cut_swap::record(
        b, &size, p.roles, &p.ring, &p.q, &[(p.roles.tag,true)], &p.ring[..64]
    );
    b.begin();
    b.play(&probe, false);
    if let Some(range)=narrow{previous_ht_narrow(b,p,&size,&p.q,range);}
    b.play(&exchange, false);
    b.end()
}

struct Emission {
    p: Ports,
    width: usize,
    split: usize,
    ops: Vec<Op>,
}

fn build(parent: bool, narrow:Option<(usize,usize)>) -> Emission {
    let mut b = B::new();
    let p = Ports {
        ring: b.alloc_n(257),
        q: b.alloc_n(128),
        low: b.alloc_n(6).try_into().unwrap(),
        sum: b.alloc_n(5).try_into().unwrap(),
        roles: Roles {tag:b.alloc(), cut:b.alloc(), toggle:b.alloc(), prefix:b.alloc()},
        phase: b.alloc(),
        payload: b.alloc_n(258),
        separate_high: if parent { Some(b.alloc()) } else { None },
    };
    let tape = if parent { reference(&mut b,&p,narrow) } else { compact(&mut b,&p,narrow) };
    b.play(&tape, false);
    b.flush_global();
    let split = b.ops.len();
    b.play(&tape, true);
    b.flush_global();
    let width = b.width() as usize;
    assert_eq!(b.peak as usize, width);
    Emission {p, width, split, ops:b.ops}
}

fn set(w: &mut [u64], wire: QubitId, lane: usize, bit: bool) {
    let b = 1u64 << lane;
    let v = &mut w[wire.0 as usize];
    *v = (*v & !b) | if bit { b } else { 0 };
}
fn get(w: &[u64], wire: QubitId, lane: usize) -> bool {
    (w[wire.0 as usize] >> lane) & 1 != 0
}

#[test]
fn q659_ordinary_column_entry_bridge() {
    compare_ordinary(None);
}

#[test]
fn q659_ordinary_previous_ht_narrow(){
    let schedule=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols,_,_)=super::pointadd_frogdrop::col_pars(&schedule);
    let cp=&cols[97]; assert!(cp.pht);
    let lo=cp.sz.0.max(256-cp.psy.1.min(128));
    let hi=cp.sz.1.min(255).min(257-cp.psy.0.max(1));
    compare_ordinary(Some((lo,hi)));
}

fn compare_ordinary(narrow:Option<(usize,usize)>){
    let old = build(true,narrow);
    let new = build(false,narrow);
    assert_eq!((old.width, new.width), (660,659));
    assert_eq!(old.p.separate_high.unwrap().0 as usize, new.width);
    let p = &old.p;
    let mut rng = Rng::new(0x7365_365f_6272_6964);
    let mut marker_pairs = [[0usize;2];2];
    let mut base_forward_t = None;
    let mut compact_forward_t = None;
    let mut narrow_changes=0;
    // All 4,096 positive size pairs, twice, in 128 complete 64-lane packs.
    for batch in 0..128 {
        let mut v = vec![0u64;old.width];
        for &q in p.ring.iter().chain(&p.payload) { v[q.0 as usize] = rng.next(); }
        let mut cases = Vec::new();
        for lane in 0..64 {
            let index = batch*64+lane;
            let y = 1 + (index % 4096)/32;
            let s = index % 32;
            let z = 226+s-y;
            let active = 128.min(257-z);
            let ht = index >= 4096;
            // Distinct fields in the ring, with a proper highest bottom bit
            // and top bit for the actual parent probe and boundary exchange.
            for j in z..257-y { set(&mut v,p.ring[j],lane,false); }
            set(&mut v,p.ring[z-1],lane,true);
            set(&mut v,p.ring[257-y],lane,true);
            set(&mut v,p.phase,lane,ht);
            for i in 0..128 {
                let bit = if ht {
                    // Exercises previous-Q tail bits all the way to the original cut.
                    i < active && !(narrow.is_some() && i==256-z && index%2==0)
                } else {
                    i+1 < y && get(&v,p.ring[255-i],lane)
                };
                set(&mut v,p.q[i],lane,bit);
            }
            for (i,&q) in p.low.iter().enumerate() {
                set(&mut v,q,lane,((y-1)>>i)&1 != 0);
            }
            set(&mut v,p.separate_high.unwrap(),lane,y>64);
            cases.push((y,s,active));
        }
        let mut packed = v[..new.width].to_vec();
        packed[p.sum[4].0 as usize] = v[p.separate_high.unwrap().0 as usize];
        // Independent direct-swap output oracle for every named payload,
        // wire, helper, phase, size-bit and arbitrary ring-bottom input.
        let mut want = v.clone();
        for (lane, &(y,s,active)) in cases.iter().enumerate() {
            for j in 0..active {
                set(&mut want,p.q[j],lane,get(&v,p.ring[256-j],lane));
                set(&mut want,p.ring[256-j],lane,get(&v,p.q[j],lane));
            }
            for i in 0..5 { set(&mut want,p.sum[i],lane,(s>>i)&1 != 0); }
            let z=226+s-y;
            if let Some((lo,hi))=narrow{
                let bit=256-z;
                if (lo..=hi).contains(&z) && get(&v,p.phase,lane)
                    && (bit>=128 || !get(&v,p.q[bit],lane)) && get(&v,p.payload[bit+1],lane) {
                    set(&mut want,p.payload[bit],lane,!get(&v,p.payload[bit],lane));
                    narrow_changes+=1;
                }
            }
            let marker = get(&want,p.q[64+((y-1)%64)],lane);
            assert_eq!(marker,y>=65);
        }
        for (parent, arm, input) in [(true,&old,&v),(false,&new,&packed)] {
            let f = run(&arm.ops[..arm.split],arm.width,&|w| w.copy_from_slice(input));
            assert_eq!(f.phase,0,"forward phase, parent={parent}, batch={batch}");
            assert_eq!(&f.q[..],&want[..arm.width],"forward wires, parent={parent}, batch={batch}");
            for (lane,&(y,_,_)) in cases.iter().enumerate() {
                let h = if parent {
                    get(&f.q,arm.p.separate_high.unwrap(),lane)
                } else {
                    get(&f.q,arm.p.q[64+((y-1)%64)],lane)
                };
                assert_eq!(h,y>=65);
                marker_pairs[usize::from(parent)][usize::from(h)] += 1;
            }
            let r = run(&arm.ops[arm.split..],arm.width,&|w| w.copy_from_slice(&f.q));
            assert_eq!(r.phase,0,"inverse phase, parent={parent}, batch={batch}");
            assert_eq!(&r.q[..],input.as_slice(),"inverse wires, parent={parent}, batch={batch}");
            let output = if parent { &mut base_forward_t } else { &mut compact_forward_t };
            if let Some(total) = *output { assert_eq!(f.tof,total); } else { *output=Some(f.tof); }
        }
    }
    let charged = |a:&Emission| a.ops[..a.split].iter().filter(|op|
        matches!(op.kind,OperationType::CCX|OperationType::CCZ)).count();
    assert_eq!(marker_pairs,[[4096,4096],[4096,4096]]);
    if narrow.is_some(){assert!(narrow_changes>0);}
    println!("q659-ordinary-narrow range={narrow:?} changed_payload_cases={narrow_changes}");
    println!("q659-ordinary-bridge C0 sizes=4096 fixtures=8192 packed_batches=128 old_q={} new_q={} old_forward_ops={} new_forward_ops={} old_primitive_ccx_ccz={} new_primitive_ccx_ccz={} old_executed_T_per_64={:?} new_executed_T_per_64={:?} semantic_h={marker_pairs:?} full_forward_inverse_phase_clean=true",old.width,new.width,old.split,new.split,charged(&old),charged(&new),base_forward_t,compact_forward_t);
}
