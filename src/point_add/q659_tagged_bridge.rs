//! Test child of q659_ordinary_bridge. Reuses its declared physical ports,
//! Q frame, ring frame, bit setters and pinned Simulator-backed test runner.
//!
//! Ordinary C=0 domain is the original bridge care. C=1 entry holds M-1
//! in E, M=98..128, a positive raw Q, and an arbitrary ring for the tagged
//! refill interface. Both phases of the test hold P and PH. Optional
//! previous-HT payload narrowing, DONE counters, and the subsequent
//! measurement-based tag erasure belong to separate interfaces.
use super::*;
use super::super::{arith, frogdrop_sched};
use frogdrop_sched::N;

#[path = "q659_done_bridge.rs"]
mod done_bridge;

fn guarded_y_exchange(b: &mut B, p: &Ports) {
    let e = with_high(&p.low,p.sum[4]);
    let c = p.roles.tag;
    let flag = p.roles.cut;
    b.x(flag);
    b.cx(c,flag);
    for i in 0..128 {
        b.cswap(flag,p.q[i],p.ring[256-i]);
        let mut ctl: Vec<_> = e.iter().enumerate()
            .map(|(k,&w)| (w,((i >> k) & 1) == 0)).collect();
        ctl.push((c,true));
        mask::mc_xor(b,&ctl,flag,&[],&p.ring[..32]);
    }
}

/// Both threshold masks may be computed on arbitrary tagged data. Only
/// their conjunction with !C selects a write to Q/ring.
fn guarded_residual(b: &mut B, p: &Ports, size: &SumSize) {
    let r = p.roles;
    let bank = &p.ring[..32];
    let selected = [(r.tag,true),(r.cut,false),(r.toggle,false)];
    b.x(r.cut);
    eq_toggle(b,&p.sum,31,r.cut,bank);
    b.x(r.toggle);
    eq_toggle(b,&size.y,127,r.toggle,bank);
    for j in 0..31 {
        mask::mc_xor(b,&selected,r.prefix,&[],bank);
        b.cswap(r.prefix,p.ring[128-j],p.q[j]);
        mask::mc_xor(b,&selected,r.prefix,&[],bank);
        eq_toggle(b,&p.sum,30-j,r.cut,bank);
        eq_toggle(b,&size.y,126-j,r.toggle,bank);
    }
    b.x(r.toggle);
    b.ccx(size.y[6],size.y[5],r.toggle);
}

fn tagged_offset(b: &mut B, p: &Ports) {
    let c = p.roles.tag;
    let selected = p.roles.cut;
    // On C=1, S stores (M-1) mod 32 and M-1 belongs to [97,127].
    // The low five XORs and the known high bit of the six-bit word
    // restore a zero destination for the selected binary MSB search.
    for i in 0..5 { b.ccx(c,p.sum[i],p.low[i]); }
    b.cx(c,p.low[5]);
    // selected = C & (raw Q[64..128] != 0). Q is restored before the
    // second identical call, so the flag can be erased in its input basis.
    let selector = |b:&mut B| {
        let mut ctl = vec![(c,false)];
        ctl.extend(p.q[64..].iter().map(|&w|(w,true)));
        b.cx(c,selected);
        mask::mc_xor(b,&ctl,selected,&[],&p.ring[..96]);
    };
    selector(b);
    for i in 0..64 { b.cswap(selected,p.q[i],p.q[i+64]); }
    let probe = frogdrop::binary_msb::record(b,&p.q[..64],&p.low,Some((c,false)),&p.ring[..96]);
    b.play(&probe,false);
    for i in (0..64).rev() { b.cswap(selected,p.q[i],p.q[i+64]); }
    selector(b);
    arith::ttk_add(b,&p.low[..5],&p.sum,Some(c),None);
}

fn combined_record(b: &mut B, p: &Ports, narrow:Option<(usize,usize)>) -> Vec<G> {
    b.begin();
    guarded_y_exchange(b,p);
    let qf = q_frame(b,p);
    b.play(&qf,false);
    // The Q marker equals the old h on ordinary inputs. Tagged Q may
    // be arbitrary here, but its packet header M-1 always has h=1.
    b.x(p.roles.tag);
    b.ccx(p.roles.tag,p.q[127],p.sum[4]);
    b.x(p.roles.tag);
    b.cx(p.roles.tag,p.sum[4]);
    let size = SumSize {y:with_high(&p.low,p.q[127]),sum:p.sum};
    let probe = outer_size::stage1_record(b,&size,p.roles,&p.ring,(97,256),&p.q[..127]);
    b.play(&probe,false);
    let rf = ring_down(b,p,&size);
    b.play(&rf,false);
    guarded_residual(b,p,&size);
    b.play(&rf,true);
    if let Some(range)=narrow{
        let previous_q:Vec<_>=(0..128).map(|i|p.ring[256-i]).collect();
        previous_ht_narrow(b,p,&size,&previous_q,range);
    }
    b.play(&qf,true);
    tagged_offset(b,p);
    b.end()
}

fn control_record(b: &mut B, p: &Ports,narrow:Option<(usize,usize)>) -> Vec<G> {
    let size = SumSize { y:with_high(&p.low,p.separate_high.unwrap()),sum:p.sum };
    let boundary = reference(b,p,narrow);
    let refill = outer_size::tagged_refill_record(b,&size,p.roles,&p.q,&p.ring);
    b.begin();
    b.play(&boundary,false);
    b.play(&refill,false);
    b.end()
}

fn make_arm(parent: bool,narrow:Option<(usize,usize)>) -> Emission {
    let mut b = B::new();
    let p = Ports {
        ring:b.alloc_n(257),q:b.alloc_n(128),low:b.alloc_n(6).try_into().unwrap(),
        sum:b.alloc_n(5).try_into().unwrap(),
        roles:Roles{tag:b.alloc(),cut:b.alloc(),toggle:b.alloc(),prefix:b.alloc()},
        phase:b.alloc(),payload:b.alloc_n(258),
        separate_high:if parent {Some(b.alloc())} else {None},
    };
    let tape = if parent {control_record(&mut b,&p,narrow)} else {combined_record(&mut b,&p,narrow)};
    b.play(&tape,false);
    b.flush_global();
    let split = b.ops.len();
    b.play(&tape,true);
    b.flush_global();
    let width = b.width() as usize;
    assert_eq!(width,b.peak as usize);
    Emission{p,width,split,ops:b.ops}
}

#[derive(Clone,Copy)]
struct TaggedImage { bottom:N, top:N, q:N, delayed:bool }

/// Construct first-HT and DQ entrances from complete initialized Euclidean
/// walks at the actual challenge modulus. This checks the scalar layout
/// at the crossing, while the native test exercises only the refill slice.
fn crossing_images() -> Vec<TaggedImage> {
    let mut rng = Rng::new(0x07_66_00_65_90_d0);
    let mut counts = [0usize;2];
    let mut images = Vec::new();
    for _ in 0..1024 {
        let x = rng.below(255);
        if x == N::ZERO {continue;}
        let (mut old_r,mut r) = (frogdrop_sched::p(),x);
        let (mut old_t,mut t) = (N::ZERO,N::from(1u64));
        while r.bit_len()>128 {
            let digit = old_r/r;
            (old_r,r) = (r,old_r%r);
            (old_t,t) = (t,old_t+digit*t);
        }
        if r == N::ZERO {continue;}
        let m=t.bit_len();
        let y=r.bit_len();
        if !(98..=128).contains(&m) || !(226..=257).contains(&(m+y)) {continue;}
        let delayed=y>m;
        let top=if delayed {old_r%r} else {old_r};
        if t.bit_len()+top.bit_len()>257 || counts[usize::from(delayed)]>=32 {continue;}
        images.push(TaggedImage{bottom:t,top,q:r,delayed});
        counts[usize::from(delayed)] += 1;
        if counts==[32,32] {break;}
    }
    assert_eq!(counts,[32,32]);
    images
}

#[derive(Clone,Copy)]
enum Fixture { Ordinary(usize,usize), Tagged(usize,usize), Image(TaggedImage) }

impl Fixture {
    /// (tagged, incoming size, resulting Y, resulting S, direct swap count).
    fn numbers(self) -> (bool,usize,usize,usize,usize) {
        match self {
            Self::Ordinary(y,s) => (false,y,y,s,128.min(31+y-s)),
            Self::Tagged(m,y) => (true,m,y,(m+y-2)&31,0),
            Self::Image(t) => {
                let (m,y)=(t.bottom.bit_len(),t.q.bit_len());
                (true,m,y,(m+y-2)&31,0)
            }
        }
    }
}

#[test]
fn q659_coherent_ordinary_and_tagged_refill() {
    compare_tagged(None);
}

#[test]
fn q659_coherent_refill_with_ht_narrow(){
    let sch=frogdrop_sched::from_text(super::super::pointadd_frogdrop::SCHED_FROGDROP);
    let (cols,_,_)=super::super::pointadd_frogdrop::col_pars(&sch);
    let cp=&cols[97];assert!(cp.pht);
    compare_tagged(Some((cp.sz.0.max(256-cp.psy.1.min(128)),cp.sz.1.min(255).min(257-cp.psy.0.max(1)))));
}

fn compare_tagged(narrow:Option<(usize,usize)>) {
    let old = make_arm(true,narrow);
    let new = make_arm(false,narrow);
    assert_eq!((old.width,new.width),(660,659));
    assert_eq!(old.p.separate_high.unwrap().0 as usize,new.width);
    let p=&old.p;
    let images=crossing_images();
    let mut cases=Vec::new();
    // Interleave branches; 64-word packs contain both gate states.
    for k in 0..4096 {
        cases.push(Fixture::Ordinary(1+k/32,k%32));
        if k<31*128 { cases.push(Fixture::Tagged(98+k/128,1+k%128)); }
        if k<images.len() { cases.push(Fixture::Image(images[k])); }
    }
    assert_eq!(cases.len(),8128);
    let mut rng=Rng::new(0x636f_6865_7265_6e74);
    let mut mixed=0;
    let mut highs=[[0usize;2];2];
    let mut proper_tagged=0;
    let mut image_counts=[0usize;2];
    let mut total_t=[0u64;2];
    let mut changes=0;
    for (batch,pack) in cases.chunks_exact(64).enumerate() {
        let mut raw=vec![0u64;old.width];
        for &q in p.ring.iter().chain(&p.q).chain(&p.payload) {raw[q.0 as usize]=rng.next();}
        raw[p.phase.0 as usize]=rng.next();
        for (lane,&case) in pack.iter().enumerate() {
            let (tag,m,y,s,swaps)=case.numbers();
            set(&mut raw,p.roles.tag,lane,tag);
            if tag {set(&mut raw,p.phase,lane,true);}
            set(&mut raw,p.separate_high.unwrap(),lane,m>64);
            for i in 0..6 {set(&mut raw,p.low[i],lane,((m-1)>>i)&1!=0);}
            match case {
                Fixture::Ordinary(_,_) => {
                    let z=226+s-y;
                    for i in z..257-y {set(&mut raw,p.ring[i],lane,false);}
                    set(&mut raw,p.ring[z-1],lane,true);
                    set(&mut raw,p.ring[257-y],lane,true);
                    for i in swaps..128 {set(&mut raw,p.q[i],lane,false);}
                }
                Fixture::Tagged(_,_) => {
                    // Ring is arbitrary here. All bits below the leading Q
                    // bit are arbitrary, and every M/Y modular refill is
                    // tested even beyond the positive ordinary sum envelope.
                    for i in y..128 {set(&mut raw,p.q[i],lane,false);}
                    set(&mut raw,p.q[y-1],lane,true);
                    if (226..=257).contains(&(m+y)) {proper_tagged+=1;}
                }
                Fixture::Image(image) => {
                    image_counts[usize::from(image.delayed)]+=1;
                    for i in 0..257 {
                        let bit=image.bottom.bit(i)||image.top.bit(256-i);
                        set(&mut raw,p.ring[i],lane,bit);
                    }
                    for i in 0..128 {set(&mut raw,p.q[i],lane,image.q.bit(i));}
                }
            }
        }
        let tag_word=raw[p.roles.tag.0 as usize];
        mixed+=usize::from(tag_word!=0 && tag_word!=u64::MAX);
        let mut decoded=raw.clone();
        let mut packed=raw[..new.width].to_vec();
        packed[p.sum[4].0 as usize]=raw[p.separate_high.unwrap().0 as usize];
        for (lane,&case) in pack.iter().enumerate() {
            let (tag,_,y,s,swaps)=case.numbers();
            for j in 0..swaps {
                set(&mut decoded,p.q[j],lane,get(&raw,p.ring[256-j],lane));
                set(&mut decoded,p.ring[256-j],lane,get(&raw,p.q[j],lane));
            }
            for i in 0..5 {set(&mut decoded,p.sum[i],lane,(s>>i)&1!=0);}
            if !tag {
                if let Some((lo,hi))=narrow {
                    let z=226+s-y;let bit=256-z;
                    if (lo..=hi).contains(&z) && get(&raw,p.phase,lane)
                        && (bit>=128||!get(&raw,p.q[bit],lane)) && get(&raw,p.payload[bit+1],lane) {
                        set(&mut decoded,p.payload[bit],lane,!get(&raw,p.payload[bit],lane));
                        changes+=1;
                    }
                }
            }
            for i in 0..6 {set(&mut decoded,p.low[i],lane,((y-1)>>i)&1!=0);}
            set(&mut decoded,p.separate_high.unwrap(),lane,y>64);
        }
        for (parent,arm,input) in [(true,&old,&raw),(false,&new,&packed)] {
            let f=run(&arm.ops[..arm.split],arm.width,&|w|w.copy_from_slice(input));
            assert_eq!(f.phase,0,"forward phase parent={parent} batch={batch}");
            assert_eq!(&f.q[..],&decoded[..arm.width],"forward wires parent={parent} batch={batch}");
            for (lane,&case) in pack.iter().enumerate() {
                let (_,_,y,_,_)=case.numbers();
                let h=if parent {get(&f.q,p.separate_high.unwrap(),lane)}
                      else {get(&f.q,p.q[64+(y-1)%64],lane)};
                assert_eq!(h,y>64);
                highs[usize::from(parent)][usize::from(h)]+=1;
            }
            let inv=run(&arm.ops[arm.split..],arm.width,&|w|w.copy_from_slice(&f.q));
            assert_eq!(inv.phase,0,"inverse phase parent={parent} batch={batch}");
            assert_eq!(&inv.q[..],input.as_slice(),"inverse wires parent={parent} batch={batch}");
            total_t[usize::from(parent)]+=f.tof;
        }
    }
    assert_eq!(image_counts,[32,32]);
    assert_eq!(proper_tagged,496);
    assert_eq!(highs[0],highs[1]);
    assert!(mixed>100);
    if narrow.is_some(){assert!(changes>0);}
    println!("q659-tagged-narrow range={narrow:?} changed_payload_cases={changes}");
    let charged=|arm:&Emission| arm.ops[..arm.split].iter().filter(|op|
        matches!(op.kind,OperationType::CCX|OperationType::CCZ)).count();
    println!("q659-tagged-bridge ordinary=4096 general_tagged=3968 ordinary_sum_valid_tagged={proper_tagged} initialized_first_ht={} initialized_dq={} mixed_packs={mixed} old_width={} new_width={} old_forward_ops={} new_forward_ops={} old_ccx_ccz={} new_ccx_ccz={} old_exec_T_numerator={} new_exec_T_numerator={} samples={} semantic_high={highs:?} full_forward_inverse_phase_clean=true",
        image_counts[0],image_counts[1],old.width,new.width,old.split,new.split,
        charged(&old),charged(&new),total_t[1],total_t[0],cases.len());
}
