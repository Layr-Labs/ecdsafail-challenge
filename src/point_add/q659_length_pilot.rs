//! One-bit-shorter interfaces to the complete HT forward and HR inverse Q-source
//! quotient-digit loops. Component pilot against the pinned production emitter.
use super::*;
include!("q659_inverse_ttk.rs");

/// On outer activity the Q word is positive and unparked, of length Y, and
/// `low` holds (Y-1) mod 64. Rotate first by 63-low. For Y<=64 this puts the
/// leading one at q63 and a zero at q127. For Y>=65 the leading one is at q127.
/// In the short case move only the lower 63 pairs, and supply the old q63=1
/// virtually. In normalized coordinates q127 now holds the omitted size bit,
/// and the logical source's leading one is implicit. Off activity this is
/// still a permutation, undone by the literal inverse at the end of the loop.
fn compact_frame(b: &mut B, low: &[QubitId; 6], q: &[QubitId], raw: &[QubitId], inverse: bool) -> Vec<G> {
    assert_eq!((q.len(), raw.len()), (128, 259));
    b.begin();
    for (k, &bit) in low.iter().enumerate() {
        let amount = 1 << k;
        b.x(bit);
        super::super::frogdrop::crot_up(b, bit, q, amount);
        super::super::frogdrop::crot_up(b, bit, raw, if inverse {259 - amount} else {amount});
        b.x(bit);
    }
    let long = q[127];
    b.x(long);
    for i in 0..63 { b.cswap(long, q[i], q[i+64]); }
    b.cx(long, q[63]);
    super::super::frogdrop::crot_up(b, long, raw, if inverse {195} else {64});
    b.x(long);
    b.end()
}

/// Forward starts with sign clear. Use sign as the restored low carry and
/// use work (initially zero) for the virtual top carry, then for the mask.
/// q127 stores the length class throughout and is never a ripple target.
fn virtual_digit(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles,first:usize,dirty:&[QubitId])->Vec<G>{
    assert!(first<128 && t.len()==129);
    b.begin();
    for &wire in t { b.x(wire); }
    for i in first..127 {
        cell(b,q[i],t[i],if i==first {r.sign} else {q[i-1]},false);
    }
    let upper_carry = if first==127 {r.sign} else {q[126]};
    let top = |b:&mut B| {
        b.cx(upper_carry,r.work); b.cx(t[127],r.work);
        b.ccx(upper_carry,t[127],r.work);
    };
    top(b);
    b.cx(r.activity,r.flight);
    literal(b,&[(r.activity,false),(t[128],false),(r.work,false)],r.flight,dirty);
    literal(b,&[(r.activity,false),(r.flight,false),(r.work,false)],t[128],dirty);
    top(b);
    b.ccx(r.activity,r.flight,r.work);
    b.cx(r.work,t[127]); b.ccx(r.work,upper_carry,t[127]);
    for i in (first..127).rev() {
        let carry = if i==first {r.sign} else {q[i-1]};
        cell(b,q[i],t[i],carry,true);
        b.cx(q[i],carry); b.ccx(r.work,carry,t[i]); b.cx(q[i],carry);
    }
    b.ccx(r.activity,r.flight,r.work);
    for &wire in t { b.x(wire); }
    b.end()
}

/// Apply the parent's physical-leading-one inverse arithmetic with a virtual
/// leading one. The dedicated work wire supplies the first carry and the
/// retained sign is never touched. Expand the virtual top carry, u OR v,
/// as 1 XOR (!u AND !v) and directly control writes by activity AND flight.
/// This also covers noncanonical dividends and arbitrary retained signs.
#[cfg(test)]
fn inverse_virtual_digit(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles,first:usize,dirty:&[QubitId])->Vec<G> {
    assert!(first<128 && t.len()==129);
    b.begin();
    for &wire in t {b.x(wire);}
    for i in first..127 {
        cell(b,q[i],t[i],if i==first {r.work} else {q[i-1]},false);
    }
    let carry=q[126];
    let xor_carry=|b:&mut B,gate:QubitId,target:QubitId| {
        b.ccx(r.activity,gate,target);
        literal(b,&[(r.activity,false),(gate,false),(carry,true),(t[127],true)],target,dirty);
    };
    b.cx(r.activity,r.flight);
    xor_carry(b,t[128],r.flight);
    xor_carry(b,r.flight,t[128]);
    literal(b,&[(r.activity,false),(r.flight,false),(carry,true)],t[127],dirty);
    for i in (first..127).rev() {
        let prior=if i==first {r.work} else {q[i-1]};
        cell(b,q[i],t[i],prior,true);
        b.cx(q[i],prior);
        literal(b,&[(r.activity,false),(r.flight,false),(prior,false)],t[i],dirty);
        b.cx(q[i],prior);
    }
    for &wire in t {b.x(wire);}
    b.end()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compact_loop(b:&mut B,low:&[QubitId;6],sum:[QubitId;5],q:&[QubitId],raw:&[QubitId],
                r:Roles,range:Ranges,dirty:&[QubitId],inverse:bool) {
    let owners:Vec<_>=low.iter().chain(sum.iter()).chain(q).chain(raw).chain(dirty).copied()
        .chain([r.activity,r.flight,r.sign,r.work]).collect();
    assert_eq!(owners.iter().copied().collect::<BTreeSet<_>>().len(),owners.len());
    assert!(dirty.len()>=4);
    let frame=compact_frame(b,low,q,raw,inverse);
    b.play(&frame,false);
    // The inherited full-Y guard uses only S. Supply the encoded high bit
    // explicitly; q127 cannot serve as a dirty donor for a mask or a carry.
    let meta=SumSize{y:[low[0],low[1],low[2],low[3],low[4],low[5],q[127]],sum};
    for j in 0..30 {
        let k = if inverse {j} else {29-j};
        if !permitted(range,k) {continue;}
        if inverse {
            selected_swap(b,&meta,r,k,raw[129-k],dirty);
            b.cx(r.sign,r.activity);
        }
        let sum_limit = if inverse {32-k} else {31-k};
        let guard=Guard{y:(1,128),sum_limit:sum_limit as isize}.witness_record(b,&meta,r.activity,r.flight,dirty);
        b.play(&guard,false);
        let yhi=range.y.1.min((if inverse {258-k} else {257-k}).saturating_sub(range.z.0));
        assert!((1..=128).contains(&yhi));
        if inverse {
            let window:Vec<_>=(0..129).map(|i|raw[258-k-i]).collect();
            let digit=inverse_compare_ttk_digit(b,q,&window,r,128-yhi,dirty);
            b.play(&digit,true);
        } else {
            let digit=virtual_digit(b,q,&raw[k..k+129],r,128-yhi,dirty);
            b.play(&digit,false);
        }
        b.play(&guard,true);
        if inverse { b.cx(r.sign,r.activity); }
        else { selected_swap(b,&meta,r,k,raw[128+k],dirty); }
    }
    b.play(&frame,true);
}

#[cfg(test)]
struct Ports {
    low:[QubitId;6], sum:[QubitId;5], q:Vec<QubitId>, raw:Vec<QubitId>, r:Roles,
    donors:Vec<QubitId>, parent_high:Option<QubitId>, width:usize,
}

#[cfg(test)]
fn circuit(parent:bool,inverse:bool,range:Ranges)->(Ports,Vec<G>){
    circuit_mode(parent,inverse,range,false)
}
#[cfg(test)]
fn circuit_mode(parent:bool,inverse:bool,range:Ranges,dispatch:bool)->(Ports,Vec<G>){
    let mut b=B::new();
    let low:[QubitId;6]=b.alloc_n(6).try_into().unwrap();
    let sum:[QubitId;5]=b.alloc_n(5).try_into().unwrap();
    let q=b.alloc_n(128); let raw=b.alloc_n(259);
    let r=Roles{activity:b.alloc(),flight:b.alloc(),sign:b.alloc(),work:b.alloc()};
    let donors=b.alloc_n(16); let parent_high=if parent {Some(b.alloc())} else {None};
    b.begin();
    if let Some(h)=parent_high {
        let meta=SumSize{y:[low[0],low[1],low[2],low[3],low[4],low[5],h],sum};
        if dispatch {
            if inverse {super::inverse(&mut b,&meta,&q,&raw,r,range,&donors);}
            else {super::forward(&mut b,&meta,&q,&raw,r,range,&donors);}
        } else if inverse {super::reference_inverse(&mut b,&meta,&q,&raw,r,range,&donors);}
        else {super::reference_forward(&mut b,&meta,&q,&raw,r,range,&donors);}
    } else {compact_loop(&mut b,&low,sum,&q,&raw,r,range,&donors,inverse);}
    let tape=b.end();
    (Ports{low,sum,q,raw,r,donors,parent_high,width:b.peak as usize},tape)
}

// Each u64 holds 64 basis cases. Reject unsupported gates, including any
// measurement, conditional, phase, or unexpanded AND. All accepted primitives
// are classical permutations with positive matrix entries.
#[cfg(test)]
fn execute(tape:&[G],w:&mut[u64],reverse:bool){
    let mut apply=|g:&G|match *g {
        G::X(t)=>w[t.0 as usize]^=u64::MAX,
        G::Cx(a,t)=>w[t.0 as usize]^=w[a.0 as usize],
        G::Ccx(a,c,t)=>w[t.0 as usize]^=w[a.0 as usize]&w[c.0 as usize],
        G::Swap(a,c)=>w.swap(a.0 as usize,c.0 as usize),
        _=>panic!("unexpected gate in unitary component: {g:?}"),
    };
    if reverse {for g in tape.iter().rev(){apply(g)}} else {for g in tape{apply(g)}}
}

#[cfg(test)]
fn random(state:&mut u64)->u64{*state^=*state<<13; *state^=*state>>7; *state^=*state<<17; *state}
#[cfg(test)]
fn put(w:&mut[u64],id:QubitId,lane:usize,value:bool){
    let mask=1u64<<lane;
    let slot=&mut w[id.0 as usize];
    *slot=(*slot & !mask) | if value {mask} else {0};
}

#[test]
fn q659_normal_dispatch(){
    let compact=super::compact_q_loops_enabled();
    for inverse in [false,true] {
        let range=Ranges{z:(112,255),y:(1,128)};
        let (_,actual)=circuit_mode(true,inverse,range,true);
        let (_,expected)=circuit(!compact,inverse,range);
        assert_eq!(actual,expected);
    }
    println!("q659-dispatch compact={compact} both production loop records agree gate by gate");
}

#[test]
fn q660_submission_default_dispatch() {
    // Exercise the initialization used by build() in a fresh grader process.
    let knobs = super::super::BAKED_KNOBS;
    for (name, value) in [("Q659_Q_SOURCE_LOOPS", "1"), ("SIMPLIFY_PRODUCTS", "0")] {
        assert_eq!(knobs.iter().filter(|(key, _)| *key == name).count(), 1);
        assert!(knobs.contains(&(name, value)));
    }
    super::super::bake_knobs();
    assert!(super::compact_q_loops_enabled());
    assert_eq!(std::env::var("SIMPLIFY_PRODUCTS").as_deref(), Ok("0"));
    q659_normal_dispatch();
}

#[test]
fn q659_compact_complete_payload_loops(){
    let mut seed=0x73d7_3d99_e3bc_1741;
    let mut basis=0;
    let scenarios=[Ranges{z:(98,256),y:(1,128)},Ranges{z:(112,255),y:(1,128)},
        Ranges{z:(194,255),y:(1,32)},Ranges{z:(225,256),y:(1,1)},
        Ranges{z:(98,136),y:(121,128)}];
    for (case,range) in scenarios.into_iter().enumerate(){for inverse in [false,true]{
        let (p,old)=circuit(true,inverse,range); let (n,new)=circuit(false,inverse,range);
        assert_eq!(p.width,n.width+1); assert_eq!(p.parent_high.unwrap().0 as usize,n.width);
        let ccx=|r:&[G]| r.iter().filter(|g|matches!(g,G::Ccx(..))).count();
        let mut active_count=0;
        for batch in 0..40 {
            let mut source:Vec<_>=(0..p.width).map(|_|random(&mut seed)).collect();
            for lane in 0..64 {
                let key=batch*64+lane;
                let y=range.y.0+key%(range.y.1+1-range.y.0);
                let s_lo=(range.z.0+y).saturating_sub(226);
                let s_hi=(range.z.1+y-226).min(31);
                assert!(s_lo<=s_hi);
                let sum=s_lo+(random(&mut seed)as usize)%(s_hi-s_lo+1);
                let active=(batch+lane)%4!=0;
                active_count+=usize::from(active);
                for i in 0..6{put(&mut source,p.low[i],lane,(y-1)>>i&1!=0);}
                for i in 0..5{put(&mut source,p.sum[i],lane,sum>>i&1!=0);}
                put(&mut source,p.parent_high.unwrap(),lane,y>64);
                if active {
                    for i in y..128 {put(&mut source,p.q[i],lane,false);}
                    put(&mut source,p.q[y-1],lane,true);
                    if (batch+lane)%5==0 {for i in 0..y-1{put(&mut source,p.q[i],lane,false);}}
                }
                put(&mut source,p.r.activity,lane,active);
                put(&mut source,p.r.flight,lane,false);
                put(&mut source,p.r.sign,lane,inverse && active && batch%3==0);
                put(&mut source,p.r.work,lane,false);
            }
            let mut a=source.clone();let mut c=source[..n.width].to_vec();
            execute(&old,&mut a,false);execute(&new,&mut c,false);
            assert_eq!(&a[..n.width],c.as_slice(),"case {case}, inverse {inverse}, batch {batch}");
            assert_eq!(a[p.parent_high.unwrap().0 as usize],source[p.parent_high.unwrap().0 as usize]);
            for id in p.q.iter().chain(&p.donors){assert_eq!(a[id.0 as usize],source[id.0 as usize]);}
            assert_eq!(p.raw.len(),259);
            execute(&new,&mut c,true);assert_eq!(c.as_slice(),&source[..n.width]);
            execute(&old,&mut a,true);assert_eq!(a,source);
            basis+=64;
        }
        println!("q659-loop case={case} inverse={inverse} width={}/{} recorded_ccx={}/{} basis=2560 active={active_count}",p.width,n.width,ccx(&old),ccx(&new));
    }}
    println!("q659-loop complete basis={basis}");
}

#[test]
fn q659_schedule_cost_for_changed_loops(){
    use super::super::{direct_middle, frogdrop_sched, pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cols,_,_)=pointadd_frogdrop::col_pars(&schedule);
    assert_eq!(cols.len(),203);
    let mut calls=[0;2];
    let mut totals=[0i64;2];
    let mut cache=std::collections::BTreeMap::new();
    for cp in &cols{
        if direct_middle::q659_fixed_dispatch(cp){continue;}
        let range=Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))};
        for (present,inverse) in [(cp.ht,false),(cp.hr,true)]{
            if !present{continue;}
            let key=(range.z,range.y,inverse);
            let delta=*cache.entry(key).or_insert_with(||{
                let count=|parent:bool| circuit(parent,inverse,range).1.iter()
                    .filter(|g|matches!(g,G::Ccx(..))).count() as i64;
                count(false)-count(true)
            });
            calls[usize::from(inverse)]+=1;
            totals[usize::from(inverse)]+=delta;
        }
    }
    // Payload is present in T1 and T4. The latter plays the records backwards.
    println!("q659-schedule columns={} ht_forward={} hr_inverse={} distinct_shapes={} ht_delta={} hr_delta={} two_traversal_raw_delta={}",
        cols.len(),calls[0],calls[1],cache.len(),totals[0],totals[1],2*(totals[0]+totals[1]));
}

#[test]
fn q659_boundary_phase_with_held_payload(){
    let mut b=B::new();
    let ring=b.alloc_n(257);let q=b.alloc_n(128);let e:[QubitId;7]=b.alloc_n(7).try_into().unwrap();
    let tag=b.alloc();let clean:[QubitId;7]=b.alloc_n(7).try_into().unwrap();
    let target=b.alloc();let _live_payload=b.alloc_n(258);
    b.begin();
    super::super::q659_boundary_phase::xor_boundary_phase(&mut b,&ring,&q,&e,tag,&clean,target);
    let tape=b.end();assert_eq!(b.peak,659);
    let ccx=tape.iter().filter(|g|matches!(g,G::Ccx(..))).count();assert_eq!(ccx,4222);
    let mut seed=0xe19b_c565_a371_0ded;
    for batch in 0..32{
        let mut w:Vec<_>=(0..659).map(|_|random(&mut seed)).collect();
        for &s in &clean{w[s.0 as usize]=0;}
        let mut flips=0;
        for lane in 0..64 {
            let y=1+(64*batch+lane)%128;
            let operand=(u128::from(random(&mut seed))<<64)|u128::from(random(&mut seed));
            let top=if y==128 {operand} else {operand&((1u128<<y)-1)};
            let neighbor=match (batch+lane)%4 {0=>top,1=>top.saturating_sub(1),2=>top.saturating_add(1),_=>operand};
            for i in 0..7{put(&mut w,e[i],lane,((y-1)>>i)&1!=0);}
            for i in 0..128{put(&mut w,ring[256-i],lane,operand>>i&1!=0);put(&mut w,q[i],lane,neighbor>>i&1!=0);}
            let cross=(batch+lane)%5==0;put(&mut w,tag,lane,cross);
            if cross||neighbor>top {flips|=1u64<<lane;}
        }
        let initial=w.clone();let mut expected=w.clone();expected[target.0 as usize]^=flips;
        execute(&tape,&mut w,false);assert_eq!(w,expected);
        execute(&tape,&mut w,true);assert_eq!(w,initial);
    }
    println!("q659-boundary width={} recorded_ccx={ccx} basis=2048 full_forward_inverse=true",b.peak);
}

#[test]
fn q659_raw_parked_length_query(){
    let mut b=B::new();
    let low:[QubitId;6]=b.alloc_n(6).try_into().unwrap();let q=b.alloc_n(128);let out=b.alloc();
    b.begin();super::super::q659_raw_length::xor_raw_length_high(&mut b,&low,&q,out);
    let word=b.end();let ccx=word.iter().filter(|g|matches!(g,G::Ccx(..))).count();assert_eq!(ccx,126);
    let mut seed=0x9ad7_faff_5031_7a40;
    for batch in 0..32{
        let mut w:Vec<_>=(0..b.peak).map(|_|random(&mut seed)).collect();let mut flips=0;
        for lane in 0..64{
            let y=1+(64*batch+lane)%128;
            for i in 0..6{put(&mut w,low[i],lane,(y-1)>>i&1!=0);}
            put(&mut w,q[y-1],lane,true);
            for i in (y+30).min(128)..128 {put(&mut w,q[i],lane,false);}
            if y>64{flips|=1u64<<lane;}
        }
        let initial=w.clone();let mut expected=w.clone();expected[out.0 as usize]^=flips;
        execute(&word,&mut w,false);assert_eq!(w,expected);
        execute(&word,&mut w,true);assert_eq!(w,initial);
    }
    println!("q659-raw width={} recorded_ccx={ccx} basis=2048 full_forward_inverse=true",b.peak);
}
