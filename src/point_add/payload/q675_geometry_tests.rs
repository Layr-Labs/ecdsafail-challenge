//! Local geometry adapters only. No full N258 production emitter is enabled.
use super::*;
use crate::point_add::{frogdrop_sched::N,q675_vform_tests::{run_tape,receipt_audit}};

fn read(q:&[u64],ports:&[QubitId],lane:usize)->N {
    ports.iter().enumerate().fold(N::ZERO,|a,(i,p)|a|(N::from((q[p.0 as usize]>>lane)&1)<<i))
}
fn put(q:&mut[u64],ports:&[QubitId],lane:usize,v:N){
    for(i,p)in ports.iter().enumerate(){let m=1u64<<lane;if v.bit(i){q[p.0 as usize]|=m}else{q[p.0 as usize]&=!m}}
}
fn noise(i:usize,seed:usize)->u64{0x9e3779b97f4a7c15u64.wrapping_mul((i+1)as u64).rotate_left((seed*7+i)as u32)}

#[test]
fn b9a_l2tree_paired_all_wire() {
    crate::point_add::bake_knobs();
    let mut b = B::new();
    let p = b.alloc_n(200);
    let t = &p[..32];
    let s = &p[32..64];
    let reg = &p[64..70];
    let extra = [(p[70], false)];
    let e = p[71];
    let pre = &p[74..79];
    let temps = &p[79..81];
    let dirty = &p[81..];
    let lo = 11;
    let hi = 27;
    b.begin();
    read_lane_and2(&mut b, reg, lo, hi, t, s, &extra, e, pre, temps, dirty);
    let old = b.end();
    let pair = erase_ripple::paired_mid_record(&mut b, t, s, reg, lo, hi,
        &extra, e, pre, temps, dirty).expect("paired geometry");
    b.begin();
    let mut range = Mask::new(reg, hi, true, extra.to_vec(), e, pre, dirty);
    range.toggle_range(&mut b, lo, hi);
    b.play(&pair, false);
    let new = b.end();
    let (of, oi) = read_lane_tree::prices(&old).unwrap();
    let (nf, ni) = read_lane_tree::prices(&new).unwrap();
    assert!(nf < of && ni < oi, "paired tree cost old={of}/{oi} new={nf}/{ni}");
    let mut bo = B::new(); bo.alloc_n(200); bo.play(&old, false);
    let old_f = bo.ops.clone(); bo.ops.clear(); bo.play(&old, true);
    let old_i = bo.ops.clone();
    let mut bn = B::new(); bn.alloc_n(200); bn.play(&new, false);
    let new_f = bn.ops.clone(); bn.ops.clear(); bn.play(&new, true);
    let new_i = bn.ops.clone();
    let mut checked = 0;
    for seed in 0..4 {
        let mut input = vec![0u64; 200];
        for i in (0..64).chain(81..200) { input[i] = noise(i, seed); }
        input[e.0 as usize] = noise(71, seed);
        for lane in 0..64 {
            let code = lane;
            put(&mut input, reg, lane, N::from(code));
            if (lo..=hi).contains(&code) && ((lane + seed) % 3 != 0) {
                input[extra[0].0.0 as usize] |= 1u64 << lane;
            }
        }
        for (inverse, old_ops, new_ops) in [(false, &old_f, &new_f), (true, &old_i, &new_i)] {
            let a = run_tape(old_ops, 200, &input, 2);
            let z = run_tape(new_ops, 200, &input, 2);
            assert_eq!(z.q, a.q, "seed={seed} inverse={inverse}");
            assert_eq!(z.phase, a.phase);
            assert_eq!(z.phase, 0);
            checked += 64;
        }
        let mut roundtrip = new_f.clone(); roundtrip.extend_from_slice(&new_i);
        let z = run_tape(&roundtrip, 200, &input, 2);
        assert_eq!(z.q, input);
        assert_eq!(z.phase, 0);
        checked += 64;
    }
    eprintln!("B9A_L2TREE_PASS lanes={checked} codes=0..63 active_range=11..27 dirty=true forward_inverse_phase0=true old_F_T={of} new_F_T={nf}");
}

#[test]
fn b9a_l2c_mask_decoder_all_wire() {
    crate::point_add::bake_knobs();
    let mut checked = 0;
    for below in [false, true] {
        for lo in [0, 2, 5] {
            let steps = [Some(12), Some(7), Some(3), Some(16), None];
            for prefix in 1..=steps.len() {
                let make = |decoded: bool, inverse: bool| {
                    let mut b = B::new();
                    let p = b.alloc_n(675);
                    let bits = &p[..8];
                    let pre = &p[8..15];
                    let base = p[15];
                    let flag = p[16];
                    let temps = &p[17..19];
                    let dirty = &p[100..];
                    let r = crate::point_add::frogdrop_col::rec(&mut b, |b| {
                        let mut m = Mask::new(bits, 15, below, vec![(base, false)], flag, temps, dirty)
                            .with_lo(lo);
                        if decoded { m = m.with_pre(pre); }
                        for &lim in &steps[..prefix] { m.goto(b, lim); }
                    });
                    b.play(&r, inverse);
                    b.ops
                };
                for inverse in [false, true] {
                    // A partial decoder leaves live prefix bits. Its inverse
                    // requires the corresponding forward output as input.
                    if inverse && prefix != steps.len() { continue; }
                    let old = make(false, inverse);
                    let new = make(true, inverse);
                    let ports: Vec<QubitId> = (0..8).map(|i| QubitId(i as u64)).collect();
                    for batch in 0..4 {
                        for seed in 0..3 {
                            let mut input = vec![0u64; 675];
                            input[15] = if seed == 0 { 0 } else if seed == 1 { u64::MAX } else { 0x5555_aaaa_3333_cccc };
                            input[16] = noise(16, seed);
                            for i in 100..675 { input[i] = noise(i, seed); }
                            for lane in 0..64 { put(&mut input, &ports, lane, N::from(batch*64+lane)); }
                            for tape in 0..3 {
                                let a = run_tape(&old, 675, &input, tape);
                                let d = run_tape(&new, 675, &input, tape);
                                assert_eq!(a.q[16], d.q[16], "below={below} lo={lo} prefix={prefix} inverse={inverse} batch={batch} seed={seed} tape={tape}");
                                for i in (0..8).chain(15..675) { assert_eq!(a.q[i], d.q[i], "wire={i} below={below} lo={lo} prefix={prefix} inverse={inverse} batch={batch} seed={seed} tape={tape}"); }
                                if prefix == steps.len() { assert_eq!(a.q, d.q); assert_eq!(a.phase, d.phase); assert_eq!(d.phase, 0); }
                                checked += 64;
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("B9A_L2C_MASK_DECODER_PASS lanes={checked} raw_codes=0..255 dirty=true active_inactive=true forward_inverse=true phase0_on_clear=true");
}

#[test]
fn q675_stage5_ring_bound_and_truncation(){
    crate::point_add::bake_knobs();let mut checked=0;let mut missing_carry_negative=0;
    for kb in 0..23usize {
        let mut b=B::new();let p=b.alloc_n(675);let sh=((usize::BITS-1-(kb+1).leading_zeros())as usize).min(4);
        let span=(NP-kb).min(258);let target=&p[258+kb..258+kb+span];let source=&p[..span];
        crate::point_add::midg::trans_masked_q(&mut b,target,source,258,kb,p[525],&p[517..525],sh,1,128,p[526],p[527],&p[528..530],&[],&p[550..]);
        let ops=b.ops.clone();receipt_audit(&ops);
        // Independent inherited N259 reference: clear only the selected source
        // boundary in its input, as guaranteed by the original two-gap layout.
        let mut full_source=p[..258].to_vec();full_source.push(p[540]);b.ops.clear();b.tof=0;
        crate::point_add::midg::trans_masked_q(&mut b,&p[258+kb..517],&full_source[..NP-kb],259,kb,p[525],&p[517..525],sh,1,128,p[526],p[527],&p[528..530],&[],&p[550..]);
        let inherited=b.ops.clone();
        // Preserve the rejected n-1 mask as an emitted negative control.
        b.ops.clear();b.tof=0;let mut mask=Mask::new(&p[517+sh..525],128>>sh,true,vec![(p[525],false)],p[526],&[],&p[550..]);
        let mut gate=|b:&mut B,i:Option<usize>|match i{
            Some(i)=>{mask.goto(b,Some((257-(kb+i)as isize).div_euclid(1<<sh)+1));Some(p[526])},
            None=>{mask.goto(b,None);None}
        };
        ripple(&mut b,&p[258+kb..517],&full_source[..NP-kb],p[527],false,&mut |_|{},&mut gate);let rejected=b.ops.clone();
        for seed in 0..4 {for sybatch in 0..2 {for active in[0,u64::MAX,0x5555555555555555]{for tape in 0..3 {
            let mut input=vec![0;675];for i in 0..517{input[i]=noise(i,seed);}input[540]=noise(540,seed);
            for i in 550..675{input[i]=noise(i,seed);}input[525]=active;
            for lane in 0..64{put(&mut input,&p[517..525],lane,N::from(1+sybatch*64+lane));}
            let mut want=input.clone();let mut reference_input=input.clone();
            for lane in 0..64{let sy=1+sybatch*64+lane;let boundary=258-kb-(sy>>sh)*(1<<sh);assert!(boundary<span);
                let low=(N::from(1)<<boundary)-N::from(1);let win=(N::from(1)<<(boundary+1))-N::from(1);let a=read(&input,target,lane);let s=read(&input,source,lane);
                let z=if active>>lane&1!=0{(a&!win)|((a+(s&low))&win)}else{a};put(&mut want,target,lane,z);
                reference_input[source[boundary].0 as usize]&=!(1u64<<lane);
            }
            let out=run_tape(&ops,675,&input,tape);assert_eq!(out.q,want,"kb{kb} sybatch{sybatch} seed{seed}");
            let refout=run_tape(&inherited,675,&reference_input,tape);let mut reference_want=want.clone();for &q in &full_source{reference_want[q.0 as usize]=reference_input[q.0 as usize];}assert_eq!(refout.q,reference_want);
            if tape==2&&active==u64::MAX{let bad=run_tape(&rejected,675,&input,tape);missing_carry_negative+=bad.q.iter().zip(&want).filter(|(a,b)|a!=b).count();}
            checked+=64;
        }}}}
        eprintln!("Q675_STAGE5_LOCAL kb={kb} span={span} ops={} Q=675",ops.len());
    }
    assert!(missing_carry_negative>0);eprintln!("Q675_STAGE5_PASS lanes={checked} missing_boundary_carry_differing_words={missing_carry_negative} inherited_zero_boundary_reference=true arbitrary_new_boundary_source_restored=true");
}

#[test]
fn q675_ht_margin1_exact_mask_and_negative(){
    crate::point_add::bake_knobs();assert_eq!(ht_mask_shift(1),0);for m in 2..40{assert_eq!(ht_mask_shift(m),if m>=16{4}else if m>=8{3}else if m>=4{2}else{1});}
    let mut b=B::new();let p=b.alloc_n(675);let t=&p[..12];let s=&p[20..32];let reg=&p[40..48];
    let extra=[(p[50],false),(p[51],true)];let pre=&p[60..67];let tmp=&p[70..72];let dirty=&p[100..];
    let mask=erase_ripple::PrefixMask{bits:reg,amax:11,flag:p[54],margin:1,shift:ht_mask_shift(1),lo:0,pre:&[]};
    let old=erase_ripple::reference_record(&mut b,t,s,p[53],p[52],reg,1,11,&extra,pre,tmp,dirty,Some(mask));
    let fused=erase_ripple::fused_record(&mut b,t,s,p[53],p[52],reg,1,11,&extra,pre,tmp,dirty,Some(mask)).unwrap();
    let mut count=0;
    for (name,r)in[("reference",old),("fused",fused)]{
        b.ops.clear();b.tof=0;b.play(&r,false);let ops=b.ops.clone();receipt_audit(&ops);
        for seed in 0..16{for tape in 0..3{
            let mut input=vec![0;675];for i in (0..12).chain(20..32).chain(100..675){input[i]=noise(i,seed);}input[50]=noise(50,seed);input[51]=noise(51,seed);input[52]=noise(52,seed);
            for lane in 0..64{put(&mut input,reg,lane,N::from(lane%12));}
            let mut want=input.clone();
            for lane in 0..64{let code=lane%12;let a=read(&input,t,lane);let src=read(&input,s,lane);let e=input[52]>>lane&1!=0;
                let m=(N::from(1)<<(code+1))-N::from(1);let z=if e{(a&!m)|((a+src)&m)}else{a};put(&mut want,t,lane,z);
                if code>=1&&input[50]>>lane&1!=0&&input[51]>>lane&1==0{
                    let carry=((m-(z&m))+(src&m)).bit(code+1);let next=code+1<12&&src.bit(code+1);
                    if !(carry^next){want[52]^=1<<lane;}
                }
            }
            let out=run_tape(&ops,675,&input,tape);assert_eq!(out.q,want,"{name} seed{seed}");count+=64;
        }}
    }
    // Concrete carry loss: source=1,target=1,t=1,enabled. Granule2 writes
    // only bit0; granule1 includes the true carry at bit1 and returns 2.
    let mut observed=vec![];
    for shift in[0,1]{b.ops.clear();b.tof=0;let mut mk=Mask::new(&reg[shift..],11>>shift,false,vec![(p[52],false)],p[54],tmp,dirty);
        let mut gate=|b:&mut B,i:Option<usize>|match i{Some(i)=>{let x=i as isize-1;mk.goto(b,Some(if x<0{0}else{x.div_euclid(1<<shift)+1}));Some(p[54])},None=>{mk.goto(b,None);None}};
        ripple(&mut b,t,s,p[53],false,&mut |_|{},&mut gate);let mut input=vec![0;675];input[0]=u64::MAX;input[20]=u64::MAX;input[40]=u64::MAX;input[52]=u64::MAX;
        let out=run_tape(&b.ops,675,&input,2);observed.push(read(&out.q,t,0));
    }
    assert_eq!(observed,vec![N::from(2),N::ZERO]);eprintln!("Q675_HT_MARGIN_PASS lanes={count} old_granule_negative=64 reference_fused_fullstate=true");
}

#[test]
fn r9_margin1_fused_carry_all_size_codes() {
    crate::point_add::bake_knobs();
    let mut b = B::new();
    let p = b.alloc_n(675);
    let t = &p[..12];
    let s = &p[20..32];
    let reg = &p[40..48];
    let extra = [(p[50], false), (p[51], true)];
    let (e, c0, flag) = (p[52], p[53], p[54]);
    let pre = &p[60..67];
    let temps = &p[70..72];
    let dirty = &p[100..];
    let mask = erase_ripple::PrefixMask {
        bits: reg, amax: 11, flag, margin: 1, shift: 0, lo: 0, pre: &[],
    };
    b.begin();
    let mut mk = Mask::new(reg, 11, false, vec![(e, false)], flag, &temps[..1], dirty);
    let mut gate = |b: &mut B, i: Option<usize>| match i {
        Some(i) => {
            let x = i as isize - 1;
            mk.goto(b, Some(if x < 0 { 0 } else { x + 1 }));
            Some(flag)
        }
        None => { mk.goto(b, None); None }
    };
    ripple(&mut b, t, s, c0, false, &mut |_| {}, &mut gate);
    let mut no_write = |_b: &mut B, _i: Option<usize>| None;
    ripple_true_carry(&mut b, t, s, c0, reg, 0, 15, &extra, e, flag,
        pre, temps, dirty, &mut no_write);
    let old = b.end();
    let new = erase_ripple::fused_record_margin1(&mut b, t, s, c0, e, reg,
        0, 15, &extra, pre, temps, dirty, Some(mask)).unwrap();
    let mut b_old = B::new(); b_old.alloc_n(675); b_old.play(&old, false);
    let old_forward = b_old.ops.clone(); b_old.ops.clear(); b_old.play(&old, true);
    let old_inverse = b_old.ops.clone();
    let mut b_new = B::new(); b_new.alloc_n(675); b_new.play(&new, false);
    let new_forward = b_new.ops.clone(); b_new.ops.clear(); b_new.play(&new, true);
    let new_inverse = b_new.ops.clone();
    let mut checked = 0;
    for seed in 0..8 {
        let mut input = vec![0u64; 675];
        for i in (0..12).chain(20..32).chain(100..675) {
            input[i] = noise(i, seed);
        }
        input[e.0 as usize] = noise(52, seed);
        input[extra[0].0.0 as usize] = noise(50, seed);
        input[extra[1].0.0 as usize] = noise(51, seed);
        for lane in 0..64 {
            let code = lane % 16;
            put(&mut input, reg, lane, N::from(code));
            if code < s.len() {
                input[s[code].0 as usize] &= !(1u64 << lane);
                if code + 1 < s.len() && seed % 2 == 1 {
                    input[s[code + 1].0 as usize] |= 1u64 << lane;
                }
            }
        }
        for (inverse, old_ops, new_ops) in [(false, &old_forward, &new_forward),
                                            (true, &old_inverse, &new_inverse)] {
            for tape in 0..3 {
                let expected = run_tape(old_ops, 675, &input, tape);
                let actual = run_tape(new_ops, 675, &input, tape);
                let diff: Vec<_> = actual.q.iter().zip(&expected.q).enumerate()
                    .filter(|(_, (a, b))| a != b).take(20)
                    .map(|(i, (a, b))| (i, a ^ b)).collect();
                assert!(diff.is_empty(), "seed={seed} tape={tape} inverse={inverse} diff={diff:?}");
                assert_eq!(actual.phase, expected.phase);
                assert_eq!(actual.phase, 0);
                checked += 64;
            }
        }
    }
    eprintln!("R9_MARGIN1_FUSED_PASS lanes={checked} codes=0..15 live_following_source=true dirty_passengers=true forward_inverse=true phase0=true old_T={} new_T={}",
        old_forward.iter().filter(|o| matches!(o.kind, crate::circuit::OperationType::CCX | crate::circuit::OperationType::CCZ)).count(),
        new_forward.iter().filter(|o| matches!(o.kind, crate::circuit::OperationType::CCX | crate::circuit::OperationType::CCZ)).count());
}

#[test]
fn r9_margin1_fused_carry_width258_all_codes() {
    crate::point_add::bake_knobs();
    let mut b = B::new();
    let p = b.alloc_n(675);
    let t = &p[..258];
    let s = &p[258..516];
    let reg = &p[516..524];
    let extra = [(p[525], false), (p[526], true)];
    let (e, c0, flag) = (p[527], p[528], p[529]);
    let pre = &p[530..537];
    let temps = &p[537..539];
    let dirty = &p[540..];
    let mask = erase_ripple::PrefixMask { bits: reg, amax: 255, flag, margin: 1, shift: 0, lo: 0, pre };
    assert!(erase_ripple::geometry(t, s, c0, e, reg, &extra, pre, temps, dirty, Some(mask)));
    b.begin();
    let mut mk = Mask::new(reg, 255, false, vec![(e, false)], flag, &temps[..1], dirty);
    let mut gate = |b: &mut B, i: Option<usize>| match i {
        Some(i) => { mk.goto(b, Some(i as isize)); Some(flag) },
        None => { mk.goto(b, None); None },
    };
    ripple(&mut b, t, s, c0, false, &mut |_| {}, &mut gate);
    let mut no_write = |_b: &mut B, _i: Option<usize>| None;
    ripple_true_carry(&mut b, t, s, c0, reg, 0, 255, &extra, e, flag,
        pre, temps, dirty, &mut no_write);
    let old = b.end();
    let new = erase_ripple::fused_record_margin1(&mut b, t, s, c0, e, reg,
        0, 255, &extra, pre, temps, dirty, Some(mask)).unwrap();
    let mut bo = B::new(); bo.alloc_n(675); bo.play(&old, false);
    let old_f = bo.ops.clone(); bo.ops.clear(); bo.play(&old, true);
    let old_i = bo.ops.clone();
    let mut bn = B::new(); bn.alloc_n(675); bn.play(&new, false);
    let new_f = bn.ops.clone(); bn.ops.clear(); bn.play(&new, true);
    let new_i = bn.ops.clone();
    let mut roundtrip = new_f.clone(); roundtrip.extend_from_slice(&new_i);
    let mut checked = 0;
    for batch in 0..4 {
        for seed in 0..3 {
            let mut input = vec![0u64; 675];
            for i in (0..516).chain(540..675) { input[i] = noise(i, seed + batch); }
            input[e.0 as usize] = noise(527, seed + batch);
            input[extra[0].0.0 as usize] = if seed == 0 { u64::MAX } else { noise(525, seed + batch) };
            input[extra[1].0.0 as usize] = if seed == 0 { 0 } else { noise(526, seed + batch) };
            for lane in 0..64 {
                let code = batch * 64 + lane;
                put(&mut input, reg, lane, N::from(code));
                input[s[code].0 as usize] &= !(1u64 << lane);
                if code + 1 < s.len() && seed == 1 {
                    input[s[code + 1].0 as usize] |= 1u64 << lane;
                }
            }
            for (inverse, a, z) in [(false, &old_f, &new_f), (true, &old_i, &new_i)] {
                let expected = run_tape(a, 675, &input, 2);
                let actual = run_tape(z, 675, &input, 2);
                let diff: Vec<_> = actual.q.iter().zip(&expected.q).enumerate()
                    .filter(|(_, (x, y))| x != y).take(12)
                    .map(|(i, (x, y))| (i, x ^ y)).collect();
                assert!(diff.is_empty(), "batch={batch} seed={seed} inverse={inverse} diff={diff:?}");
                assert_eq!(actual.phase, expected.phase);
                assert_eq!(actual.phase, 0);
                checked += 64;
            }
            let restored = run_tape(&roundtrip, 675, &input, 2);
            assert_eq!(restored.q, input);
            assert_eq!(restored.phase, 0);
            checked += 64;
        }
    }
    eprintln!("R9_MARGIN1_WIDE_PASS lanes={checked} codes=0..255 width=258 live_following_source=true dirty_passengers=true forward_inverse_roundtrip=true phase0=true old_F_T={} new_F_T={}",
        bo.tof, bn.tof);
}

#[test]
fn b9a_mask_public_lower_bound_all_wire() {
    crate::point_add::bake_knobs();
    let mut checked = 0;
    for shift in [0usize, 1] {
        for below in [false, true] {
            let tlo = 11usize;
            let thi = 27usize;
            let lo = tlo >> shift;
            let amax = thi >> shift;
            let mut b = B::new();
            let p = b.alloc_n(64);
            let reg = &p[..8-shift];
            let (e, g) = (p[8], p[9]);
            let temps = &p[10..12];
            let dirty = &p[12..];
            for limit in [0isize, lo as isize, lo as isize + 1, amax as isize, amax as isize + 1] {
                b.begin();
                let mut old = Mask::new(reg, amax, below, vec![(e,false)], g, temps, dirty);
                old.goto(&mut b, Some(limit));
                let old_rec = b.end();
                b.begin();
                let mut new = Mask::new(reg, amax, below, vec![(e,false)], g, temps, dirty).with_lo(lo);
                new.goto(&mut b, Some(limit));
                let new_rec = b.end();
                b.ops.clear(); b.tof = 0; b.play(&old_rec,false); let old_ops = b.ops.clone();
                b.ops.clear(); b.tof = 0; b.play(&new_rec,false); let new_ops = b.ops.clone();
                b.ops.clear(); b.tof = 0; b.play(&new_rec,false); b.play(&new_rec,true);
                let roundtrip = b.ops.clone();
                for seed in 0..3 {
                    let mut input = vec![0u64;64];
                    for i in 12..64 { input[i] = noise(i,seed); }
                    for lane in 0..64 {
                        let code = [tlo-1,tlo,tlo+1,thi,thi+1][lane%5];
                        put(&mut input,reg,lane,N::from(code>>shift));
                        if (tlo..=thi).contains(&code) { input[e.0 as usize] |= 1u64<<lane; }
                    }
                    for tape in 0..3 {
                        let a = run_tape(&old_ops,64,&input,tape);
                        let n = run_tape(&new_ops,64,&input,tape);
                        assert_eq!(a.q,n.q,"shift={shift} below={below} limit={limit} seed={seed} tape={tape}");
                        assert_eq!(a.phase,n.phase);
                        let back = run_tape(&roundtrip,64,&input,tape);
                        assert_eq!(back.q,input);
                        assert_eq!(back.phase,0);
                        checked += 64;
                    }
                }
            }
        }
    }
    eprintln!("B9A_MASK_LO_PASS lanes={checked} shifts=0,1 boundary=tlo-1,tlo,tlo+1,thi,thi+1 dirty=true forward_inverse=true phase0=true");
}

#[test]
fn q675_final_transition_distinct_padding(){
    crate::point_add::bake_knobs();let mut b=B::new();let p=b.alloc_n(675);let ring=&p[..258];let payload=&p[258..517];let q=&p[517..543];
    let source=final_transition_source(ring,&[p[545],p[546]],&p[547..550]);assert_eq!(source.len(),259);assert_eq!(&source[257..],&[p[545],p[546]]);
    let source259=final_transition_source(&p[..259],&[p[545],p[546]],&[]);let mut inherited=p[..259].to_vec();inherited[258]=p[545];assert_eq!(source259,inherited);
    assert!(std::panic::catch_unwind(||final_transition_source(ring,&[p[545],p[545]],&[])).is_err());
    assert!(std::panic::catch_unwind(||final_transition_source(ring,&[p[545],p[547]],&p[547..550])).is_err());
    trans_q0(&mut b,payload,q,None,&[(p[547],false)],&source,NP,None,p[548],p[549],&[],&p[550..]);receipt_audit(&b.ops);
    let mut count=0;let mut dirty_negative=0;
    for seed in 0..8{for tape in 0..3{for active in[0,u64::MAX,0x5555555555555555]{
        let mut input=vec![0;675];for i in (0..257).chain(258..543).chain(550..675){input[i]=noise(i,seed);}input[257]=u64::MAX;input[547]=active;
        let mut want=input.clone();let target:Vec<_>=payload.iter().rev().copied().collect();
        for lane in 0..64{if active>>lane&1!=0{let x=read(&input,&p[..257],lane);let quotient=read(&input,q,lane);let v=read(&input,&target,lane);put(&mut want,&target,lane,(v+x*quotient)&((N::from(1)<<259)-N::from(1)));}}
        let out=run_tape(&b.ops,675,&input,tape);assert_eq!(out.q,want);count+=64;
        if tape==2&&active==u64::MAX{let mut bad=input.clone();bad[546]=u64::MAX;let out=run_tape(&b.ops,675,&bad,tape);assert_eq!(out.q[546],u64::MAX);dirty_negative+=payload.iter().filter(|p|out.q[p.0 as usize]!=want[p.0 as usize]).count();}
    }}}
    assert!(dirty_negative>0);eprintln!("Q675_ENDPOINT_PASS lanes={count} dirty_padding_differences={dirty_negative} ops={} Q=675 returned_zero_support_required=true",b.ops.len());
}

#[test]
fn q675_actual_endpoint_padding_ports(){
    crate::point_add::bake_knobs();
    for n in[258,259]{for parity in 0..2{
        let(_b,mut fd,pool,p)=crate::point_add::q675_layout_tests::ports(n);
        if parity==1{std::mem::swap(&mut fd.sy,&mut fd.sx);}
        let sc=ColScr::carve_col(&pool,&fd.sx,&p,24,23,40,false);
        let pl=crate::point_add::pointadd_frogdrop::pl_col(&p,&fd,&pool);
        assert_eq!(pl.dirty,fd.ring[n-28..]);assert_eq!(pl.dirty.len(),28);
        let mut free=pl.free.clone();free.extend_from_slice(&fd.sx);
        let mut sa=sc.sz.clone();sa.push(sc.sw);let ds=dig_scr(&free,&sa,&fd.sy,&pl.dirty);
        let mut forbidden=pl.p.clone();forbidden.extend_from_slice(&fd.q[..KD]);forbidden.extend([fd.ph,ds.g,ds.c0]);forbidden.extend_from_slice(&ds.tmp);
        let out=final_transition_source(&fd.ring,&[ds.zeros[0],ds.e[0]],&forbidden);
        assert_eq!(out.len(),259);assert_eq!(out[n-1],ds.zeros[0]);if n==258{assert_eq!(out[258],ds.e[0]);}
        assert!(ds.e.iter().chain(&ds.zeros).all(|q|!ds.dirty.contains(q)));
        eprintln!("Q675_ENDPOINT_PORTS n={n} parity={parity} zero0={} e0={} g={} c0={} tmp={:?} dirty={} source_last={:?} return_zero_contract=DigScr",ds.zeros[0].0,ds.e[0].0,ds.g.0,ds.c0.0,ds.tmp.iter().map(|p|p.0).collect::<Vec<_>>(),pl.dirty.len(),out[out.len()-2..].iter().map(|p|p.0).collect::<Vec<_>>());
    }}
}
