//! Test child of the staged tagged_bridge module. This adds the actual
//! RA64 prior-DONE/fresh-DONE activity at the previous-HT payload narrow.
use super::*;
use super::super::super::{direct_column::Column, direct_frame, direct_payload, pointadd_frogdrop};

/// Direct Fredkin with conditions !C and unsigned byte < exclusive.
/// The disjoint lexicographic cubes are tested against a stable XOR
/// difference, so an additional clean swap-mask wire is unnecessary.
fn selected_swap(b:&mut B, byte:&[QubitId], exclusive:usize, tag:QubitId,
                 q:QubitId, ring:QubitId, dirty:&[QubitId]) {
    assert_eq!(byte.len(),8);
    assert!(exclusive<256);
    b.cx(q,ring);
    for k in (0..8).rev().filter(|&k| ((exclusive>>k)&1)!=0) {
        let mut ctl = vec![(tag,true),(ring,false),(byte[k],true)];
        ctl.extend((k+1..8).map(|i| (byte[i],(exclusive>>i)&1==0)));
        mask::mc_xor(b,&ctl,q,&[],dirty);
    }
    b.cx(q,ring);
}

/// PH & !C & (some Q[64..121] OR all Q[122..128] zero), XORed into cut.
/// Bit 121 is intentionally absent from the final zero test.
fn old_q_predicate(b:&mut B,p:&Ports) {
    let mut ctl=vec![(p.phase,false),(p.roles.tag,true)];
    let bank=&p.ring[..96];
    mask::mc_xor(b,&ctl,p.roles.cut,&[],bank);
    ctl.extend(p.q[64..121].iter().map(|&w|(w,true)));
    mask::mc_xor(b,&ctl,p.roles.cut,&[],bank);
    ctl.extend(p.q[122..128].iter().map(|&w|(w,true)));
    mask::mc_xor(b,&ctl,p.roles.cut,&[],bank);
}

fn compact_mask(b:&mut B,p:&Ports,qf:&[G])->Vec<G> {
    let r=p.roles;
    let bank=&p.ring[..96];
    let size=SumSize{y:with_high(&p.low,r.toggle),sum:p.sum};
    let address=direct_frame::z_byte_record(b,&size,r.prefix,bank);
    let byte:Vec<_>=size.y.iter().copied().chain([r.prefix]).collect();
    b.begin();
    b.cx(p.q[127],r.toggle);
    b.play(qf,true);
    b.play(&address,false);
    for i in 64..128 {
        // Undo precisely original Z-cut swaps with Z <= 256-i, i.e.
        // Z-1 < 256-i. Ring indices 129..192 avoid the dirty bank.
        selected_swap(b,&byte,256-i,r.tag,p.q[i],p.ring[256-i],bank);
    }
    let exposure=b.end();
    b.begin();
    b.play(&exposure,false);
    old_q_predicate(b,p);
    b.play(&exposure,true);
    b.end()
}

/// Reference arm uses the pinned Column::xor_done twice with the precise
/// extra controls from Column::xor_ht_narrow_activity, plus its leading
/// PH & !C term. The full three-term expression is independent of the new
/// simplified predicate and precedes the parent's Q/ring exchange.
fn reference_mask(b:&mut B,p:&Ports,size:&SumSize)->Vec<G> {
    let r=p.roles;
    let col=Column{meta:size,roles:r,ring:&p.ring,q:&p.q,phase:p.phase,
        compact:Some(&p.payload),dirty:&p.payload,clean_external:&[]};
    b.begin();
    b.x(r.tag);b.ccx(p.phase,r.tag,r.cut);b.x(r.tag);
    col.xor_done(b,r.cut,&[(r.tag,true)]);
    let mut fresh=vec![(r.tag,true),(p.q[121],false)];
    fresh.extend(p.q[122..128].iter().map(|&w|(w,true)));
    col.xor_done(b,r.cut,&fresh);
    b.end()
}

fn use_mask(b:&mut B,p:&Ports,size:&SumSize,q_view:&[QubitId],range:(usize,usize),
            mask_word:&[G],diagnostic:bool) {
    b.play(mask_word,false);
    if diagnostic {
        // Independent observable for every shot, including cases where a
        // correctly enabled narrow has no data effect. This is a separate
        // word from the charged direct_payload::narrow_ht arm.
        b.cx(p.roles.cut,p.payload[0]);
    } else {
        direct_payload::narrow_ht(b,size,&p.payload,q_view,range,p.roles.cut,
                                  p.roles.toggle,p.roles.prefix,&p.ring[..96]);
    }
    b.play(mask_word,true);
}

fn candidate(b:&mut B,p:&Ports,range:(usize,usize),diag:bool)->Vec<G> {
    b.begin();
    guarded_y_exchange(b,p);
    let qf=q_frame(b,p);
    b.play(&qf,false);
    b.x(p.roles.tag);b.ccx(p.roles.tag,p.q[127],p.sum[4]);b.x(p.roles.tag);
    b.cx(p.roles.tag,p.sum[4]);
    let size=SumSize{y:with_high(&p.low,p.q[127]),sum:p.sum};
    let s=outer_size::stage1_record(b,&size,p.roles,&p.ring,(97,256),&p.q[..127]);
    b.play(&s,false);
    let rf=ring_down(b,p,&size);
    b.play(&rf,false);
    guarded_residual(b,p,&size);
    b.play(&rf,true);
    let witness=compact_mask(b,p,&qf);
    let q_view:Vec<_>=(0..128).map(|i|p.ring[256-i]).collect();
    use_mask(b,p,&size,&q_view,range,&witness,diag);
    b.play(&qf,true);
    tagged_offset(b,p);
    b.end()
}

fn baseline(b:&mut B,p:&Ports,range:(usize,usize),diag:bool)->Vec<G> {
    let size=SumSize{y:with_high(&p.low,p.separate_high.unwrap()),sum:p.sum};
    let s=outer_size::stage1_record(b,&size,p.roles,&p.ring,(97,256),&p.q);
    let x=byte_cut_swap::record(b,&size,p.roles,&p.ring,&p.q,&[(p.roles.tag,true)],&p.ring[..64]);
    let fill=outer_size::tagged_refill_record(b,&size,p.roles,&p.q,&p.ring);
    let witness=reference_mask(b,p,&size);
    b.begin();
    b.play(&s,false);
    use_mask(b,p,&size,&p.q,range,&witness,diag);
    b.play(&x,false);
    b.play(&fill,false);
    b.end()
}

fn arm(parent:bool,range:(usize,usize),diag:bool)->Emission {
    let mut b=B::new();
    let p=Ports{ring:b.alloc_n(257),q:b.alloc_n(128),low:b.alloc_n(6).try_into().unwrap(),
        sum:b.alloc_n(5).try_into().unwrap(),
        roles:Roles{tag:b.alloc(),cut:b.alloc(),toggle:b.alloc(),prefix:b.alloc()},
        phase:b.alloc(),payload:b.alloc_n(258),separate_high:if parent{Some(b.alloc())}else{None}};
    let tape=if parent{baseline(&mut b,&p,range,diag)}else{candidate(&mut b,&p,range,diag)};
    b.play(&tape,false);b.flush_global();
    let split=b.ops.len();
    b.play(&tape,true);b.flush_global();
    let width=b.width() as usize;assert_eq!(b.peak as usize,width);
    Emission{p,width,split,ops:b.ops}
}

#[derive(Clone,Copy)]
struct State {
    bottom:N, top:N, previous:N, counter:usize, old_m:usize, y:usize,
    tagged:bool, phase:bool, category:usize,
}

/// At a fixed late schedule column collect actual scalar terminal operands
/// with the actual number of non-skipped q=0 idle maps since finishing.
/// category 0=fresh A0, 1=old A0, 2=old B0.
fn terminal_images(cols:&[super::super::super::frogdrop_col::ColPar])->Vec<State> {
    let mut rng=Rng::new(0x444f_4e45_3635_3901);
    let c=150;
    let mut found=[0usize;3];
    let mut images=Vec::new();
    for _ in 0..8192 {
        let input=rng.below(255);
        if input==N::ZERO{continue;}
        let shot=frogdrop_sched::shot(input,128);
        let first=shot.recs.len();
        if first>c || first==0 {continue;}
        let count=1+c-first;
        assert!(count<128);
        let active_maps=cols[first..c].iter()
            .filter(|cp| !(cp.dn&&!cp.nomap&&cp.sz!=(0,0)&&cp.m>121)).count();
        let a0=active_maps%2==0;
        let category=if count==1{0}else if a0{1}else{2};
        if found[category]>=16{continue;}
        let (mut rp,mut rr)=(frogdrop_sched::p(),input);
        let (mut tp,mut tt)=(N::ZERO,N::from(1u64));
        while rr>N::from(1u64){
            let digit=rp/rr;(rp,rr)=(rr,rp%rr);(tp,tt)=(tt,tp+digit*tt);
        }
        assert_eq!(rr,N::from(1u64));
        if rp.bit_len()>26 || rp<=N::from(1u64){continue;}
        let (bottom,previous,top)=if a0{(tt,rp,N::from(1u64))}else{(tp,N::from(1u64),rp)};
        let y=top.bit_len();let z=bottom.bit_len();
        if !(226..=257).contains(&(y+z)) || !(98..=255).contains(&z){continue;}
        found[category]+=1;
        images.push(State{bottom,top,previous,counter:count,old_m:y,y,tagged:false,phase:true,category});
        if found==[16,16,16]{break;}
    }
    assert_eq!(found,[16,16,16]);
    images
}

/// Integer source predicate, deliberately stated as DONE and fresh cases.
fn expected_act(p:&Ports,words:&[u64],lane:usize)->bool {
    let ph=get(words,p.phase,lane);let tag=get(words,p.roles.tag,lane);
    let mid_clear=p.q[64..121].iter().all(|&w|!get(words,w,lane));
    let cnt=(0..7).map(|i|usize::from(get(words,p.q[121+i],lane))<<i).sum::<usize>();
    let done=ph&&mid_clear&&cnt!=0;
    ph&&!tag&&(!done||cnt==1)
}

#[test]
fn q659_real_done_guard_and_conjugated_ht_narrow() {
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cols,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cols[97];
    assert!(cp.pht&&cp.dn);
    let range=(cp.sz.0.max(256-cp.psy.1.min(128)),cp.sz.1.min(255).min(257-cp.psy.0.max(1)));
    assert_eq!(range,(128,255));
    let terminal=terminal_images(&cols);
    let tagged=crossing_images();
    let mut cases=Vec::new();
    for case in &terminal { cases.push(*case); }
    for image in tagged {
        cases.push(State{bottom:image.bottom,top:image.top,previous:image.q,counter:0,
            old_m:image.bottom.bit_len(),y:image.q.bit_len(),tagged:true,phase:true,
            category:if image.delayed{4}else{3}});
    }
    // Explicit synthetic sparse/dense predicate witnesses at every formerly
    // swapped high position. Compact marker care still holds on every row.
    let mut rng=Rng::new(0x646f_6e65_6d69_6431);
    for i in 0..400 {
        let h=64+i%64;
        let z=256-h;
        let y=(226-z).max(1)+((i/64)%4);
        let y=y.min(128);
        assert!((226..=257).contains(&(z+y)));
        let mut top=rng.below(y-1)|(N::from(1u64)<<(y-1));
        let mut previous=N::ZERO;
        let mode=i/64;
        // At a short-width input, the false class marker e+64 is at least
        // 63 positions beyond Y and therefore outside this previous word.
        if mode%3==0 { previous|=N::from(1u64)<<h; }
        if h>=122 && mode%2==0 { previous|=N::from(1u64)<<64; }
        if mode%3==1 && h>=122 { previous=N::from(1u64)<<122; }
        if mode%3==2 && h>=121 { previous=N::from(1u64)<<121; }
        if y>64 && mode%2==1 { top|=N::from(1u64)<<64; }
        let bottom=rng.below(z-1)|(N::from(1u64)<<(z-1));
        cases.push(State{bottom,top,previous,counter:0,old_m:y,y,tagged:false,
            phase:mode!=5,category:5});
    }
    assert_eq!(cases.len(),512);
    let mut summary=Vec::new();
    for diagnostic in [false,true] {
        let old=arm(true,range,diagnostic);let new=arm(false,range,diagnostic);
        assert_eq!((old.width,new.width),(660,659));
        let p=&old.p;let mut rng=Rng::new(0x6572_6173_6564_6375);
        let mut visits=[0usize;6];let mut keep=[0usize;6];
        let mut changed=[0usize;6];let mut naive_disagreements=0;let mut totals=[0u64;2];
        for (batch,block) in cases.chunks_exact(64).enumerate(){
            let mut raw=vec![0u64;old.width];
            for &w in &p.payload{raw[w.0 as usize]=rng.next();}
            for (lane,image) in block.iter().enumerate(){
                let a=*image;
                assert!(a.bottom.bit_len()+a.top.bit_len()<=257);
                assert!(a.previous.bit_len()<=128);
                let q:N=a.previous|(N::from(a.counter as u64)<<121usize);
                for i in 0..257 {set(&mut raw,p.ring[i],lane,a.bottom.bit(i)||a.top.bit(256-i));}
                for i in 0..128 {set(&mut raw,p.q[i],lane,q.bit(i));}
                for i in 0..6 {set(&mut raw,p.low[i],lane,((a.old_m-1)>>i)&1!=0);}
                set(&mut raw,p.separate_high.unwrap(),lane,a.old_m>64);
                set(&mut raw,p.phase,lane,a.phase);set(&mut raw,p.roles.tag,lane,a.tagged);
                let z=a.bottom.bit_len();
                if (range.0..=range.1).contains(&z) {set(&mut raw,p.payload[257-z],lane,true);}
            }
            let mut packed=raw[..new.width].to_vec();
            packed[p.sum[4].0 as usize]=raw[p.separate_high.unwrap().0 as usize];
            let mut want=raw.clone();
            for (lane,a) in block.iter().enumerate(){
                visits[a.category]+=1;
                let z=a.bottom.bit_len();
                let act=expected_act(p,&raw,lane);keep[a.category]+=usize::from(act);
                let swaps=if a.tagged{0}else{128.min(257-z)};
                for i in 0..swaps{
                    set(&mut want,p.q[i],lane,get(&raw,p.ring[256-i],lane));
                    set(&mut want,p.ring[256-i],lane,get(&raw,p.q[i],lane));
                }
                naive_disagreements+=usize::from(act != expected_act(p,&want,lane));
                let sum=if a.tagged{(a.old_m+a.y-2)&31}else{z+a.y-226};
                for i in 0..5{set(&mut want,p.sum[i],lane,(sum>>i)&1!=0);}
                for i in 0..6{set(&mut want,p.low[i],lane,((a.y-1)>>i)&1!=0);}
                set(&mut want,p.separate_high.unwrap(),lane,a.y>64);
                let i=256-z;
                if diagnostic {
                    if act{set(&mut want,p.payload[0],lane,!get(&raw,p.payload[0],lane));}
                } else if act&&(range.0..=range.1).contains(&z)
                        &&(i>=128||!get(&raw,p.q[i],lane))&&get(&raw,p.payload[i+1],lane){
                    changed[a.category]+=1;
                    set(&mut want,p.payload[i],lane,!get(&raw,p.payload[i],lane));
                }
                assert_eq!(get(&want,p.q[64+(a.y-1)%64],lane),a.y>64);
            }
            for (parent,e,input) in [(true,&old,&raw),(false,&new,&packed)]{
                let f=run(&e.ops[..e.split],e.width,&|w|w.copy_from_slice(input));
                assert_eq!(f.phase,0,"forward phase diag={diagnostic} parent={parent} batch={batch}");
                assert_eq!(&f.q[..],&want[..e.width],"forward wires diag={diagnostic} parent={parent} batch={batch}");
                let rev=run(&e.ops[e.split..],e.width,&|w|w.copy_from_slice(&f.q));
                assert_eq!(rev.phase,0,"inverse phase diag={diagnostic} parent={parent} batch={batch}");
                assert_eq!(&rev.q[..],input.as_slice(),"inverse wires diag={diagnostic} parent={parent} batch={batch}");
                totals[usize::from(parent)]+=f.tof;
            }
        }
        assert_eq!(visits,[16,16,16,32,32,400]);
        assert_eq!(&keep[..5],&[16,0,0,0,0]);
        assert!(naive_disagreements>0);
        // On the collected fresh A0 rows the selected R bit is already one:
        // the guard is live although the legal payload narrow can be the
        // identity. The separate P0 diagnostic observes that guard directly.
        if !diagnostic {assert!(changed[5]>0);}
        let charged=|e:&Emission|e.ops[..e.split].iter().filter(|g|matches!(g.kind,OperationType::CCX|OperationType::CCZ)).count();
        summary.push((diagnostic,old.split,new.split,charged(&old),charged(&new),totals,keep,changed,naive_disagreements));
    }
    println!("q659-done-bridge real_scalar_column=150 narrow_range={range:?} raw_cases=512 diagnostic_cases=512 widths=660/659 [diag,oldops,newops,oldccx,newccx,exec(new/old),active,changed,postQ_naive_mismatch]={summary:?} full_forward_inverse_phase_clean=true");
}
