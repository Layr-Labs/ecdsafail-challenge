//! Focused W1a byte, lane, rotation and constant-carry fixtures.
use super::*;

fn apply(gates:&[G],state:&mut[u8]){
    for g in gates {match *g {
        G::X(t)=>state[t.0 as usize]^=1,
        G::Cx(c,t)=>state[t.0 as usize]^=state[c.0 as usize],
        G::Ccx(a,c,t)|G::AndC(a,c,t)|G::AndU(a,c,t)=>
            state[t.0 as usize]^=state[a.0 as usize]&state[c.0 as usize],
        G::Cz(_,_)|G::ZIf(_,_)=>{},
        G::Swap(a,t)=>state.swap(a.0 as usize,t.0 as usize),
        G::Mark(_)=>{},
        _=>panic!("fixture does not interpret gate: {g:?}"),
    }}
}
fn set_word(state:&mut[u8],bits:&[QubitId],value:usize){
    for(i,&q)in bits.iter().enumerate(){state[q.0 as usize]=((value>>i)&1)as u8;}
}
fn word(state:&[u8],bits:&[QubitId])->usize{
    bits.iter().enumerate().map(|(i,&q)|(state[q.0 as usize]as usize)<<i).sum()
}
fn randomize(state:&mut[u8],mut seed:u64){
    for bit in state{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;*bit=(seed&1)as u8;}
}
fn metadata(b:&mut B)->SumSize{
    SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()}
}
fn builder()->B{
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;b
}

#[test]
fn w1a_byte7_exhaustive_metadata(){
    let mut b=builder();let meta=metadata(&mut b);let flag=b.alloc();let dirty=b.alloc_n(20);
    let base=z_byte_record(&mut b,&meta,flag,&dirty);
    let new=z_byte7_record(&mut b,&meta,&dirty);
    for e in 0..128{for s in 0..32{
        let mut initial=vec![0;b.width() as usize];randomize(&mut initial,(e*37+s*271+1)as u64);
        set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);initial[flag.0 as usize]=0;
        let(mut a,mut n)=(initial.clone(),initial.clone());apply(&base,&mut a);apply(&new,&mut n);
        assert_eq!(word(&a,&meta.y)&127,word(&n,&meta.y),"E={e} S={s}");
        assert_eq!(word(&n,&meta.y),(224+s-e)%128,"E={e} S={s}");
        for &q in meta.sum.iter().chain(&dirty){assert_eq!(a[q.0 as usize],n[q.0 as usize]);}
        assert_eq!(a[flag.0 as usize],((224+s-e)>>7)as u8);
    }}
}

#[test]
fn w1a_lane7_and_rotate_against_base(){
    for (floor,overflow) in [(98,2),(128,0),(200,0)]{
        let hi=(floor+127+overflow).min(256);
        let mut b=builder();let meta=metadata(&mut b);let flag=b.alloc();
        let ring=b.alloc_n(257);let a=b.alloc();let target=b.alloc();let dirty=b.alloc_n(20);
        let old_lane=z_lane_record(&mut b,&meta,&ring,flag,(floor,hi),0,Some((a,target)),&dirty);
        let new_lane=z_lane7_record(&mut b,&meta,&ring,floor,overflow,0,Some((a,target)),&dirty);
        let old_flip=z_lane_record(&mut b,&meta,&ring,flag,(floor,hi),0,None,&dirty);
        let new_flip=z_lane7_record(&mut b,&meta,&ring,floor,overflow,0,None,&dirty);
        for e in 0..128{for s in 0..32{
            let z=225+s-e;if z<floor||z>hi{continue;}
            let mut initial=vec![0;b.width() as usize];randomize(&mut initial,(e*157+s*911+floor)as u64);
            set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);initial[flag.0 as usize]=0;
            for (base,new) in [(&old_lane,&new_lane),(&old_flip,&new_flip)]{
                let(mut x,mut y)=(initial.clone(),initial.clone());apply(base,&mut x);apply(new,&mut y);
                assert_eq!(x,y,"floor={floor} E={e} S={s} Z={z}");
            }
        }}
    }
    for (floor,overflow) in [(98,2),(128,0),(200,0)]{
        let hi=(floor+127+overflow).min(256);
        let mut b=builder();let meta=metadata(&mut b);let flag=b.alloc();
        let cycle=b.alloc_n(17);let dirty=b.alloc_n(20);
        let old=rotate_z_record(&mut b,&meta,&cycle,flag,(floor,hi),None,false,&dirty);
        let new=rotate_z7_record(&mut b,&meta,&cycle,floor,overflow,false,&dirty);
        for e in 0..128{for s in 0..32{
            let z=225+s-e;if z<floor||z>hi{continue;}
            let mut initial=vec![0;b.width() as usize];randomize(&mut initial,(e*103+s*739+floor)as u64);
            set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);initial[flag.0 as usize]=0;
            let(mut x,mut y)=(initial.clone(),initial.clone());apply(&old,&mut x);apply(&new,&mut y);
            assert_eq!(x,y,"rotation floor={floor} E={e} S={s} Z={z}");
        }}
    }
}

#[test]
fn w1a_v_const0_exhaustive(){
    let mut b=builder();let meta=metadata(&mut b);let carry=b.alloc();let target=b.alloc();let dirty=b.alloc_n(20);
    for j in 0..=32{
        let mut old=builder();let old_meta=metadata(&mut old);let old_carry=old.alloc();let old_target=old.alloc();let old_dirty=old.alloc_n(20);
        let base=rec(&mut old,|b|v_gate_latched(b,&old_meta,j,old_target,old_carry,&old_dirty));
        let new=rec(&mut b,|b|v_gate_latched_const0(b,&meta,j,target,&dirty));
        for e in 0..128{for s in 0..32{
            let mut initial=vec![0;b.width() as usize];randomize(&mut initial,(e*61+s*41+j*2027)as u64);
            set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);initial[carry.0 as usize]=0;
            let(mut x,mut y)=(initial.clone(),initial.clone());apply(&base,&mut x);apply(&new,&mut y);
            assert_eq!(x,y,"j={j} E={e} S={s}");
        }}
    }
}

#[test]
fn w1a_top_head_real_width(){
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let flag=b.alloc();let q127=b.alloc();let dirty=b.alloc_n(20);
    let old=normalized_top_record(&mut b,&meta,&ring,flag,&dirty);
    let new=normalized_top_head_record(&mut b,&meta,&ring,q127,&dirty);
    for s in 0..32{for trial in 0..4{
        let mut initial=vec![0;b.width() as usize];
        randomize(&mut initial,(s*7717+trial*2999+1)as u64);
        set_word(&mut initial,&meta.sum,s);initial[flag.0 as usize]=0;
        initial[q127.0 as usize]=1;
        let(mut a,mut n)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&new,&mut n);
        assert_eq!(a,n,"normalized top S={s} trial={trial}");
    }}
}

#[test]
fn f1_pair_top_frame_with_inactive_passengers(){
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let flag=b.alloc();let q127=b.alloc();let a=b.alloc();let dirty=b.alloc_n(20);
    let old=normalized_top_record(&mut b,&meta,&ring,flag,&dirty);
    let new=normalized_top_head_record(&mut b,&meta,&ring,q127,&dirty);
    let old_pair=rec(&mut b,|b|{b.play(&old,false);b.ccx(a,ring[0],ring[256]);b.play(&old,true);});
    let new_pair=rec(&mut b,|b|{b.play(&new,false);b.ccx(a,ring[0],ring[256]);b.play(&new,true);});
    for e in 0..128{for s in 0..32{for trial in 0..2{
        let mut start=vec![0;b.width() as usize];randomize(&mut start,(e*811+s*37+trial)as u64);
        set_word(&mut start,&meta.y,e);set_word(&mut start,&meta.sum,s);
        start[flag.0 as usize]=0;start[a.0 as usize]=trial as u8;
        if trial==1{start[q127.0 as usize]=1;}
        let(mut x,mut y)=(start.clone(),start.clone());apply(&old_pair,&mut x);apply(&new_pair,&mut y);
        assert_eq!(x,y,"F1-PAIR E={e} S={s} A={trial}");
    }}}
}

#[test]
fn f1_zpair_box_and_out_of_box_passengers(){
    for (floor,overflow) in [(98,2),(112,16),(128,0)]{
        let hi=(floor+127+overflow).min(256);
        let mut b=builder();let meta=metadata(&mut b);let flag=b.alloc();
        let ring=b.alloc_n(257);let a=b.alloc();let dirty=b.alloc_n(20);
        let old=z_lane_record(&mut b,&meta,&ring,flag,(floor,hi),0,None,&dirty);
        let new=z_lane7_record(&mut b,&meta,&ring,floor,overflow,0,None,&dirty);
        let old_pair=rec(&mut b,|b|{b.play(&old,false);b.ccx(a,ring[0],ring[256]);b.play(&old,true);});
        let new_pair=rec(&mut b,|b|{b.play(&new,false);b.ccx(a,ring[0],ring[256]);b.play(&new,true);});
        for e in 0..128{for s in 0..32{
            let z=225+s-e;let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(e*131+s*883+floor)as u64);
            set_word(&mut start,&meta.y,e);set_word(&mut start,&meta.sum,s);
            start[flag.0 as usize]=0;start[a.0 as usize]=u8::from(floor<=z&&z<=hi);
            let(mut x,mut y)=(start.clone(),start.clone());apply(&old_pair,&mut x);apply(&new_pair,&mut y);
            assert_eq!(x,y,"F1-ZPAIR floor={floor} E={e} S={s} Z={z}");
        }}
    }
}

#[test]
fn f1_vph_tape_exact_lane_rename(){
    use super::super::midg::direct_native_ring_v::{record3,record3_ph};
    fn map(g:G,from:QubitId,to:QubitId)->G{
        let m=|q|if q==from{to}else{q};
        match g{
            G::X(a)=>G::X(m(a)),G::Cx(a,b)=>G::Cx(m(a),m(b)),
            G::Ccx(a,b,c)=>G::Ccx(m(a),m(b),m(c)),G::Cz(a,b)=>G::Cz(m(a),m(b)),
            G::Swap(a,b)=>G::Swap(m(a),m(b)),
            G::AndC(a,b,c)=>G::AndC(m(a),m(b),m(c)),
            G::AndU(a,b,c)=>G::AndU(m(a),m(b),m(c)),
            G::XIf(a,x)=>G::XIf(m(a),x),G::ZIf(a,x)=>G::ZIf(m(a),x),
            G::RowAdd(a,b)=>G::RowAdd(a,b),G::Mark(a)=>G::Mark(a),
            G::DeferredErase(a,b)=>G::DeferredErase(a,b),
        }
    }
    for zrange in [(98,256),(128,255),(98,224),(128,200)]{
        let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
        let q=b.alloc_n(128);let a=b.alloc();let e=b.alloc();let mask=b.alloc();
        let ph=b.alloc();let dirty=b.alloc_n(25);
        let old=record3(&mut b,&meta,&ring,&q,a,e,mask,ph,&[],zrange,&dirty);
        let new=record3_ph(&mut b,&meta,&ring,&q,a,e,ph,&[],zrange,&dirty);
        assert_eq!(old.len(),new.len(),"VPH tape length zrange={zrange:?}");
        for (i,(x,y)) in old.iter().zip(&new).enumerate(){
            assert_eq!(map(*x,mask,ph),*y,"VPH tape gate {i} zrange={zrange:?}");
            assert_eq!(map(*y,mask,ph),*y,"VPH mask name at gate {i}");
        }
    }
}

#[test]
fn f1_vph_pair_inactive_passengers(){
    use super::super::midg::direct_native_ring_v::{record3,record3_ph};
    use super::super::cross_four::Gate;
    use super::super::k5_ph_ports::{Context,Roles,Traversal,top_target,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::{Source,r14_fixture_record};
    std::env::set_var("C658_WP1","1");
    for (zrange,gate) in [((98,256),Gate::Top(0)),((98,256),Gate::Bottom(0)),
        ((112,255),Gate::Top(13)),((112,255),Gate::Bottom(14))]{
        let mut b=builder();b.r14_pass=1;
        let meta=metadata(&mut b);let ring=b.alloc_n(257);let q=b.alloc_n(128);
        let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();let dirty=b.alloc_n(28);
        let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity:a,flight:e,mask:m},
            dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
        let (target,gate_index)=match gate{Gate::Top(j)=>(top_target(&c,j),j),Gate::Bottom(k)=>(natural_target(&c,k),k),_=>unreachable!()};
        let old=record3(&mut b,&meta,&ring,&q,a,e,m,ph,&[],zrange,&dirty);
        let new=record3_ph(&mut b,&meta,&ring,&q,a,e,ph,&[],zrange,&dirty);
        let body=r14_fixture_record(&mut b,&c,&target,gate,true,Source::Parked,0,1);
        let old_pair=rec(&mut b,|b|{b.play(&old,false);b.play(&body,false);b.play(&old,true);});
        let new_pair=rec(&mut b,|b|{b.play(&new,false);b.play(&body,false);b.play(&new,true);});
        for y in [1,2,16,31,32,113,128]{for s in [0,1,16,31]{for trial in 0..2{
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(zrange.0*10007+y*991+s*47+trial*13)as u64);
            set_word(&mut start,&meta.y,y-1);set_word(&mut start,&meta.sum,s);
            start[a.0 as usize]=0;start[e.0 as usize]=0;start[m.0 as usize]=0;
            start[ph.0 as usize]=trial as u8;
            let(mut x,mut z)=(start.clone(),start.clone());apply(&old_pair,&mut x);apply(&new_pair,&mut z);
            assert_eq!(x,start,"F1-VPH old inactive body gate={gate_index} Y={y} S={s} PH={trial}");
            assert_eq!(z,start,"F1-VPH new inactive body gate={gate_index} Y={y} S={s} PH={trial}");
        }}}
    }
    std::env::remove_var("C658_WP1");
}

#[test]
fn f1_vph_merged_bodies_inactive_packed(){
    use super::super::midg::direct_native_ring_v::{record3,record3_ph};
    use super::super::cross_four::Gate;
    use super::super::k5_ph_ports::{Context,Roles,Traversal,top_target,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::{Source,r14_fixture_record};
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::tests_frogdrop::run;
    std::env::set_var("C658_WP1","1");std::env::set_var("C658_FP3","1");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut prefix_bodies=0usize;let mut other_bodies=0usize;
    for col in [37usize,85,113,139,146,202]{
        let cp=&cps[col];let y_bounds=(cp.sy.0.max(1),cp.sy.1.min(128));
        for gate in [Gate::Top(0),Gate::Bottom(14)]{
            let gate_index=match gate{Gate::Top(j)|Gate::Bottom(j)=>j,_=>unreachable!()};
            for (kind,close) in [(0usize,1usize),(0,2),(1,0),(2,3)]{
                let mut b=builder();b.r14_pass=1;
                let meta=metadata(&mut b);let ring=b.alloc_n(257);let q=b.alloc_n(128);
                let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
                let dirty=b.alloc_n(30);
                let c=Context{size:&meta,ring:&ring,q:&q,ph,
                    roles:Roles{activity:a,flight:e,mask:m},dirty:&dirty,y_bounds,qb:30,
                    clean_external:&[],excluded:&[],traversal:Traversal::T1};
                let target=match gate{Gate::Top(j)=>top_target(&c,j),
                    Gate::Bottom(k)=>natural_target(&c,k),_=>unreachable!()};
                let old=record3(&mut b,&meta,&ring,&q,a,e,m,ph,&[],cp.sz,&dirty);
                let new=record3_ph(&mut b,&meta,&ring,&q,a,e,ph,&[],cp.sz,&dirty);
                let body=r14_fixture_record(&mut b,&c,&target,gate,true,
                    Source::Parked,kind,close);
                let old_pair=rec(&mut b,|b|{b.play(&old,false);b.play(&body,false);b.play(&old,true);});
                let new_pair=rec(&mut b,|b|{b.play(&new,false);b.play(&body,false);b.play(&new,true);});
                b.play(&old_pair,false);b.flush_global();let old_ops=std::mem::take(&mut b.ops);
                b.play(&new_pair,false);b.flush_global();let new_ops=std::mem::take(&mut b.ops);
                let width=b.width() as usize;let mut start=vec![0u64;width];
                let mut seed=(col as u64)*0x9e37_79b9+(kind*17+close*3)as u64;
                for word in &mut start{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;*word=seed;}
                for &port in meta.y.iter().chain(&meta.sum){start[port.0 as usize]=0;}
                for shot in 0..64{
                    let y=y_bounds.0+(shot*29+kind*7+close)%(y_bounds.1-y_bounds.0+1);
                    let sum=(shot*11+col+kind)%32;
                    for(i,&port)in meta.y.iter().enumerate(){
                        if (y-1)>>i&1!=0{start[port.0 as usize]|=1u64<<shot;}
                    }
                    for(i,&port)in meta.sum.iter().enumerate(){
                        if sum>>i&1!=0{start[port.0 as usize]|=1u64<<shot;}
                    }
                }
                for port in [a,e,m]{start[port.0 as usize]=0;}
                let old_out=run(&old_ops,width,&|v|*v=start.clone());
                let new_out=run(&new_ops,width,&|v|*v=start.clone());
                assert_eq!(old_out.q,start,"V-PH old inactive col={col} gate_index={gate_index} kind={kind} close={close}");
                assert_eq!(old_out.phase,0,"V-PH old phase col={col} gate_index={gate_index} kind={kind} close={close}");
                assert_eq!(new_out.q,start,"V-PH new inactive col={col} gate_index={gate_index} kind={kind} close={close}");
                assert_eq!(new_out.phase,0,"V-PH new phase col={col} gate_index={gate_index} kind={kind} close={close}");
                if y_bounds.1>=115{prefix_bodies+=1}else{other_bodies+=1;}
            }
        }
    }
    assert!(prefix_bodies>0&&other_bodies>0);
    eprintln!("K5_VPH_MERGED_INACTIVE prefix_bodies={prefix_bodies} other_bodies={other_bodies}");
    std::env::remove_var("C658_WP1");std::env::remove_var("C658_FP3");
}

#[test]
fn f1_lsb_all_tail_widths(){
    for len in 1..=33{
        let mut b=builder();let e=b.alloc();let q=b.alloc();let m=b.alloc();
        let tail=b.alloc_n(len);let dirty=b.alloc_n(len+8);
        let base=rec(&mut b,|b|{
            b.ccx(e,q,m);super::super::frogdrop::inc_mixed(b,m,&tail,&[],&dirty);b.ccx(e,q,m);
        });
        let new=rec(&mut b,|b|{
            let word:Vec<_>=[e,q].into_iter().chain(tail.iter().copied()).collect();
            super::super::modp_frogdrop::inc_dirty_free(b,&word,&dirty);
            b.x(e);b.cx(e,q);
        });
        for trial in 0..64{
            let mut initial=vec![0;b.width() as usize];
            randomize(&mut initial,(len*8191+trial*661+1)as u64);initial[m.0 as usize]=0;
            let(mut a,mut n)=(initial.clone(),initial.clone());apply(&base,&mut a);apply(&new,&mut n);
            assert_eq!(a,n,"tail len={len} trial={trial}");
        }
    }
}

#[test]
fn f1_ff_all_controller_gates_real_width(){
    use super::super::cross_four::Gate;
    use super::super::k5_ph_controller::Controller;
    use super::super::k5_ph_ports::{Context,Roles,Traversal};
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let activity=b.alloc();let flight=b.alloc();let mask=b.alloc();
    let dirty=b.alloc_n(30);
    let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity,flight,mask},
        dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
    let mut controller=Controller::new(&c,true);controller.fixture_normalized();let x=ring[128];
    let gates=(0..15).map(Gate::Top).chain((0..15).map(Gate::Bottom))
        .chain((0..30).map(Gate::Natural));
    for gate in gates{
        let base=rec(&mut b,|b|{let g=controller.gate_record(b,gate);b.play(&g,false);
            b.cswap(mask,x,flight);b.play(&g,true);});
        let folded=rec(&mut b,|b|controller.folded_cswap(b,gate,x,flight));
        for e in [0,1,95,96,97,111,112,113,126,127]{
            for s in [0,1,2,16,17,30,31]{for trial in 0..4{
                let mut initial=vec![0;b.width() as usize];
                randomize(&mut initial,(e*9103+s*719+trial*61+1)as u64);
                set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);
                initial[activity.0 as usize]=(trial&1)as u8;
                initial[q[127].0 as usize]=if trial&1==1{1}else{((trial>>1)&1)as u8};
                initial[mask.0 as usize]=0;
                let(mut a,mut n)=(initial.clone(),initial.clone());apply(&base,&mut a);apply(&folded,&mut n);
                assert_eq!(a,n,"E={e} S={s} trial={trial}");
            }}
        }
    }
}

#[test]
fn f1_wf_all_forms_gates_sources_real_width(){
    use super::super::cross_four::Gate;
    use super::super::k5_ph_ports::{Context,Roles,Traversal,top_target,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::{Source,r14_fixture_record};
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let activity=b.alloc();let flight=b.alloc();let mask=b.alloc();
    let dirty=b.alloc_n(30);
    for source in [Source::Parked,Source::EmptyQ]{
        let hi=if source==Source::Parked{114}else{128};
        let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity,flight,mask},
            dirty:&dirty,y_bounds:(1,hi),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
        for gate in (0..15).map(Gate::Top).chain((0..15).map(Gate::Bottom)){
            let index=match gate{Gate::Top(j)|Gate::Bottom(j)=>j,_=>unreachable!()};
            let t=match gate{Gate::Top(j)=>top_target(&c,j),Gate::Bottom(k)=>natural_target(&c,k),_=>unreachable!()};
            for (kind,close) in [(0,0),(0,1),(0,2),(1,0),(2,0),(2,3)]{
                if source==Source::EmptyQ&&close==2{continue;}
                std::env::remove_var("C658_WP1");
                let old=r14_fixture_record(&mut b,&c,&t,gate,true,source,kind,close);
                std::env::set_var("C658_WP1","1");
                let new=r14_fixture_record(&mut b,&c,&t,gate,true,source,kind,close);
                for trial in 0..3{
                    let e=if trial==0{1}else if trial==1{hi/2}else{hi-1};
                    let s=(index*7+kind*11+close*3+trial*13)%32;
                    let mut initial=vec![0;b.width() as usize];
                    randomize(&mut initial,(index*9953+kind*1871+close*317+trial*109+hi)as u64);
                    set_word(&mut initial,&meta.y,e-1);set_word(&mut initial,&meta.sum,s);
                    initial[activity.0 as usize]=(trial&1)as u8;
                    initial[flight.0 as usize]=0;initial[mask.0 as usize]=0;
                    if trial&1==1{initial[q[127].0 as usize]=1;}
                    let(mut a,mut n)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&new,&mut n);
                    assert_eq!(a,n,"WF source={source:?} gate_index={index} kind={kind} close={close} E={e} S={s}");
                    let inverse:Vec<_>=new.iter().rev().cloned().collect();
                    apply(&inverse,&mut a);
                    assert_eq!(a,initial,"WF inverse source={source:?} gate_index={index} kind={kind} close={close} E={e} S={s}");
                }
                // The inherited witness may already be one, provided it
                // implies activity and this gate. E=0,S=0 satisfies every
                // Top and Bottom selector in this fixture.
                let mut initial=vec![0;b.width() as usize];
                randomize(&mut initial,(index*19937+kind*991+close*101+hi)as u64);
                set_word(&mut initial,&meta.y,0);set_word(&mut initial,&meta.sum,0);
                initial[activity.0 as usize]=1;initial[flight.0 as usize]=1;
                initial[mask.0 as usize]=0;initial[q[127].0 as usize]=1;
                let(mut a,mut n)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&new,&mut n);
                assert_eq!(a,n,"WF preexisting witness source={source:?} gate_index={index} kind={kind} close={close}");
            }
        }
    }
    std::env::remove_var("C658_WP1");
}

#[test]
fn f2_k2g_swap_tree_binding_before_production(){
    use super::super::c659_ht::r14_fixture_k2g;
    for (bits,span,top,lo,hi) in [
        (3,5,7,2,7),(5,25,33,7,31),(7,257,257,0,127),(7,257,256,0,127)
    ]{
        let mut b=builder();let word=b.alloc_n(bits);let t=b.alloc_n(span);
        let s=b.alloc_n(span);let cut=b.alloc();let dirty=b.alloc_n(16);
        let old=r14_fixture_k2g(&mut b,&word,&t,&s,cut,lo,hi,top,&dirty,false);
        let gathered=r14_fixture_k2g(&mut b,&word,&t,&s,cut,lo,hi,top,&dirty,true);
        for v in 0..(1usize<<bits){for ctl in 0..2{for trial in 0..2{
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(bits*65537+span*271+v*31+ctl*7+trial)as u64);
            set_word(&mut start,&word,v);start[cut.0 as usize]=ctl as u8;
            let(mut x,mut y)=(start.clone(),start.clone());
            apply(&old,&mut x);apply(&gathered,&mut y);
            assert_eq!(x,y,"F2-K2G bits={bits} span={span} top={top} lo={lo} hi={hi} v={v} cut={ctl} trial={trial}");
        }}}
    }
}

#[test]
fn f2_k2c_ttk_transition_real_width(){
    use super::super::c659_ht::r14_fixture_k2_transition;
    for (is_y,top,lo,hi,span) in [
        (true,7,2,6,6),(false,33,7,31,27),
        (true,258,1,128,257),(true,257,1,128,257)
    ]{
        let mut b=builder();let meta=metadata(&mut b);let source=b.alloc_n(span);
        let target=b.alloc_n(span);let q=b.alloc_n(128);let ph=b.alloc();
        let a=b.alloc();let e=b.alloc();let m=b.alloc();let dirty=b.alloc_n(20);
        let boundary=(is_y,top,lo,hi);
        let old=r14_fixture_k2_transition(&mut b,&meta,&source,&q,ph,[a,e,m],&dirty,&target,boundary,false);
        let new=r14_fixture_k2_transition(&mut b,&meta,&source,&q,ph,[a,e,m],&dirty,&target,boundary,true);
        let words=if is_y{128}else{32};
        for w in 0..words{for state in 0..3{for trial in 0..2{
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(top*99991+lo*211+w*67+state*13+trial)as u64);
            if is_y{set_word(&mut start,&meta.y,w);}else{set_word(&mut start,&meta.sum,w);}
            let in_range=if is_y{lo<=w+1&&w+1<=hi}else{lo<=w&&w<=hi};
            let active=state>0;let cut=state==2&&in_range;
            start[a.0 as usize]=u8::from(active);start[e.0 as usize]=u8::from(cut);
            start[m.0 as usize]=0;
            let(mut x,mut y)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut y);
            let tag=y[a.0 as usize];let flight=y[e.0 as usize];
            y[a.0 as usize]=tag|flight;y[m.0 as usize]=flight&(tag^1);
            assert_eq!(x,y,"F2-K2C Y={is_y} top={top} lo={lo} hi={hi} w={w} state={state} trial={trial}");
        }}}
    }
}

#[test]
fn f2_k2d_natural_division_real_width(){
    use super::super::c659_ht::r14_fixture_k2_division;
    std::env::set_var("C658_WP2","1");std::env::set_var("C658_WP2_K2D","1");
    for (hi,k) in [(128,0),(128,10),(114,29),(97,5)]{
        let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
        let q=b.alloc_n(128);let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let dirty=b.alloc_n(30);
        let old=r14_fixture_k2_division(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,(1,hi),k,false);
        let new=r14_fixture_k2_division(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,(1,hi),k,true);
        for y in [1,hi/2,hi]{for s in [0,1,2,16,31]{for witness in 0..1{
            // K2D's S-inh forward entry has flight=0, not merely e=>A&G.
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(hi*9973+k*1031+y*47+s*11+witness)as u64);
            set_word(&mut start,&meta.y,y-1);set_word(&mut start,&meta.sum,s);
            start[a.0 as usize]=1;start[e.0 as usize]=witness as u8;
            start[m.0 as usize]=0;start[q[127].0 as usize]=1;
            let(mut x,mut z)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut z);
            assert_eq!(x,z,"F2-K2D hi={hi} k={k} Y={y} S={s} e={witness}");
        }}}
    }
    std::env::remove_var("C658_WP2_K2D");std::env::remove_var("C658_WP2");
}

#[test]
fn f1_fp3_prefix_real_width(){
    use super::super::cross_four::Gate;
    use super::super::k5_ph_ports::{Context,Roles,Traversal,top_target,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::{Source,r14_fixture_record};
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
    let dirty=b.alloc_n(30);
    let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity:a,flight:e,mask:m},
        dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
    for gate in (0..14).map(Gate::Top).chain((0..15).map(Gate::Bottom)){
        let index=match gate{Gate::Top(j)|Gate::Bottom(j)=>j,_=>unreachable!()};
        let target=match gate{Gate::Top(j)=>top_target(&c,j),Gate::Bottom(k)=>natural_target(&c,k),_=>unreachable!()};
        for (kind,close) in [(0,0),(0,1),(0,2),(1,0)]{
            std::env::remove_var("C658_FP3");
            let old=r14_fixture_record(&mut b,&c,&target,gate,true,Source::Parked,kind,close);
            std::env::set_var("C658_FP3","1");
            let new=r14_fixture_record(&mut b,&c,&target,gate,true,Source::Parked,kind,close);
            for y in [1,96,112,113,128]{for s in [0,1,16,31]{for activity in 0..2{
                let mut start=vec![0;b.width() as usize];
                randomize(&mut start,(index*100003+kind*701+close*73+y*31+s*7+activity)as u64);
                set_word(&mut start,&meta.y,y-1);set_word(&mut start,&meta.sum,s);
                start[a.0 as usize]=activity as u8;
                start[e.0 as usize]=u8::from(kind==1&&activity==1&&s&1==1);
                start[m.0 as usize]=0;if activity==1{start[q[127].0 as usize]=1;}
                let(mut x,mut z)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut z);
                if x!=z{let first=x.iter().zip(&z).position(|(u,v)|u!=v).unwrap();
                    panic!("F1-FP3 first={first} top={} gate={index} kind={kind} close={close} Y={y} S={s} A={activity}",matches!(gate,Gate::Top(_)));}
                let inverse:Vec<_>=new.iter().rev().copied().collect();apply(&inverse,&mut z);
                assert_eq!(z,start,"F1-FP3 inverse top={} gate={index} kind={kind} close={close} Y={y} S={s} A={activity}",matches!(gate,Gate::Top(_)));
            }}}
        }
    }
    std::env::remove_var("C658_FP3");
}

#[test]
fn f2_save_top_byte7_real_width(){
    use super::super::c659_ht::r14_fixture_save_top;
    std::env::set_var("C658_WP2","1");std::env::set_var("C658_WP2_SB","1");
    for zrange in [(98,227),(112,255),(128,255)]{
        let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
        let q=b.alloc_n(128);let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let dirty=b.alloc_n(25);
        let old=r14_fixture_save_top(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,zrange,false);
        let new=r14_fixture_save_top(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,zrange,true);
        for eword in 0..128{for s in 0..32{
            let z=225+s-eword;let active=zrange.0<=z&&z<=zrange.1;
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(zrange.0*1009+eword*137+s*17)as u64);
            set_word(&mut start,&meta.y,eword);set_word(&mut start,&meta.sum,s);
            start[a.0 as usize]=u8::from(active);start[m.0 as usize]=0;
            let(mut x,mut y)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut y);
            if x!=y{let first=x.iter().zip(&y).position(|(u,v)|u!=v).unwrap();
                panic!("F2-SAVE first={first} zrange={zrange:?} E={eword} S={s} Z={z} A={active}");}
        }}
    }
    std::env::remove_var("C658_WP2_SB");std::env::remove_var("C658_WP2");
}

#[test]
fn f2_fetch_folded_real_width(){
    use super::super::c659_ht::r14_fixture_fetch;
    std::env::set_var("C658_WP2","1");std::env::set_var("C658_WP2_FETCH","1");
    for (k,lo,hi) in [(0,0,128),(10,1,128),(29,17,128)]{
        let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
        let q=b.alloc_n(128);let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let dirty=b.alloc_n(28);
        for correction in [false,true]{
            let sum_lo=if correction{(31usize-k).saturating_sub(7)}else{0};
            let old=r14_fixture_fetch(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,
                (lo.max(1),hi),k,sum_lo,correction,false);
            let new=r14_fixture_fetch(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,
                (lo.max(1),hi),k,sum_lo,correction,true);
            for s in [0,1,2,15,16,31-k,31]{for y in [1,2,63,96,127,128]{for state in 0..4{
                let mut start=vec![0;b.width() as usize];
                randomize(&mut start,(k*100003+sum_lo*7919+s*101+y*37+state*7+usize::from(correction))as u64);
                set_word(&mut start,&meta.sum,s);set_word(&mut start,&meta.y,y-1);
                start[a.0 as usize]=u8::from(state!=0);
                start[e.0 as usize]=u8::from(state>=2);
                start[m.0 as usize]=u8::from(state==3);
                let mut encoded=start.clone();encoded[a.0 as usize]^=encoded[m.0 as usize];
                encoded[m.0 as usize]=0;
                let(mut x,mut z)=(start.clone(),encoded.clone());apply(&old,&mut x);apply(&new,&mut z);
                let mut decoded=z.clone();let tag=decoded[a.0 as usize];let cut=decoded[e.0 as usize];
                decoded[a.0 as usize]=tag|cut;decoded[m.0 as usize]=cut&(tag^1);
                // State 3 exists inside K2C, but the in-range return
                // cancels its mask before either surrounding fetch.
                if state!=3{assert_eq!(x,decoded,
                    "F2-FETCH k={k} lo={lo} hi={hi} sum={s} Y={y} state={state} correction={correction}");}
                let inverse:Vec<_>=new.iter().rev().copied().collect();apply(&inverse,&mut z);
                assert_eq!(z,encoded,"F2-FETCH inverse k={k} sum={s} Y={y} state={state} correction={correction}");
            }}}
        }
    }
    std::env::remove_var("C658_WP2_FETCH");std::env::remove_var("C658_WP2");
}

#[test]
fn f2_k2_first_step_encoded_fetch_real_width(){
    use super::super::c659_ht::r14_fixture_k2_first_step;
    for key in ["C658_WP2","C658_WP2_K2C","C658_WP2_K2D","C658_WP2_FETCH"]{
        std::env::set_var(key,"1");
    }
    for k in [0,10,29]{
        let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
        let q=b.alloc_n(128);let ph=b.alloc();let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let mut raw=b.alloc_n(258);raw.push(ph);let dirty=b.alloc_n(28);
        let old=r14_fixture_k2_first_step(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,&raw,k,false);
        let new=r14_fixture_k2_first_step(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,&raw,k,true);
        for y in [1,31,63,96,127,128]{for s in [0,1,16,31]{for trial in 0..2{
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(k*10007+y*991+s*47+trial*13)as u64);
            set_word(&mut start,&meta.y,y-1);set_word(&mut start,&meta.sum,s);
            start[a.0 as usize]=1;start[e.0 as usize]=0;start[m.0 as usize]=0;
            start[q[127].0 as usize]=1;
            let(mut x,mut z)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut z);
            let tag=z[a.0 as usize];let cut=z[e.0 as usize];
            z[a.0 as usize]=tag|cut;z[m.0 as usize]=cut&(tag^1);
            if x!=z{let first=x.iter().zip(&z).position(|(u,v)|u!=v).unwrap();
                panic!("F2-K2-STEP first={first} k={k} Y={y} S={s} trial={trial} old_roles=({},{},{}) new_roles=({tag},{cut},{})",
                    x[a.0 as usize],x[e.0 as usize],x[m.0 as usize],z[m.0 as usize]);}
        }}}
    }
    for key in ["C658_WP2_FETCH","C658_WP2_K2D","C658_WP2_K2C","C658_WP2"]{
        std::env::remove_var(key);
    }
}

#[test]
fn f2_complete_post_digit_sampled_real_width(){
    use super::super::c659_ht::r14_fixture_post_digit;
    for key in ["C658_WP2","C658_WP2_K2C","C658_WP2_K2D","C658_WP2_FETCH",
        "C658_WP2_SB","C658_WP2_FLAG"]{std::env::set_var(key,"1");}
    for (y_bounds,zrange,ys) in [
        ((1,128),(98,227),[1,96,128]),
        ((50,114),(112,255),[50,96,114]),
    ]{
        let mut b=builder();b.r14_pass=1;let meta=metadata(&mut b);
        let ring=b.alloc_n(257);let q=b.alloc_n(128);let ph=b.alloc();
        let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let mut raw=b.alloc_n(258);raw.push(ph);let dirty=b.alloc_n(30);
        let old=r14_fixture_post_digit(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,
            &raw,y_bounds,zrange,false);
        let new=r14_fixture_post_digit(&mut b,&meta,&ring,&q,ph,[a,e,m],&dirty,
            &raw,y_bounds,zrange,true);
        for y in ys{for s in [0,16,31]{
            let mut start=vec![0;b.width() as usize];
            randomize(&mut start,(zrange.0*10007+y*991+s*47)as u64);
            set_word(&mut start,&meta.y,y-1);set_word(&mut start,&meta.sum,s);
            let zvalue=226+s-y;let active=zrange.0<=zvalue&&zvalue<=zrange.1;
            if !active{continue;}
            start[a.0 as usize]=u8::from(active);start[e.0 as usize]=0;start[m.0 as usize]=0;
            if active{start[q[127].0 as usize]=1;}
            let(mut x,mut z)=(start.clone(),start.clone());apply(&old,&mut x);apply(&new,&mut z);
            if x!=z{let first=x.iter().zip(&z).position(|(u,v)|u!=v).unwrap();
                panic!("F2-S5 first={first} y_bounds={y_bounds:?} zrange={zrange:?} Y={y} S={s} old_roles=({},{},{}) new_roles=({},{},{})",
                    x[a.0 as usize],x[e.0 as usize],x[m.0 as usize],
                    z[a.0 as usize],z[e.0 as usize],z[m.0 as usize]);}
            let back:Vec<_>=new.iter().rev().copied().collect();apply(&back,&mut z);
            assert_eq!(z,start,"F2-S5 inverse zrange={zrange:?} Y={y} S={s}");
        }}
    }
    for key in ["C658_WP2_FLAG","C658_WP2_SB","C658_WP2_FETCH","C658_WP2_K2D",
        "C658_WP2_K2C","C658_WP2"]{std::env::remove_var(key);}
}

#[test]
#[ignore = "immediate local pair lacks the production reverse-boundary source"]
fn f1_f2_g3_invalid_immediate_pair_screen(){
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,
        k1_complete_caller,k5_ph_ports,pointadd_frogdrop};
    use crate::point_add::tests_frogdrop::run;
    std::env::set_var("C658_T23","1");
    crate::point_add::bake_knobs();k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let wanted=std::env::var("K5_G3_COL").ok().map(|v|vec![v.parse::<usize>().unwrap()])
        .unwrap_or_else(||vec![37usize,85,97,114,126]);
    for payload_first in [true,false]{
        for key in ["C658_WP1","C658_WP2","C658_WP1_VPH","C658_WP2_K2C",
            "C658_WP2_K2D","C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG"]{
            std::env::remove_var(key);
        }
        let mut seed_builder=k1_complete_caller::builder();
        let seed_layout=k1_complete_caller::Layout::allocate(&mut seed_builder);
        let mut state=k1_complete_caller::initial(&seed_layout,payload_first,0).q[..659].to_vec();
        state[seed_layout.fd.ring[256].0 as usize]=u64::MAX;
        drop(seed_builder);drop(seed_layout);
        let mut captures=Vec::new();
        let mut source_ops=0usize;
        for cp in cps.iter().take(*wanted.iter().max().unwrap()+1){
            if wanted.contains(&cp.col){captures.push((cp.col,state.clone()));}
            let mut b=builder();let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
            ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
            let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,ph,
                cnt:q[121..128].to_vec()};
            frogdrop_col::set_counter_epoch(&mut fd,cp.col);
            let pass=if payload_first{k5_ph_ports::Traversal::T1}else{k5_ph_ports::Traversal::T3};
            b.r14_pass=if payload_first{1}else{3};
            b.r14_roles=[terminal[0],terminal[1],pool[2]];
            c659::r14_k5_pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,pass);
            b.r14_pass=0;b.flush_global();source_ops+=b.ops.len();
            state=run(&b.ops,659,&|v|*v=state.clone()).q;
        }
        assert_eq!(captures.len(),wanted.len());
        eprintln!("K5_G3_NATIVE_SOURCE pair={} producer_ops={source_ops}",if payload_first{"T1/T2"}else{"T3/T4"});
        for (col,input) in captures{
            let mut outputs=Vec::new();
            for admitted in [false,true]{
                std::env::set_var("C658_WP1",if admitted{"1"}else{"0"});
                std::env::set_var("C658_WP2",if admitted{"1"}else{"0"});
                if admitted{
                    for key in ["C658_WP1_VPH","C658_WP2_K2C","C658_WP2_K2D",
                        "C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG"]{
                        std::env::set_var(key,"1");
                    }
                }
                let mut b=builder();
                let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
                ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
                let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
                assert_eq!(b.width(),659);
                let mut fd=frogdrop_col::Fd{ring:ring.clone(),q:q.clone(),sy:y,sx:sum,
                    ph,cnt:q[121..128].to_vec()};
                frogdrop_col::set_counter_epoch(&mut fd,col);
                let cp=&cps[col];
                let (first,second)=if payload_first{
                    (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
                }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
                b.r14_pass=if payload_first{1}else{3};
                b.r14_roles=[terminal[0],terminal[1],pool[2]];
                c659::r14_k5_pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,first);
                b.r14_pass=if payload_first{2}else{4};
                c659::r14_k5_pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,second);
                b.r14_pass=0;b.flush_global();
                let got=run(&b.ops,659,&|v|*v=input.clone());
                for i in 0..659{if !(256..514).contains(&i){
                    assert_eq!(got.q[i],input[i],"K5-G3 nonpayload wire={i} col={col} pair={payload_first} admitted={admitted}");
                }}
                eprintln!("K5_G3 col={col} pair={} admitted={admitted} ops={} phase={:016x}",
                    if payload_first{"T1/T2"}else{"T3/T4"},b.ops.len(),got.phase);
                outputs.push((got.q,got.phase));
            }
            assert_eq!(outputs[0],outputs[1],"K5-G3 base/new all-wire and phase col={col} pair={payload_first}");
        }
    }
    for key in ["C658_WP1","C658_WP2","C658_WP1_VPH","C658_WP2_K2C",
        "C658_WP2_K2D","C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG"]{
        std::env::remove_var(key);
    }
}

/// Replay the production forward prefix, endpoint and reverse suffix before
/// comparing a column. T2's P0 host is not valid immediately after a T1
/// prefix: it becomes available at the reverse traversal boundary.
#[test]
fn f1_f2_g3_captured_cross_pairs(){
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,
        k1_complete_caller,k5_ph_ports,pointadd_frogdrop};
    use crate::point_add::tests_frogdrop::run;
    std::env::set_var("C658_T23","1");
    crate::point_add::bake_knobs();k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,b0,last)=pointadd_frogdrop::col_pars(&schedule);
    let wanted=std::env::var("K5_G3_COL").ok().map(|v|vec![v.parse::<usize>().unwrap()])
        .unwrap_or_else(||vec![37usize,85,97,113,114,126]);
    for payload_first in [true,false]{
        let mut seed_builder=k1_complete_caller::builder();
        let seed_layout=k1_complete_caller::Layout::allocate(&mut seed_builder);
        let mut input=k1_complete_caller::initial(&seed_layout,payload_first,0).q[..659].to_vec();
        input[seed_layout.fd.ring[256].0 as usize]=u64::MAX;
        drop(seed_builder);drop(seed_layout);
        let (first,second)=if payload_first{
            (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
        }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
        let step=|idx:Option<usize>,pass:k5_ph_ports::Traversal,
                  state:&mut Vec<u64>,phase:&mut u64|{
            let mut b=builder();let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
            ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
            let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,ph,
                cnt:q[121..128].to_vec()};
            b.r14_pass=match pass{k5_ph_ports::Traversal::T1=>1,
                k5_ph_ports::Traversal::T2=>2,k5_ph_ports::Traversal::T3=>3,
                k5_ph_ports::Traversal::T4=>4};
            b.r14_roles=[terminal[0],terminal[1],pool[2]];
            if let Some(col)=idx{
                frogdrop_col::set_counter_epoch(&mut fd,col);
                c659::r14_k5_pair_column_for_fixture(&mut b,&fd,&cps[col],&pool,&terminal,pass);
            }else{
                c659::r14_k5_pair_endpoint_for_fixture(&mut b,&fd,b0.as_ref(),
                    &last,&pool,&terminal,pass);
            }
            b.r14_pass=0;b.flush_global();
            let got=run(&b.ops,659,&|v|*v=state.clone());
            *state=got.q;*phase^=got.phase;
        };
        let mut outputs=Vec::new();
        for admitted in [false,true]{
            for key in ["C658_WP1","C658_WP2","C658_WP1_VPH","C658_WP2_K2C",
                "C658_WP2_K2D","C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG",
                "C658_WP2_ROT_TAG"]{std::env::remove_var(key);}
            if admitted{
                for key in ["C658_WP1","C658_WP2","C658_WP1_VPH","C658_WP2_K2C",
                    "C658_WP2_K2D","C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG",
                    "C658_WP2_ROT_TAG"]{std::env::set_var(key,"1");}
            }
            let mut state=input.clone();let mut phase=0u64;
            let mut checkpoints=Vec::new();
            for cp in &cps{
                step(Some(cp.col),first,&mut state,&mut phase);
                if wanted.contains(&cp.col){checkpoints.push((cp.col,"forward",state.clone(),phase));}
            }
            step(None,first,&mut state,&mut phase);
            // c659 forward final_consts and inverse initial final_consts cancel
            // consecutively, before the reverse endpoint.
            step(None,second,&mut state,&mut phase);
            for cp in cps.iter().rev(){
                step(Some(cp.col),second,&mut state,&mut phase);
                if wanted.contains(&cp.col){checkpoints.push((cp.col,"reverse",state.clone(),phase));}
            }
            for i in 0..659{if !(256..514).contains(&i){
                assert_eq!(state[i],input[i],
                    "K5-G3 full-pair nonpayload wire={i} pair={payload_first} admitted={admitted}");
            }}
            eprintln!("K5_G3_FULL pair={} admitted={admitted} phase={phase:016x}",
                if payload_first{"T1/T2"}else{"T3/T4"});
            outputs.push((state,phase,checkpoints));
        }
        assert_eq!(&outputs[0].0,&outputs[1].0,"K5-G3 full-pair all-wire pair={payload_first}");
        assert_eq!(outputs[0].1,outputs[1].1,"K5-G3 full-pair phase pair={payload_first}");
        for (base,new) in outputs[0].2.iter().zip(&outputs[1].2){
            assert_eq!((base.0,base.1),(new.0,new.1));
            assert_eq!((&base.2,base.3),(&new.2,new.3),
                "K5-G3 checkpoint pair={payload_first} col={} side={}",base.0,base.1);
        }
    }
    for key in ["C658_WP1","C658_WP2","C658_WP1_VPH","C658_WP2_K2C",
        "C658_WP2_K2D","C658_WP2_FETCH","C658_WP2_SB","C658_WP2_FLAG",
        "C658_WP2_ROT_TAG"]{std::env::remove_var(key);}
}

#[test]
#[ignore = "diagnostic mask-port trace for WP2 scope census"]
fn f2_mask_port_trace_c37(){
    use crate::point_add::{c659_ht,frogdrop_sched,pointadd_frogdrop};
    std::env::set_var("C658_WP2","1");
    for key in ["C658_WP2_K2C","C658_WP2_K2D","C658_WP2_FETCH",
        "C658_WP2_SB","C658_WP2_FLAG","C658_WP2_ROT_TAG"]{
        std::env::set_var(key,"1");
    }
    std::env::set_var("R13_PROFILE_OUT","/tmp/r14-k5-mask-trace-unused.tsv");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    let mut b=builder();let ring=b.alloc_n(257);let mut raw=b.alloc_n(258);
    let q=b.alloc_n(128);let meta=metadata(&mut b);let phase=b.alloc();
    let roles=[b.alloc(),b.alloc(),b.alloc()];let dirty=raw.clone();raw.push(phase);
    let tape=c659_ht::r14_fixture_post_digit(&mut b,&meta,&ring,&q,phase,roles,
        &dirty,&raw,(cp.sy.0.max(1),cp.sy.1.min(128)),cp.sz,true);
    let mask=roles[2];let mut hits=Vec::new();let mut marks=Vec::new();
    for (i,g) in tape.iter().enumerate(){
        if let G::Mark(id)=g{marks.push((i,*id));}
        let ports:Vec<QubitId>=match *g{
            G::X(x)|G::XIf(x,_)|G::ZIf(x,_)=>vec![x],
            G::Cx(x,y)|G::Cz(x,y)|G::Swap(x,y)=>vec![x,y],
            G::Ccx(x,y,z)|G::AndC(x,y,z)|G::AndU(x,y,z)=>vec![x,y,z],
            _=>vec![],
        };
        if ports.contains(&mask){hits.push((i,*g));}
    }
    eprintln!("K5_MASK_TRACE c37 mask={} ops={} hits={} marks={marks:?}",
        mask.0,tape.len(),hits.len());
    for (i,g) in hits.iter().take(18).chain(hits.iter().rev().take(18)){
        eprintln!("K5_MASK_TRACE op[{i}] {g:?}");
    }
}

#[test]
fn f2_wp2_source_scope_zero_all_ht(){
    use crate::point_add::{c659_ht,frogdrop_sched,pointadd_frogdrop};
    std::env::set_var("C658_WP2","1");
    for key in ["C658_WP2_K2C","C658_WP2_K2D","C658_WP2_FETCH",
        "C658_WP2_SB","C658_WP2_FLAG","C658_WP2_ROT_TAG"]{
        std::env::set_var(key,"1");
    }
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let mut checked=0;
    for cp in cps.iter().filter(|cp|{
        let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
        cp.ht&&!fixed
    }){
        let mut b=builder();let ring=b.alloc_n(257);let mut raw=b.alloc_n(258);
        let q=b.alloc_n(128);let meta=metadata(&mut b);let phase=b.alloc();
        let roles=[b.alloc(),b.alloc(),b.alloc()];let dirty=raw.clone();raw.push(phase);
        assert_eq!(b.width(),659);
        let tape=c659_ht::r14_fixture_post_digit(&mut b,&meta,&ring,&q,phase,roles,
            &dirty,&raw,(cp.sy.0.max(1),cp.sy.1.min(128)),cp.sz,true);
        let mask=roles[2];
        for (index,g) in tape.iter().enumerate(){
            let hit=match *g{
                G::X(a)|G::XIf(a,_)|G::ZIf(a,_)=>a==mask,
                G::Cx(a,z)|G::Cz(a,z)|G::Swap(a,z)=>a==mask||z==mask,
                G::Ccx(a,z,t)|G::AndC(a,z,t)|G::AndU(a,z,t)=>
                    a==mask||z==mask||t==mask,
                _=>false,
            };
            assert!(!hit,"WP2 source pool2 touch col={} gate={index} {g:?}",cp.col);
        }
        checked+=1;
    }
    assert_eq!(checked,102);
    eprintln!("K5_WP2_SCOPE_ZERO ht_columns={checked}");
    for key in ["C658_WP2","C658_WP2_K2C","C658_WP2_K2D","C658_WP2_FETCH",
        "C658_WP2_SB","C658_WP2_FLAG","C658_WP2_ROT_TAG"]{
        std::env::remove_var(key);
    }
}

#[test]
fn f2_rotation_pair_out_of_box_real_width(){
    for (floor,hi) in [(98usize,227usize),(112,255),(128,255)]{
        let overflow=hi.saturating_sub(floor+127);
        for cycle_len in [257,259]{for inverse in [false,true]{
            let mut b=builder();let meta=metadata(&mut b);let flag=b.alloc();
            let cycle=b.alloc_n(cycle_len);let a=b.alloc();let dirty=b.alloc_n(24);
            let old=rotate_z_record(&mut b,&meta,&cycle,flag,(floor,hi),None,inverse,&dirty);
            let new=rotate_z7_record(&mut b,&meta,&cycle,floor,overflow,inverse,&dirty);
            let old_pair=rec(&mut b,|b|{
                b.play(&old,false);b.ccx(a,cycle[0],cycle[cycle_len-1]);b.play(&old,true);
            });
            let new_pair=rec(&mut b,|b|{
                b.play(&new,false);b.ccx(a,cycle[0],cycle[cycle_len-1]);b.play(&new,true);
            });
            for e in [0,1,30,63,95,111,126,127]{for s in 0..32{
                let z=225+s-e;let active=floor<=z&&z<=hi;
                let mut start=vec![0;b.width() as usize];
                randomize(&mut start,(floor*1009+hi*137+cycle_len*31+e*19+s*7+usize::from(inverse))as u64);
                set_word(&mut start,&meta.y,e);set_word(&mut start,&meta.sum,s);
                start[flag.0 as usize]=0;start[a.0 as usize]=u8::from(active);
                let(mut x,mut y)=(start.clone(),start.clone());
                apply(&old_pair,&mut x);apply(&new_pair,&mut y);
                assert_eq!(x,y,"F2-ROT floor={floor} hi={hi} len={cycle_len} inv={inverse} E={e} S={s} Z={z} A={active}");
                let back:Vec<_>=new_pair.iter().rev().copied().collect();apply(&back,&mut y);
                assert_eq!(y,start,"F2-ROT inverse floor={floor} len={cycle_len} E={e} S={s}");
            }}
        }}
    }
}

#[test]
fn f2_rotation_tag_host_pair_real_width(){
    use super::super::c659_ht::rotate_tag_record;
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut ranges=vec![(None,(98,227)),(None,(112,255)),(None,(128,255))];
    for col in [85usize,88,97,101,112,114]{ranges.push((Some(col),cps[col].sz));}
    for (column,(floor,hi)) in ranges{
        if let Some(col)=column{eprintln!("F2_TAGROT_COLUMN col={col} zrange=({floor},{hi})");}
        for cycle_len in [257,259]{
            let mut b=builder();let meta=metadata(&mut b);let mask=b.alloc();let tag=b.alloc();
            let cycle=b.alloc_n(cycle_len);let dirty=b.alloc_n(24);
            let old=rotate_z_record(&mut b,&meta,&cycle,mask,(floor,hi),None,true,&dirty);
            let new=rotate_tag_record(&mut b,&meta,&cycle,tag,(floor,hi),true,&dirty);
            let old_pair=rec(&mut b,|b|{b.play(&old,false);
                b.ccx(tag,cycle[0],cycle[cycle_len-1]);b.play(&old,true);});
            let new_pair=rec(&mut b,|b|{b.play(&new,false);
                b.ccx(tag,cycle[0],cycle[cycle_len-1]);b.play(&new,true);});
            for e in [0,1,30,63,95,111,126,127]{for s in 0..32{
                let zvalue=225+s-e;let active=floor<=zvalue&&zvalue<=hi;
                let mut start=vec![0;b.width() as usize];
                randomize(&mut start,(floor*10007+cycle_len*991+e*47+s*13)as u64);
                set_word(&mut start,&meta.y,e);set_word(&mut start,&meta.sum,s);
                start[mask.0 as usize]=0;start[tag.0 as usize]=u8::from(active);
                if active{let(mut x,mut y)=(start.clone(),start.clone());
                    apply(&old,&mut x);apply(&new,&mut y);
                    assert_eq!(x,y,"F2-TAGROT frame floor={floor} hi={hi} E={e} S={s}");}
                let(mut x,mut y)=(start.clone(),start.clone());
                apply(&old_pair,&mut x);apply(&new_pair,&mut y);
                assert_eq!(x,y,"F2-TAGROT pair floor={floor} hi={hi} E={e} S={s} active={active}");
                let back:Vec<_>=new_pair.iter().rev().copied().collect();apply(&back,&mut y);
                assert_eq!(y,start,"F2-TAGROT inverse floor={floor} E={e} S={s}");
            }}
        }
    }
}

#[test]
fn f1_e5_bottom_witness_real_width(){
    use super::super::bottom_comparator::{witness_record3,witness_record3_e5};
    use super::super::k5_ph_ports::{Context,Roles,Traversal};
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let activity=b.alloc();let flight=b.alloc();let mask=b.alloc();
    let dirty=b.alloc_n(30);
    let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity,flight,mask},
        dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
    for k in [0,5,14]{
        let d=c.bank(&[q[127]]);
        let old=witness_record3(&mut b,&c,k,&d);
        let new=witness_record3_e5(&mut b,&c,k,&d);
        for e in 0..128{for s in 0..32{for role in 0..4{
            let mut initial=vec![0;b.width() as usize];
            randomize(&mut initial,(k*9917+e*271+s*47+role*13+1)as u64);
            set_word(&mut initial,&meta.y,e);set_word(&mut initial,&meta.sum,s);
            initial[activity.0 as usize]=(role&1)as u8;
            initial[flight.0 as usize]=((role>>1)&1)as u8;initial[mask.0 as usize]=0;
            if role!=0{initial[q[127].0 as usize]=1;}
            let(mut a,mut n)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&new,&mut n);
            assert_eq!(a,n,"E5 k={k} E={e} S={s} role={role}");
            let inverse:Vec<_>=new.iter().rev().cloned().collect();apply(&inverse,&mut a);
            assert_eq!(a,initial,"E5 inverse k={k} E={e} S={s} role={role}");
        }}}
    }
}

#[test]
fn f1_wf_natural_payload_twins_real_width(){
    use super::super::k5_ph_ports::{Context,Roles,Traversal,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::r14_fixture_twin;
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let activity=b.alloc();let flight=b.alloc();let mask=b.alloc();
    let dirty=b.alloc_n(30);
    let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity,flight,mask},
        dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
    for k in 0..30{
        let t=natural_target(&c,k);
        std::env::remove_var("C658_WP1");let old=r14_fixture_twin(&mut b,&c,&t,k);
        std::env::set_var("C658_WP1","1");let new=r14_fixture_twin(&mut b,&c,&t,k);
        for trial in 0..8{
            let e=[1,2,37,63,85,96,113,128][trial];let s=(k*7+trial*13)%32;
            let mut initial=vec![0;b.width() as usize];
            randomize(&mut initial,(k*7793+trial*163+1)as u64);
            set_word(&mut initial,&meta.y,e-1);set_word(&mut initial,&meta.sum,s);
            initial[activity.0 as usize]=(trial&1)as u8;
            initial[flight.0 as usize]=0;initial[mask.0 as usize]=0;
            if trial&1==1{initial[q[127].0 as usize]=1;}
            let(mut a,mut n)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&new,&mut n);
            assert_eq!(a,n,"WF twin k={k} E={e} S={s}");
            let inverse:Vec<_>=new.iter().rev().cloned().collect();apply(&inverse,&mut a);
            assert_eq!(a,initial,"WF twin inverse k={k} E={e} S={s}");
        }
    }
    std::env::remove_var("C658_WP1");
}

#[test]
fn f1_held_bottom_prep_refutation(){
    use super::super::cross_four::Gate;
    use super::super::k5_ph_ports::{Context,Roles,Traversal,natural_target};
    use super::super::normalized_cross_arithmetic::ph_controller::{Source,r14_fixture_record};
    use super::super::bottom_comparator::held_prep_record3;
    let mut b=builder();let meta=metadata(&mut b);let ring=b.alloc_n(257);
    let q=b.alloc_n(128);let ph=b.alloc();let activity=b.alloc();let flight=b.alloc();let mask=b.alloc();
    let dirty=b.alloc_n(30);
    let c=Context{size:&meta,ring:&ring,q:&q,ph,roles:Roles{activity,flight,mask},
        dirty:&dirty,y_bounds:(1,128),qb:30,clean_external:&[],excluded:&[],traversal:Traversal::T1};
    let t=natural_target(&c,0);let d=c.bank(&[q[127]]);
    let prep=held_prep_record3(&mut b,&c,0,&d);
    std::env::remove_var("C658_WP1");
    let old=r14_fixture_record(&mut b,&c,&t,Gate::Bottom(0),true,Source::EmptyQ,0,0);
    std::env::set_var("C658_WP1","1");std::env::set_var("C658_WP1_WF_SPLIT","1");
    std::env::set_var("C658_WP1_WFBOT","1");std::env::set_var("C658_WP1_WF_HELDBOT","1");
    let held=r14_fixture_record(&mut b,&c,&t,Gate::Bottom(0),true,Source::EmptyQ,0,0);
    let mut first=None;
    for trial in 0..64{
        let mut initial=vec![0;b.width() as usize];randomize(&mut initial,(trial*991+17)as u64);
        set_word(&mut initial,&meta.y,49);set_word(&mut initial,&meta.sum,0);
        initial[activity.0 as usize]=1;initial[flight.0 as usize]=0;
        initial[mask.0 as usize]=0;initial[q[127].0 as usize]=1;
        let mut prepared=initial.clone();apply(&prep,&mut prepared);
        assert_eq!(prepared[q[127].0 as usize],0,"E=50 is the low Bottom class");
        let(mut a,mut h)=(initial.clone(),initial.clone());apply(&old,&mut a);apply(&held,&mut h);
        if a!=h{first=Some((trial,a.iter().zip(&h).position(|(x,y)|x!=y).unwrap()));break;}
    }
    std::env::remove_var("C658_WP1_WF_HELDBOT");std::env::remove_var("C658_WP1_WFBOT");
    std::env::remove_var("C658_WP1_WF_SPLIT");std::env::remove_var("C658_WP1");
    let (trial,lane)=first.expect("held prep unexpectedly matched on low Bottom class");
    println!("HELD_BOTTOM_REFUTED E=50 S=0 k=0 A=1 e=0 m=0 Q127=1 trial={trial} differing_wire={lane}");
}
