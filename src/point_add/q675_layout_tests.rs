//! Staged, test-only Q675 layout. No candidate arithmetic is admitted.
use super::{builder::{B,G}, frogdrop_col::{Fd,ColPar,ColScr}, midg::S1};
use crate::circuit::QubitId;
use std::{cell::{Cell,RefCell},collections::BTreeSet};
thread_local! {
    static MODE:Cell<u8>=const{Cell::new(0)};
    static ROWS:RefCell<Vec<String>>=const{RefCell::new(Vec::new())};
}
pub(crate) fn layout_candidate(cp:&ColPar)->bool {
    let on=MODE.with(|x|x.get()>=2);
    if on {assert_eq!((cp.n,cp.k,cp.h),(258,0,1));}
    on
}
fn ids(q:&[QubitId])->Vec<u64>{q.iter().map(|q|q.0).collect()}
#[allow(clippy::too_many_arguments)]
pub(crate) fn capture(cp:&ColPar,fd:&Fd,sc:&ColScr,s:&S1,u:&S1,zh:&[QubitId],win:&[QubitId],
    h:usize,rs:usize,cap:usize,fhr:bool,fht:bool,cross:bool,zoff:bool,sgw:bool,prot:&[G])->bool {
    let mode=MODE.with(|m|m.get());if mode==0{return false;}
    assert_eq!(h,cp.n-257);assert_eq!(rs,h-1);assert_eq!(cap,rs+5);
    assert_eq!(s.r.len(),24);assert_eq!(zh.len(),24);assert_eq!(win.len(),27);
    assert_eq!(win[0],fd.ring[h-1]);assert_eq!(s.zero,win[0]);
    assert_eq!(s.r.iter().filter(|q|win.contains(q)).copied().collect::<Vec<_>>(),vec![win[0]]);
    assert_eq!(s.r.iter().filter(|q|zh.contains(q)).copied().collect::<Vec<_>>(),vec![fd.ring[cp.n-1]]);
    assert_eq!(s.r.iter().copied().collect::<BTreeSet<_>>().len(),24);
    assert!(s.r.iter().chain(win).chain(zh).all(|q|!sc.dirty.contains(q)));
    assert!(s.r.iter().all(|q|!s.andc.contains(q)&&!u.andc.contains(q)));
    let slots:Vec<_>=(0..cap).map(|i|if i<rs {fd.ring[i]} else {fd.sx[1+i-rs]}).collect();
    assert_eq!(slots.iter().copied().collect::<BTreeSet<_>>().len(),cap);
    assert!(!slots.contains(&s.zero));assert!(slots.iter().all(|q|!sc.dirty.contains(q)));
    let fixed:Vec<_>=if fhr||fht{(0..23).map(|i|fd.q[cp.sy.1+1+i]).collect()}else{vec![]};
    assert!(fixed.iter().all(|q|!s.r.contains(q)));
    if mode>=2 {assert!(s.r.contains(&fd.q[125]));assert!(!s.andc.contains(&fd.q[125]));assert!(!u.andc.contains(&fd.q[125]));}
    let row=format!("{{\"n\":{},\"col\":{},\"sz\":{:?},\"sy_range\":{:?},\"h\":{},\"slot_capacity\":{},\"r\":{:?},\"win\":{:?},\"zh\":{:?},\"sy\":{:?},\"sx\":{:?},\"sz_ports\":{:?},\"q\":{:?},\"dirty\":{:?},\"park_bank\":{:?},\"unpark_bank\":{:?},\"slots\":{:?},\"fixed_park\":{:?},\"fixed_hr\":{},\"fixed_ht\":{},\"cross\":{},\"zoff\":{},\"sgw\":{},\"rotation_record_gates\":{}}}",cp.n,cp.col,cp.sz,cp.sy,h,cap,ids(&s.r),ids(win),ids(zh),ids(&fd.sy),ids(&fd.sx),ids(&sc.sz),ids(&fd.q),ids(&sc.dirty),ids(&s.andc),ids(&u.andc),ids(&slots),ids(&fixed),fhr,fht,cross,zoff,sgw,prot.len()).replace("(\"","[\"");
    // Tuple Debug uses parentheses; convert only the two numeric tuple fields.
    let row=row.replace(&format!("{:?}",cp.sz),&format!("[{},{}]",cp.sz.0,cp.sz.1)).replace(&format!("{:?}",cp.sy),&format!("[{},{}]",cp.sy.0,cp.sy.1));
    ROWS.with(|r|r.borrow_mut().push(row));mode!=3
}
pub(crate) fn ports(n:usize)->(B,Fd,Vec<QubitId>,Vec<QubitId>){
    let mut b=B::new();let x=b.alloc_n(256);let y=b.alloc_n(256);
    // Same allocation/free sequence as both offset operations, without their gates.
    for _ in 0..2 {let t=b.alloc_n(128);let f=b.alloc_n(3);b.free_n(&f);b.free_n(&t);}
    let mut dirty=y;dirty.extend(b.alloc_n(3));
    let mut ring=x;ring.extend(b.alloc_n(n-256));let q=b.alloc_n(128);let cnt=q[121..].to_vec();
    let fd=Fd{ring,q,sy:b.alloc_n(8),sx:b.alloc_n(8),ph:b.alloc(),cnt};let pool=b.alloc_n(13);
    assert_eq!(b.live,(n+417)as u64);assert_eq!(b.width(),(n+417)as u64);(b,fd,pool,dirty)
}
#[test]
fn q675_actual_middle_port_census(){
    super::bake_knobs();let mut count=0;
    for (mode,n) in [(1,259),(2,258)]{
        MODE.with(|m|m.set(mode));let (mut b,mut fd,pool,dirty)=ports(n);
        let (mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
        assert_eq!(cols.len(),203);
        for cp in &mut cols {cp.n=n;cp.h=n-257;
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
            super::midg::middle(&mut b,&fd,cp,&sc,None,&[],&mut |_|panic!("layout entered arithmetic"));
            assert_eq!(b.op_count(),0);assert!(!cp.nomap);std::mem::swap(&mut fd.sy,&mut fd.sx);count+=1;
        }
        assert_eq!(b.width(),(n+417)as u64);
    }
    MODE.with(|m|m.set(0));assert_eq!(count,406);
    let path=std::env::var("Q675_PORT_ROWS").expect("fresh census output required");
    let mut f=std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
    use std::io::Write;ROWS.with(|r|for row in r.borrow().iter(){writeln!(f,"{row}").unwrap();});
    eprintln!("Q675_LAYOUT_PASS columns=406 actual_allocated_widths=676,675 arithmetic_emitted=0 precision=24 window=27 candidate_is_layout_only=true");
}
#[test]
fn q675_head_equivalence_and_negative_bindings(){
    for k in 0..=17 {let h=k+2;assert_eq!(h-1,k+1);assert_eq!(24-h,22-k);assert_eq!(h+4,k+6);}
    let (_,fd,_,_)=ports(258);let bad_fixed:Vec<_>=(0..23).map(|i|fd.q[102+1+i]).collect();
    assert!(bad_fixed.contains(&fd.q[125]));let good_fixed:Vec<_>=(0..23).map(|i|fd.q[101+1+i]).collect();assert!(!good_fixed.contains(&fd.q[125]));
    assert_eq!(258-257,1);assert_eq!((258-257)-1,0);
    eprintln!("Q675_HEAD_PASS legacy_geometries=18 fixed_park_alias_negative=detected");
}

#[test]
fn q675_small_builder_stream_matches_original_serializer(){
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    let dir=std::path::PathBuf::from(std::env::var("Q675_STREAM_DIR").expect("fresh fixture directory required"));
    std::fs::create_dir(&dir).expect("refuse existing stream fixture directory");
    fn body(b:&mut B,cancel:bool){
        b.global_cancel=cancel;let q=b.alloc_n(12);b.declare_qubits(0,&q[..4]);
        let c=b.declare_bits(2,4);b.x_if(q[0],c[0]);
        b.begin();b.and_c(q[0],q[1],q[2]);b.cx(q[2],q[3]);b.and_u(q[0],q[1],q[2]);let r=b.end();
        b.play(&r,false);b.play(&r,true);b.swap(q[4],q[5]);b.z_if(q[0],c[1]);
        b.x(q[7]);b.x(q[7]);b.flush_global();b.nonce_identity_pair(Some(q[0]),q[1]);b.flush_global();
    }
    for cancel in [false,true]{
        let mut flat=B::new();body(&mut flat,cancel);let a=dir.join(format!("flat-{cancel}.bin"));crate::write_ops(&flat.ops,&a).unwrap();
        let z=dir.join(format!("stream-{cancel}.bin"));assert!(!z.exists());
        std::env::set_var("LOWQ_EXACT_STREAM_PATH",&z);let mut stream=B::new();std::env::remove_var("LOWQ_EXACT_STREAM_PATH");
        body(&mut stream,cancel);assert!(stream.ops.is_empty());assert_eq!(stream.op_count(),flat.ops.len()as u64);
        assert_eq!(stream.finish_stream(),Some(flat.ops.len()as u64));assert_eq!(stream.tof,flat.tof);assert_eq!(stream.width(),flat.width());
        assert_eq!(std::fs::read(&a).unwrap(),std::fs::read(&z).unwrap());
        eprintln!("Q675_STREAM_PASS cancel={cancel} physical_ops={} Q={} T={} packed_bytes_equal=true",flat.ops.len(),flat.width(),flat.tof);
    }
    assert!(std::fs::create_dir(&dir).is_err());
}

#[test]
fn q675_physical_frame_care_and_inverse(){
    let(mut b,fd,pool,dirty)=ports(258);let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
    let r=super::midg::q675_frame_probe(&mut b,&fd.ring,&sc.sz,&fd.sy,&dirty);
    b.play(&r,false);let off=b.ops.len();let t=b.tof;b.play(&r,true);
    assert!(b.ops.iter().all(|o|matches!(o.kind,crate::circuit::OperationType::X|crate::circuit::OperationType::CX|crate::circuit::OperationType::CCX|crate::circuit::OperationType::Swap)));
    let cases:Vec<_>=(1usize..=128).flat_map(|sy|(0usize..=25).filter_map(move|gap|{let sz=257-sy-gap;(sz<=255).then_some((sy,sz,gap))})).collect();
    let mut count=0;let mut bad_care=0;
    for batch in cases.chunks(64){for noise in 0..3 {
        let mut q=vec![0u64;675];for(i,&x)in fd.ring.iter().chain(&dirty).enumerate(){q[x.0 as usize]=match noise{0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*13)as u32)};}
        for(lane,&(sy,sz,_))in batch.iter().enumerate(){for i in 0..8{q[fd.sy[i].0 as usize]|=(((sy>>i)&1)as u64)<<lane;q[sc.sz[i].0 as usize]|=(((sz>>i)&1)as u64)<<lane;}}
        let f=super::tests_frogdrop::run(&b.ops[..off],675,&|x|*x=q.clone());assert_eq!(f.phase,0);
        for(lane,&(_,_,gap))in batch.iter().enumerate(){let code=match gap{23=>54,24=>86,25=>118,_=>gap};let tb=code&31;
            for i in 0..8{assert_eq!((f.q[sc.sz[i].0 as usize]>>lane)&1,((code>>i)&1)as u64);}
            for i in 107..258{assert_eq!((f.q[fd.ring[(i+tb)%258].0 as usize]>>lane)&1,(q[fd.ring[i].0 as usize]>>lane)&1);}
            for &d in dirty.iter().chain(&fd.sy){assert_eq!((f.q[d.0 as usize]^q[d.0 as usize])>>lane&1,0);}
            // Wrong inherited +22 view at N259 differs at a physical endpoint.
            if noise==2&&gap!=0{let a=(257+tb)%258;let stale=(258+tb)%258;if ((f.q[fd.ring[a].0 as usize]^f.q[fd.ring[stale].0 as usize])>>lane)&1!=0{bad_care+=1;}}
        }
        let rt=super::tests_frogdrop::run(&b.ops,675,&|x|*x=q.clone());assert_eq!(rt.q,q);assert_eq!(rt.phase,0);count+=batch.len();
    }}
    assert!(bad_care>0);eprintln!("Q675_FRAME_PASS lanes={count} forward_ops={off} T={t} Q=675 care=107..257 inverse_full_state=true stale_index_detected={bad_care}");
}

#[cfg(test)] pub(crate) fn vform_mode(on:bool){MODE.with(|m|m.set(if on{3}else{0}));}
#[cfg(test)] pub(crate) fn vform_on()->bool{MODE.with(|m|m.get()==3)}
