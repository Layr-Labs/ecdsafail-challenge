use super::*;
use super::super::builder::B;
use super::super::frogdrop_sched::{N,p};
use super::super::tests_frogdrop::Rng;
use super::super::tests_strip::put;
use crate::circuit::{analyze_ops,Op,OperationType as K,BitId,QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Tape{base:usize,at:usize,mode:usize,state:u64}
impl Tape{fn new(base:usize,mode:usize)->Self{Self{base,at:0,mode,state:0x98123456789abcde}}}
impl XofReader for Tape{fn read(&mut self,out:&mut[u8]){assert_eq!(out.len(),8);let value=match self.mode{0=>0,1=>u64::MAX,2=>{let mut v=0;for lane in 0..64{if ((self.base+lane)>>self.at)&1!=0{v|=1u64<<lane;}}v},_=>{self.state^=self.state<<13;self.state^=self.state>>7;self.state^=self.state<<17;self.state}};self.at+=1;out.copy_from_slice(&value.to_le_bytes());}}
fn get(q:&[u64],w:&[QubitId],lane:usize)->N{let mut n=N::ZERO;for(i,x)in w.iter().enumerate(){if(q[x.0 as usize]>>lane)&1!=0{n|=N::from(1u64)<<i;}}n}
fn guarded(ops:&[Op])->Vec<Op>{let mut v=vec![Op{kind:K::PushCondition,c_condition:BitId(42),..Op::empty()}];v.extend_from_slice(ops);v.push(Op{kind:K::PopCondition,..Op::empty()});v}
fn audit_private(ops:&[Op])->(usize,f64){let mut reads=0;let mut depth=0i32;let mut model=0.0;for(i,o)in ops.iter().enumerate(){if o.c_condition==BitId(0){assert!(i>0);assert_eq!(ops[i-1].kind,K::Hmr);assert_eq!(ops[i-1].c_target,BitId(0));assert_eq!(ops[i-1].c_condition,crate::circuit::NO_BIT);assert!(matches!(o.kind,K::CZ|K::Z|K::PushCondition));reads+=1;}if o.c_target==BitId(0){assert_eq!(o.kind,K::Hmr);assert_eq!(o.c_condition,crate::circuit::NO_BIT);}if o.kind==K::PushCondition{depth+=1;}else if o.kind==K::PopCondition{depth-=1;assert!(depth>=0);}else if matches!(o.kind,K::CCX|K::CCZ){model+=2f64.powi(-depth-i32::from(o.c_condition!=crate::circuit::NO_BIT));}}assert_eq!(depth,0);(reads,model)}

#[test]
fn immediate_carry_scope_isolation(){
    for exact in[false,true,false]{fix_pair_test_reset();let mut b=B::new();let z=b.alloc_n(6);let y=b.alloc_n(6);let ms=Ms::with(&mut b,4);if exact{fix_pair_begin_save_internal_exact(0);}else{fix_pair_begin_save(0);}assert!(add_flag_u(&mut b,&ms,&z,&y));fix_pair_end_save();FIX_PAIR_STACK.with(|s|assert_eq!(s.borrow()[0].0.is_empty(),exact));assert!(!FIX_PAIR_INTERNAL_EXACT.with(|v|v.get()));fix_pair_test_reset();}
    eprintln!("IMMEDIATE_SCOPE default_paired_internal_debts_preserved=true lambda_opt_in_only=true");
}

#[test]
fn immediate_carry_small_exhaustive_outcomes(){
    let mut b=B::new();let z=b.alloc_n(6);let y=b.alloc_n(6);let ms=Ms::with(&mut b,4);b.ops.clear();fix_pair_test_reset();fix_pair_begin_save_internal_exact(0);
    assert!(add_flag_u(&mut b,&ms,&z,&y));fix_pair_end_save();FIX_PAIR_STACK.with(|s|assert!(s.borrow().iter().all(|d|d.0.is_empty()&&d.1.is_none())));fix_pair_test_reset();
    let ops=guarded(&b.ops);let(nq,nb,_,_)=analyze_ops(ops.iter());let draws=ops.iter().filter(|o|matches!(o.kind,K::Hmr|K::R)).count();assert!(draws<=16);let tapes=1usize<<draws;let mut cases=0u64;
    for a in 0..64usize{for yv in 0..64usize{for mask in[0,u64::MAX,0x9696_9696_9696_9696]{for base in(0..tapes).step_by(64){let mut tape=Tape::new(base,2);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);s.bits[42]=mask;s.bits[0]=0x8ca3_9876_12ab_cdfe;s.qubits[ms.one.0 as usize]=u64::MAX;
        for lane in 0..64{put(&mut s.qubits,&z,lane,N::from(a));put(&mut s.qubits,&y,lane,N::from(yv));}
        s.apply_iter(ops.iter());assert_eq!(s.phase,0);assert_eq!(s.bits[42],mask);for q in&ms.r{assert_eq!(s.qubits[q.0 as usize],0);}
        for lane in 0..64{let active=(mask>>lane)&1!=0;let sum=if active{a+yv}else{a};assert_eq!(get(&s.qubits,&z,lane),N::from(sum&63));assert_eq!(get(&s.qubits,&y,lane),N::from(yv));assert_eq!((s.qubits[ms.k.0 as usize]>>lane)&1,if active{((a+yv)>>6)as u64}else{0});cases+=1;}
    }}}}
    eprintln!("IMMEDIATE_SMALL cases={cases} draws={draws} all_outcomes={tapes} Q={nq}");
}

#[test]
fn immediate_carry_production_add_all_channels(){
    let mut rng=Rng::new(0xc0a870);let mut cases=0;let m=N::from(1u64)<<256;let mask=m-N::from(1u64);
    for room in[54,55]{let mut b=B::new();let z=b.alloc_n(256);let y=b.alloc_n(256);let ms=Ms::with(&mut b,room);b.ops.clear();fix_pair_test_reset();fix_pair_begin_save_internal_exact(0);assert!(add_flag_u(&mut b,&ms,&z,&y));fix_pair_end_save();FIX_PAIR_STACK.with(|s|assert!(s.borrow().iter().all(|d|d.0.is_empty())));fix_pair_test_reset();let ops=guarded(&b.ops);let(nq,nb,_,_)=analyze_ops(ops.iter());
      for mode in[0,1,3]{for batch in 0..16{let mut tape=Tape::new(0,mode);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);let active=if batch%3==2{0}else if batch%3==0{u64::MAX}else{0x5a3c_5a3c_5a3c_5a3c};s.bits[42]=active;s.bits[0]=0xfedcba9876543210;s.qubits[ms.one.0 as usize]=u64::MAX;let mut values=vec![];
        for lane in 0..64{let(a,c)=if batch==0{let j=[1,52,53,54,55,105,156,206][lane%8];let a=(m-(N::from(1u64)<<j)-N::from((lane%3+1)as u64))&mask;let c=(N::from(1u64)<<j)+N::from((lane%7+2)as u64);(a,c)}else{(rng.below(256),rng.below(256))};put(&mut s.qubits,&z,lane,a);put(&mut s.qubits,&y,lane,c);values.push((a,c));}
        s.apply_iter(ops.iter());assert_eq!(s.phase,0);for q in&ms.r{assert_eq!(s.qubits[q.0 as usize],0);}assert_eq!(s.bits[42],active);
        for(lane,(a,c))in values.iter().enumerate(){let act=(active>>lane)&1!=0;let sum=if act{*a+*c}else{*a};assert_eq!(get(&s.qubits,&z,lane),sum&mask);assert_eq!(get(&s.qubits,&y,lane),*c);assert_eq!((s.qubits[ms.k.0 as usize]>>lane)&1,if act{u64::from(sum>=m)}else{0});cases+=1;}
      }}
      eprintln!("IMMEDIATE_ADD room={room} Q={nq} staticT={} ops={}",ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count(),ops.len());
    }eprintln!("IMMEDIATE_ADD cases={cases}");
}

fn pair(room:usize,old:bool)->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Ms,QubitId,usize){
    fix_pair_test_reset();FIX_INTERNAL_TEST_OLD_DEFER.with(|v|v.set(old));let mut b=B::new();let z=b.alloc_n(256);let y=b.alloc_n(256);let sign=b.alloc();let ms=Ms::with(&mut b,room);b.ops.clear();let mut zz=z.clone();
    fix_pair_begin_save_internal_exact(0);signed_modadd_halve(&mut b,&ms,&mut zz,&y,Some(sign));fix_pair_end_save();
    FIX_PAIR_STACK.with(|s|{assert_eq!(s.borrow().len(),1);assert_eq!(s.borrow()[0].0.is_empty(),!old);assert!(s.borrow()[0].1.is_some());});let mid=b.ops.len();let mid_z=zz.clone();
    fix_pair_begin_repay();mod_double(&mut b,&ms,&mut zz);b.x(sign);signed_modadd(&mut b,&ms,&zz,&y,Some(sign));b.x(sign);fix_pair_end_repay();fix_pair_test_reset();
    assert_eq!(z,zz);(b,z,y,mid_z,ms,sign,mid)
}

#[test]
fn immediate_carry_signed_halve_pair_and_old_negative(){
    let m=N::from(1u64)<<256;let pm=p();let inv2=(pm+N::from(1u64))>>1;let mut rng=Rng::new(0xd0a870);let mut checked=0;let mut old_phase=0u64;
    for room in[54,55]{for old in[false,true]{let(b,z,y,mid_z,ms,sign,mid)=pair(room,old);let(nq,nb,_,_)=analyze_ops(b.ops.iter());for mode in[0,1,3]{for batch in 0..8{let mut tape=Tape::new(0,mode);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);s.qubits[ms.one.0 as usize]=u64::MAX;let mut vals=vec![];
      for lane in 0..64{let (a,yv,sg)=if batch==0{let cut=if room==54{53}else{54};let a=m-(N::from(1u64)<<cut)-N::from(1u64);let yv=(N::from(1u64)<<cut)+N::from(2u64);(a,yv,false)}else{(rng.below(256)%pm,rng.below(256)%pm,lane%2==1)};put(&mut s.qubits,&z,lane,a);put(&mut s.qubits,&y,lane,yv);if sg{s.qubits[sign.0 as usize]|=1u64<<lane;}vals.push((a,yv,sg));}
      s.apply_iter(b.ops[..mid].iter());for(lane,(a,yv,sg))in vals.iter().enumerate(){let sum=if *sg{(*a+pm-*yv)%pm}else{(*a+*yv)%pm};assert_eq!(get(&s.qubits,&mid_z,lane)%pm,sum.mul_mod(inv2,pm));}for q in&ms.r{assert_eq!(s.qubits[q.0 as usize],0);}assert_eq!(s.qubits[ms.k.0 as usize],0);
      s.apply_iter(b.ops[mid..].iter());for(lane,(a,yv,sg))in vals.iter().enumerate(){assert_eq!(get(&s.qubits,&z,lane),*a);assert_eq!(get(&s.qubits,&y,lane),*yv);assert_eq!((s.qubits[sign.0 as usize]>>lane)&1,u64::from(*sg));checked+=1;}for q in ms.r.iter().chain([&ms.k]){assert_eq!(s.qubits[q.0 as usize],0);}
      if !old{assert_eq!(s.phase,0);}else if batch==0&&mode==1{assert_eq!(s.phase,u64::MAX);old_phase+=64;}
    }}}
    }assert!(old_phase>=128);eprintln!("IMMEDIATE_HALVE_PAIR checked={checked} old_negative_phase_lanes={old_phase}");
}

// Directly exercise CarryU's captured measurement frame while inner ANDU
// writes reuse private bit 0. The spectator and outer guard are arbitrary.
#[test]
fn immediate_carry_predicate_all_outcomes_and_negative(){
    let mut b=B::new();let a=b.alloc_n(3);let t=b.alloc_n(3);let ctl=b.alloc();let cin=b.alloc();let flag=b.alloc();let pool=b.alloc_n(3);let spectator=b.alloc();
    b.carry_erase_cin(&a,&t,ctl,flag,&pool,Some(cin));
    let good=guarded(&b.ops);let mut bad=good.clone();let cz=bad.iter().position(|o|o.kind==K::CZ&&o.q_control1==ctl).expect("predicate CZ");bad[cz]=Op{kind:K::DebugPrint,..Op::empty()};
    let (nq,nb,_,_)=analyze_ops(good.iter());let draws=good.iter().filter(|o|matches!(o.kind,K::Hmr|K::R)).count();assert_eq!(draws,4);let mut cases=0;let mut negative=0;
    for av in 0..8usize{for tv in 0..8usize{for cv in 0..2usize{for control in 0..2usize{for mask in[0,u64::MAX,0x963c_963c_963c_963c]{for broken in[false,true]{let mut tape=Tape::new(0,2);let mut s=Simulator::new((nq as usize).max(b.width() as usize),nb as usize,&mut tape);s.bits[42]=mask;s.bits[0]=0xa5a5_a5a5_a5a5_a5a5;s.qubits[spectator.0 as usize]=0x1a2b3c4d5e6f7890;
        for lane in 0..64{put(&mut s.qubits,&a,lane,N::from(av));put(&mut s.qubits,&t,lane,N::from(tv));if cv!=0{s.qubits[cin.0 as usize]|=1<<lane;}if control!=0{s.qubits[ctl.0 as usize]|=1<<lane;}if control!=0&&av+tv+cv>=8{s.qubits[flag.0 as usize]|=1<<lane;}}
        let prior=s.qubits.clone();s.apply_iter(if broken{bad.iter()}else{good.iter()});for q in a.iter().chain(&t).chain([&ctl,&cin,&spectator]){assert_eq!(s.qubits[q.0 as usize],prior[q.0 as usize]);}for q in &pool{assert_eq!(s.qubits[q.0 as usize],0);}assert_eq!(s.qubits[flag.0 as usize],prior[flag.0 as usize]&!mask);assert_eq!(s.bits[42],mask);
        if broken{negative+=s.phase.count_ones()as u64;}else{assert_eq!(s.phase,0);cases+=64;}
    }}}}}}assert!(negative>0);eprintln!("IMMEDIATE_PREDICATE cases={cases} unique_outcomes=16 repeated_lanes=4 missing_CZ_phase_lanes={negative}");
}

#[test]
fn immediate_carry_captured_guards_actual_boundary(){
    let av=N::from_str_radix("a3e6e833332348bba76fe6c8bb855ee1c0f49644f731acb80d3fffff4c2db854",16).unwrap();
    let yv=N::from_str_radix("a9ec14ab982fd2d3e1dff8ffec25e0e1b591ab1e8896d57fcc3ae7b485b4f54a",16).unwrap();
    let mut cases=0;
    for room in[54,55]{let(b,z,y,_,ms,sign,_)=pair(room,false);let mut ops=vec![Op{kind:K::PushCondition,c_condition:BitId(42),..Op::empty()},Op{kind:K::BitInvert,c_target:BitId(42),..Op::empty()},Op{kind:K::PushCondition,c_condition:BitId(43),..Op::empty()}];ops.extend_from_slice(&b.ops);ops.extend([Op{kind:K::PopCondition,..Op::empty()},Op{kind:K::PopCondition,..Op::empty()}]);let(nq,nb,_,_)=analyze_ops(ops.iter());
      for mode in[0,1,3]{for outer in[0,u64::MAX,0xa3c5_a3c5_a3c5_a3c5]{for inner in[0,u64::MAX,0x9d2f_9d2f_9d2f_9d2f]{let mut tape=Tape::new(0,mode);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);s.bits.fill(0x5a6b7c8d9e102345);s.bits[42]=outer;s.bits[43]=inner;s.qubits[ms.one.0 as usize]=u64::MAX;for lane in 0..64{put(&mut s.qubits,&z,lane,av);put(&mut s.qubits,&y,lane,yv);if lane%2==1{s.qubits[sign.0 as usize]|=1<<lane;}}let prior=s.qubits.clone();s.apply_iter(ops.iter());assert_eq!(s.qubits,prior);assert_eq!(s.phase,0);assert_eq!(s.bits[42],0);assert_eq!(s.bits[43],inner);cases+=64;}}}
    }eprintln!("IMMEDIATE_CAPTURED cases={cases} outer_guard_mutated_after_capture=true stale_private_bits=true both_signs=true");
}

#[test]
fn immediate_carry_full_tail_local_model(){
    let pm=p();let inv2_256=N::from(2u64).pow_mod(pm-N::from(2u64),pm).pow_mod(N::from(256u64),pm);let mut metrics=vec![];let mut cases=0;
    for old in[true,false]{fix_pair_test_reset();FIX_INTERNAL_TEST_OLD_DEFER.with(|v|v.set(old));let mut b=B::new();let c=b.alloc_n(256);let y=b.alloc_n(256);let z=b.alloc_n(256);let ms=Ms::with(&mut b,54);let mut zz=z.clone();fix_pair_begin_save_internal_exact(0);product_tail_neg_s_offset(&mut b,&ms,&mut zz,&c,&y,256);fix_pair_end_save();
      FIX_PAIR_STACK.with(|s|{let st=s.borrow();assert_eq!(st.len(),256);assert_eq!(st.iter().map(|d|d.0.len()).sum::<usize>(),if old{1024}else{0});assert!(st.iter().all(|d|d.1.is_some()));});let mid=b.ops.len();let midz=zz.clone();fix_pair_begin_repay();product_tail_neg_s_offset_uncompute(&mut b,&ms,&mut zz,&c,&y,256);fix_pair_end_repay();assert_eq!(zz,z);fix_pair_test_reset();let(nq,nb,_,_)=analyze_ops(b.ops.iter());let static_t=b.ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();let (private_reads,model)=audit_private(&b.ops);eprintln!("IMMEDIATE_PRIVATE old={old} reads={private_reads} modelT={model} balanced=true");metrics.push((nq,static_t,b.ops.len(),nb));eprintln!("IMMEDIATE_FULL_TAIL old={old} Q={nq} staticT={static_t} ops={} bits={nb}",b.ops.len());
      let mut rng=Rng::new(0xe0a870);for mode in[0,1,3]{for _batch in 0..4{let mut tape=Tape::new(0,mode);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);let mut vals=vec![];for lane in 0..64{let cv=rng.below(256)%pm;let yv=rng.below(256)%pm;put(&mut s.qubits,&c,lane,cv);put(&mut s.qubits,&y,lane,yv);vals.push((cv,yv));}s.apply_iter(b.ops[..mid].iter());for(lane,(cv,yv))in vals.iter().enumerate(){let want=(pm-cv.mul_mod(*yv,pm).mul_mod(inv2_256,pm))%pm;assert_eq!(get(&s.qubits,&midz,lane)%pm,want);}s.apply_iter(b.ops[mid..].iter());for(lane,(cv,yv))in vals.iter().enumerate(){assert_eq!(get(&s.qubits,&c,lane),*cv);assert_eq!(get(&s.qubits,&y,lane),*yv);cases+=1;}for q in z.iter().chain(&ms.r).chain([&ms.k]){assert_eq!(s.qubits[q.0 as usize],0);}if !old{assert_eq!(s.phase,0);}
      }}
    }assert_eq!(metrics[0].0,metrics[1].0);assert_eq!(metrics[1].1-metrics[0].1,52736);assert_eq!(metrics[0].3-metrics[1].3,1024);eprintln!("IMMEDIATE_FULL_TAIL cases={cases} extra_staticT=52736 fair_HMR_model_extraT=26368 extraQ=0 removed_internal_receipt_bits=1024");
}

// A deliberately unsupported surrounding-helper case. The exact internal
// repair is not a repair of the unchanged CMPT32 overflow approximation.
#[test]
fn immediate_carry_separate_cmpt32_boundary_negative(){
    let mut count=0;
    for room in[54,55]{let(b,z,y,_,ms,sign,_)=pair(room,false);let cut=if room==54{53}else{54};let a=N::from(1u64)<<cut;let yv=a+N::from(2u64);let(nq,nb,_,_)=analyze_ops(b.ops.iter());
      let last=b.ops.iter().rposition(|o|o.kind==K::Hmr&&o.q_target==ms.k).unwrap();audit_private(&b.ops[..last]);audit_private(&b.ops[last..]);
      for mode in[0,1]{let mut tape=Tape::new(0,mode);let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);s.qubits[ms.one.0 as usize]=u64::MAX;s.qubits[sign.0 as usize]=u64::MAX;for lane in 0..64{put(&mut s.qubits,&z,lane,a);put(&mut s.qubits,&y,lane,yv);}s.apply_iter(b.ops[..last].iter());
        // Reverse add has already returned the exact input. Its genuine
        // overflow is still1; complementing the top32 produces allones,
        // while y_top32=0 and inverse sign=0 give comparator carry0.
        assert_eq!(s.phase,0);assert_eq!(s.qubits[ms.k.0 as usize],u64::MAX);assert_eq!(s.qubits[sign.0 as usize],0);
        for lane in 0..64{assert_eq!(get(&s.qubits,&y,lane)>>224,N::ZERO);assert_eq!(get(&s.qubits,&z[224..],lane),(N::from(1u64)<<32)-N::from(1u64));}
        s.apply_iter(b.ops[last..].iter());assert_eq!(s.phase,if mode==1{u64::MAX}else{0});for lane in 0..64{assert_eq!(get(&s.qubits,&z,lane),a);assert_eq!(get(&s.qubits,&y,lane),yv);}assert_eq!(s.qubits[sign.0 as usize],u64::MAX);for q in ms.r.iter().chain([&ms.k]){assert_eq!(s.qubits[q.0 as usize],0);}count+=64;
      }eprintln!("IMMEDIATE_CMPT32 room={room} last_overflow_HMR={last} cut={cut} actual_overflow=1 comparator=0 phase_before=0 phase_after=measurement");
    }eprintln!("IMMEDIATE_CMPT32 unsupported_cases={count} preserved_failure=true");
}
