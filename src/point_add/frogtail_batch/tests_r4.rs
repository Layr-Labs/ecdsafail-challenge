//! Raw source-generated whole point-add, independent curve specification.
use super::{builder::B,tests_frogdrop::Rng,frogdrop_sched::N};
use crate::circuit::analyze_ops;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput,Update};
fn curve()->crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
    type U=ruint::aliases::U256;let hx=|s:&str|U::from_str_radix(s,16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve{
      modulus:hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
      a:U::ZERO,b:U::from(7u64),
      gx:hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
      gy:hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
      order:hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")}
}
#[test]
#[ignore]
fn r4_raw_whole_256() {
    let mut b=B::new();let(x,y)=super::pointadd_strip::point_add(&mut b);
    assert_eq!(b.live,512,"whole point-add leaked a coordinate/scratch owner");
    let(nq,nb,_,regs)=analyze_ops(b.ops.iter());assert!(nq<=super::pointadd_strip::peak());
    let expected=super::tests_chunked::expected_t(&b.ops);
    eprintln!("R4_WHOLE_EMIT live_return={} actual_peak={} touchedQ={nq} raw_native={} raw_cond={} raw_expected={expected} ops={} source_literal_cap={}",b.live,b.peak,b.tof,b.tof_cond,b.ops.len(),super::pointadd_strip::PEAK0);
    let curve=curve();let mut rng=Rng::new(2024);
    let to_u=|v:N|ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap());
    let mut cases=vec![];
    for _ in 0..256 {
      let a=curve.mul(curve.gx,curve.gy,to_u(rng.below(250)+N::from(1u64)));
      let r=curve.mul(curve.gx,curve.gy,to_u(rng.below(250)+N::from(1u64)));
      let wanted=curve.add(r.0,r.1,a.0,a.1);cases.push((r,a,wanted));
    }
    let mut h=sha3::Shake256::default();h.update(b"r4-native-whole256");let mut xof=h.finalize_xof();
    let mut sim=Simulator::new(nq as usize,nb as usize,&mut xof);
    let coordinate_ids= x.iter().chain(&y).map(|q|q.0).collect::<std::collections::BTreeSet<_>>();
    let mut total_bad=0;let mut phase_bad=0;let mut anc_bad=0;
    for (batch,rows) in cases.chunks(64).enumerate(){
      sim.clear_for_shot();
      for(shot,(r,a,_))in rows.iter().enumerate(){sim.set_register(&regs[0],r.0,shot);sim.set_register(&regs[1],r.1,shot);sim.set_register(&regs[2],a.0,shot);sim.set_register(&regs[3],a.1,shot);}
      sim.apply_iter(b.ops.iter());let mut bad=0;
      for(shot,(_,_,want))in rows.iter().enumerate(){if sim.get_register(&regs[0],shot)!=want.0||sim.get_register(&regs[1],shot)!=want.1{bad+=1;eprintln!("R4_BAD_WORD shot={}",batch*64+shot);}}
      let mut dirty=0;for q in 0..nq{if !coordinate_ids.contains(&q){dirty|=sim.qubits[q as usize];}}
      eprintln!("R4_BATCH batch={batch} cls={bad} pha_mask={:#018x} anc_mask={dirty:#018x}",sim.phase);
      total_bad+=bad;phase_bad+=sim.phase.count_ones();anc_bad+=dirty.count_ones();
    }
    eprintln!("R4_WHOLE_256 cls={total_bad} pha={phase_bad} anc={anc_bad} actual_T_SAMPLE={} raw_expected={expected} NORMAL_ACTUAL_T=NONE",sim.stats.toffoli_gates as f64/256.0);
    assert_eq!((total_bad,phase_bad,anc_bad),(0,0,0),"raw whole native gate must pass before postpass/nonce");
}
