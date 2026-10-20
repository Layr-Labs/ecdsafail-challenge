//! Independent forward and inverse word specs for mixed finish multiplication.
use super::builder::B;
use crate::circuit::{analyze_ops,OperationType as K};
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed(u8);
impl XofReader for Fixed {fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}

#[test]
fn qmin_full_finish_mask_lent() {
    let mut total=0u64;let mut seed=0xcafe12345678u64;
    let mut next=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed};
    for room in [1usize,2,3,4,5,6,9] {for inverse in [false,true] {
      let mut b=B::new();let q=b.alloc_n(21);let source=b.alloc_n(21);let g=b.alloc_n(5);let e=b.alloc();
      let tmp=b.alloc_n(8);let pool=b.alloc_n(room);let a0=b.alloc();let spectators=b.alloc_n(2);
      b.begin();super::frogstrip::finish_mask_lent(&mut b,&q,&source,&g,e,&tmp,&pool,a0);let rec=b.end();b.play(&rec,inverse);
      let(_,nb,_,_)=analyze_ops(b.ops.iter());
      for byte in [0u8,255,170] {for enabled in [false,true] {for gap in 0..if enabled{20}else{32} {
        for batch in 0..8 {
          let mut fixed=Fixed(byte);let mut sim=Simulator::new(b.width()as usize,nb as usize,&mut fixed);
          for i in 0..21 {sim.qubits[q[i].0 as usize]=next();sim.qubits[source[i].0 as usize]=match batch{0=>0,1=>!0,2..=5=>if i%4==batch-2{!0}else{0},_=>next()};}
          if enabled {sim.qubits[e.0 as usize]=!0;}
          for i in 0..5 {if(gap>>i)&1==1 {sim.qubits[g[i].0 as usize]=!0;}}
          for &x in &spectators {sim.qubits[x.0 as usize]=next();}
          let initial=sim.qubits.clone();sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0,"mask room={room} inverse={inverse} gap={gap} e={enabled} HMR={byte}");
          for i in 0..21 {let mut want=initial[q[i].0 as usize];
            if enabled {
              if i==19 {want^=!0;}if i==20 {want^=initial[source[1].0 as usize];}
              if i+2<21 && i<gap {want^=initial[source[i+2].0 as usize];}
            }
            assert_eq!(sim.qubits[q[i].0 as usize],want,"mask word i={i}");
          }
          for i in 0..b.width() {if !q.iter().any(|x|x.0==i){assert_eq!(sim.qubits[i as usize],initial[i as usize],"mask borrowed/source/flag/spectator i={i}");}}
          total+=64;
        }
      }}}
    }}
    eprintln!("QMIN_FULL_MASK_NATIVE_PASS forward/inverse word/phase/restoration/spectator cases={total}");
}

#[test]
fn qmin_finish_forward_word_spec() {
    let mut total=0u64;
    for width in [3usize,4,5,6,7,8] {
      let modulus=1u64<<width;let mask=modulus-1;
      for room in [0usize,3,10,14,18,22] {
        for inverse in [false,true] {
          let mut b=B::new();let a=b.alloc_n(width-1);let q=b.alloc_n(width);let e=b.alloc();
          let ctl=b.alloc();let pool=b.alloc_n(room);let spectators=b.alloc_n(2);
          let mut full_pool=pool.clone();full_pool.push(ctl);
          b.begin();super::frogstrip::radix4_finish_mul(&mut b,&a,&q,e,ctl,&full_pool);let rec=b.end();
          b.play(&rec,inverse);let(_,nb,_,_)=analyze_ops(b.ops.iter());let nq=b.width();
          let cases=1usize<<(2*width+2);
          for byte in [0u8,255,170] {for base in (0..cases).step_by(64) {
            let mut fixed=Fixed(byte);let mut sim=Simulator::new(nq as usize,nb as usize,&mut fixed);
            for shot in 0..64 {let row=(base+shot)as u64;
              for i in 0..width-1 {sim.qubits[a[i].0 as usize]|=((row>>i)&1)<<shot;}
              for i in 0..width {sim.qubits[q[i].0 as usize]|=((row>>(width-1+i))&1)<<shot;}
              sim.qubits[e.0 as usize]|=((row>>(2*width-1))&1)<<shot;
              for i in 0..2 {sim.qubits[spectators[i].0 as usize]|=((row>>(2*width+i))&1)<<shot;}
            }
            let initial=sim.qubits.clone();sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0,"width={width} room={room} inv={inverse} byte={byte} base={base}");
            for shot in 0..64 {let row=(base+shot)as u64;let aa=row&((1<<(width-1))-1);let qq=(row>>(width-1))&mask;let enabled=(row>>(2*width-1))&1;
              let multiplier=1+2*aa;
              // Newton iteration computes the independent odd modular inverse.
              let mut inv=1u64;for _ in 0..width {inv=inv.wrapping_mul(2u64.wrapping_sub(multiplier.wrapping_mul(inv)))&mask;}
              let factor=if inverse{inv}else{multiplier};let want=if enabled==1{qq*factor&mask}else{qq};
              let actual=q.iter().enumerate().fold(0u64,|s,(i,x)|s|(((sim.qubits[x.0 as usize]>>shot)&1)<<i));
              assert_eq!(actual,want,"width={width} room={room} inv={inverse} row={row}");
            }
            for i in 0..nq {if !q.iter().any(|x|x.0==i){assert_eq!(sim.qubits[i as usize],initial[i as usize],"borrow/source/spectator q{i}");}}
            total+=64;
          }}
        }
      }
    }
    eprintln!("QMIN_FINISH_NATIVE_PASS independent word/phase/scratch/spectator cases={total}");
}

#[test]
#[ignore]
fn qmin_resource_sweep() {
    let caps=std::env::var("QMIN_CAPS").unwrap_or_else(|_|"948,947,946,945,944,943,942,941,940,939,938,937,936".into());
    for cap in caps.split(',').map(|x|x.parse::<u64>().unwrap()) {
      std::env::set_var("STRIP_PEAK",cap.to_string());
      let mut b=B::new();let(x,y)=super::pointadd_strip::point_add(&mut b);
      let(nq,nb,_,_)=analyze_ops(b.ops.iter());
      let raw=super::tests_chunked::expected_t(&b.ops);
      let emitted=b.ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
      let raw_ops=b.ops.len();let mut ops=std::mem::take(&mut b.ops);
      for _ in 0..32 {
        let previous=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
        ops=super::super::truth_simplify::simplify_products(ops);
        let current=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
        if previous==current {break;}
      }
      let post=super::tests_chunked::expected_t(&ops);
      let post_emitted=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
      let(post_nq,_,_,_)=analyze_ops(ops.iter());
      eprintln!("QMIN_RESOURCE cap={cap} actual_live_peak={} touched_Q={nq} postpass_touched_Q={post_nq} bits={nb} raw_emitted_T={emitted} raw_cond_T={} raw_expected_T={raw:.3} fixed_postpass_expected_ESTIMATE={post:.3} fixed_postpass_emitted_T={post_emitted} normal_actual_T=NONE data={},{} raw_ops={raw_ops} post_ops={}",b.peak,b.tof_cond,x.len(),y.len(),ops.len());
    }
}

/// Cheap first gate: emits the actual whole source but skips all postpasses.
#[test]
#[ignore]
fn qmin_raw_resource_sweep() {
    let caps=std::env::var("QMIN_CAPS").unwrap_or_else(|_|"948,947,946,945,944,943,942,941,940".into());
    for cap in caps.split(',').map(|x|x.parse::<u64>().unwrap()) {
      std::env::set_var("STRIP_PEAK",cap.to_string());
      let mut b=B::new();super::pointadd_strip::point_add(&mut b);
      let(nq,nb,_,_)=analyze_ops(b.ops.iter());
      let raw=super::tests_chunked::expected_t(&b.ops);
      let emitted=b.ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
      eprintln!("QMIN_RAW cap={cap} actual_live_peak={} touched_Q={nq} bits={nb} raw_emitted_T={emitted} raw_cond_T={} raw_expected_T={raw:.3} fixed_postpass_estimate=UNMEASURED normal_actual_T=NONE ops={}",b.peak,b.tof_cond,b.ops.len());
    }
}

#[test]
#[ignore]
fn qmin_best_cap_postpass() {
    let cap=std::env::var("QMIN_CAP").expect("QMIN_CAP required").parse::<u64>().unwrap();
    std::env::set_var("STRIP_PEAK",cap.to_string());
    let mut b=B::new();super::pointadd_strip::point_add(&mut b);
    let(nq,nb,_,_)=analyze_ops(b.ops.iter());let raw=super::tests_chunked::expected_t(&b.ops);
    let mut ops=std::mem::take(&mut b.ops);
    for pass in 1..=15 {
      let previous=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
      ops=super::super::truth_simplify::simplify_products(ops);
      let current=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
      let expected=super::tests_chunked::expected_t(&ops);
      eprintln!("QMIN_ONE_POSTPASS cap={cap} pass={pass} native={current} expected_ESTIMATE={expected:.3} raw_expected_T={raw:.3} actual_live_peak={} touched_Q={nq} bits={nb} normal_actual_T=NONE",b.peak);
      if previous==current {break;}
    }
}

/// Threshold boundary checks on the entire field primitive, preserving the
/// inherited WM66/CMPT32 maps. Random field rows are local evidence, not an
/// all-input/no-failure theorem for the inherited approximate comparisons.
#[test]
fn qmin_fused_threshold_field_specs() {
    use super::frogdrop_sched::{p,N};use super::modp_ft::*;
    use super::tests_frogdrop::Rng;
    let pm=p();
    let halve=|v:N| if v.bit(0){(v+pm)>>1}else{v>>1};
    let mut count=0;
    for room in [73usize,74,81,82] {for kind in 0..4usize {for mode in 0..3usize {
      if kind>=2 && mode!=0 {continue;}
      let mut b=B::new();let original_z=b.alloc_n(256);let mut z=original_z.clone();let y=b.alloc_n(256);let sign=b.alloc();
      let k=b.alloc();let r=b.alloc_n(room);let one=b.alloc();b.x(one);let ms=Ms{k,r,one};let spectators=b.alloc_n(2);
      let sg=match mode{0=>None,1=>Some(sign),_=>Some(one)};
      match kind {0=>signed_modadd_double(&mut b,&ms,&mut z,&y,sg),1=>signed_modadd_halve(&mut b,&ms,&mut z,&y,sg),
        2=>mod_double_n(&mut b,&ms,&mut z,4),_=>mod_halve_n(&mut b,&ms,&mut z,4)}
      let(_,nb,_,_)=analyze_ops(b.ops.iter());let mut rng=Rng::new(137+room as u64+kind as u64);
      for byte in [0u8,255,170] {for batch in 0..4usize {
        let mut fixed=Fixed(byte);let mut sim=Simulator::new(b.width()as usize,nb as usize,&mut fixed);
        let mut wants=vec![];
        for shot in 0..64 {let zz=rng.below(256)%pm;let yy=rng.below(256)%pm;let negative=mode==2 || (mode==1 && shot%2==1);
          for i in 0..256 {if zz.bit(i){sim.qubits[original_z[i].0 as usize]|=1<<shot;}if yy.bit(i){sim.qubits[y[i].0 as usize]|=1<<shot;}}
          if negative && mode==1 {sim.qubits[sign.0 as usize]|=1<<shot;}
          for (i,&s) in spectators.iter().enumerate(){if(shot+batch+i)%3==0{sim.qubits[s.0 as usize]|=1<<shot;}}
          let sum=if negative{(zz+pm-yy)%pm}else{(zz+yy)%pm};
          let want=match kind{0=>(sum<<1)%pm,1=>halve(sum),2=>(zz<<4)%pm,_=>{let mut v=zz;for _ in 0..4{v=halve(v);}v}};
          wants.push(want);
        }
        let initial=sim.qubits.clone();sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0,"field threshold room={room} kind={kind} signmode={mode} HMR={byte}");
        for shot in 0..64 {let mut actual=N::ZERO;for (i,&q) in z.iter().enumerate(){if(sim.qubits[q.0 as usize]>>shot)&1==1{actual|=N::from(1u64)<<i;}}
          assert_eq!(actual,wants[shot],"field threshold room={room} kind={kind} signmode={mode} shot={shot}");}
        for i in 0..b.width(){if !z.iter().any(|q|q.0==i) && i!=one.0 {assert_eq!(sim.qubits[i as usize],initial[i as usize],"field source/scratch/spectator i={i}");}}
        assert_eq!(sim.qubits[one.0 as usize],!0);
        count+=64;
      }}
      eprintln!("QMIN_THRESHOLD_NATIVE room={room} kind={kind} signmode={mode} emitted_T={} expected_ESTIMATE={:.3} touched_Q={}",b.tof,super::tests_chunked::expected_t(&b.ops),b.width());
    }}}
    eprintln!("QMIN_THRESHOLD_FIELD_NATIVE_PASS cases={count}");
}
