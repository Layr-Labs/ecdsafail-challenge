//! Bounded actual-Builder/native-Simulator gate, separate from normal qualification.
use super::{builder::Builder,lowq_mm_adapter as port,skycof_mm::{Cfg,Field}};
use crate::circuit::{analyze_ops,QubitId as Q};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::digest::XofReader;
struct Forced(u8);
impl XofReader for Forced {fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}
fn p()->U256{U256::from_limbs([0xfffffffefffffc2f,u64::MAX,u64::MAX,u64::MAX])}
fn put(words:&mut[u64],qs:&[Q],shot:usize,v:U256){for(i,q)in qs.iter().enumerate(){if v.bit(i){words[q.0 as usize]|=1<<shot;}}}
fn get(words:&[u64],qs:&[Q],shot:usize)->U256{let mut v=U256::ZERO;for(i,q)in qs.iter().enumerate(){if(words[q.0 as usize]>>shot)&1!=0{v|=U256::from(1u64)<<i;}}v}
fn outside(words:&[u64],keep:&[Q])->u64{words.iter().enumerate().filter(|(i,_)|!keep.iter().any(|q|q.0 as usize==*i)).fold(0,|a,(_,w)|a|w)}
fn cost(ops:&[crate::circuit::Op])->f64{use crate::circuit::OperationType as K;let(mut d,mut t)=(0,0.0);for o in ops{match o.kind{K::PushCondition=>d+=1,K::PopCondition=>d-=1,K::CCX|K::CCZ=>t+=0.5f64.powi(d),_=>()}}assert_eq!(d,0);t}
#[test]
fn lowq_fullwidth_role_smoke(){
    let pm=p();let one=U256::from(1u64);let mut scale=one;
    for _ in 0..404{scale=if scale.bit(0){(scale>>1)+(pm>>1)+one}else{scale>>1};}
    let roles=[("MM1",24,28,70,200,404,true),("MM2_3",25,24,270,0,0,false),
        ("MM4",22,25,270,0,0,false),("MM5_6",24,30,70,200,404,true)];
    let mut seed=0x103820261011u64;
    let mut rnd=||{let mut v=U256::ZERO;for j in 0..4{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;v|=U256::from(seed)<<(64*j);}v.reduce_mod(pm)};
    for(name,guard,cw,room,pass,k,neg)in roles{
        let mut c=Builder::new();let a=c.alloc_qubits(256);let m=c.alloc_qubits(256);let spectators=c.alloc_qubits(pass);
        let cfg=Cfg::windowed(Field::secp(),guard,cw,room);let before=c.active_qubits();
        let out=port::mulf(&mut c,cfg,&a,&m,k,neg);let forward=c.take_ops();
        port::mulf_inv(&mut c,cfg,&a,&m,k,neg,out.clone());let inverse=c.take_ops();assert_eq!(c.active_qubits(),before);
        let(nq,nb)=c.i13_dims();let mut rows=vec![];
        for shot in 0..64{let pair=match shot{0=>(pm-one,one),1=>(U256::ZERO,one),2=>(one,U256::ZERO),
            3=>(one,one),4=>(pm-U256::from(2u64),one),5=>(pm-one,pm-one),
            6=>((one<<66)-one,one),7=>(one<<128,one),_=>(rnd(),rnd())};rows.push(pair);}
        for byte in [0u8,255,170]{
            let mut r=Forced(byte);let mut s=Simulator::new(nq,nb.max(1),&mut r);
            for(shot,&(av,mv))in rows.iter().enumerate(){put(&mut s.qubits,&a,shot,av);put(&mut s.qubits,&m,shot,mv);}
            for(i,q)in spectators.iter().enumerate(){s.qubits[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(i as u32);}
            let initial=s.qubits.clone();s.apply_iter(forward.iter());let phase_f=s.phase;
            let mut fkeep=a.clone();fkeep.extend(&m);fkeep.extend(&spectators);fkeep.extend(&out);
            let scratch_f=outside(&s.qubits,&fkeep);
            for(shot,&(av,mv))in rows.iter().enumerate(){let mut want=av.mul_mod(mv,pm);if k!=0{want=want.mul_mod(scale,pm);}if neg&&!want.is_zero(){want=pm-want;}
                let good=get(&s.qubits,&out,shot)==want;
                let src=get(&s.qubits,&a,shot)==av&&get(&s.qubits,&m,shot)==mv;
                if shot<8{eprintln!("LOWQ_EDGE role={name} HMR={byte} slot={shot} value_ok={good} source_ok={src} phase={} scratch={}",(phase_f>>shot)&1,(scratch_f>>shot)&1);}
                else{assert!(good,"random forward value role{name} shot{shot}");assert!(src,"random source role{name} shot{shot}");}
            }
            assert_eq!(phase_f&!0xff,0,"random forward phase role{name} HMR{byte}");assert_eq!(scratch_f&!0xff,0,"random forward scratch");
            s.xof.0=byte^255;s.apply_iter(inverse.iter());
            let mut keep=a.clone();keep.extend(&m);keep.extend(&spectators);let scratch=outside(&s.qubits,&keep);
            for(shot,&(av,mv))in rows.iter().enumerate(){let restored=get(&s.qubits,&a,shot)==av&&get(&s.qubits,&m,shot)==mv;
                if shot<8{eprintln!("LOWQ_PAIR_EDGE role={name} HMR={byte} slot={shot} source_ok={restored} phase={} scratch={}",(s.phase>>shot)&1,(scratch>>shot)&1);}
                else{assert!(restored,"random inverse source role{name} shot{shot}");}}
            assert_eq!(s.phase&!0xff,0,"random paired phase role{name} HMR{byte}");assert_eq!(scratch&!0xff,0,"random paired scratch role{name} HMR{byte}");
            for q in &spectators{assert_eq!(s.qubits[q.0 as usize],initial[q.0 as usize]);}
        }
        eprintln!("LOWQ_ROLE_GATE role={name} guard={guard} cw={cw} sw={} sh={} room={room} touched_Q={} peak={} fwd_T={} inv_T={} random56x3=PASS",34+guard,32+guard,nq,c.peak_total(),cost(&forward),cost(&inverse));
    }
}

#[test]
fn lowq_raw_whole_resource(){
    super::skycof::pointadd::snapshot_knobs();super::skycof::pointadd::install_recipe();
    let ops=super::skycof::pointadd::build_point_add();let(nq,nb,_,regs)=analyze_ops(ops.iter());
    assert_eq!(regs.len(),4);assert_eq!(nq,1038);
    eprintln!("LOWQ_RAW_WHOLE Q={nq} bits={nb} ops={} expected_T={} NORMAL_QUALIFICATION=NONE",ops.len(),cost(&ops));
}

fn curve()->crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve{
    let hx=|s:&str|U256::from_str_radix(s,16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve{
        modulus:p(),a:U256::ZERO,b:U256::from(7u64),
        gx:hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy:hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order:hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")}
}
#[test]
fn lowq_native_whole256(){
    use sha3::digest::{Update,ExtendableOutput};
    super::skycof::pointadd::snapshot_knobs();super::skycof::pointadd::install_recipe();
    let ops=super::skycof::pointadd::build_point_add();let(nq,nb,_,regs)=analyze_ops(ops.iter());
    assert_eq!(nq,1038);assert_eq!(regs.len(),4);
    let cv=curve();let mut cases=vec![];
    // Feasible directed on-curve cases, avoiding unsupported equal-x/infinity.
    // Consecutive small multiples with a near-opposite addend sum to -G.
    for k in 1..=16u64{
        let r=cv.mul(cv.gx,cv.gy,U256::from(k));
        let a=cv.mul(cv.gx,cv.gy,cv.order-U256::from(k+1));
        assert_ne!(r.0,a.0);cases.push((r,a,cv.add(r.0,r.1,a.0,a.1)));
    }
    let mut seed=2024u64;
    let mut scalar=||{let mut v=U256::ZERO;for j in 0..4{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;v|=U256::from(seed)<<(64*j);}v};
    while cases.len()<272{
        let r=cv.mul(cv.gx,cv.gy,scalar());let a=cv.mul(cv.gx,cv.gy,scalar());
        if r.0==a.0||r.0.is_zero()&&r.1.is_zero()||a.0.is_zero()&&a.1.is_zero(){continue;}
        cases.push((r,a,cv.add(r.0,r.1,a.0,a.1)));
    }
    let mut h=sha3::Shake256::default();h.update(b"skycof-lowq-native-whole256-v1");let mut rd=h.finalize_xof();
    let mut s=Simulator::new(nq as usize,nb as usize,&mut rd);let(mut cls,mut pha,mut anc)=(0,0,0);
    for(batch,rows)in cases.chunks(64).enumerate(){
        s.clear_for_shot();let mask=if rows.len()==64{u64::MAX}else{(1u64<<rows.len())-1};
        for(shot,(r,a,_))in rows.iter().enumerate(){s.set_register(&regs[0],r.0,shot);s.set_register(&regs[1],r.1,shot);s.set_register(&regs[2],a.0,shot);s.set_register(&regs[3],a.1,shot);}
        s.apply_iter(ops.iter());let mut bad=0;
        for(shot,(_,_,want))in rows.iter().enumerate(){if s.get_register(&regs[0],shot)!=want.0||s.get_register(&regs[1],shot)!=want.1{bad+=1;eprintln!("LOWQ_WHOLE_BAD shot={} directed={}",batch*64+shot,batch*64+shot<16);}}
        let ph=s.phase&mask;for reg in &regs{for q in reg{if let crate::circuit::QubitOrBit::Qubit(q)=q{*s.qubit_mut(*q)=0;}}}
        let dirty=s.qubits.iter().fold(0,|a,w|a|w)&mask;
        eprintln!("LOWQ_WHOLE_BATCH batch={batch} shots={} cls={bad} phase={ph:#018x} anc={dirty:#018x}",rows.len());
        cls+=bad;pha+=ph.count_ones();anc+=dirty.count_ones();
    }
    // The simulator charges all 64 lanes, including 48 inactive final-batch lanes.
    // This bounded correctness gate deliberately does not report an actual-T mean.
    eprintln!("LOWQ_WHOLE_NATIVE directed16_random256 cls={cls} pha={pha} anc={anc} Q={nq} bits={nb} ops={} expected_T={} ACTUAL_MEAN=NOT_MEASURED NORMAL_QUALIFICATION=NONE",ops.len(),cost(&ops));
    assert_eq!((cls,pha,anc),(0,0,0),"whole native gate failed; attribute against old before any precision change");
}
