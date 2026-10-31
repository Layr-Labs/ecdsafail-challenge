//! Zero-clean-workspace folds. Controls stay in their original data wires;
//! multi-controlled increments use the controls as low counter bits, then
//! restore those low bits. Borrowed tape words are restored exactly.
use super::{Builder,lowroom};
use crate::circuit::QubitId as Q;
use alloy_primitives::U256;
use super::heo::carry::lag::mcx;

fn inc(c:&mut Builder,ctl:&[(Q,bool)],x:&[Q],dirty:&[Q]) {
    if x.is_empty(){return;}
    for &(q,p) in ctl {if !p {c.x(q);}}
    let cs:Vec<Q>=ctl.iter().map(|p|p.0).collect();
    let mut reg=cs.clone();reg.extend(x);
    lowroom::inc_dirty(c,&reg,dirty);
    c.x_all(&cs);lowroom::inc_dirty(c,&cs,dirty);c.x_all(&cs);
    for &(q,p) in ctl.iter().rev(){if !p{c.x(q);}}
}
fn digits(mut v:u128,n:usize)->Vec<(usize,bool)>{
    let mut out=Vec::new();let mut i=0;
    while v!=0 && i<n {if v&1!=0{let neg=v&3==3;if neg{v+=1}else{v-=1}out.push((i,neg));}v>>=1;i+=1;}out
}
fn add(c:&mut Builder,ctl:&[(Q,bool)],b:&[Q],v:u128,dirty:&[Q]) {
    for(p,neg)in digits(v,b.len()) {let x=&b[p..];if neg{c.x_all(x);}inc(c,ctl,x,dirty);if neg{c.x_all(x);}}
}
fn complement(c:&mut Builder,ctl:&[(Q,bool)],b:&[Q],dirty:&[Q]) {for &q in b {mcx(c,ctl,q,dirty);}}
fn consts(f:U256,n:usize)->(u128,u128) {
    let a=f.as_limbs();assert_eq!((a[2],a[3]),(0,0));assert!(n<125);
    let f=(a[0] as u128 | (a[1] as u128)<<64)&((1u128<<(n+1))-1);assert_eq!(f&1,1);
    (f>>1,(f&((1u128<<n)-1))-1)
}
fn pool(used:&[Q],n:usize)->Vec<Q>{
    let out:Vec<_>=lowroom::pool_snapshot().into_iter().filter(|q|!used.contains(q)).collect();
    assert!(out.len()>=n+4);out
}
pub(crate) fn needed(c:&Builder)->bool {
    std::env::var_os("WALK_ZERO").is_some() && c.active_qubits() as usize>=super::walk_policy::physical_cap()
}
pub(crate) fn halve(c:&mut Builder,z:&[Q],s:Q,o:Q,f:U256) {
    let b=&z[1..];let(c1,c2)=consts(f,b.len());let mut used=z.to_vec();used.extend([s,o]);let dirty=pool(&used,b.len());
    let before=c.report_totals().map_or(0.0,|x|x.1);
    let p=z[0];let mi=[(o,false),(s,false),(p,true)];let vp=[(o,true),(s,true),(p,true)];
    complement(c,&mi,b,&dirty);
    inc(c,&[(o,true),(p,true)],b,&dirty); // first' XOR V0 = o & p
    c.cx(s,p);add(c,&[(p,true)],b,c1,&dirty);c.cx(s,p);
    add(c,&vp,b,c2,&dirty);
    complement(c,&mi,b,&dirty);c.cx(o,p);
    eprintln!("WALK_ZERO_FOLD div n={} live={} T={}",b.len(),c.active_qubits(),c.report_totals().map_or(0.0,|x|x.1)-before);
}
/// Entry z[0]=d XOR s XOR v0. Exit z[0]=d XOR s XOR v0 XOR o;
/// d stays implicit throughout, so its otherwise temporary extraction is absent.
pub(crate) fn double_parked(c:&mut Builder,z:&[Q],s:Q,v0:Q,o:Q,f:U256) {
    let b=&z[1..];let(c1,c2)=consts(f,b.len());let mut used=z.to_vec();used.extend([s,v0,o]);let dirty=pool(&used,b.len());
    let before=c.report_totals().map_or(0.0,|x|x.1);let p=z[0];c.cx(o,p);
    let host=|c:&mut Builder|{c.cx(s,p);c.cx(v0,p);c.cx(o,p);};
    let mi=[(p,true),(o,false),(s,true)];let vp=[(p,true),(o,true),(s,false)];
    host(c);complement(c,&mi,b,&dirty);host(c);
    // first XOR minus XOR V0 = MAJ(v0,!z0_final,o). Three disjoint cubes.
    inc(c,&[(v0,true),(o,true)],b,&dirty);
    inc(c,&[(v0,false),(p,false),(o,true)],b,&dirty);
    inc(c,&[(v0,true),(p,false),(o,false)],b,&dirty);
    c.cx(s,p);c.cx(v0,p);add(c,&[(p,true)],b,c1,&dirty);c.cx(v0,p);c.cx(s,p);
    host(c);add(c,&vp,b,c2,&dirty);complement(c,&mi,b,&dirty);host(c);
    eprintln!("WALK_ZERO_FOLD mul n={} live={} T={}",b.len(),c.active_qubits(),c.report_totals().map_or(0.0,|x|x.1)-before);
}

pub fn selftest(){
    use crate::sim::Simulator;
    use sha3::{Shake256,digest::{Update,ExtendableOutput}};
    std::env::set_var("FWSK_LEAN","1");std::env::set_var("SQ_LOWROOM","1");std::env::set_var("FWSK_CV","1");
    std::env::set_var("FWSK_LEAN_ROOM","100000");std::env::remove_var("WALK_ZERO");
    let mut total=0;
    for n in [2usize,3,4,5,6,7,35,36] {for kind in 0..4 {let mul=kind==1;let term=kind>=2;let inverse=kind==3;
        let mut circuits=Vec::new();let mut regs=None;
        for candidate in [false,true] {
            let mut c=Builder::new();let z=c.alloc_qubits(n+1);let s=c.alloc_qubit();let o=c.alloc_qubit();let v=c.alloc_qubit();let d=c.alloc_qubit();let dirty=c.alloc_qubits(n+4);
            let begin=c.op_count();let f=U256::from(if n==2{1u64}else if n<=7{5}else{0x1000003d1});
            lowroom::with_pool(dirty.clone(),||{
                if term {if candidate {terminal(&mut c,&z,s,v,d,o,inverse,f);}else{assert!(super::fwsk_lean::fold_terminal(&mut c,&z,s,v,d,o,inverse,f));}}
                else if mul {if candidate {c.cx(d,z[0]);double_parked(&mut c,&z,s,v,o,f);}else{assert!(super::fwsk_lean::fold_double(&mut c,&z,s,v,d,o,true,f));}}
                else if candidate {halve(&mut c,&z,s,o,f);}else{assert!(super::fwsk_lean::fold_halve(&mut c,&z,s,o,f));}
            });
            let(nq,nb)=c.i13_dims();let ops=c.take_ops();circuits.push((nq,nb,ops[begin..].to_vec()));regs=Some((z,s,o,v,d,dirty));
        }
        let(z,s,o,v,d,dirty)=regs.unwrap();let base=dirty.last().unwrap().0 as usize+1;
        let mut rows=Vec::new();let mut random=1731u64;
        for sel in 0..if term{32u64}else{16u64} {let count=if n<=7{1usize<<n}else{1024};for i in 0..count {
            random^=random<<13;random^=random>>7;random^=random<<17;
            let b=if n<=7{i as u64}else{random&((1u64<<n)-1)};rows.push((sel,b,random));
        }}
        for batch in rows.chunks(64) {
            let mut outcomes=Vec::new();
            for(nq,nb,ops)in &circuits {
                let mut h=Shake256::default();h.update(b"walk-zero-fold-v1");let mut rng=h.finalize_xof();let mut sim=Simulator::new(*nq,*nb,&mut rng);
                for(l,&(sel,b,ran))in batch.iter().enumerate(){
                    let mut put=|q:Q,x:u64|{if x&1!=0{*sim.qubit_mut(q)|=1u64<<l;}};
                    let ss=sel&1;let oo=sel>>1&1;let vv=sel>>2&1;let dd=sel>>3&1;
                    put(s,ss);put(o,oo);put(v,vv);put(d,dd);put(z[0],if term{sel>>4&1}else if mul{ss^vv}else{vv});
                    for(i,&q)in z[1..].iter().enumerate(){put(q,b>>i);}
                    for(i,&q)in dirty.iter().enumerate(){put(q,ran>>(i%64));}
                }
                sim.apply_iter(ops.iter());assert_eq!(sim.phase,0,"fold phase n={n} mul={mul}");
                for q in base..*nq {assert_eq!(sim.qubit(Q(q as u64)),0,"fold ancilla");}
                outcomes.push((0..base).map(|q|sim.qubit(Q(q as u64))).collect::<Vec<_>>());
            }
            assert_eq!(outcomes[0],outcomes[1],"fold mismatch n={n} mul={mul}");total+=batch.len();
        }
        eprintln!("WALK_ZERO_TEST fold n={n} kind={kind} cases={} PASS",rows.len());
    }}
    // Exhaustive multi-controlled increments, including nonzero borrowed wires.
    for nc in 0..=4 {for nx in 1..=5 {
        let mut c=Builder::new();let cs=c.alloc_qubits(nc);let xs=c.alloc_qubits(nx);let g=c.alloc_qubits(nc+nx+1);let start=c.op_count();
        let ctl:Vec<_>=cs.iter().enumerate().map(|(i,&q)|(q,i%2==0)).collect();inc(&mut c,&ctl,&xs,&g);let(nq,nb)=c.i13_dims();let ops=c.take_ops();
        let mut h=Shake256::default();h.update(b"walk-zero-increment-v1");let mut rng=h.finalize_xof();let mut sim=Simulator::new(nq,nb,&mut rng);
        for word in 0..1usize<<(nc+nx) {sim.clear_for_shot();for(i,&q)in cs.iter().chain(&xs).enumerate(){*sim.qubit_mut(q)=if word>>i&1!=0{u64::MAX}else{0};}for(i,&q)in g.iter().enumerate(){*sim.qubit_mut(q)=0x9612f7a345678bdeu64.rotate_left(i as u32);}
            let before:Vec<_>=(0..nq).map(|q|sim.qubit(Q(q as u64))).collect();sim.apply_iter(ops[start..].iter());
            let pred=(0..nc).all(|i|(word>>i&1!=0)==(i%2==0));let expected=((word>>nc)+usize::from(pred))&((1<<nx)-1);
            for(i,&q)in xs.iter().enumerate(){assert_eq!(sim.qubit(q),if expected>>i&1!=0{u64::MAX}else{0});}
            for &q in cs.iter().chain(&g){assert_eq!(sim.qubit(q),before[q.0 as usize]);}assert_eq!(sim.phase,0);total+=1;
        }
    }}
    eprintln!("WALK_ZERO_TEST PASS cases={total}");
}

pub(crate) fn terminal(c:&mut Builder,z:&[Q],t:Q,q0:Q,d:Q,o:Q,inverse:bool,f:U256) {
    let b=&z[1..];let(c1,c2)=consts(f,b.len());let mut used=z.to_vec();used.extend([t,q0,d,o]);let dirty=pool(&used,b.len());
    let before=c.report_totals().map_or(0.,|x|x.1);let p=z[0];
    if inverse {c.x(q0);} else {c.cx(o,p);c.cx(d,p);}
    let mi=[(d,true),(o,false),(t,true)];let vp=[(d,true),(o,true),(t,false)];
    complement(c,&mi,b,&dirty);
    // A disjoint truth-table expansion costs extra increments at this single
    // terminal site, while keeping all four selectors in existing data wires.
    for row in 0..16u8 {
        let zz=row&1!=0;let oo=row&2!=0;let dd=row&4!=0;let tt=row&8!=0;
        let first=(if inverse{zz}else{zz^oo^dd})&(oo^dd);
        if first ^ (dd&!oo&tt) ^ (dd&oo&!tt) {
            inc(c,&[(p,zz),(o,oo),(d,dd),(t,tt)],b,&dirty);
        }
    }
    // Reproduce the parent's paired increment even outside its exclusive
    // selector domain. Its high carry is V XOR (U AND low_bit), not an OR.
    // XOR = V + U*low_bit - 2*V*U*low_bit, implemented without a V wire.
    let _=c2;c.cx(t,p);c.cx(q0,p);
    for (at,neg) in digits(c1,b.len()) {
        if neg {c.x_all(&b[at..]);}
        inc(c,&vp,&b[at+1..],&dirty);
        inc(c,&[(p,true),(b[at],true)],&b[at+1..],&dirty);
        if at+2<b.len() {
            let high=&b[at+2..];c.x_all(high);
            inc(c,&[(p,true),(b[at],true),(d,true),(o,true),(t,false)],high,&dirty);
            c.x_all(high);
        }
        c.cx(p,b[at]);
        if neg {c.x_all(&b[at..]);}
    }
    c.cx(q0,p);c.cx(t,p);complement(c,&mi,b,&dirty);
    if inverse {c.x(q0);c.cx(o,p);c.cx(d,p);}
    eprintln!("WALK_ZERO_FOLD term n={} inverse={inverse} live={} T={}",b.len(),c.active_qubits(),c.report_totals().map_or(0.,|x|x.1)-before);
}
