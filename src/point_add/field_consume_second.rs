//! Two consumed high multiplier bits. All extra qubits are borrowed; the
//! 256-bit output consists of254 zero lanes plus the original two input bits.
use super::arith::{ttk_add,ttk_carry};
use super::builder::{B,G};
use super::mask::mcx_dirty;
use super::modp_frogdrop::{add_const_exact,inc_dirty_free,C};
use super::canonical_short::short_modadd_canonical as short_modadd;
use crate::circuit::QubitId;

fn controlled_dirty(b:&mut B,r:&[G],c:QubitId,dirty:&[QubitId]) {
    for &gate in r {
        match gate {
            G::X(t)=>b.cx(c,t),
            G::Cx(a,t)=>b.ccx(c,a,t),
            G::Ccx(a,d,t)=> {
                let q=*dirty.iter().find(|&&q|q!=a&&q!=d&&q!=t&&q!=c).unwrap();
                mcx_dirty(b,&[c,a,d],t,&[q]);
            },
            G::Swap(a,t)=>{
                b.cx(a,t);b.ccx(c,t,a);b.cx(a,t);
            },
            _=>panic!("integer prefix contains nonunitary gate {gate:?}")
        }
    }
}
fn vflag(b:&mut B,a:&[QubitId],v:usize,out:QubitId,dirty:&[QubitId]) {
    for &q in &a[..v]{b.x(q);}
    mcx_dirty(b,&a[..=v],out,dirty);
    for &q in &a[..v]{b.x(q);}
}

/// Integer k*a modulo2^n for k0,k1 initially in z[n-2],z[n-1].
/// Descending v2(a) leaves z0 clean at every v>=1: prior output has even
/// product, and the unprocessed input has all low n-2 lanes zero.
fn integer_seed(b:&mut B,z:&[QubitId],a:&[QubitId],dirty:&[QubitId]) {
    let n=z.len();assert_eq!(a.len(),n-1);assert!(n>=4);
    for v in (0..n-1).rev() {
        let enabled=if v==0 {a[0]} else {z[0]};
        if v!=0{vflag(b,a,v,enabled,dirty);}
        b.begin();
        if n-2!=v {b.swap(z[n-2],z[v]);}
        if n-1!=v+1 {b.swap(z[n-1],z[v+1]);}
        let hi=&a[v+1..];
        let l=hi.len();
        if l==1 {b.ccx(z[v+1],hi[0],z[v+2]);}
        else if l>=2 {ttk_add(b,hi,&z[v+2..],Some(z[v+1]),None);}
        if l==1 {
            mcx_dirty(b,&[z[v],hi[0],z[v+1]],z[n-1],&dirty[..1]);
            b.ccx(z[v],hi[0],z[v+1]);
        } else if l>=2 {
            ttk_add(b,hi,&z[v+1..n-1],Some(z[v]),Some((z[n-1],dirty[0])));
        }
        let r=b.end();
        controlled_dirty(b,&r,enabled,dirty);
        if v!=0{vflag(b,a,v,enabled,dirty);}
    }
}

fn xor_lt_const(b:&mut B,a:&[QubitId],k:u64,out:QubitId,enable:Option<QubitId>,dirty:&[QubitId]) {
    for i in (0..a.len().min(64)).rev() {
        if(k>>i)&1==0{continue;}
        let mut controls=Vec::new();let mut flips=Vec::new();
        if let Some(q)=enable{controls.push(q);}
        for j in i..a.len() {
            controls.push(a[j]);
            let want=j!=i&&j<64&&(k>>j)&1!=0;
            if !want{b.x(a[j]);flips.push(a[j]);}
        }
        mcx_dirty(b,&controls,out,dirty);
        for &q in flips.iter().rev(){b.x(q);}
    }
}
fn xor_zero(b:&mut B,z:&[QubitId],out:QubitId,enable:Option<QubitId>,dirty:&[QubitId]) {
    let mut controls=z.to_vec();if let Some(q)=enable{controls.push(q);}
    for &q in z{b.x(q);}
    mcx_dirty(b,&controls,out,dirty);
    for &q in z{b.x(q);}
}
fn carry_plain(b:&mut B,a:&[QubitId],t:&[QubitId],out:QubitId) {
    let n=a.len();assert_eq!(t.len(),n);assert!(n>=2);
    b.begin();for i in 1..n{b.cx(a[i],t[i]);}let s1=b.end();
    b.play(&s1,false);b.cx(a[n-1],out);
    b.begin();
    for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
    for i in 0..n-1{b.ccx(t[i],a[i],a[i+1]);}
    let s23=b.end();b.play(&s23,false);
    b.ccx(t[n-1],a[n-1],out);
    b.play(&s23,true);b.play(&s1,true);
}
/// out ^= optional_enable & [z<a], for a255 with implicit zero highbit.
fn xor_short_lt(b:&mut B,z:&[QubitId],a:&[QubitId],out:QubitId,enable:Option<QubitId>,d:QubitId,e:QubitId) {
    let n=a.len();assert_eq!(z.len(),n+1);
    for &q in &z[..n]{b.x(q);}b.x(z[n]);
    for _ in 0..2 {
        b.ccx(z[n],d,out);
        match enable {Some(c)=>ttk_carry(b,a,&z[..n],c,d,e),None=>carry_plain(b,a,&z[..n],d)}
    }
    b.x(z[n]);for &q in &z[..n]{b.x(q);}
}
fn shift_source(b:&mut B,a:&[QubitId],z:&[QubitId],c:u64,reverse:bool) {
    b.begin();add_const_exact(b,a,None,c,z);let r=b.end();b.play(&r,reverse);
}
/// z <- (g ? A-z : z) modulo2^n, A=zero_extend(a). Exact involution.
fn reflect_action(b:&mut B,z:&[QubitId],a:&[QubitId],g:QubitId,dirty_extra:&[QubitId]) {
    let n=a.len();assert_eq!(z.len(),n+1);
    for &q in z{b.cx(g,q);}
    ttk_add(b,a,&z[..n],Some(g),Some((z[n],dirty_extra[0])));
    let mut xr=vec![g];xr.extend(z);
    let mut dirty=a.to_vec();dirty.extend_from_slice(&dirty_extra[..2]);
    inc_dirty_free(b,&xr,&dirty);b.x(g);
}

/// Predicate of R_{a-C}. For a>C it selects (0,a) except a-C, plus(p,2^n).
/// All source shifts/XOR encodings are restored before return.
fn first_predicate(b:&mut B,z:&[QubitId],a:&[QubitId],out:QubitId,h:QubitId,d:QubitId,e:QubitId,c:u64) {
    for _ in 0..2 {
        xor_short_lt(b,z,a,out,Some(h),d,e);
        xor_zero(b,z,out,Some(h),a);
        shift_source(b,a,z,c,true);
        for i in 0..a.len(){b.cx(a[i],z[i]);}
        xor_zero(b,z,out,Some(h),a);
        for i in 0..a.len(){b.cx(a[i],z[i]);}
        shift_source(b,a,z,c,false);
        for &q in z{b.x(q);}
        xor_lt_const(b,z,c-1,out,Some(h),a);
        for &q in z{b.x(q);}
        // h ^= [a>C]. Pairing the toggle block cancels the initial dirty h.
        b.x(h);xor_lt_const(b,a,c+1,h,None,z);
    }
}
fn normalize_seed(b:&mut B,z:&[QubitId],a:&[QubitId],dirty:&[QubitId],c:u64) {
    assert!(dirty.len()>=6);
    let(g,h,d,e)=(dirty[0],dirty[1],dirty[2],dirty[3]);
    for _ in 0..2 {
        shift_source(b,a,z,c,true);
        reflect_action(b,z,a,g,&dirty[4..6]);
        shift_source(b,a,z,c,false);
        first_predicate(b,z,a,g,h,d,e,c);
    }
    for _ in 0..2 {
        reflect_action(b,z,a,g,&dirty[4..6]);
        xor_short_lt(b,z,a,g,None,d,e);
        xor_zero(b,z,g,None,a);
    }
}

pub fn product_consume_two_high_nf(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],ylow:&[QubitId]) {
    assert_eq!(z.len(),256);assert_eq!(a.len(),255);assert_eq!(ylow.len(),254);
    integer_seed(b,z,a,ylow);
    normalize_seed(b,z,a,ylow,C);
    for i in(0..254).rev() {
        super::canonical_short::mod_double_canonical(b,z,ylow,C);
        short_modadd(b,z,a,ylow[i],ylow[(i+1)%254],ylow[(i+2)%254],ylow[(i+3)%254],ylow[(i+4)%254],C);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{Op,OperationType as K,NO_BIT};
    fn simulate<'a>(ops:impl IntoIterator<Item=&'a Op>,mut q:Vec<u64>)->Vec<u64>{
        for op in ops{assert_eq!(op.c_condition,NO_BIT);let t=op.q_target.0 as usize;let a=op.q_control1.0 as usize;let c=op.q_control2.0 as usize;
            match op.kind{K::X=>q[t]^=u64::MAX,K::CX=>q[t]^=q[a],K::CCX=>q[t]^=q[a]&q[c],K::Swap=>q.swap(t,a),_=>panic!("unexpected {:?}",op.kind)}
        }q
    }
    fn put(q:&mut[u64],v:&[QubitId],lane:usize,x:u64){for(i,k)in v.iter().enumerate(){if(x>>i)&1!=0{q[k.0 as usize]|=1u64<<lane;}}}
    fn get(q:&[u64],v:&[QubitId],lane:usize)->u64{v.iter().enumerate().map(|(i,k)|((q[k.0 as usize]>>lane)&1)<<i).sum()}
    fn prime(p:usize)->bool{p>=2&&!(2..).take_while(|d|d*d<=p).any(|d|p%d==0)}
    #[test]
    fn integer_prefix_all_values_and_dirty_bits(){
        let mut cases=0;
        for n in 4..=10{
            let mut b=B::new();let a=b.alloc_n(n-1);let z=b.alloc_n(n);let dirty=b.alloc_n(n.max(6));
            integer_seed(&mut b,&z,&a,&dirty);
            let count=((1usize<<(n-1))-1)*4*64;
            for first in(0..count).step_by(64){
                let mut start=vec![0;b.width()as usize];
                for lane in 0..64.min(count-first){let code=first+lane;let av=code/256+1;let k=(code/64)%4;let dv=code%64;
                    put(&mut start,&a,lane,av as u64);put(&mut start,&z[n-2..],lane,k as u64);put(&mut start,&dirty,lane,dv as u64);
                }
                let end=simulate(b.ops.iter(),start.clone());
                for lane in 0..64.min(count-first){let code=first+lane;let av=code/256+1;let k=(code/64)%4;
                    assert_eq!(get(&end,&z,lane),(av*k% (1<<n))as u64,"integer n{n} a{av} k{k}");assert_eq!(get(&end,&a,lane),av as u64);
                }
                for q in &dirty{assert_eq!(end[q.0 as usize],start[q.0 as usize]);}
                assert_eq!(simulate(b.ops.iter().rev(),end),start);
                cases+=64.min(count-first);
            }
        }
        eprintln!("TWO_BIT_INTEGER_SEED_PASS cases={cases} inverse=true every_nonzero_source=true");
    }
    #[test]
    fn normalized_prefix_all_sources_and_dirty_bits(){
        let mut cases=0;
        for n in 5..=10{for c in[1,3,5,7,9,11,13].into_iter().filter(|&c|3*c<(1<<n)-c&&prime((1<<n)-c)){
            let p=(1<<n)-c;
            let mut b=B::new();let a=b.alloc_n(n-1);let z=b.alloc_n(n);let dirty=b.alloc_n(n.max(6));
            integer_seed(&mut b,&z,&a,&dirty);normalize_seed(&mut b,&z,&a,&dirty,c as u64);
            let count=(p/2)*4*64;
            for first in(0..count).step_by(64){
                let mut start=vec![0;b.width()as usize];
                for lane in 0..64.min(count-first){let code=first+lane;let av=code/256+1;let k=(code/64)%4;let dv=code%64;
                    put(&mut start,&a,lane,av as u64);put(&mut start,&z[n-2..],lane,k as u64);put(&mut start,&dirty,lane,dv as u64);
                }
                let end=simulate(b.ops.iter(),start.clone());
                for lane in 0..64.min(count-first){let code=first+lane;let av=code/256+1;let k=(code/64)%4;
                    assert_eq!(get(&end,&z,lane),(av*k%p)as u64,"normalized n{n} c{c} a{av} k{k}");assert_eq!(get(&end,&a,lane),av as u64);
                }
                for q in &dirty{assert_eq!(end[q.0 as usize],start[q.0 as usize]);}
                assert_eq!(simulate(b.ops.iter().rev(),end),start);cases+=64.min(count-first);
            }
        }}
        eprintln!("TWO_BIT_NORMALIZED_SEED_PASS cases={cases} inverse=true every_valid_source=true");
    }
    fn putn(q:&mut[u64],ports:&[QubitId],lane:usize,x:super::super::frogdrop_sched::N){
        for(i,k)in ports.iter().enumerate(){if x.bit(i){q[k.0 as usize]|=1u64<<lane;}}
    }
    fn getn(q:&[u64],ports:&[QubitId],lane:usize)->super::super::frogdrop_sched::N{
        use super::super::frogdrop_sched::N;
        let mut x=N::ZERO;for(i,k)in ports.iter().enumerate(){if(q[k.0 as usize]>>lane)&1!=0{x|=N::from(1u64)<<i;}}x
    }
    #[test]
    fn normalized_seed_wide_native_all_valuations(){
        use super::super::frogdrop_sched::{N,p};use super::super::tests_frogdrop::Rng;
        use crate::sim::Simulator;use sha3::digest::{ExtendableOutput,Update};
        let pp=p();let mut inputs=Vec::new();
        for v in 0..255{let a=N::from(1u64)<<v;inputs.push(a);if a*N::from(3u64)<=pp/ N::from(2u64){inputs.push(a*N::from(3u64));}}
        for center in[N::from(C),pp/N::from(3u64),(N::from(1u64)<<256)/N::from(3u64),pp/N::from(2u64)]{
            for delta in -3i64..=3{let a=if delta<0{center-N::from((-delta)as u64)}else{center+N::from(delta as u64)};
                if a>N::ZERO&&a<=pp/N::from(2u64){inputs.push(a);}
            }
        }
        inputs.sort();inputs.dedup();let pairs:Vec<_>=inputs.into_iter().flat_map(|a|(0..4u64).map(move|k|(a,k))).collect();
        let mut b=B::new();let a=b.alloc_n(255);let z=b.alloc_n(256);let dirty=b.alloc_n(254);let resident=b.alloc_n(7);
        integer_seed(&mut b,&z,&a,&dirty);normalize_seed(&mut b,&z,&a,&dirty,C);
        assert_eq!(b.peak,772);
        let mut rng=Rng::new(0x32772);
        for batch in pairs.chunks(64){
            let mut h=sha3::Shake256::default();h.update(b"two-bit-seed-wide-v1");let mut xof=h.finalize_xof();
            let mut sim=Simulator::new(b.width()as usize,1,&mut xof);
            for(lane,&(av,k))in batch.iter().enumerate(){putn(&mut sim.qubits,&a,lane,av);putn(&mut sim.qubits,&z[254..],lane,N::from(k));
                putn(&mut sim.qubits,&dirty,lane,rng.below(254));putn(&mut sim.qubits,&resident,lane,N::from(rng.next()&127));}
            let start=sim.qubits.clone();sim.apply_iter(b.ops.iter());
            for(lane,&(av,k))in batch.iter().enumerate(){assert_eq!(getn(&sim.qubits,&z,lane),av.mul_mod(N::from(k),pp),"wide seed a={av} k={k}");assert_eq!(getn(&sim.qubits,&a,lane),av);}
            for q in dirty.iter().chain(&resident){assert_eq!(sim.qubits[q.0 as usize],start[q.0 as usize]);}assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,start);assert_eq!(sim.phase,0);
        }
        eprintln!("TWO_BIT_WIDE_SEED_NATIVE_PASS cases={} all_v2_0_through254=true Q={} T={} N={} inverse=true",pairs.len(),b.peak,b.tof,b.ops.len());
    }
    #[test]
    fn consumptive_two_bit_wide_native_product(){
        use super::super::frogdrop_sched::{N,p};use super::super::tests_frogdrop::Rng;
        use crate::circuit::analyze_ops;use crate::sim::Simulator;use sha3::digest::{ExtendableOutput,Update};
        let pp=p();let mask=(N::from(1u64)<<254)-N::from(1u64);
        let mut b=B::new();let a=b.alloc_n(255);let ylow=b.alloc_n(254);let z=b.alloc_n(256);let resident=b.alloc_n(7);let mut out=z.clone();
        product_consume_two_high_nf(&mut b,&mut out,&a,&ylow);
        let(nq,nb,_,_)=analyze_ops(b.ops.iter());assert_eq!(nq,765);assert_eq!(b.peak,772);
        let mut h=sha3::Shake256::default();h.update(b"two-bit-product-wide-v1");let mut xof=h.finalize_xof();
        let mut sim=Simulator::new(b.width()as usize,(nb as usize).max(1),&mut xof);let mut rng=Rng::new(0x772af31);let(mut av,mut yv)=(Vec::new(),Vec::new());
        for lane in 0..64{let x=match lane{
            0..=3=>N::from((lane+1)as u64),4=>N::from(C-1),5=>N::from(C),6=>N::from(C+1),7=>pp>>1,8=>(pp>>1)-N::from(1u64),
            9=>N::from(1u64)<<254,10=>pp/N::from(3u64),11=>pp/N::from(3u64)+N::from(1u64),12=>(N::from(1u64)<<256)/N::from(3u64),13=>(N::from(1u64)<<256)/N::from(3u64)+N::from(1u64),
            _=>rng.below(255)%(pp>>1)+N::from(1u64)};
            let y=match lane{0=>N::ZERO,1=>N::from(1u64),2=>pp-N::from(1u64),3=>N::from(1u64)<<255,4=>pp-N::from(1u64),5=>N::from(1u64)<<255,6=>(N::from(1u64)<<255)-N::from(1u64),_=>rng.below(256)%pp};
            putn(&mut sim.qubits,&a,lane,x);putn(&mut sim.qubits,&ylow,lane,y&mask);putn(&mut sim.qubits,&z[254..],lane,y>>254);putn(&mut sim.qubits,&resident,lane,N::from(rng.next()&127));av.push(x);yv.push(y);
        }
        let start=sim.qubits.clone();sim.apply_iter(b.ops.iter());
        for lane in 0..64{assert_eq!(getn(&sim.qubits,&out,lane)%pp,av[lane].mul_mod(yv[lane],pp),"two-bit wide product lane{lane}");assert_eq!(getn(&sim.qubits,&a,lane),av[lane]);assert_eq!(getn(&sim.qubits,&ylow,lane),yv[lane]&mask);}
        for q in &resident{assert_eq!(sim.qubits[q.0 as usize],start[q.0 as usize]);}assert_eq!(sim.phase,0);
        sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,start);assert_eq!(sim.phase,0);
        eprintln!("TWO_BIT_WIDE_PRODUCT_NATIVE_PASS cases=64 Q={} T={} N={} inverse=true phase0=true",b.peak,b.tof,b.ops.len());
    }
}
