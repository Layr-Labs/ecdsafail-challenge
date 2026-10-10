//! Exact ancilla-free modular addition for a one-lane-short source.
//! For M=2^n,p=M-C and0<=z,a<p, the output is canonical (z+ctl*a)%p.
//! All helpers are borrowed arbitrary states and returned unchanged.
use super::arith::{ttk_add,ttk_carry};
use super::builder::B;
use super::mask::mcx_dirty;
use super::modp_frogdrop::add_const_exact;
use crate::circuit::QubitId;

fn short_less(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,out:QubitId,d:QubitId,e:QubitId){
    let n=a.len();assert_eq!(z.len(),n+1);
    for &q in&z[..n]{b.x(q);}b.x(z[n]);
    for _ in 0..2{
        b.ccx(z[n],d,out);
        ttk_carry(b,a,&z[..n],ctl,d,e);
    }
    b.x(z[n]);for &q in&z[..n]{b.x(q);}
}
/// out^=ctl&[z>=2^n-C] via complemented z<C disjoint constant prefixes.
fn high_interval(b:&mut B,z:&[QubitId],c:u64,ctl:QubitId,out:QubitId,dirty:&[QubitId]){
    for &q in z{b.x(q);}
    for i in(0..z.len().min(64)).rev(){
        if(c>>i)&1==0{continue;}
        let mut controls=vec![ctl];let mut flips=Vec::new();
        for j in i..z.len(){controls.push(z[j]);let want=j!=i&&j<64&&(c>>j)&1!=0;if !want{b.x(z[j]);flips.push(z[j]);}}
        mcx_dirty(b,&controls,out,dirty);
        for &q in flips.iter().rev(){b.x(q);}
    }
    for &q in z{b.x(q);}
}
pub(super) fn short_modadd_canonical(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,
                                    _spare:QubitId,g:QubitId,d:QubitId,e:QubitId,c:u64){
    let n=a.len();assert_eq!(z.len(),n+1);assert!(n>=2);
    // Exact zero-extension add: the target highbit receives low-word carry.
    ttk_add(b,a,&z[..n],Some(ctl),Some((z[n],d)));
    // R1(z)=p+a-1-z modM. Its selected set is [0,a) union[p,M), whose
    // complement[a,p) is invariant under R1. This holds also when a<C.
    for _ in 0..2{
        for &q in z{b.cx(g,q);}
        ttk_add(b,a,&z[..n],Some(g),Some((z[n],d)));
        let mut dirty=a.to_vec();dirty.extend([d,e]);
        b.begin();add_const_exact(b,z,Some(g),c,&dirty);let shift=b.end();b.play(&shift,true);
        short_less(b,z,a,ctl,g,d,e);
        high_interval(b,z,c,ctl,g,a);
    }
    // R2(z)=a-1-z on [0,a), with highbit read-only. The two dirty echoes
    // preserve every helper, and their composition fixes both kinds of wrap.
    for _ in 0..2{
        for &q in&z[..n]{b.cx(g,q);}
        ttk_add(b,a,&z[..n],Some(g),None);
        short_less(b,z,a,ctl,g,d,e);
    }
}

/// Exact canonical doubling. The high selector is repaired before rotation:
/// q=old_high XOR[low>=2^(n-1)-(C-1)/2] = [2z>=p] on canonical inputs.
/// After rotation q occupies bit0, and the exact(C-1) increment excludes it.
pub(super) fn mod_double_canonical(b:&mut B,z:&mut Vec<QubitId>,dirty:&[QubitId],c:u64){
    assert!(c&1==1);
    let n=z.len();let d=(c-1)/2;let h=z[n-1];
    for &q in&z[..n-1]{b.x(q);}
    for i in(0..(n-1).min(64)).rev(){
        if(d>>i)&1==0{continue;}
        let mut controls=Vec::new();let mut flips=Vec::new();
        for j in i..n-1{controls.push(z[j]);let want=j!=i&&j<64&&(d>>j)&1!=0;if !want{b.x(z[j]);flips.push(z[j]);}}
        mcx_dirty(b,&controls,h,dirty);
        for &q in flips.iter().rev(){b.x(q);}
    }
    for &q in&z[..n-1]{b.x(q);}
    let top=z.pop().unwrap();z.insert(0,top);
    add_const_exact(b,z,Some(z[0]),c-1,dirty);
}

#[cfg(test)]
mod tests{
    use super::*;use crate::circuit::{OperationType as K,NO_BIT};
    fn run<'a>(ops:impl IntoIterator<Item=&'a crate::circuit::Op>,mut q:Vec<u64>)->Vec<u64>{for op in ops{assert_eq!(op.c_condition,NO_BIT);let t=op.q_target.0 as usize;let a=op.q_control1.0 as usize;let c=op.q_control2.0 as usize;match op.kind{K::X=>q[t]^=u64::MAX,K::CX=>q[t]^=q[a],K::CCX=>q[t]^=q[a]&q[c],K::Swap=>q.swap(t,a),_=>panic!("unexpected {:?}",op.kind)}}q}
    fn put(q:&mut[u64],ports:&[QubitId],lane:usize,x:u64){for(i,k)in ports.iter().enumerate(){if(x>>i)&1!=0{q[k.0 as usize]|=1u64<<lane;}}}
    fn get(q:&[u64],ports:&[QubitId],lane:usize)->u64{ports.iter().enumerate().map(|(i,k)|((q[k.0 as usize]>>lane)&1)<<i).sum()}
    #[test]
    fn exact_canonical_double_all_small_inputs_and_dirty(){
        let mut cases=0;
        for n in 4..=10{for c in[1,3,5,7,9,11,13,15].into_iter().filter(|&c|c<(1u64<<(n-1))){
            let p=(1u64<<n)-c;let mut b=B::new();let z=b.alloc_n(n);let dirty=b.alloc_n(n);let mut out=z.clone();mod_double_canonical(&mut b,&mut out,&dirty,c);
            let count=p as usize*64;
            for first in(0..count).step_by(64){let mut start=vec![0;b.width()as usize];for lane in 0..64.min(count-first){let code=first+lane;put(&mut start,&z,lane,(code/64)as u64);put(&mut start,&dirty,lane,(code%64)as u64);}
                let end=run(b.ops.iter(),start.clone());for lane in 0..64.min(count-first){assert_eq!(get(&end,&out,lane),(2*((first+lane)/64)as u64)%p,"double n{n} c{c}");}for q in&dirty{assert_eq!(end[q.0 as usize],start[q.0 as usize]);}assert_eq!(run(b.ops.iter().rev(),end),start);cases+=64.min(count-first);
            }
        }}
        eprintln!("CANONICAL_DOUBLE_EXHAUSTIVE_PASS cases={cases} inverse=true dirty_restored=true");
    }
    #[test]
    fn canonical_double_wide_native_boundary_and_dirty(){
        use super::super::frogdrop_sched::{N,p};use super::super::tests_frogdrop::Rng;
        use crate::sim::Simulator;use sha3::digest::{ExtendableOutput,Update};
        let pp=p();let c=super::super::modp_frogdrop::C;let mut values=Vec::new();
        for center in[N::ZERO,N::from(c),pp/N::from(2u64),N::from(1u64)<<255,pp-N::from(1u64)]{
            for delta in -64i64..=64{if delta<0&&center<N::from((-delta)as u64){continue;}let z=if delta<0{center-N::from((-delta)as u64)}else{center+N::from(delta as u64)};if z<pp{values.push(z);}}
        }
        let mut rng=Rng::new(0x256772);for _ in 0..512{values.push(rng.below(256)%pp);}values.sort();values.dedup();
        let mut b=B::new();let z=b.alloc_n(256);let dirty=b.alloc_n(254);let mut out=z.clone();mod_double_canonical(&mut b,&mut out,&dirty,c);
        let putn=|q:&mut[u64],ports:&[QubitId],lane:usize,x:N|{for(i,k)in ports.iter().enumerate(){if x.bit(i){q[k.0 as usize]|=1u64<<lane;}}};
        let getn=|q:&[u64],ports:&[QubitId],lane:usize|{let mut x=N::ZERO;for(i,k)in ports.iter().enumerate(){if(q[k.0 as usize]>>lane)&1!=0{x|=N::from(1u64)<<i;}}x};
        for batch in values.chunks(64){let mut h=sha3::Shake256::default();h.update(b"canonical-double-wide-v1");let mut xof=h.finalize_xof();let mut sim=Simulator::new(b.width()as usize,1,&mut xof);
            for(lane,&zv)in batch.iter().enumerate(){putn(&mut sim.qubits,&z,lane,zv);putn(&mut sim.qubits,&dirty,lane,rng.below(254));}
            let start=sim.qubits.clone();sim.apply_iter(b.ops.iter());for(lane,&zv)in batch.iter().enumerate(){assert_eq!(getn(&sim.qubits,&out,lane),(zv+zv)%pp,"wide double z={zv}");}
            for q in&dirty{assert_eq!(sim.qubits[q.0 as usize],start[q.0 as usize]);}assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,start);assert_eq!(sim.phase,0);
        }
        eprintln!("CANONICAL_DOUBLE_WIDE_NATIVE_PASS cases={} T={} N={} inverse=true dirty_restored=true phase0=true",values.len(),b.tof,b.ops.len());
    }
}
