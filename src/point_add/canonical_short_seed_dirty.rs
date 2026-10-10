//! Exact ancilla-free modular addition for a one-lane-short source.
//! For M=2^n,p=M-C and0<=z,a<p, the output is canonical (z+ctl*a)%p.
//! All helpers are borrowed arbitrary states and returned unchanged.
use super::arith::{ttk_add,ttk_carry};
use super::builder::B;
use super::mask::mcx_dirty;
use super::modp_frogdrop::add_const_exact;
use crate::circuit::QubitId;

/// Exact small-constant predicate on every raw target state. A shared high-zero
/// prefix is factored through one arbitrary dirty lane; its incoming value
/// cancels between two low-word predicates, and every borrow is restored.
pub(super) fn xor_lt_small(b:&mut B,z:&[QubitId],c:u64,ctl:Option<QubitId>,out:QubitId,dirty:&[QubitId]){
    if c==0{return;}
    let low=(u64::BITS-c.leading_zeros())as usize;
    assert!(low<=z.len());
    fn direct(b:&mut B,z:&[QubitId],c:u64,ctl:Option<QubitId>,out:QubitId,d:&[QubitId]){
        for i in(0..z.len().min(64)).rev(){if(c>>i)&1==0{continue;}
            let mut cs=Vec::new();if let Some(q)=ctl{cs.push(q);}let mut flips=Vec::new();
            for j in i..z.len(){cs.push(z[j]);let want=j!=i&&j<64&&(c>>j)&1!=0;if !want{b.x(z[j]);flips.push(z[j]);}}
            mcx_dirty(b,&cs,out,d);for &q in flips.iter().rev(){b.x(q);}
        }
    }
    let hi_controls=z.len()-low+usize::from(ctl.is_some());
    let needed=hi_controls.saturating_sub(2).max(low.saturating_sub(1));
    if low==z.len()||dirty.len()<needed+1{direct(b,z,c,ctl,out,dirty);return;}
    let flag=dirty[0];let bank=&dirty[1..];
    for _ in 0..2{
        direct(b,&z[..low],c,Some(flag),out,bank);
        let mut cs=Vec::new();if let Some(q)=ctl{cs.push(q);}
        for &q in&z[low..]{b.x(q);cs.push(q);}mcx_dirty(b,&cs,flag,bank);
        for &q in&z[low..]{b.x(q);}
    }
}

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
    xor_lt_small(b,z,c,Some(ctl),out,dirty);
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
    xor_lt_small(b,&z[..n-1],d,None,h,dirty);
    for &q in&z[..n-1]{b.x(q);}
    let top=z.pop().unwrap();z.insert(0,top);
    add_const_exact(b,z,Some(z[0]),c-1,dirty);
}

