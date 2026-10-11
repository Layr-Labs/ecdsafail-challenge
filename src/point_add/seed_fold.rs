//! Exact ancilla-free modular addition for a one-lane-short source.
//! For M=2^n,p=M-C and0<=z,a<p, the output is canonical (z+ctl*a)%p.
//! All helpers are borrowed arbitrary states and returned unchanged.
use super::arith::ttk_add;
use super::builder::B;
use super::mask::mcx_dirty;
use super::modp_frogdrop::add_const_exact;
use crate::circuit::QubitId;

/// Exact small-constant predicate on every raw target state. A shared high-zero
/// prefix is factored through one arbitrary dirty lane; its incoming value
/// cancels between two low-word predicates, and every borrow is restored.
pub(super) fn xor_lt_small(b:&mut B,z:&[QubitId],c:u64,ctl:Option<QubitId>,out:QubitId,dirty:&[QubitId]){
    super::canonical_short_clean::xor_lt_small(b,z,c,ctl,out,dirty);
}

fn short_less(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,out:QubitId,d:QubitId,e:QubitId){
    let n=a.len();assert_eq!(z.len(),n+1);
    for &q in&z[..n]{b.x(q);}b.x(z[n]);
    // One shared carry ladder computes the exact product of both enables.
    // This replaces the dirty masked echo around two complete carry ladders.
    b.begin();for i in 1..n{b.cx(a[i],z[i]);}let s1=b.end();b.play(&s1,false);
    mcx_dirty(b,&[ctl,z[n],a[n-1]],out,&[d]);
    b.begin();for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
    for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}let s23=b.end();b.play(&s23,false);
    mcx_dirty(b,&[ctl,z[n],z[n-1],a[n-1]],out,&[d,e]);
    b.play(&s23,true);b.play(&s1,true);
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
        b.begin();add_const_split(b,z,g,c,&dirty);let shift=b.end();b.play(&shift,true);
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


/// Exact raw-state t += ctl*c mod2^n using one arbitrary dirty carry loan.
/// Two high increments separated by controlled complements cancel the loan's
/// incoming value. The post-low carry predicate is erased before low/ctl change.
pub(super) fn add_const_split(b:&mut B,t:&[QubitId],ctl:QubitId,c:u64,dirty:&[QubitId]){
 if c==0{return;}
 let l=(u64::BITS-c.leading_zeros())as usize;
 if l>=t.len(){add_const_exact(b,t,Some(ctl),c,dirty);return;}
 let d=dirty[0];let bank=&dirty[1..];let low=&t[..l];let high=&t[l..];
 let mut increment=vec![d];increment.extend_from_slice(high);
 super::modp_frogdrop::inc_dirty_free(b,&increment,bank);b.x(d);
 for &q in high{b.cx(d,q);}
 add_const_exact(b,low,Some(ctl),c,bank);
 super::canonical_short_clean::xor_lt_small(b,low,c,Some(ctl),d,bank);
 super::modp_frogdrop::inc_dirty_free(b,&increment,bank);b.x(d);
 super::canonical_short_clean::xor_lt_small(b,low,c,Some(ctl),d,bank);
 for &q in high{b.cx(d,q);}
}
