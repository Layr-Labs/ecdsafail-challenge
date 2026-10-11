//! Exact canonical arithmetic with one explicit clean carry flag.
//! For M=2^n,p=M-C and0<=z,a<p, the output is canonical (z+ctl*a)%p.
//! The clean flag starts and ends zero; all other helpers are arbitrary and restored.
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
/// Zero-extended source add with exact full-width carry into clean.
/// The original target high is retained until both low-carry hooks have fired.
fn short_add_carry(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,clean:QubitId,d:QubitId,e:QubitId){
 let n=a.len();assert_eq!(z.len(),n+1);
 for i in 1..n{b.cx(a[i],z[i]);}
 mcx_dirty(b,&[ctl,z[n],a[n-1]],clean,&[d]);
 for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
 for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}
 mcx_dirty(b,&[ctl,z[n],z[n-1],a[n-1]],clean,&[d,e]);
 mcx_dirty(b,&[ctl,z[n-1],a[n-1]],z[n],&[d]);
 for i in(1..n).rev(){b.ccx(ctl,a[i],z[i]);b.ccx(z[i-1],a[i-1],a[i]);}
 for i in 1..n-1{b.cx(a[i],a[i+1]);}b.ccx(ctl,a[0],z[0]);
 for i in 1..n{b.cx(a[i],z[i]);}b.ccx(ctl,a[n-1],z[n]);
}
/// Canonical add with one actual clean carry flag, arbitrary restored d/e.
pub(super) fn short_modadd_canonical(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,
                                    _spare:QubitId,g:QubitId,d:QubitId,e:QubitId,c:u64){
    short_add_carry(b,z,a,ctl,g,d,e);
    high_interval(b,z,c,ctl,g,a);
    let mut dirty=a.to_vec();dirty.extend([d,e]);
    add_const_exact(b,z,Some(g),c,&dirty);
    short_less(b,z,a,ctl,g,d,e);
}

/// Exact t += ctl*c modulo2^n with one clean carry. Strip trailing zeros,
/// split at the highest constant bit, and pay/erase the carry from the low word.
pub(super) fn add_small_clean(b:&mut B,t:&[QubitId],ctl:QubitId,c:u64,clean:QubitId,dirty:&[QubitId]){
    if c==0{return;}let shift=c.trailing_zeros()as usize;
    if shift>=t.len(){return;}let z=&t[shift..];let k=c>>shift;
    let l=(u64::BITS-k.leading_zeros())as usize;
    if l>=z.len(){add_const_exact(b,z,Some(ctl),k,dirty);return;}
    for &q in &z[..l]{b.x(q);}xor_lt_small(b,&z[..l],k,Some(ctl),clean,dirty);for &q in &z[..l]{b.x(q);}
    add_const_exact(b,&z[..l],Some(ctl),k,dirty);
    let mut high=vec![clean];high.extend_from_slice(&z[l..]);
    super::modp_frogdrop::inc_dirty_free(b,&high,dirty);b.x(clean);
    xor_lt_small(b,&z[..l],k,Some(ctl),clean,dirty);
}
/// Shared prefix through an actual clean flag, restored before return.
fn xor_lt_small_clean(b:&mut B,z:&[QubitId],c:u64,out:QubitId,clean:QubitId,dirty:&[QubitId]){
    if c==0{return;}let low=(u64::BITS-c.leading_zeros())as usize;
    if low>=z.len(){xor_lt_small(b,z,c,None,out,dirty);return;}
    for &q in &z[low..]{b.x(q);}mcx_dirty(b,&z[low..],clean,dirty);for &q in &z[low..]{b.x(q);}
    xor_lt_small(b,&z[..low],c,Some(clean),out,dirty);
    for &q in &z[low..]{b.x(q);}mcx_dirty(b,&z[low..],clean,dirty);for &q in &z[low..]{b.x(q);}
}
/// Exact canonical doubling. The high selector is repaired before rotation:
/// q=old_high XOR[low>=2^(n-1)-(C-1)/2] = [2z>=p] on canonical inputs.
/// After rotation q occupies bit0, and the exact(C-1) increment excludes it.
pub(super) fn mod_double_canonical(b:&mut B,z:&mut Vec<QubitId>,dirty:&[QubitId],c:u64,clean:QubitId){
    assert!(c&1==1);
    let n=z.len();let d=(c-1)/2;let h=z[n-1];
    for &q in&z[..n-1]{b.x(q);}
    xor_lt_small_clean(b,&z[..n-1],d,h,clean,dirty);
    for &q in&z[..n-1]{b.x(q);}
    let top=z.pop().unwrap();z.insert(0,top);
    add_small_clean(b,z,z[0],c-1,clean,dirty);
}

