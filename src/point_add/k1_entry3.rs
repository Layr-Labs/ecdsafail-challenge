//! Repaired K1 N1/N2. Clean-output encoders, not arbitrary-output XOR oracles.
use super::*;

fn active_xor(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    lit(b,controls,target,dirty);
    if let Some((ph,c))=nand {
        let mut off=controls.to_vec();off.extend([(ph,false),(c,false)]);
        lit(b,&off,target,dirty);
    }
}

fn binary(b:&mut B,word:&[QubitId],out:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require(word.len()==128&&out.len()==7,Error::Shape);
    record(b,|b|{
        let mut swaps=Vec::new();
        for j in (0..7).rev() {
            let h=1usize<<j;
            if h>1 {active_xor(b,&[],out[j],nand,dirty);}
            let ctl:Vec<_>=word[h..2*h].iter().map(|&q|(q,h>1)).collect();
            active_xor(b,&ctl,out[j],nand,dirty);
            for i in 0..h {b.cswap(out[j],word[i],word[i+h]);swaps.push((out[j],word[i],word[i+h]));}
        }
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
    })
}

/// The existing TTK ladder with only its sum writes gated by NAND(PH,C).
/// This is the k=7 N2 add, with no carry output and no borrowed clean bit.
fn add(b:&mut B,a:&[QubitId],t:&[QubitId],nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    require(a.len()==7&&t.len()==7,Error::Shape);
    for i in 1..7 {b.cx(a[i],t[i]);}
    for i in (1..6).rev() {b.cx(a[i],a[i+1]);}
    for i in 0..6 {b.ccx(t[i],a[i],a[i+1]);}
    for i in (1..7).rev() {
        active_xor(b,&[(a[i],false)],t[i],nand,dirty);
        b.ccx(t[i-1],a[i-1],a[i]);
    }
    for i in 1..6 {b.cx(a[i],a[i+1]);}
    active_xor(b,&[(a[0],false)],t[0],nand,dirty);
    for i in 1..7 {b.cx(a[i],t[i]);}
}

pub(super) fn entry(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require((ring.len(),q.len(),y.len(),m.len())==(257,128,7,7),Error::Shape);
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(m).copied()
        .chain(nand.into_iter().flat_map(|(p,c)|[p,c])).collect();
    require(ports.iter().copied().collect::<BTreeSet<_>>().len()==ports.len(),Error::Alias);
    require(nand.is_none_or(|(p,c)|!dirty.contains(&p)&&!dirty.contains(&c)),Error::HeldPort);
    record(b,|b|{
        // N1: highest support of real Q and virtual one at address y.
        let mut swaps=Vec::new();
        for j in (0..7).rev() {
            let h=1usize<<j;
            for l in j+1..7 {b.cx(m[l],y[l]);}
            if h>1||nand.is_some() {
                active_xor(b,&[],m[j],nand,dirty);
                let upper:Vec<_>=q[h..2*h].iter().map(|&q|(q,true)).collect();
                active_xor(b,&upper,m[j],nand,dirty);
            } else {active_xor(b,&[(q[1],false)],m[0],nand,dirty);}
            let virtual_one:Vec<_>=q[h..2*h].iter().map(|&q|(q,true))
                .chain(y[j+1..].iter().map(|&q|(q,true))).chain([(y[j],false)]).collect();
            active_xor(b,&virtual_one,m[j],nand,dirty);
            for l in (j+1..7).rev() {b.cx(m[l],y[l]);}
            for i in 0..h {b.cswap(m[j],q[i],q[i+h]);swaps.push((m[j],q[i],q[i+h]));}
        }
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
        // N2: align the reversed physical window by complement(M), erase y.
        for &v in m {b.x(v);}add(b,m,y,nand,dirty);for &v in m {b.x(v);}
        let window:Vec<_>=ring.iter().rev().take(128).copied().collect();
        let rot=record(b,|b|{
            for &v in m {b.x(v);}
            for(k,&v)in m.iter().enumerate() {super::super::super::crot_up(b,v,&window,1usize<<k);}
            for &v in m {b.x(v);}
        });
        b.play(&rot,false);let erase=binary(b,&window,y,nand,dirty);b.play(&erase,true);b.play(&rot,true);
    })
}
