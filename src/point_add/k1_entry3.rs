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
    add_n(b,a,t,nand,dirty);
}
fn add_n(b:&mut B,a:&[QubitId],t:&[QubitId],nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    let n=t.len();require(a.len()==n&&n>=2,Error::Shape);
    for i in 1..n {b.cx(a[i],t[i]);}
    for i in (1..n-1).rev() {b.cx(a[i],a[i+1]);}
    for i in 0..n-1 {b.ccx(t[i],a[i],a[i+1]);}
    for i in (1..n).rev() {
        active_xor(b,&[(a[i],false)],t[i],nand,dirty);
        b.ccx(t[i-1],a[i-1],a[i]);
    }
    for i in 1..n-1 {b.cx(a[i],a[i+1]);}
    active_xor(b,&[(a[0],false)],t[0],nand,dirty);
    for i in 1..n {b.cx(a[i],t[i]);}
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

// Six-bit TTK sum with a seventh carry target. The addend is restored.
fn add_carry(b:&mut B,a:&[QubitId],t:&[QubitId],z:QubitId,
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    require(a.len()==6&&t.len()==6,Error::Shape);
    for i in 1..6 {b.cx(a[i],t[i]);}
    active_xor(b,&[(a[5],false)],z,nand,dirty);
    for i in (1..5).rev() {b.cx(a[i],a[i+1]);}
    for i in 0..5 {b.ccx(t[i],a[i],a[i+1]);}
    active_xor(b,&[(t[5],false),(a[5],false)],z,nand,dirty);
    for i in (1..6).rev() {
        active_xor(b,&[(a[i],false)],t[i],nand,dirty);
        b.ccx(t[i-1],a[i-1],a[i]);
    }
    for i in 1..5 {b.cx(a[i],a[i+1]);}
    active_xor(b,&[(a[0],false)],t[0],nand,dirty);
    for i in 1..6 {b.cx(a[i],t[i]);}
}
#[cfg(test)]
pub(super) fn diagnostic_add_carry(b:&mut B,a:&[QubitId],t:&[QubitId],z:QubitId,
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    record(b,|b|add_carry(b,a,t,z,nand,dirty))
}

fn binary_v(b:&mut B,word:&[QubitId],out:&[QubitId],qa:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require(word.len()==128&&out.len()==7&&qa.len()==32,Error::Shape);
    record(b,|b|{
        // Forward A then B; the played inverse runs B then A.
        active_xor(b,&[(out[5],false)],out[6],nand,dirty);
        let mut a=vec![(out[5],false)];a.extend(word[64..].iter().map(|&v|(v,true)));
        active_xor(b,&a,out[6],nand,dirty);
        active_xor(b,&[],out[5],nand,dirty);
        active_xor(b,&qa.iter().map(|&v|(v,true)).collect::<Vec<_>>(),out[5],nand,dirty);
        let mut swaps=Vec::new();
        for i in 0..64 {b.cswap(out[6],word[i],word[i+64]);swaps.push((out[6],word[i],word[i+64]));}
        for j in (0..6).rev() {
            let h=1usize<<j;
            if h>1 {active_xor(b,&[],out[j],nand,dirty);}
            let ctl:Vec<_>=word[h..2*h].iter().map(|&v|(v,h>1)).collect();
            active_xor(b,&ctl,out[j],nand,dirty);
            for i in 0..h {b.cswap(out[j],word[i],word[i+h]);swaps.push((out[j],word[i],word[i+h]));}
        }
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
    })
}

// dM6ea entry: the high M bit is virtual in Q[64..96), then held on y5.
// The caller runs en_a followed by en_b and reverses the combined tape at exit.
pub(super) fn entry_v(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->(Vec<G>,Vec<G>) {
    require((ring.len(),q.len(),y.len(),m.len())==(257,128,7,6),Error::Shape);
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(m).copied()
        .chain(nand.into_iter().flat_map(|(p,c)|[p,c])).collect();
    require(ports.iter().copied().collect::<BTreeSet<_>>().len()==ports.len(),Error::Alias);
    require(nand.is_none_or(|(p,c)|!dirty.contains(&p)&&!dirty.contains(&c)),Error::HeldPort);
    let qa=&q[64..96];
    let mut sw6=Vec::new();
    let en_a=record(b,|b|{
        // N1 j=6, with the two OR terms merged on initially clean S0.
        active_xor(b,&[],m[0],nand,dirty);
        let mut ctl:Vec<_>=q[64..128].iter().map(|&v|(v,true)).collect();ctl.push((y[6],true));
        active_xor(b,&ctl,m[0],nand,dirty);
        for i in 0..64 {b.cswap(m[0],q[i],q[i+64]);sw6.push((q[i],q[i+64]));}
        b.cx(m[0],y[6]);
        active_xor(b,&[],m[0],nand,dirty);
        active_xor(b,&qa.iter().map(|&v|(v,true)).collect::<Vec<_>>(),m[0],nand,dirty);
        let mut swaps=Vec::new();
        for j in (0..6).rev() {
            let h=1usize<<j;
            for l in j+1..6 {b.cx(m[l],y[l]);}
            if h>1||nand.is_some() {
                active_xor(b,&[],m[j],nand,dirty);
                active_xor(b,&q[h..2*h].iter().map(|&v|(v,true)).collect::<Vec<_>>(),m[j],nand,dirty);
            }else{active_xor(b,&[(q[1],false)],m[0],nand,dirty);}
            let virtual_one:Vec<_>=q[h..2*h].iter().map(|&v|(v,true))
                .chain(y[j+1..].iter().map(|&v|(v,true))).chain([(y[j],false)]).collect();
            active_xor(b,&virtual_one,m[j],nand,dirty);
            for l in (j+1..6).rev() {b.cx(m[l],y[l]);}
            for i in 0..h {b.cswap(m[j],q[i],q[i+h]);swaps.push((m[j],q[i],q[i+h]));}
        }
        active_xor(b,&[],y[6],nand,dirty);
        active_xor(b,&qa.iter().map(|&v|(v,true)).collect::<Vec<_>>(),y[6],nand,dirty);
        for &v in m {b.x(v);}add_carry(b,m,&y[..6],y[6],nand,dirty);for &v in m {b.x(v);}
        let window:Vec<_>=ring.iter().rev().take(128).copied().collect();
        let rot=record(b,|b|{
            for &v in m {b.x(v);}
            for(k,&v) in m.iter().enumerate() {super::super::super::crot_up(b,v,&window,1usize<<k);}
            for &v in m {b.x(v);}
        });
        b.play(&rot,false);let erase=binary_v(b,&window,y,qa,nand,dirty);b.play(&erase,true);b.play(&rot,true);
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
    });
    let en_b=record(b,|b|for &(a,z) in sw6.iter().rev(){b.cswap(y[5],a,z);});
    (en_a,en_b)
}

fn pad_add_entry(b:&mut B,a:&[QubitId],t:&[QubitId],pad:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    require(a.len()==5&&t.len()==7&&pad.len()==2,Error::Shape);
    let mut ap=a.to_vec();ap.extend_from_slice(pad);
    add_n(b,&ap,t,nand,dirty);
    let sub=record(b,|b|add_n(b,pad,&t[5..],nand,dirty));b.play(&sub,true);
}
fn ql4_rot_stage(b:&mut B,ctl:QubitId,window:&[QubitId],j:usize) {
    b.x(ctl);super::super::super::crot_up(b,ctl,window,1usize<<j);b.x(ctl);
}
fn ql4_dbracket(b:&mut B,ph:QubitId,tag:QubitId,y5:QubitId,d:QubitId,dirty:&[QubitId]) {
    b.cx(d,y5);lit(b,&[(ph,false),(tag,false),(y5,false)],d,dirty);b.cx(d,y5);
}

// dM6eb E1-E17. The active interface is [S0..S4,cut,y5] = M;
// on Native DONE the two D-brackets make the tape the identity.
pub(super) fn entry_ql4(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require((ring.len(),q.len(),y.len(),m.len())==(257,128,7,6),Error::Shape);
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(m).copied()
        .chain(nand.into_iter().flat_map(|(p,c)|[p,c])).collect();
    require(ports.iter().copied().collect::<BTreeSet<_>>().len()==ports.len(),Error::Alias);
    require(nand.is_none_or(|(p,c)|!dirty.contains(&p)&&!dirty.contains(&c)),Error::HeldPort);
    let (a,bb,c,d)=(q[120],q[119],q[63],q[118]);let cut=m[5];
    let window:Vec<_>=ring.iter().rev().take(128).copied().collect();
    record(b,|b|{
        let mut swaps=Vec::new();
        // E1-E6: N1 stages 6..1, each followed by its early rotation.
        for j in (1..7).rev(){
            let h=1usize<<j;let home=if j==6{m[0]}else{m[j]};
            for l in j+1..7 {b.cx(if l==6{m[0]}else{m[l]},y[l]);}
            active_xor(b,&[],home,nand,dirty);
            active_xor(b,&q[h..2*h].iter().map(|&v|(v,true)).collect::<Vec<_>>(),home,nand,dirty);
            let vo:Vec<_>=q[h..2*h].iter().map(|&v|(v,true))
                .chain(y[j+1..].iter().map(|&v|(v,true))).chain([(y[j],false)]).collect();
            active_xor(b,&vo,home,nand,dirty);
            for l in (j+1..7).rev(){b.cx(if l==6{m[0]}else{m[l]},y[l]);}
            for i in 0..h {b.cswap(home,q[i],q[i+h]);swaps.push((j,q[i],q[i+h]));}
            ql4_rot_stage(b,home,&window,j);
        }
        // E7: pre-add the high two bits before the j=0 virtual-one test.
        active_xor(b,&[(y[5],false),(cut,true)],y[6],nand,dirty);
        active_xor(b,&[(cut,true)],y[5],nand,dirty);
        active_xor(b,&[(m[0],true)],y[6],nand,dirty);
        // E8: injective fold into the two light M6 lanes and one light M5 lane.
        b.cswap(m[0],cut,a);b.cswap(m[0],bb,c);
        lit(b,&[(m[0],false),(a,true)],bb,dirty);
        b.cx(a,m[0]);lit(b,&[(a,true),(bb,false)],m[0],dirty);
        // E9-E10: N1 j=0, with positive high-y tests, then rotation 0.
        for l in 1..5{b.cx(m[l],y[l]);}
        if nand.is_some(){active_xor(b,&[],m[0],nand,dirty);
            active_xor(b,&[(q[1],true)],m[0],nand,dirty);
        }else{active_xor(b,&[(q[1],false)],m[0],nand,dirty);}
        let vo:Vec<_>=std::iter::once((q[1],true))
            .chain(y[1..5].iter().map(|&v|(v,true)))
            .chain([(y[5],false),(y[6],false),(y[0],false)]).collect();
        active_xor(b,&vo,m[0],nand,dirty);
        for l in (1..5).rev(){b.cx(m[l],y[l]);}
        b.cswap(m[0],q[0],q[1]);swaps.push((0,q[0],q[1]));
        ql4_rot_stage(b,m[0],&window,0);
        // E11-E12: low five-bit padded add, then the inherited erase.
        for &v in &m[..5]{b.x(v);}pad_add_entry(b,&m[..5],y,&ring[..2],nand,dirty);
        for &v in &m[..5]{b.x(v);}
        let erase=binary(b,&window,y,nand,dirty);b.play(&erase,true);
        // E13: park arbitrary DONE E5 during ungated fold and undo.
        if let Some((ph,tag))=nand{ql4_dbracket(b,ph,tag,y[5],d,dirty);}
        // E14: fold out, leaving M6 on y5 and restoring the light bands.
        b.cx(a,y[5]);lit(b,&[(a,true),(bb,false)],y[5],dirty);
        lit(b,&[(y[5],false),(a,true)],bb,dirty);
        b.cswap(y[5],bb,c);b.cswap(y[5],cut,a);
        // E15-E16: restore Q, then undo all early rotations.
        for &(j,u,v) in swaps.iter().rev(){let ctl=if j==6{y[5]}else{m[j]};b.cswap(ctl,u,v);}
        let mut mm=m.to_vec();mm.push(y[5]);
        let rot=record(b,|b|{
            for &v in &mm{b.x(v);}
            for(j,&v) in mm.iter().enumerate(){super::super::super::crot_up(b,v,&window,1usize<<j);}
            for &v in &mm{b.x(v);}
        });b.play(&rot,true);
        // E17: return the DONE E5 from Q118.
        if let Some((ph,tag))=nand{ql4_dbracket(b,ph,tag,y[5],d,dirty);}
    })
}

// Public-box fold for Plain c41-81.  At entry S=0, C=>M>=97, and
// C=0=>M>=32.  During N1, C is parked in S0.  The resulting (cut,tag)
// code is (M5^C,M6^C); its excluded 00 word represents C=1.
fn not_m5(cut:QubitId,tag:QubitId)->[(QubitId,bool);2] {[(cut,true),(tag,false)]}
fn not_m6(cut:QubitId,tag:QubitId)->[(QubitId,bool);2] {[(tag,true),(cut,false)]}
fn xor_decoded(b:&mut B,not:&[(QubitId,bool);2],target:QubitId,dirty:&[QubitId]) {
    b.x(target);lit(b,not,target,dirty);
}
fn rot_decoded(b:&mut B,window:&[QubitId],step:usize,not:&[(QubitId,bool);2],dirty:&[QubitId]) {
    let n=window.len();let mut a=n;let mut z=step%n;
    while z!=0 {let r=a%z;a=z;z=r;}
    for s in 0..a {
        let len=n/a;
        let cyc:Vec<_>=(0..len).map(|k|(s+k*step)%n).collect();
        for k in (1..len).rev() {
            let x=window[cyc[k]];let y=window[cyc[k-1]];
            swap(b,not,x,y,None,dirty);
        }
    }
}
pub(super) fn entry_m6fold(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    dirty:&[QubitId])->Vec<G> {
    require((ring.len(),q.len(),y.len(),m.len())==(257,128,7,7),Error::Shape);
    let cut=m[5];let tag=m[6];let nm5=not_m5(cut,tag);let nm6=not_m6(cut,tag);
    record(b,|b|{
        b.swap(tag,m[0]); // C moves into the initially zero S0.
        let mut swaps:Vec<Vec<G>>=Vec::new();
        for j in (1..7).rev() {
            let h=1usize<<j;
            for l in j+1..7 {b.cx(m[l],y[l]);}
            active_xor(b,&[],m[j],None,dirty);
            let upper:Vec<_>=q[h..2*h].iter().map(|&q|(q,true)).collect();
            active_xor(b,&upper,m[j],None,dirty);
            let virtual_one:Vec<_>=q[h..2*h].iter().map(|&q|(q,true))
                .chain(y[j+1..].iter().map(|&q|(q,true))).chain([(y[j],false)]).collect();
            active_xor(b,&virtual_one,m[j],None,dirty);
            for l in (j+1..7).rev() {b.cx(m[l],y[l]);}
            let sw=record(b,|b|for i in 0..h {b.cswap(m[j],q[i],q[i+h]);});
            b.play(&sw,false);swaps.push(sw);
        }
        b.cx(m[0],cut);b.cx(m[0],tag);
        lit(b,&[(cut,true),(tag,true)],m[0],dirty); // folded S0 returns zero
        for l in 1..5 {b.cx(m[l],y[l]);}
        xor_decoded(b,&nm5,y[5],dirty);xor_decoded(b,&nm6,y[6],dirty);
        let virtual_one:Vec<_>=std::iter::once((q[1],true))
            .chain(y[1..].iter().map(|&v|(v,true))).chain([(y[0],false)]).collect();
        active_xor(b,&[(q[1],false)],m[0],None,dirty);
        active_xor(b,&virtual_one,m[0],None,dirty);
        for l in (1..5).rev() {b.cx(m[l],y[l]);}
        xor_decoded(b,&nm5,y[5],dirty);xor_decoded(b,&nm6,y[6],dirty);
        let sw0=record(b,|b|b.cswap(m[0],q[0],q[1]));b.play(&sw0,false);swaps.push(sw0);
        for (j,sw) in swaps.iter().rev().enumerate() {
            if j<5 {b.play(sw,true);}else{
                let h=1usize<<j;let not=if j==5{&nm5}else{&nm6};
                for i in (0..h).rev() {b.swap(q[i],q[i+h]);swap(b,not,q[i],q[i+h],None,dirty);}
            }
        }
        // E + ~M = E - M - 1.  Subtract low five M bits, then correct
        // the high bits with the decoded folded controls.
        let sub=pad::pad_add_f(b,&m[..5],y,&ring[..2],&Enable::One,&[],
            Exclusions{held:&[],forbidden:&[]}).expect("fold N2 pad add");
        b.play(&sub,true);
        lit(b,&[(y[5],true)],y[6],dirty);
        lit(b,&[(cut,true),(tag,false),(y[5],true)],y[6],dirty);
        xor_decoded(b,&nm5,y[5],dirty);xor_decoded(b,&nm6,y[6],dirty);
        super::super::super::super::modp_frogdrop::add_const_exact(b,y,None,127,dirty);
        let window:Vec<_>=ring.iter().rev().take(128).copied().collect();
        let rot=record(b,|b|{
            for k in 0..5 {b.x(m[k]);super::super::super::crot_up(b,m[k],&window,1usize<<k);b.x(m[k]);}
            rot_decoded(b,&window,32,&nm5,dirty);
            rot_decoded(b,&window,64,&nm6,dirty);
        });
        b.play(&rot,false);let erase=binary(b,&window,y,None,dirty);b.play(&erase,true);b.play(&rot,true);
        xor_decoded(b,&nm6,y[5],dirty);b.cx(y[5],tag);b.cx(tag,cut);
    })
}
