//! Known-output addition, including zero-extended sources, with two carry wires.
use super::Builder;
use crate::circuit::QubitId;
pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,out:&[(bool,Vec<QubitId>)]) {
    let n=b.len();assert!(n>=1&&a.len()<=n);assert_eq!(out.len(),n);
    assert!(a.iter().all(|q|!b.contains(q)));
    assert!(cin.is_none_or(|q|!b.contains(&q)));
    assert!(out.iter().all(|(_,qs)|qs.iter().all(|q|!b.contains(q))));
    let mut outgoing=None;
    for i in(0..n).rev(){
        let incoming=if i==0{cin}else{
            let p=c.alloc_qubit();if let Some(&ai)=a.get(i){c.cx(ai,p);}c.cx(b[i],p);
            if out[i].0{c.x(p);}for &q in &out[i].1{c.cx(q,p);}Some(p)
        };
        if let Some(&ai)=a.get(i){c.cx(ai,b[i]);}if let Some(p)=incoming{c.cx(p,b[i]);}
        if let Some(q)=outgoing{
            let m=c.alloc_bit();c.hmr(q,m);
            // carry_out = a*s + a + a*p + s*p + p in GF(2).
            if let Some(&ai)=a.get(i){c.cz_if(ai,b[i],m);c.z_if(ai,m);if let Some(p)=incoming{c.cz_if(ai,p,m);}}
            if let Some(p)=incoming{c.cz_if(b[i],p,m);c.z_if(p,m);}
            c.free_bit(m);c.free(q);
        }
        outgoing=if i>0{incoming}else{None};
    }
    assert!(outgoing.is_none());
}
