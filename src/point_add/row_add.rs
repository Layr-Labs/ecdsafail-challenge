use super::builder::B;
use crate::circuit::QubitId;

#[derive(Clone,Debug)]
pub struct Row {
    pub g:QubitId,pub t:Vec<QubitId>,pub s:Vec<QubitId>,pub tail:Vec<QubitId>,
    pub c0:QubitId,pub h:QubitId,pub bank:Vec<QubitId>,pub dirty:Vec<QubitId>,pub chunk:usize,
}
fn tail_cost(tail:usize,k:usize)->usize {
    if tail==0{return 0;}
    let k=k.min(tail-1);let suffix=tail-k;
    k+if suffix==1{0}else{4*suffix}+1
}
pub fn model(n:usize,tail:usize,bank:usize,chunk:usize)->(usize,usize,usize) {
    let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(tail>0);
    let last=n-(blocks-1)*chunk;
    let comparison=if tail>0{n-blocks}else{n-last-(blocks-1)};
    let sum=2*n-usize::from(tail==0);
    let tc=tail_cost(tail,bank-flags);
    (sum+tc,comparison,flags)
}
pub fn choose(b:&mut B,g:QubitId,t:&[QubitId],s:&[QubitId],tail:&[QubitId],c0:QubitId,h:QubitId,
    bank:&[QubitId],dirty:&[QubitId],old_anc:usize,old_and:usize)->bool {
    let mut extra_bank=bank.to_vec();if !tail.is_empty(){assert!(!bank.contains(&h));extra_bank.push(h);}let bank=&extra_bank;
    let n=t.len();let old=3*n-old_and.min(n)+tail_cost(tail.len(),old_anc);
    let mut best=None;
    for chunk in 1..=n {
        let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(!tail.is_empty());
        if flags+chunk.saturating_sub(1)>bank.len(){continue;}
        let (u,c,_)=model(n,tail.len(),bank.len(),chunk);let expected2=2*u+c;
        if expected2<2*old && best.as_ref().is_none_or(|&(cost,_)|expected2<cost){best=Some((expected2,chunk));}
    }
    if let Some((_,chunk))=best {
        b.row_add(Row{g,t:t.to_vec(),s:s.to_vec(),tail:tail.to_vec(),c0,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});true
    } else {false}
}

fn block(b:&mut B,g:QubitId,t:&[QubitId],s:&[QubitId],incoming:QubitId,flag:Option<QubitId>,work:&[QubitId]) {
    let n=t.len();assert!(n>=1&&s.len()==n&&work.len()>=n-1);
    for i in 0..n {
        let prev=if i==0{incoming}else{work[i-1]};
        b.cx(prev,t[i]);b.cx(prev,s[i]);
        let next=if i+1<n{Some(work[i])}else{flag};
        if let Some(next)=next {b.and_c(t[i],s[i],next);b.cx(prev,next);}
    }
    for i in (0..n).rev() {
        let prev=if i==0{incoming}else{work[i-1]};
        if i+1<n {b.cx(prev,work[i]);b.and_u(t[i],s[i],work[i]);}
        b.cx(prev,t[i]);b.ccx(g,s[i],t[i]);b.cx(prev,s[i]);
    }
}

// Exact full-width overflow phase carry(u + v + incoming). Equivalently,
// this is the predicate ~u < v + incoming. The incoming wire is restored.
fn cmp_phase(b:&mut B,u:&[QubitId],v:&[QubitId],incoming:QubitId,work:&[QubitId]) {
    let n=u.len();assert!(n==v.len()&&work.len()>=n-1);
    if n==1 {
        b.cz(u[0],v[0]);b.cz(u[0],incoming);b.cz(v[0],incoming);
    }else{
        b.cx(u[0],v[0]);b.cx(u[0],incoming);
        b.and_c(incoming,v[0],work[0]);b.cx(work[0],u[0]);
        for i in 1..n-1 {
            b.cx(u[i],v[i]);b.cx(u[i],u[i-1]);b.and_c(u[i-1],v[i],work[i]);b.cx(work[i],u[i]);
        }
        b.cz(u[n-1],v[n-1]);b.cz(u[n-1],u[n-2]);b.cz(v[n-1],u[n-2]);
        for i in (1..n-1).rev() {
            b.cx(work[i],u[i]);b.and_u(u[i-1],v[i],work[i]);b.cx(u[i],u[i-1]);b.cx(u[i],v[i]);
        }
        b.cx(work[0],u[0]);b.and_u(incoming,v[0],work[0]);b.cx(u[0],incoming);b.cx(u[0],v[0]);
    }
}

pub fn emit(b:&mut B,row:&Row,inverse:bool) {
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
    let n=row.t.len();let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    for j in 0..blocks {
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let flag=flags.get(j).copied();
        block(b,row.g,&row.t[lo..hi],&row.s[lo..hi],previous,flag,work);
        if let Some(flag)=flag{previous=flag;}
    }
    if !row.tail.is_empty() {
        let tail_work=work.to_vec();
        b.and_c(row.g,flags[nf-1],row.c0);
        super::frogdrop::inc_mixed(b,row.c0,&row.tail,&tail_work,&row.dirty);
        b.and_u(row.g,flags[nf-1],row.c0);
    }
    for j in (0..nf).rev() {
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let incoming=if j==0{row.c0}else{flags[j-1]};
        // Comparator input is t XOR g: original_t when g=0, ~post_sum when g=1.
        // carry(original_t+s+incoming) equals [post_sum<s+incoming].
        // Therefore both branches recover the same ungated overflow exactly.
        b.row_measure(flags[j]);b.row_condition(true);
        for &q in &row.t[lo..hi]{b.cx(row.g,q);}
        cmp_phase(b,&row.t[lo..hi],&row.s[lo..hi],incoming,work);
        for &q in &row.t[lo..hi]{b.cx(row.g,q);}
        b.row_condition(false);
    }
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
}
