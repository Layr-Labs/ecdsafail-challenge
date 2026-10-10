use super::builder::B;
use crate::circuit::QubitId;

#[derive(Clone,Copy,Debug)]
pub struct MuxSource {pub sigma:QubitId}
// mux=None retains the original clean-c0 RowAdd contract. mux=Some retains
// arbitrary c0 as the sign/incoming carry; s is the full original B source,
// t is its paid min(m+1,width) low word and tail is the FULL remaining word.
// bank, h, and source-copy targets are clean; sigma/g/c0 remain unchanged.
#[derive(Clone,Debug)]
pub struct Row {
    pub g:QubitId,pub t:Vec<QubitId>,pub s:Vec<QubitId>,pub tail:Vec<QubitId>,
    pub mux:Option<MuxSource>,pub signed_binary:bool,pub c0:QubitId,pub h:QubitId,pub bank:Vec<QubitId>,pub dirty:Vec<QubitId>,pub chunk:usize,
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
        b.row_add(Row{signed_binary:false,mux:None,g,t:t.to_vec(),s:s.to_vec(),tail:tail.to_vec(),c0,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});true
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
    if row.signed_binary {emit_signed(b,row,inverse);return;}
    if let Some(mux)=row.mux {emit_mux(b,row,mux,inverse);return;}
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

// Exact signed source mux. The sign c0 is retained and arbitrary. The source
// is B=a[1..]; sigma selects B or 2B with a paid high zero extension.
fn mux_copy(b:&mut B,row:&Row,mux:MuxSource,lo:usize,copy:&[QubitId]) {
    for (j,&w) in copy.iter().enumerate(){
        let i=lo+j;let a=row.s.get(i).copied();let prev=i.checked_sub(1).and_then(|i|row.s.get(i)).copied();
        match (a,prev){
            (Some(a),Some(prev))=>{b.cx(a,w);b.cx(prev,a);b.ccx(mux.sigma,a,w);b.cx(prev,a);},
            (Some(a),None)=>{b.cx(a,w);b.ccx(mux.sigma,a,w);},
            (None,Some(prev))=>{b.ccx(mux.sigma,prev,w);},
            (None,None)=>{},
        }
        b.cx(row.c0,w);
    }
}
fn mux_erase(b:&mut B,row:&Row,mux:MuxSource,lo:usize,copy:&[QubitId]) {
    // W_i = B_i XOR sigma*(B_i XOR B_{i-1}) XOR sign.
    // The HMR outcome is CLASSICAL, so the conditional phase is quadratic.
    for (j,&w)in copy.iter().enumerate(){
        let i=lo+j;b.row_measure_slot(w,1);b.row_condition_slot(true,1);
        if let Some(&a)=row.s.get(i){b.z_if(a,crate::circuit::NO_BIT);b.cz(mux.sigma,a);}
        if let Some(a)=i.checked_sub(1).and_then(|i|row.s.get(i)).copied(){b.cz(mux.sigma,a);}
        b.z_if(row.c0,crate::circuit::NO_BIT);b.row_condition_slot(false,1);
    }
}
// Includes every source CCX and the one signed tail AND. Selectors are paid
// by the frame caller (3T). Source-copy cleanup is zero Toffoli.
pub fn mux_model(n:usize,tail:usize,bank:usize,chunk:usize)->(usize,usize,usize){
    let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(tail>0);let last=n-(blocks-1)*chunk;
    let c=if tail>0{2*n-blocks}else{2*(n-last)-(blocks-1)};
    (3*n-usize::from(tail==0)+tail_cost(tail,bank-flags)+3,c,flags)
}
pub fn mux_best(n:usize,tail:usize,bank:usize)->Option<(usize,usize)>{
    let mut best=None;
    for chunk in 1..=n{let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(tail>0);
        if flags+2*chunk-1>bank{continue;}
        let(u,c,_)=mux_model(n,tail,bank,chunk);let cost=2*u+c;
        if best.is_none_or(|(old,_)|cost<old){best=Some((cost,chunk));}
    }best
}
fn emit_mux(b:&mut B,row:&Row,mux:MuxSource,inverse:bool){
    let n=row.t.len();assert!(n>=1&&row.s.len()+1>=n&&row.chunk>=1&&row.chunk<=n);
    let fixed=[row.g,row.c0,row.h,mux.sigma];
    assert_eq!(fixed.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),4);
    assert_eq!(row.bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),row.bank.len());
    assert!(!row.bank.iter().any(|q|fixed.contains(q)||row.t.contains(q)||row.tail.contains(q)||row.s.contains(q)||row.dirty.contains(q)));
    assert!(!row.s.iter().any(|q|fixed.contains(q)||row.t.contains(q)||row.tail.contains(q)));
    assert!(!row.t.iter().chain(&row.tail).any(|q|fixed.contains(q)||row.dirty.contains(q)));
    let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    assert!(row.bank.len()>=nf+2*row.chunk-1);
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
    for j in 0..blocks{
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let len=hi-lo;
        let(copy,carry)=work.split_at(len);let flag=flags.get(j).copied();
        mux_copy(b,row,mux,lo,copy);
        block(b,row.g,&row.t[lo..hi],copy,previous,flag,carry);
        mux_erase(b,row,mux,lo,copy);
        if let Some(flag)=flag{previous=flag;}
    }
    if !row.tail.is_empty(){
        let cout=flags[nf-1];b.cx(row.c0,cout);
        b.and_c(row.g,cout,row.h);
        // The high virtual source bits equal sign. Cout-sign is +cout on
        // the positive branch and -(1-cout) on the negative branch.
        for &q in &row.tail{b.cx(row.c0,q);}
        super::frogdrop::inc_mixed(b,row.h,&row.tail,work,&row.dirty);
        for &q in &row.tail{b.cx(row.c0,q);}
        b.and_u(row.g,cout,row.h);b.cx(row.c0,cout);
    }
    for j in (0..nf).rev(){
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let len=hi-lo;
        let(copy,carry)=work.split_at(len);let incoming=if j==0{row.c0}else{flags[j-1]};
        b.row_measure(flags[j]);b.row_condition(true);
        mux_copy(b,row,mux,lo,copy);
        for &q in &row.t[lo..hi]{b.cx(row.g,q);}
        cmp_phase(b,&row.t[lo..hi],copy,incoming,carry);
        for &q in &row.t[lo..hi]{b.cx(row.g,q);}
        mux_erase(b,row,mux,lo,copy);
        b.row_condition(false);
    }
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
}

// Literal unconditional signed source. Source complement is Clifford and
// every source lane is restored; c0 is the retained arbitrary sign/incoming.
pub fn signed_best(n:usize,tail:usize,bank:usize)->Option<(usize,usize)>{
    let mut best=None;
    for chunk in 1..=n{
        let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(tail>0);
        if flags+chunk-1>bank{continue;}
        let last=n-(blocks-1)*chunk;
        let conditional=if tail>0{n-blocks}else{n-last-(blocks-1)};
        let tail_t=if tail>0{tail_cost(tail,bank-flags)-1}else{0};
        let unconditional=n-usize::from(tail==0)+tail_t;
        let cost=2*unconditional+conditional;
        if best.is_none_or(|(old,_)|cost<old){best=Some((cost,chunk));}
    }
    best
}
fn signed_block(b:&mut B,t:&[QubitId],s:&[QubitId],incoming:QubitId,flag:Option<QubitId>,work:&[QubitId]){
    let n=t.len();assert!(n>=1&&s.len()==n&&work.len()>=n-1);
    for i in 0..n{
        let prev=if i==0{incoming}else{work[i-1]};
        b.cx(prev,t[i]);b.cx(prev,s[i]);
        let next=if i+1<n{Some(work[i])}else{flag};
        if let Some(next)=next{b.and_c(t[i],s[i],next);b.cx(prev,next);}
    }
    for i in (0..n).rev(){
        let prev=if i==0{incoming}else{work[i-1]};
        if i+1<n{b.cx(prev,work[i]);b.and_u(t[i],s[i],work[i]);}
        b.cx(prev,t[i]);b.cx(s[i],t[i]);b.cx(prev,s[i]);
    }
}
fn emit_signed(b:&mut B,row:&Row,inverse:bool){
    assert!(row.mux.is_none());
    let n=row.t.len();assert!(n>=1&&row.s.len()==n&&row.chunk>=1&&row.chunk<=n);
    assert_eq!(row.bank.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),row.bank.len());
    assert!(!row.bank.iter().any(|q|*q==row.c0||row.t.contains(q)||row.tail.contains(q)||row.s.contains(q)||row.dirty.contains(q)));
    assert!(!row.s.iter().any(|q|*q==row.c0||row.t.contains(q)||row.tail.contains(q)));
    assert!(!row.t.iter().chain(&row.tail).any(|q|*q==row.c0||row.dirty.contains(q)));
    let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    assert!(row.bank.len()>=nf+row.chunk-1);
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
    for &q in &row.s{b.cx(row.c0,q);}
    for j in 0..blocks{
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let flag=flags.get(j).copied();
        signed_block(b,&row.t[lo..hi],&row.s[lo..hi],previous,flag,work);
        if let Some(flag)=flag{previous=flag;}
    }
    if !row.tail.is_empty(){
        let cout=flags[nf-1];b.cx(row.c0,cout);
        for &q in &row.tail{b.cx(row.c0,q);}
        super::frogdrop::inc_mixed(b,cout,&row.tail,work,&row.dirty);
        for &q in &row.tail{b.cx(row.c0,q);}
        b.cx(row.c0,cout);
    }
    for j in (0..nf).rev(){
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let incoming=if j==0{row.c0}else{flags[j-1]};
        b.row_measure(flags[j]);b.row_condition(true);
        for &q in &row.t[lo..hi]{b.x(q);}
        cmp_phase(b,&row.t[lo..hi],&row.s[lo..hi],incoming,work);
        for &q in &row.t[lo..hi]{b.x(q);}
        b.row_condition(false);
    }
    for &q in &row.s{b.cx(row.c0,q);}
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
}
