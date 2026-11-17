use super::builder::B;
use crate::circuit::QubitId;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct MuxSource {pub sigma:QubitId}
// mux=None retains the original clean-c0 RowAdd contract. mux=Some retains
// arbitrary c0 as the sign/incoming carry; s is the full original B source,
// t is its paid min(m+1,width) low word and tail is the FULL remaining word.
// bank, h, and source-copy targets are clean; sigma/g/c0 remain unchanged.
#[derive(Clone,Debug,PartialEq,Eq)]
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

// Forward-only deferred phase collection releases globally clean physical
// flags after all block sums. Retained classical masks are never scratch.
fn early_forward_flags(b:&mut B,row:&Row,flags:&[QubitId],deferred:&Option<(bool,Vec<crate::circuit::BitId>)>)->bool {
    if row.tail.is_empty()||flags.len()<2{return false;}
    if let Some((true,masks))=deferred {
        assert_eq!(masks.len(),flags.len());
        for j in 0..flags.len()-1 {b.hmr_to(flags[j],masks[j]);}
        true
    } else {false}
}
fn released_tail_bank(flags:&[QubitId],work:&[QubitId],early:bool)->Vec<QubitId> {
    let mut bank=Vec::new();if early{bank.extend_from_slice(&flags[..flags.len()-1]);}bank.extend_from_slice(work);bank
}

pub fn emit(b:&mut B,row:&Row,inverse:bool) {
    if b.deferred_inverse_active()&&row.mux.is_none() {let k=predecessor_count(row);if k>0 {emit_predecessors(b,row,inverse,k);return;}}
    if row.signed_binary {emit_signed(b,row,inverse);return;}
    if let Some(mux)=row.mux {emit_mux(b,row,mux,inverse);return;}
    if inverse{for &q in row.t.iter().chain(&row.tail){b.cx(row.g,q);}}
    let n=row.t.len();let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    let deferred=b.deferred_row_enter(row,inverse,nf);
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    for j in 0..blocks {
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let flag=flags.get(j).copied();
        block(b,row.g,&row.t[lo..hi],&row.s[lo..hi],previous,flag,work);
        if let Some(flag)=flag{previous=flag;}
    }
    if let Some((false,masks))=&deferred { for (flag,mask) in flags.iter().zip(masks) { b.z_if(*flag,*mask); } }
    let early=early_forward_flags(b,row,flags,&deferred);
    let tail_work=released_tail_bank(flags,work,early);
    if !row.tail.is_empty() {
        b.and_c(row.g,flags[nf-1],row.c0);
        super::frogdrop::inc_mixed(b,row.c0,&row.tail,&tail_work,&row.dirty);
        b.and_u(row.g,flags[nf-1],row.c0);
    }
    for j in (0..nf).rev() {
        if let Some((true,masks))=&deferred { if !early||j+1==nf {b.hmr_to(flags[j],masks[j]);} continue; }
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
    if inverse{for &q in row.t.iter().chain(&row.tail){b.cx(row.g,q);}}
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
    let deferred=b.deferred_row_enter(row,inverse,nf);
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    if inverse{for &q in row.t.iter().chain(&row.tail){b.cx(row.g,q);}}
    for j in 0..blocks{
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let len=hi-lo;
        let(copy,carry)=work.split_at(len);let flag=flags.get(j).copied();
        mux_copy(b,row,mux,lo,copy);
        block(b,row.g,&row.t[lo..hi],copy,previous,flag,carry);
        mux_erase(b,row,mux,lo,copy);
        if let Some(flag)=flag{previous=flag;}
    }
    if let Some((false,masks))=&deferred { for (flag,mask) in flags.iter().zip(masks) { b.z_if(*flag,*mask); } }
    let early=early_forward_flags(b,row,flags,&deferred);
    let tail_work=released_tail_bank(flags,work,early);
    if !row.tail.is_empty(){
        let cout=flags[nf-1];b.cx(row.c0,cout);
        b.and_c(row.g,cout,row.h);
        // The high virtual source bits equal sign. Cout-sign is +cout on
        // the positive branch and -(1-cout) on the negative branch.
        for &q in &row.tail{b.cx(row.c0,q);}
        super::frogdrop::inc_mixed(b,row.h,&row.tail,&tail_work,&row.dirty);
        for &q in &row.tail{b.cx(row.c0,q);}
        b.and_u(row.g,cout,row.h);b.cx(row.c0,cout);
    }
    for j in (0..nf).rev(){
        if let Some((true,masks))=&deferred { if !early||j+1==nf {b.hmr_to(flags[j],masks[j]);} continue; }
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
    if inverse{for &q in row.t.iter().chain(&row.tail){b.cx(row.g,q);}}
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
    let deferred=b.deferred_row_enter(row,inverse,nf);
    let flags=&row.bank[..nf];let work=&row.bank[nf..];let mut previous=row.c0;
    if inverse{for &q in row.t.iter().chain(&row.tail){b.x(q);}}
    for &q in &row.s{b.cx(row.c0,q);}
    for j in 0..blocks{
        let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let flag=flags.get(j).copied();
        signed_block(b,&row.t[lo..hi],&row.s[lo..hi],previous,flag,work);
        if let Some(flag)=flag{previous=flag;}
    }
    if let Some((false,masks))=&deferred { for (flag,mask) in flags.iter().zip(masks) { b.z_if(*flag,*mask); } }
    let early=early_forward_flags(b,row,flags,&deferred);
    let tail_work=released_tail_bank(flags,work,early);
    if !row.tail.is_empty(){
        let cout=flags[nf-1];b.cx(row.c0,cout);
        for &q in &row.tail{b.cx(row.c0,q);}
        super::frogdrop::inc_mixed(b,cout,&row.tail,&tail_work,&row.dirty);
        for &q in &row.tail{b.cx(row.c0,q);}
        b.cx(row.c0,cout);
    }
    for j in (0..nf).rev(){
        if let Some((true,masks))=&deferred { if !early||j+1==nf {b.hmr_to(flags[j],masks[j]);} continue; }
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

fn predecessor_inc_cost(n:usize,bank:usize)->usize {
    if n<=1{return 0;}let old=bank.min(n-1);let suffix=n-old;
    let mut best=old+if suffix==1{0}else{4*suffix};
    for k in 0..=old {let suffix=n-k;if super::frogdrop::conditional_inc_need(suffix)<=bank-k {
        best=best.min(k+super::frogdrop::conditional_inc_cost(suffix));
    }}best
}
fn predecessor_count(row:&Row)->usize {
    let n=row.t.len();if row.chunk<=1{return 0;}
    let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    let eligible=(0..nf).filter(|&j|n.min((j+1)*row.chunk)-j*row.chunk>1).count();
    let spare=row.bank.len()-nf-(row.chunk-1);let max=spare.min(eligible);
    let old=predecessor_inc_cost(row.tail.len(),row.bank.len()-nf);
    let(mut score,mut chosen)=(0isize,0usize);
    for k in 1..=max {let delta=predecessor_inc_cost(row.tail.len(),row.bank.len()-nf-k)-old;
        let candidate=k as isize-2*delta as isize;if candidate>score{score=candidate;chosen=k;}
    }chosen
}
fn predecessor_block(b:&mut B,row:&Row,t:&[QubitId],s:&[QubitId],incoming:QubitId,flag:Option<QubitId>,work:&[QubitId],loan:Option<QubitId>) {
    let n=t.len();assert!(n>0&&s.len()==n&&work.len()>=n-1);
    for i in 0..n {let prev=if i==0{incoming}else{work[i-1]};b.cx(prev,t[i]);b.cx(prev,s[i]);
        let next=if i+1<n{Some(work[i])}else{flag};if let Some(next)=next{b.and_c(t[i],s[i],next);b.cx(prev,next);}
    }
    for i in (0..n).rev(){let prev=if i==0{incoming}else{work[i-1]};
        if i+1<n&&!(loan.is_some()&&i+2==n){b.cx(prev,work[i]);b.and_u(t[i],s[i],work[i]);}
        b.cx(prev,t[i]);if row.signed_binary{b.cx(s[i],t[i]);}else{b.ccx(row.g,s[i],t[i]);}b.cx(prev,s[i]);
    }
    if let Some(q)=loan{assert!(n>1);b.swap(work[n-2],q);}
}
fn predecessor_flip(b:&mut B,row:&Row,t:&[QubitId]){for &q in t{if row.signed_binary{b.x(q);}else{b.cx(row.g,q);}}}
fn emit_predecessors(b:&mut B,row:&Row,inverse:bool,k:usize){
    assert!(row.mux.is_none());let n=row.t.len();let blocks=n.div_ceil(row.chunk);let nf=blocks-1+usize::from(!row.tail.is_empty());
    assert!(k>0&&nf+k+row.chunk-1<=row.bank.len());
    let deferred=b.deferred_row_enter(row,inverse,nf);assert!(matches!(&deferred,Some((false,_))));
    let flags=&row.bank[..nf];let loans=&row.bank[nf..nf+k];let work=&row.bank[nf+k..];
    let mut held=vec![None;nf];let mut used=0;
    for j in 0..nf {if used<k&&n.min((j+1)*row.chunk)-j*row.chunk>1{held[j]=Some(loans[used]);used+=1;}}
    assert_eq!(used,k);
    if inverse{predecessor_flip(b,row,&row.t);predecessor_flip(b,row,&row.tail);}
    if row.signed_binary{for &q in &row.s{b.cx(row.c0,q);}}
    let mut previous=row.c0;
    for j in 0..blocks {let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let flag=flags.get(j).copied();
        predecessor_block(b,row,&row.t[lo..hi],&row.s[lo..hi],previous,flag,work,held.get(j).copied().flatten());
        if let Some(q)=flag{previous=q;}
    }
    if let Some((false,masks))=&deferred{for (q,m)in flags.iter().zip(masks){b.z_if(*q,*m);}}
    if !row.tail.is_empty(){let cout=flags[nf-1];
        if row.signed_binary {b.cx(row.c0,cout);for &q in &row.tail{b.cx(row.c0,q);}
            super::frogdrop::inc_mixed(b,cout,&row.tail,work,&row.dirty);
            for &q in &row.tail{b.cx(row.c0,q);}b.cx(row.c0,cout);
        }else{b.and_c(row.g,cout,row.c0);super::frogdrop::inc_mixed(b,row.c0,&row.tail,work,&row.dirty);b.and_u(row.g,cout,row.c0);}
    }
    for j in (0..nf).rev(){let lo=j*row.chunk;let hi=n.min(lo+row.chunk);let incoming=if j==0{row.c0}else{flags[j-1]};
        b.row_measure(flags[j]);b.row_condition(true);
        if let Some(q)=held[j]{
            predecessor_flip(b,row,&row.t[hi-1..hi]);b.cz(row.t[hi-1],row.s[hi-1]);b.cz(row.t[hi-1],q);b.cz(row.s[hi-1],q);predecessor_flip(b,row,&row.t[hi-1..hi]);
            b.row_condition(false);b.row_measure(q);b.row_condition(true);
            predecessor_flip(b,row,&row.t[lo..hi-1]);cmp_phase(b,&row.t[lo..hi-1],&row.s[lo..hi-1],incoming,work);predecessor_flip(b,row,&row.t[lo..hi-1]);
        }else{predecessor_flip(b,row,&row.t[lo..hi]);cmp_phase(b,&row.t[lo..hi],&row.s[lo..hi],incoming,work);predecessor_flip(b,row,&row.t[lo..hi]);}
        b.row_condition(false);
    }
    if row.signed_binary{for &q in &row.s{b.cx(row.c0,q);}}
    if inverse{predecessor_flip(b,row,&row.t);predecessor_flip(b,row,&row.tail);}
}
