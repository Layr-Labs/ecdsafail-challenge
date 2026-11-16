//! STRICT common-top recoding, including the explicit literal native suffix.
//! A selected boundary and every replaced row already reach physical top257
//! with their inherited target/tail spans. No old carry cutoff is extended.
use super::super::builder::{B,G};
use super::super::row_add::{Row,MuxSource};
use super::super::arith::{ttk_add,up_m,down_m,Dm};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Kind { Signed, Booth }
#[derive(Clone,Copy,Debug)]
pub(crate) struct Plan { pub start:usize, pub kind:Kind, pub old:usize, pub new:usize }

fn incdirty(n:usize)->usize {
    if n<=5 {[0,0,0,1,5,13][n]} else {4*n-4}
}
fn need(n:usize)->usize {
    if n<=1{return 0;} let(mut rem,mut low,mut d)=(n-1,2,1);
    while rem>low+1{rem-=low+1;low=2*low+1;d+=1;} d
}
fn inc(n:usize,a:usize)->usize {
    if n==0{return 0;} let oldk=a.min(n-1);
    let old=oldk+if n-oldk==1{0}else{4*(n-oldk)};
    let mut best=None;
    for k in 0..=oldk {let u=n-k;let z=need(u);
        let cost=k+if u<=1{0}else{3*(u-1)-2*z};
        if z<=a-k && cost<old && best.is_none_or(|v|cost<v){best=Some(cost);}}
    best.unwrap_or(oldk+if n-oldk==1{0}else{incdirty(n-oldk+1)})
}
// Exact donor requirement of inherited inc_mixed. A chosen conditional
// summary uses its clean work only; fallback dirty increment consumes the
// entire restored suffix word, including its retained control.
fn inc_donors(n:usize,a:usize)->usize {
    if n==0{return 0;}let k=a.min(n-1);let old=k+if n-k==1{0}else{4*(n-k)};
    for j in 0..=k{let u=n-j;let z=need(u);
        let cost=j+if u<=1{0}else{3*(u-1)-2*z};
        if z<=a-j && cost<old{return 0;}}
    if n-k==1{0}else{n-k+1}
}
fn ordinary(n:usize,t:usize,a:usize,variable:bool)->usize {
    let bank=a+usize::from(!variable);let na=if t==0{0}else{t.min(bank)};
    let nc=n.min(bank-na);
    3*n-nc+if t==0{0}else if t==1{1}else if na>0{1+inc(t,na-1)}else{incdirty(t+2)}
}
fn signed(n:usize,t:usize,a:usize)->Option<(usize,usize)> {
    // Chunk zero denotes an exact ordinary ripple conjugated by target
    // complement. With no tail TTK needs no clean carry; a tail reserves
    // one actual zero for the full MAJ carry and uses the inherited increment.
    let mut best=None;
    for chunk in 1..=n {let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(t>0);
        if flags+chunk-1>a{continue;}
        let last=n-(blocks-1)*chunk;
        let c=if t>0{n-blocks}else{n-last-(blocks-1)};
        let u=n-usize::from(t==0)+if t>0{inc(t,a-flags)}else{0};
        if best.is_none_or(|(v,_)|u+c<v){best=Some((u+c,chunk));}}
    let literal=if t==0{Some(2*n-2)}
        else if a>0{Some(2*n+inc(t,a-1))}else{None};
    if let Some(lit)=literal{
        if best.is_none_or(|(cost,_)|lit<cost){best=Some((lit,0));}
    }
    best
}
fn booth(n:usize,t:usize,a:usize)->Option<(usize,usize)> {
    let mut best=None;
    for chunk in 1..=n {let blocks=n.div_ceil(chunk);let flags=blocks-1+usize::from(t>0);
        if flags+2*chunk-1>a{continue;}
        let last=n-(blocks-1)*chunk;
        let c=if t>0{2*n-blocks}else{2*(n-last)-(blocks-1)};
        let u=3*n-usize::from(t==0)+if t>0{inc(t,a-flags)+1}else{0}+3;
        if best.is_none_or(|(v,_)|u+c<v){best=Some((u+c,chunk));}}
    best
}

/// Identical public integer dispatch priced in source_price.py.
/// `old` is the unchanged row topology with the two optional no-P clean
/// ports already supplied. A recoded block must beat that full alternative.
/// No candidate record is generated for a rejected alternative.
pub(crate) fn choose(top:usize,llo:usize,lhi:usize,target:usize,source:usize,
    tail:usize,qlen:usize,external:usize)->Option<Plan>{
    assert_eq!(top,257);assert!(external==0||external==2);
    let a=qlen-source;let mut base=Vec::new();
    for i in llo..top-1 {
        let nm=(target-1).min(top-i-1);let n=nm.min(source-1);
        let t=nm+tail.min(top-i-1-nm)-n;
        base.push(ordinary(n,t,a+external,i<lhi));
    }
    let old:usize=base.iter().sum();let mut best=Plan{start:top-1,kind:Kind::Signed,old,new:old};
    // Original row i reaches min(top, i + target + tail). Only its
    // already-saturated suffix admits one exact common-modulus recurrence.
    // Below this boundary retain the original target/source/tail slices.
    let first = llo.max(top.saturating_sub(target.saturating_add(tail)));
    let mut prefix:usize=base[..first-llo].iter().sum();
    for start in first..top-2 {
        let n=(source-1).min(top-start-1);let t=top-start-1-n;
        if start>=lhi || a+external>0 {
            let boundary=if start<lhi{ordinary(n,t,a+external-1,true)+2}else{ordinary(n,t,a+external,false)};
            let mut cost=prefix+boundary;let mut valid=true;
            for i in start+1..top {
                let n=(source-1).min(top-i);let t=top-i-n;if n==0{continue;}
                if let Some((r,_))=signed(n,t,a+usize::from(i>=lhi)+external){
                    cost+=r+if i<lhi{24}else{0};
                }else{valid=false;break;}
            }
            if valid&&cost<best.new{best=Plan{start,kind:Kind::Signed,old,new:cost};}
            if start%2==0 && start>=lhi+1 && (external==2||a>=2){
                let mut cost=prefix+boundary;let mut valid=true;
                for j in (start..top-1).step_by(2){
                    let n=source.min(top-j-1);let t=top-j-1-n;
                    if let Some((r,_))=booth(n,t,a-if external==2{0}else{2}){cost+=r;}
                    else{valid=false;break;}
                }
                if valid&&cost<best.new{best=Plan{start,kind:Kind::Booth,old,new:cost};}
            }
        }
        prefix+=base[start-llo];
    }
    (best.new<old).then_some(best)
}

fn donors(universe:&[QubitId],held:&[QubitId])->Vec<QubitId>{
    let mut seen=BTreeSet::new();universe.iter().copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect()
}
fn emit_signed(b:&mut B,v:&[QubitId],q:&[QubitId],source:usize,i:usize,
    e:QubitId,g:QubitId,external:&[QubitId],variable:bool,universe:&[QubitId],literal_only:bool){
    let n=(source-1).min(v.len()-i);let t=&v[i..i+n];let tail=&v[i+n..];
    let(sign,spare)=if variable{(g,e)}else{(e,g)};
    let mut bank=q[source..].to_vec();if !variable{bank.push(g);}bank.extend(external);
    let chunk=if literal_only{
        // Native NAND frame executes U on arbitrary inactive operands.
        // No Q suffix is borrowed: only the existing globally-zero G
        // supplies the one full carry at row129. Other rows are plain TTK.
        assert!(!variable&&external.is_empty()&&source==128&&q.len()==128);
        assert!(i>=129&&v.len()==257&&tail.len()<=1);0
    }else{signed(n,tail.len(),bank.len()).expect("selected signed row bank").1};
    let held:Vec<_>=t.iter().chain(tail).chain(&q[1..1+n]).chain(&bank).chain(external).copied().chain([e,g]).collect();
    let dirty=donors(universe,&held);
    if variable{b.and_c(e,v[i],sign);}else{b.cx(v[i],sign);}b.x(sign);
    if chunk==0 {
        // C_sign ADD_B C_sign is ADD_(+/-B) over the entire original
        // target modulus. The sign stays outside the ripple throughout.
        for &bit in t.iter().chain(tail){b.cx(sign,bit);}
        if tail.is_empty(){
            if n==1{b.cx(q[1],t[0]);}else{ttk_add(b,&q[1..1+n],t,None,None);}
        }else{
            let carry=bank[0];let rest=&bank[1..];
            assert!(dirty.len()>=inc_donors(tail.len(),rest.len()));
            let up=up_m(b,t,&q[1..1+n],carry,false);
            let down=down_m(b,t,&q[1..1+n],carry,Dm::Sum,false);
            b.play(&up,false);
            super::inc_mixed(b,q[n],tail,rest,&dirty);
            b.play(&down,false);
        }
        for &bit in t.iter().chain(tail){b.cx(sign,bit);}
    }else{
        let flags=n.div_ceil(chunk)-1+usize::from(!tail.is_empty());
        assert!(dirty.len()>=inc_donors(tail.len(),bank.len()-flags));
        b.row_add(Row{signed_binary:true,mux:None,g:spare,t:t.to_vec(),
            s:q[1..1+n].to_vec(),tail:tail.to_vec(),c0:sign,h:spare,bank,dirty,chunk});
    }
    if variable{b.x(sign);b.ccx(e,q[1],sign);b.and_u(e,v[i],sign);}
    else{b.cx(v[i],sign);b.cx(q[1],sign);b.x(sign);}
}
fn emit_booth(b:&mut B,v:&[QubitId],q:&[QubitId],source:usize,j:usize,
    e:QubitId,g:QubitId,external:&[QubitId],universe:&[QubitId]){
    assert!(j>=1&&j%2==0&&j+1<v.len());
    let mut bank=q[source..].to_vec();
    let(u,h)=if external.len()==2{(external[0],external[1])}else{
        assert!(bank.len()>=2);let pair=(bank[0],bank[1]);bank.drain(..2);pair};
    let sigma=g;let sign=e;let(low,prev,high)=(v[j],v[j-1],v[j+1]);
    let n=source.min(v.len()-j-1);let tail=&v[j+1+n..];
    let(_,chunk)=booth(n,tail.len(),bank.len()).expect("selected Booth row bank");
    let held:Vec<_>=v[j-1..].iter().chain(&q[1..source]).chain(&bank).chain(external).copied().chain([e,g,u,h]).collect();
    let dirty=donors(universe,&held);
    let flags=n.div_ceil(chunk)-1+usize::from(!tail.is_empty());
    assert!(dirty.len()>=inc_donors(tail.len(),bank.len()-flags));
    b.x(sigma);b.cx(low,sigma);b.cx(prev,sigma);b.cx(high,sign);
    b.cx(high,u);b.cx(prev,u);b.cx(low,sign);b.x(sigma);
    b.ccx(sign,sigma,u);b.x(sigma);b.cx(low,sign);
    b.row_add(Row{signed_binary:false,mux:Some(MuxSource{sigma}),g:u,
        t:v[j+1..j+1+n].to_vec(),s:q[1..source].to_vec(),tail:tail.to_vec(),
        c0:sign,h,bank,dirty,chunk});
    b.cx(sign,u);b.cx(prev,u);b.cx(low,sign);b.x(sigma);
    b.and_u(sign,sigma,u);b.x(sigma);b.cx(low,sign);
    b.x(sigma);b.cx(low,sigma);b.cx(prev,sigma);
    b.cx(high,sign);b.ccx(q[1],low,sign);b.ccx(q[1],prev,sign);
}
/// Full-top inverse boundary row; variable case reserves an actual clean
/// carry rather than treating retained E as zero under complemented G.
fn boundary(b:&mut B,v:&[QubitId],q:&[QubitId],source:usize,start:usize,
    e:QubitId,g:QubitId,external:&[QubitId],variable:bool,booth_kind:bool,universe:&[QubitId]){
    let n=(source-1).min(v.len()-start-1);let target=&v[start+1..start+1+n];let tail=&v[start+1+n..];
    let mut work=q[source..].to_vec();let(enable,c0)=if variable{
        assert!(!booth_kind);work.extend(external);assert!(!work.is_empty());
        let carry=work.remove(0);b.and_c(e,v[start],g);b.x(g);(g,carry)
    }else{work.push(g);work.extend(external);let bit=v[if booth_kind{start-1}else{start}];
        if !booth_kind{b.x(bit);}(bit,e)};
    let na=if tail.is_empty(){0}else{tail.len().min(work.len())};let nc=n.min(work.len()-na);
    let held:Vec<_>=target.iter().chain(tail).chain(&q[1..1+n]).chain(&work).chain(external).copied().chain([e,g,c0,enable]).collect();
    let dirty=donors(universe,&held);
    let need=if tail.len()<=1{0}else if na==0{tail.len()+2}else{inc_donors(tail.len(),na-1)};
    assert!(dirty.len()>=need);
    b.begin();super::joint_tail::cadd_tail_no_h(b,enable,target,&q[1..1+n],tail,
        c0,&work[..na],&dirty,&work[na..na+nc]);let rec=b.end();b.play(&rec,true);
    if variable{b.x(g);b.and_u(e,v[start],g);}
    else if !booth_kind{b.x(v[start]);}
}

/// Descending recoded block; leaves E's cut walk live only if the chosen
/// start is below lhi. Caller continues the original rows below start and
/// performs its original final equality cleanup.
pub(crate) fn emit(b:&mut B,v:&[QubitId],q:&[QubitId],source:usize,lhi:usize,
    plan:Plan,e:QubitId,g:QubitId,external:&[QubitId],universe:&[QubitId],
    literal_only:bool,mut eq:impl FnMut(&mut B,usize)) -> bool {
    let mut begun=false;
    match plan.kind{
        Kind::Signed=>{
            for i in (plan.start+1..v.len()).rev(){
                let variable=i<lhi;
                if variable{if !begun{b.x(e);begun=true;}eq(b,i+1);}
                emit_signed(b,v,q,source,i,e,g,external,variable,universe,literal_only);
            }
            if plan.start<lhi{if !begun{b.x(e);begun=true;}eq(b,plan.start+1);}
            boundary(b,v,q,source,plan.start,e,g,external,plan.start<lhi,false,universe);
        },
        Kind::Booth=>{
            for j in (plan.start..v.len()-1).step_by(2).rev(){emit_booth(b,v,q,source,j,e,g,external,universe);}
            boundary(b,v,q,source,plan.start,e,g,external,false,true,universe);
        }
    }begun
}
