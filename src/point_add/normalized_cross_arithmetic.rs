//! SOURCE-ONLY native arithmetic in the common MSB-pivot coordinate.
//! Q129 has been rotated UP by 127-E and ring257 DOWN by that amount.
//! Q'[127] is the actual leading ONE on activity; Q'[128] is q0.
//! V6: exact shared arithmetic Bottom comparator plus the public low-Y reduction.
//! Full unparked source epochs still bypass the variable park prefix.
//! The lower fourteen source cells contain a variable data/park separator.
//! No gate emission, integration, compilation or execution accompanies this file.

use super::builder::{B,G};
use super::cross_four::{Cross,Gate,VTop};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
enum Op { Divide, Add, VBit(VTop) }
#[derive(Clone,Copy)]
enum Close { None, Inplace, EraseInplace(QubitId), Store(VTop) }

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn cover(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi {let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());lo+=1usize<<free;
    }out
}
fn product(a:Vec<Vec<(QubitId,bool)>>,z:Vec<Vec<(QubitId,bool)>>)->Vec<Vec<(QubitId,bool)>>{
    let mut out=vec![];for x in a{for y in &z{let mut t=x.clone();t.extend(y);out.push(t);}}out
}
fn lit(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==target));let mut seen=BTreeSet::new();
    let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=target&&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,target,&[],&d);
}
fn bank(c:&Cross<'_>)->Vec<QubitId>{let r=c.roles;
    let mut seen:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
        .chain(c.clean_external.iter().copied())
        .chain([c.phase,r.activity,r.flight,r.mask,r.x128,c.q[127]]).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).copied().filter(|q|seen.insert(*q)).collect()
}
fn xor_terms(b:&mut B,t:&[Vec<(QubitId,bool)>],out:QubitId,extra:&[(QubitId,bool)],d:&[QubitId]){
    for term in t{let mut all=term.clone();all.extend_from_slice(extra);lit(b,&all,out,d);}
}

/// One combined Gate witness. No separate low/high-Y activity witness.
/// Unlike the old variable-boundary kernel, Top must retain its capacity
/// condition explicitly: the fixed query at128 cannot enforce Y+j<=128.
fn witness(b:&mut B,c:&Cross<'_>,gate:Gate,d:&[QubitId])->Vec<G>{
    let r=c.roles;
    // A1 and every skipped-flight e1 are images of the same public
    // column envelope. If Yhi+j<=128, capacity is implied throughout
    // this complete guard and its inverse. No arithmetic span is cut.
    let gate=match gate{
        Gate::Top(j) if c.y_bounds.1<=128-j=>Gate::Natural(j),
        Gate::Bottom(k) if c.y_bounds.1<=114=>Gate::Natural(k+15),g=>g};
    if let Gate::Bottom(k)=gate{
        assert!(k<15);
        let byte:Vec<_>=c.size.y.iter().copied().chain([r.mask]).collect();
        let negative=product(cover(&byte,128-k,256),cover(&c.size.sum,17-k,32));
        let old_pair=188+4*negative.iter().map(|t|match t.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum::<usize>();
        if super::bottom_comparator::arithmetic_price(k)<old_pair{
            return super::bottom_comparator::witness_record(b,c,k,d);
        }
        let address=super::direct_frame::z_byte_record(b,c.size,r.mask,d);
        return rec(b,|b|{b.play(&address,false);
            for (a,t) in [(r.activity,r.flight),(r.flight,r.activity)]{
                xor_terms(b,&negative,t,&[(a,false)],d);
            }b.play(&address,true);
        });
    }
    let (positive,negative)=match gate{
        Gate::Natural(k)=>(cover(&c.size.sum,0,32-k),cover(&c.size.sum,32-k,32)),
        Gate::Top(j)=>{
            assert!(j<15);
            let p=product(cover(&c.size.y,0,128-j),cover(&c.size.sum,0,32-j));
            let ey=cover(&c.size.y,128-j,128);
            let es=cover(&c.size.sum,32-j,32);
            let mut n=ey.clone();
            n.extend(product(cover(&c.size.y,0,128-j),es.clone()));
            // !Gate = Efail OR Sfail = Efail XOR Sfail XOR Efail*Sfail.
            // Every predicate is on unchanged metadata; overlaps cancel
            // algebraically, including all off-activity metadata words.
            let mut union=ey.clone();union.extend(es.clone());union.extend(product(ey,es));
            if price(&union)<price(&n){n=union;}(p,n)
        },Gate::Bottom(_)=>unreachable!(),
    };
    fn price(t:&[Vec<(QubitId,bool)>])->usize{t.iter().map(|x|match x.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum()}
    let complement=price(&positive)<price(&negative);
    let terms=if complement{positive}else{negative};
    rec(b,|b|for(a,t)in[(r.activity,r.flight),(r.flight,r.activity)]{
        if complement{b.cx(a,t);}xor_terms(b,&terms,t,&[(a,false)],d);
    })
}

/// A four-bit decoder only during the prefix-up or prefix-down epoch.
/// Q'127 is a genuine leading ONE on activity and is not a prefix operand.
/// X Q'127; Q'127 ^= E6 E5 E4 changes it into the high-class root on activity.
/// E4..6 are then conditional-zero prefixes. Off activity the complete
/// prefix epoch is an arbitrary reversible permutation with exact inverse.
/// The code intentionally contains no measured AND cleanup.
struct Prefix<'a>{e:&'a[QubitId],root:QubitId,cur:Option<usize>}
impl Prefix<'_>{
    fn enter(&self,b:&mut B,d:&[QubitId]){
        b.x(self.root);lit(b,&[(self.e[4],false),(self.e[5],false),(self.e[6],false)],self.root,d);
        for &q in &self.e[4..7]{b.x(q);}
    }
    fn cell(&self,b:&mut B,level:usize,v:usize){
        let(a,na)=if level==0{(self.e[3],v&8==0)}else{(self.e[3+level],false)};
        let(z,nz)=(self.e[2-level],v>>(2-level)&1==0);
        if na{b.x(a);}if nz{b.x(z);}b.ccx(a,z,self.e[4+level]);if nz{b.x(z);}if na{b.x(a);}
    }
    fn goto(&mut self,b:&mut B,v:usize){
        assert!(v<16);let mut keep=0;
        if let Some(old)=self.cur{while keep<3&&((old^v)>>(2-keep))==0{keep+=1;}
            for i in(keep..3).rev(){self.cell(b,i,old);}}
        for i in keep..3{self.cell(b,i,v);}self.cur=Some(v);
    }
    fn xor_eq(&self,b:&mut B,out:QubitId){b.ccx(self.root,self.e[6],out);}
    fn xor_above(&self,b:&mut B,v:usize,out:QubitId,d:&[QubitId]){
        // Cached higher-prefix bits refer to the SAME v used by goto.
        for i in(0..4).rev(){if v>>i&1!=0{continue;}
            let mut ctl=vec![(self.root,false),(self.e[i],false)];
            if i==2{ctl.push((self.e[3],v&8==0));}
            else if i<2{ctl.push((self.e[5-i],false));}
            lit(b,&ctl,out,d);
        }
    }
    fn leave(&mut self,b:&mut B,d:&[QubitId]){
        if let Some(v)=self.cur{for i in(0..3).rev(){self.cell(b,i,v);}}self.cur=None;
        for &q in &self.e[4..7]{b.x(q);}
        lit(b,&[(self.e[4],false),(self.e[5],false),(self.e[6],false)],self.root,d);b.x(self.root);
    }
}

fn cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,inverse:bool){
    if inverse{b.ccx(x,t,s);b.cx(s,x);b.cx(s,t);}
    else{b.cx(s,t);b.cx(s,x);b.ccx(x,t,s);}
}
fn controlled_cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,enable:QubitId,inverse:bool,d:&[QubitId]){
    static FOLD: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let fold=*FOLD.get_or_init(||match std::env::var("SCHROTT_CONTROLLED_CELL"){
        Ok(v) if v=="0"=>false,Ok(v) if v=="1"=>true,
        Err(std::env::VarError::NotPresent)=>true,
        _=>panic!("SCHROTT_CONTROLLED_CELL must be 0 or 1"),
    });
    controlled_cell_with_fold(b,s,t,x,enable,inverse,d,fold);
}
fn controlled_cell_with_fold(b:&mut B,s:QubitId,t:QubitId,x:QubitId,enable:QubitId,inverse:bool,d:&[QubitId],fold:bool){
    // Full-domain identity on distinct ports: two shared-control CCX gates
    // equal CX(u,v); CCX(a,b,u); CX(u,v). No clean-state assumption.
    if inverse{
        lit(b,&[(enable,false),(x,false),(t,false)],s,d);
        if fold{b.cx(x,t);b.ccx(enable,s,x);b.cx(x,t);}
        else{b.ccx(enable,s,x);b.ccx(enable,s,t);}
    }else{
        if fold{b.cx(t,x);b.ccx(enable,s,t);b.cx(t,x);}
        else{b.ccx(enable,s,t);b.ccx(enable,s,x);}
        lit(b,&[(enable,false),(x,false),(t,false)],s,d);
    }
}

#[cfg(test)]
mod schrottkahn_integration_tests {
    use super::*;
    use crate::circuit::{Op as Primitive,OperationType,NO_BIT};

    fn run(ops:&[Primitive],mut state:u64)->u64{
        for op in ops{
            assert_eq!(op.c_condition,NO_BIT);
            let t=op.q_target.0;
            match op.kind{
                OperationType::CX=>state^=((state>>op.q_control1.0)&1)<<t,
                OperationType::CCX=>state^=(((state>>op.q_control1.0)&1)&((state>>op.q_control2.0)&1))<<t,
                _=>panic!("unexpected controlled-cell primitive {:?}",op.kind),
            }
        }state
    }
    fn oracle(mut state:u64,p:[u64;4],inverse:bool)->u64{
        let [s,t,x,e]=p;
        if inverse{
            state^=(((state>>e)&1)&((state>>x)&1)&((state>>t)&1))<<s;
        }
        let product=((state>>e)&1)&((state>>s)&1);
        state^=product<<t;state^=product<<x;
        if !inverse{
            state^=(((state>>e)&1)&((state>>x)&1)&((state>>t)&1))<<s;
        }state
    }

    #[test]
    fn schrottkahn_full_domain_ports_and_cancellation(){
        assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
        let maps=[[0,1,2,3],[3,2,1,0],[6,0,4,2],[2,5,0,6],[5,4,3,2],[1,3,5,0]];
        let mut rows=0;let mut mutants=0;
        for p in maps{for inverse in [false,true]{for fold in [false,true]{
            for cancel in [false,true]{for global in [false,true]{
                let mut b=B::new();b.alloc_n(7);
                b.cancel_simple_pairs=cancel;b.cancel_commuting_pairs=cancel;b.global_cancel=global;
                let dirty:Vec<_>=p.into_iter().chain(0..7).chain(0..7).map(QubitId).collect();
                b.begin();controlled_cell_with_fold(&mut b,QubitId(p[0]),QubitId(p[1]),QubitId(p[2]),QubitId(p[3]),inverse,&dirty,fold);
                let rec=b.end();b.play(&rec,false);b.flush_global();
                assert_eq!(b.tof,if fold{5}else{6});
                assert_eq!(b.ops.len(),if fold{7}else{6});
                assert_eq!(b.peak,7);
                for input in 0..128{
                    let output=run(&b.ops,input);
                    assert_eq!(output,oracle(input,p,inverse));
                    let reversed:Vec<_>=b.ops.iter().rev().copied().collect();
                    assert_eq!(run(&reversed,output),input);rows+=1;
                }
                for i in 0..b.ops.len(){
                    let mut bad=b.ops.clone();bad.remove(i);
                    assert!((0..128).any(|input|run(&bad,input)!=oracle(input,p,inverse)));
                    mutants+=1;
                }
                // Nested recording/inverse play must preserve the same map.
                b.ops.clear();b.begin();b.play(&rec,true);let undo=b.end();
                b.play(&undo,false);b.flush_global();
                for input in 0..128{assert_eq!(run(&b.ops,input),oracle(input,p,!inverse));rows+=1;}
            }}
        }}}
        eprintln!("SCHROTT_INTEGRATION_PASS rows={rows} deletion_mutants={mutants} port_maps=6 profiles=4 directions=2 branches=2");
    }

    #[test]
    fn schrottkahn_baked_entry_matches_fold(){
        assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
        super::super::bake_knobs();
        assert_eq!(std::env::var("SCHROTT_CONTROLLED_CELL").unwrap(),"1");
        for inverse in [false,true]{
            let mut actual=B::new();actual.alloc_n(5);
            controlled_cell(&mut actual,QubitId(0),QubitId(1),QubitId(2),QubitId(3),inverse,&[QubitId(4)]);
            let mut expected=B::new();expected.alloc_n(5);
            controlled_cell_with_fold(&mut expected,QubitId(0),QubitId(1),QubitId(2),QubitId(3),inverse,&[QubitId(4)],true);
            assert_eq!(actual.ops,expected.ops);
        }
    }
}
fn lower(b:&mut B,c:&Cross<'_>,s:QubitId,t:QubitId,x:QubitId,add:bool,d:&[QubitId]){
    let r=c.roles;b.cx(s,x);
    let mut ctl=vec![(r.mask,false),(r.flight,false),(x,false)];
    if !add{ctl.push((r.activity,false));}lit(b,&ctl,t,d);b.cx(s,x);
}

/// Multi-control Fredkin with literal primitive accounting: four Toffolis.
fn first_swap(b:&mut B,p:&Prefix<'_>,a:QubitId,z:QubitId,d:&[QubitId]){
    b.cx(a,z);lit(b,&[(p.root,false),(p.e[6],false),(z,false)],a,d);b.cx(a,z);
}
/// Exact all-data parity, not a one-hot assumption. At decoder v2,
/// XOR_{v=2..15} H*eq(v) = H*(1 XOR pre0 XOR pre1).
/// Each dirty terminal-prefix term occurs14times and cancels; the complete
/// sixteen-address XOR is1, while eq0 XOR eq1=pre0 XOR pre1 at this cursor.
fn parity14(b:&mut B,p:&Prefix<'_>,out:QubitId){
    assert_eq!(p.cur,Some(2));
    b.cx(p.root,out);b.ccx(p.root,p.e[4],out);b.ccx(p.root,p.e[5],out);
}
fn prefix(b:&mut B,c:&Cross<'_>,t:&[QubitId],carry:QubitId,down:bool,add:bool,d:&[QubitId]){
    let mut p=Prefix{e:&c.size.y,root:c.q[127],cur:None};p.enter(b,d);
    // M is the XOR of first-boundary predicates already passed. It equals
    // [delta<=i] on activity, but may be an arbitrary parity off activity.
    if down{p.goto(b,2);parity14(b,&p,c.roles.mask);b.cswap(c.roles.mask,carry,c.q[13]);}
    let order:Vec<_>=if down{(0..14).rev().collect()}else{(0..14).collect()};
    for i in order{let v=15-i;p.goto(b,v);let x=if i==0{carry}else{c.q[i-1]};
        if down{
            controlled_cell(b,c.q[i],t[i],x,c.roles.mask,true,d);
            lower(b,c,c.q[i],t[i],x,add,d);
            if i>0{first_swap(b,&p,carry,c.q[i-1],d);}
            p.xor_eq(b,c.roles.mask);
        }else{
            p.xor_eq(b,c.roles.mask);
            if i>0{first_swap(b,&p,carry,c.q[i-1],d);}
            controlled_cell(b,c.q[i],t[i],x,c.roles.mask,false,d);
        }
    }
    if !down{b.cswap(c.roles.mask,carry,c.q[13]);parity14(b,&p,c.roles.mask);}
    p.leave(b,d);
}
fn top_query(b:&mut B,c:&Cross<'_>,positive:bool,d:&[QubitId]){
    let lim=32-c.qb;
    let terms=if positive{cover(&c.size.sum,lim,32)}else{cover(&c.size.sum,0,lim)};
    xor_terms(b,&terms,c.roles.mask,&[(c.roles.activity,false)],d);
}
fn normal_decision(b:&mut B,enable:QubitId,e:QubitId,t:QubitId,x:QubitId,d:&[QubitId]){
    b.cx(enable,e);lit(b,&[(enable,false),(t,false),(x,false)],e,d);
}

/// The same stable call surface as cross_running_flight::D, but callers
/// must establish the complete Q/ring coordinate and pass fixed129 targets.
/// payload_open additionally requires NO parked Q bits: Q'[128] is the
/// conditional-zero carry. Otherwise PH is phase and remains the carry.
pub(crate) struct D{pub ht:bool,pub payload_open:bool}
impl D{
    fn record(&self,b:&mut B,c:&Cross<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close)->Vec<G>{
        assert_eq!((c.q.len(),c.size.y.len(),c.size.sum.len(),t.len()),(128,7,5,129));
        assert_eq!(c.qb,30);let r=c.roles;let add=matches!(op,Op::Add);
        if let Gate::Top(j)=gate{if c.y_bounds.0>128-j{return vec![];}}
        // Public source-domain/capacity pruning only. Top additionally
        // has Y<=128-j on the complete acted sector (ADD has e=>Gate).
        // If that upper bound<=114, every source cell below14 is virtual
        // zero, even with all15 parks held; the inactive extension is identity.
        let acted_hi=if let Gate::Top(j)=gate{c.y_bounds.1.min(128-j)}else{c.y_bounds.1};
        let has_prefix=acted_hi>=115&&!self.payload_open;
        // Q is normalized with its leading ONE at127. The unchanged
        // public Y bound makes every bit below128-Yhi logically zero.
        // With held parks only the first14 positions need their separate
        // exact prefix; if absent, zero+target with carry0 has no carry.
        // Omitting those MAJ/restore identities leaves both complete
        // source/target words intact, including arbitrary off-A values.
        let first=if has_prefix{14}else{128-acted_hi};
        let carry=if self.payload_open{r.x128}else{c.phase};
        let mut ports=BTreeSet::new();
        assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
            .chain([r.activity,r.flight,r.mask,carry]).all(|q|ports.insert(q)));
        let d=bank(c);let split=matches!(op,Op::VBit(VTop::Frame(0)));
        let complement=matches!(op,Op::Divide);
        b.begin();let guard=if add{vec![]}else{witness(b,c,gate,&d)};b.play(&guard,false);
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        if complement{for &q in t{b.x(q);}}
        if has_prefix{prefix(b,c,t,carry,false,add,&d);}
        for i in first..128{cell(b,c.q[i],t[i],if i==first{carry}else{c.q[i-1]},false);}
        if !add{
            if split{top_query(b,c,false,&d);normal_decision(b,r.mask,r.flight,t[128],c.q[127],&d);top_query(b,c,false,&d);}
            else{normal_decision(b,r.activity,r.flight,t[128],c.q[127],&d);}
        }
        if add{b.cx(r.flight,r.mask);}else{b.ccx(r.activity,r.flight,r.mask);}
        b.ccx(r.mask,c.q[127],t[128]);
        for i in(first..128).rev(){let x=if i==first{carry}else{c.q[i-1]};cell(b,c.q[i],t[i],x,true);
            if split&&i==127{
                b.ccx(r.activity,r.flight,r.mask);
                top_query(b,c,true,&d);
                lit(b,&[(r.mask,false),(t[i],true),(x,true)],r.flight,&d);
                top_query(b,c,true,&d);b.ccx(r.activity,r.flight,r.mask);
            }
            b.cx(c.q[i],x);b.ccx(r.mask,x,t[i]);b.cx(c.q[i],x);
        }
        if add{b.cx(r.flight,r.mask);}else{b.ccx(r.activity,r.flight,r.mask);}
        if has_prefix{prefix(b,c,t,carry,true,add,&d);}
        if complement{for &q in t{b.x(q);}}
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        // Complete adjacent pairs only, on their inherited e0 entry/image.
        // W has narrowed A to A&Gate; source/target/phase are now in the
        // old arithmetic output coordinates. Off Gate e holds skipped A,
        // so EVERY moved write retains narrowed A, including park erase.
        // Metadata is unchanged, hence the same W^-1 still closes exactly.
        match close{
            Close::None=>{},
            Close::Inplace|Close::EraseInplace(_)=>{
                assert!(matches!(op,Op::Divide));
                if let Close::EraseInplace(slot)=close{b.ccx(r.activity,r.flight,slot);}
                b.cswap(r.activity,t[128],r.flight);
            },
            Close::Store(top)=>{
                assert!(matches!(op,Op::VBit(_)));
                match top{
                    VTop::Zero=>b.cx(r.activity,t[128]),
                    VTop::Frame(j)=>if j!=0{b.cx(r.activity,t[128]);}else{
                        let donor:Vec<_>=d.iter().copied().filter(|q|*q!=t[128]).collect();
                        for mut term in cover(&c.size.sum,0,32-c.qb){
                            term.push((r.activity,false));
                            mc_xor(b,&term,t[128],c.clean_external,&donor);
                        }
                    },
                }
                b.cswap(r.activity,t[128],r.flight);
            },
        }
        b.play(&guard,true);b.end()
    }
    pub(crate) fn divide(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::None);b.play(&r,inverse);}
    /// Forward D;I, inverse I;D^-1, on the complete divide image.
    pub(crate) fn divide_inplace(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::Inplace);b.play(&r,inverse);}
    pub(crate) fn divide_erase_inplace(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,slot:QubitId){let r=self.record(b,c,t,g,Op::Divide,Close::EraseInplace(slot));b.play(&r,false);}
    pub(crate) fn add(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate){let r=self.record(b,c,t,g,Op::Add,Close::None);b.play(&r,false);}
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::None);b.play(&r,false);}
    pub(crate) fn vbit_store(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::Store(top));b.play(&r,false);}
}
