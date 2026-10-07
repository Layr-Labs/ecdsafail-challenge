//! Post-entry Sign erasure with one shortened comparison bit and cargo handoff.
//! Entry Sign=0 in phases00/01/10, arbitrary in11 (same domain as T10).
//! Old T11 was the identity outside11; other arithmetic is identity on11.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
pub(super) fn code(circ:&mut Circuit,p1:&QReg,p2:&QReg,sign:&QReg,helpers:&[QReg],inverse:bool){
    let start=circ.b.ops.len();let word=[p1,p2,sign];
    // 3->1, 7->5, 1->4, 0->0, 2->2. Thus P1 is phase11, P2=0 there.
    let affine=super::metadata_muxlease::active("Q793_AFFINE_SIGN_CODE");
    for(left,right)in[(1usize,4usize),(1,3),(5,7)]{if affine{super::metadata_rank5::affine_word_transposition(circ,&word,&[],helpers,left,right);continue;}let mut value=left;let mut edges=Vec::new();for bit in 0..3{if(left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());for(bit,v)in edges{let cs:Vec<_>=(0..3).filter(|&i|i!=bit).map(|i|(word[i],v>>i&1!=0)).collect();mixed_mcx(circ,&cs,word[bit],helpers);}}
    if inverse{circ.b.ops[start..].reverse();}
}
fn joint_degree()->usize { std::env::var("Q795_SIGN_JOINT_PREFIX").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(0).min(3) }
struct Range<'a>{rank:&'a[QReg],low:&'a[QReg],sm:&'a[QReg],guard:&'a QReg,cache:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],j:usize,group:isize,position:usize,joint:usize}
impl Range<'_>{
    // Refine each output XOR of the existing high oracle. Its cache is never
    // an input, and low is in the prepared address basis at every output write.
    // Temporary carry/rank arithmetic is unchanged. No qubit is allocated.
    fn refined(&self,circ:&mut Circuit,h:isize,p:usize,skip:Option<usize>){
        use crate::circuit::OperationType;
        if h<0{return;}
        let start=circ.b.ops.len();
        super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,-1,h);
        let ops=circ.b.ops.split_off(start);let degree=joint_degree();
        let wires:Vec<_>=self.rank.iter().chain(self.low).chain(self.sm).chain(self.dirty).chain([self.guard,self.cache,self.mask]).collect();
        for op in ops {
            assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));
            assert!(op.q_control1.0!=self.cache.id()as u64 && op.q_control2.0!=self.cache.id()as u64,"joint cache used as input");
            if op.q_target.0!=self.cache.id()as u64 {circ.b.ops.push(op);continue;}
            let mut cs:Vec<_>=(0..degree).filter(|&i|skip!=Some(i)).map(|i|(&self.low[6-degree+i],p>>i&1!=0)).collect();
            for id in [op.q_control1,op.q_control2] {if id.0==u64::MAX{continue;}let q=*wires.iter().find(|q|q.id()as u64==id.0).expect("high oracle control missing");assert!(!cs.iter().any(|(c,_)|c.id()==q.id()),"prefix aliases oracle input");cs.push((q,true));}
            let lenders:Vec<_>=self.dirty.iter().filter(|q|!cs.iter().any(|(c,_)|c.id()==q.id())).map(QReg::borrowed_alias).collect();
            mixed_mcx(circ,&cs,self.cache,&lenders);
        }
    }
    fn select_joint(&mut self,circ:&mut Circuit,h:isize,p:usize){
        if joint_degree()==0{self.select(circ,h);return;}
        if (h,p)!=(self.group,self.joint){
            let diff=p^self.joint;
            // Equal-width prefix minterms differing in one bit XOR to the
            // common cube with that bit omitted. For degree1 this is just
            // the original unrefined high predicate: no repeated carry oracle.
            if h==self.group&&h>=0&&diff.count_ones()==1 {
                self.refined(circ,h,p,Some(diff.trailing_zeros()as usize));
            } else {self.refined(circ,self.group,self.joint,None);self.refined(circ,h,p,None);}
            self.group=h;self.joint=p;
        }
    }
    fn high(&self,circ:&mut Circuit,h:isize){if(0..5).contains(&h){super::metadata_phase115_phased::sum_flag_raw(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,h as usize);}}
    fn select(&mut self,circ:&mut Circuit,h:isize){if joint_degree()!=0{assert_eq!(h,-1);self.select_joint(circ,h,0);return;}if h!=self.group{
        if super::metadata_muxlease::active("Q795_SIGN_TRANSITION"){super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.low,self.sm,self.guard,self.cache,self.dirty,self.j,self.group,h);}
        else{self.high(circ,self.group);self.high(circ,h);}self.group=h;
    }}
    fn equality(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg){self.equality_impl(circ,value,extra,target,false);}
    fn equality_impl(&mut self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg,clean_mask:bool){
        if !(1..=257).contains(&value){return;}let degree=joint_degree();self.select_joint(circ,(value/64)as isize,(value&63)>>(6-degree));let mut cs=vec![(self.guard,true),(self.cache,true)];cs.extend((0..6-degree).map(|i|(&self.low[i],value>>i&1!=0)));cs.extend_from_slice(extra);
        if clean_mask{super::conditional_mcx::guarded(circ,self.guard,&cs[1..],target,self.mask,true,&self.dirty[0]);}
        else{mixed_mcx(circ,&cs,target,self.dirty);}
    }
    // mask = [position < 259-(C+S)] under guard, true at position0.
    fn set(&mut self,circ:&mut Circuit,p:usize){let base=if super::metadata_muxlease::active("Q795_PHASE_LOAN"){256usize}else{257};for k in self.position.min(p)..self.position.max(p){if k<=base{self.equality(circ,base-k,&[],self.mask);}}self.position=p;}
}
fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:Option<&QReg>,dirty:&[QReg],j:usize,inverse:bool,n:usize){
    let start=circ.b.ops.len();let mut r=Range{rank,low,sm,guard,cache,mask,dirty,j,group:-1,position:0,joint:0};circ.cx(guard,mask);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in(1..n).rev(){if let Some(z)=sign{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in(1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    let mut mask_pristine=true;
    // Only the complete inverse/plain + forward/Sign pair is identity off
    // guard. Mask updates and all Sign consumers retain guard. Then the same
    // arbitrary mask selects matching data maps on both off-guard passes.
    let pair_raw=super::metadata_muxlease::active("Q795_SIGN_PAIR_UNGUARDED");
    for(i,tag,data,out)in cells{if tag==2{circ.cx(data[0],out);continue;}let extras:Vec<_>=data.iter().map(|&q|(q,true)).collect();if tag==1{let base=if super::metadata_muxlease::active("Q795_PHASE_LOAN"){256usize}else{257};if i<=base{r.equality_impl(circ,base-i,&extras,out,mask_pristine&&super::metadata_muxlease::active("Q796_SIGN_MASK_LOAN"));}continue;}let mut cs=if pair_raw{Vec::new()}else{vec![(guard,true)]};if tag==0{mask_pristine=false;r.set(circ,i);cs.push((mask,true));}cs.extend(extras);mixed_mcx(circ,&cs,out,dirty);}
    r.set(circ,0);r.select(circ,-1);circ.cx(guard,mask);if inverse{circ.b.ops[start..].reverse();}
}
fn compare(circ:&mut Circuit,rank:&[QReg],a:&[QReg],b:&[QReg],low:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,mask:&QReg,sign:&QReg,dirty:&[QReg],j:usize,n:usize){
    // carry(a + NOT b) = [a>b]. Complementing that gives [b>=a].
    // Compute only the carry propagation, write its two terms, and undo;
    // no sum is needed or retained by phase11.
    for q in &b[..n]{circ.x(q);}
    let start=circ.b.ops.len();let mut r=Range{rank,low,sm,guard,cache,mask,dirty,j,group:-1,position:0,joint:0};circ.cx(guard,mask);
    for i in 0..n{circ.cx(&a[i],&b[i]);}circ.cx(&a[0],&b[0]);
    for i in (1..n-1).rev(){circ.cx(&a[i],&a[i+1]);}
    for i in 0..n-1{r.set(circ,i+1);mixed_mcx(circ,&[(guard,true),(mask,true),(&a[i],true),(&b[i],true)],&a[i+1],dirty);}
    r.set(circ,0);r.select(circ,-1);circ.cx(guard,mask);let compute=circ.b.ops[start..].to_vec();
    for i in 1..n{r.equality(circ,257-i,&[(&a[i],true),(&b[i],true)],sign);}r.select(circ,-1);
    circ.b.ops.extend(compute.into_iter().rev());
    for i in 1..n{r.equality(circ,257-i,&[(&a[i],true)],sign);}r.select(circ,-1);
    for q in &b[..n]{circ.x(q);}circ.cx(guard,sign);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize){
    // Read-only diagnostics: no operation or allocation changes.
    let census=std::env::var_os("Q795_SIGN_CENSUS").is_some();
    let mut last=circ.b.ops.len();
    let mut mark=|circ:&Circuit,name:&str|{if census {
        let ops=&circ.b.ops[last..];
        let t=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();
        eprintln!("Q795_SIGN_STAGE name={name} ops={} T={t}",ops.len());
        last=circ.b.ops.len();
    }};
    code(circ,p1,p2,sign,helpers,false);super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);let mask=&helpers[0];let dirty=&helpers[1..];let addresses:Vec<_>=(0..256).map(|v|&w1[258-v]).collect();
    mark(circ,"phase_and_handoff_in");
    let dual=super::metadata_muxlease::active("Q795_PHASE_LOAN");
    if dual{
        assert!(!super::metadata_muxlease::active("Q799_T11_COMPARE"),"top-loan direct comparator not adapted");
        super::q795_t11_top::move_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    }
    mark(circ,"top_cargo_in");
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);
    mark(circ,"mask_loan_in");
    if dual{
        super::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
        circ.cswap(p1,p2,mask);circ.ccx(p1,p2,sign);
        super::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    }
    mark(circ,"top_flag_and_park_in");
    if super::metadata_muxlease::active("Q795_SIGN_TWO_PASS") {
        assert!(dual,"two-pass top carry loan requires Q795_PHASE_LOAN");
        super::q795_sign_two_pass::emit(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j,n);
    } else {
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,false);
    if super::metadata_muxlease::active("Q799_T11_COMPARE"){compare(circ,rank,w1,w2,c,sm,p1,p2,mask,sign,dirty,j,n);}else{
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,None,dirty,j,true,n);
        prefix(circ,rank,w1,w2,c,sm,p1,p2,mask,Some(sign),dirty,j,false,n);
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,p1,None,dirty,j,true);
    }
    mark(circ,"comparison");
    if dual{
        super::q795_t11::park_c1(circ,p1,p2,sign,helpers);circ.cswap(p1,p2,mask);
        super::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    }
    mark(circ,"top_flag_and_park_out");
    super::metadata_muxlease::exchange(circ,rank,c,1,Some(p1),mask,&addresses,dirty,true);
    mark(circ,"mask_loan_out");
    if dual{super::q795_t11_top::move_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);}
    mark(circ,"top_cargo_out");
    super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);code(circ,p1,p2,sign,helpers,true);
    mark(circ,"phase_and_handoff_out");
}
