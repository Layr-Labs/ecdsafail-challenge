use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_REG};
mod decoder;

fn optional_bit(x:u16)->BitId {
    if x==u16::MAX {NO_BIT} else {BitId(x as u64)}
}
fn operation([kind,a,b,c]:[u16;4])->Op {
    use OperationType::*;
    let qa=QubitId(a as u64);let qb=QubitId(b as u64);
    let mut op=Op::empty();
    op.kind=match kind {
        1=>{op.r_target=RegisterId(a as u64);Register}
        2=>{op.r_target=RegisterId(a as u64);op.q_target=qb;AppendToRegister}
        18=>{op.r_target=RegisterId(a as u64);op.c_target=BitId(b as u64);AppendToRegister}
        3|4|5=>{op.c_target=BitId(a as u64);op.c_condition=optional_bit(b);
            if kind==3 {BitInvert} else if kind==4 {BitStore0} else {BitStore1}}
        6|7=>{op.q_target=qa;op.c_condition=optional_bit(b);if kind==6{X}else{Z}}
        8|9=>{op.q_control1=qa;op.q_target=qb;op.c_condition=optional_bit(c);if kind==8{CX}else{CZ}}
        12=>{op.q_target=qa;op.c_target=optional_bit(b);Hmr}
        13=>{op.q_control2=qa;op.q_control1=qb;op.q_target=QubitId(c as u64);CCX}
        15=>{op.c_condition=BitId(a as u64);PushCondition}
        16=>PopCondition,
        _=>panic!("Unsupported gate-record operation {}",kind),
    };
    op
}
mod schedule;
mod peephole;
use schedule::RecordTarget;
/// Packaged-row view of the decoded op list for the exact peephole pass (removed ops are DEBUG_PRINT
/// placeholders until the final compaction drops them).
struct OpRows<'a>(&'a mut Vec<Op>,Vec<(usize,[[u16;4];3])>);
impl peephole::Rows for OpRows<'_>{
    fn len(&self)->usize{self.0.len()}
    fn get(&self,i:usize)->[u16;4]{
        use OperationType::*;
        let o=self.0[i];
        let bit=|x:BitId|if x==NO_BIT{65535}else{x.0 as u16};
        match o.kind{
            DebugPrint=>if o.r_target==NO_REG{[peephole::TOMB,65535,65535,65535]}else{[peephole::BLOCK,65535,65535,65535]},
            Register=>[1,o.r_target.0 as u16,65535,65535],
            AppendToRegister=>if o.c_target!=NO_BIT{[18,o.r_target.0 as u16,bit(o.c_target),65535]}else{[2,o.r_target.0 as u16,o.q_target.0 as u16,65535]},
            BitInvert=>[3,bit(o.c_target),bit(o.c_condition),65535],
            BitStore0=>[4,bit(o.c_target),bit(o.c_condition),65535],
            BitStore1=>[5,bit(o.c_target),bit(o.c_condition),65535],
            X=>[6,o.q_target.0 as u16,bit(o.c_condition),65535],
            Z=>[7,o.q_target.0 as u16,bit(o.c_condition),65535],
            CX=>[8,o.q_control1.0 as u16,o.q_target.0 as u16,bit(o.c_condition)],
            CZ=>[9,o.q_control1.0 as u16,o.q_target.0 as u16,bit(o.c_condition)],
            Hmr=>{assert!(o.c_condition==NO_BIT);[12,o.q_target.0 as u16,bit(o.c_target),65535]}
            CCX=>{assert!(o.c_condition==NO_BIT);[13,o.q_control2.0 as u16,o.q_control1.0 as u16,o.q_target.0 as u16]}
            PushCondition=>[15,bit(o.c_condition),65535,65535],
            PopCondition=>[16,65535,65535,65535],
            _=>panic!("peephole: unsupported operation {:?}",o.kind),
        }
    }
    fn set(&mut self,i:usize,r:[u16;4]){
        self.0[i]=if r[0]==peephole::TOMB{let mut o=Op::empty();o.kind=OperationType::DebugPrint;o}else{operation(r)};
    }
    fn expand(&mut self,i:usize,block:[[u16;4];3]){
        let mut o=Op::empty();o.kind=OperationType::DebugPrint;o.r_target=RegisterId(1);self.0[i]=o;
        assert!(self.1.last().map_or(true,|l|l.0<i));self.1.push((i,block));
    }
    fn block(&self,i:usize)->[[u16;4];3]{
        let j=self.1.binary_search_by_key(&i,|e|e.0).expect("peephole block");self.1[j].1
    }
}
/// Drop removed rows and splice in blocks, in place: a forward pass with a small carry queue
/// for the rare prefixes where blocks outgrow removals.
fn materialize(ops:&mut Vec<Op>,blocks:&[(usize,[[u16;4];3])]){
    let n=ops.len();let mut w=0usize;let mut bi=0usize;
    let mut q:std::collections::VecDeque<Op>=std::collections::VecDeque::new();
    for r in 0..n{
        let o=ops[r];
        if o.kind==OperationType::DebugPrint{
            if o.r_target!=NO_REG{
                assert_eq!(blocks[bi].0,r);
                for row in blocks[bi].1{q.push_back(operation(row));}
                bi+=1;
            }
        }else{q.push_back(o);}
        while w<=r{match q.pop_front(){Some(x)=>{ops[w]=x;w+=1;}None=>break}}
    }
    assert_eq!(bi,blocks.len());
    ops.truncate(w);
    if !q.is_empty(){ops.reserve_exact(q.len());ops.extend(q);}
}
struct Circuit(Vec<Op>);
impl RecordTarget for Circuit{
    fn read_prior(&mut self,i:usize)->[u16;4]{
        use OperationType::*;
        let o=self.0[i];let mut r=[o.kind as u16,65535,65535,65535];
        let bit=|x:BitId|if x==NO_BIT{65535}else{x.0 as u16};
        match o.kind{
            Register=>r[1]=o.r_target.0 as u16,
            AppendToRegister=>{r[1]=o.r_target.0 as u16;if o.c_target!=NO_BIT{r[0]=18;r[2]=bit(o.c_target);}else{r[2]=o.q_target.0 as u16;}}
            BitInvert|BitStore0|BitStore1=>{r[1]=bit(o.c_target);r[2]=bit(o.c_condition);}
            X|Z=>{r[1]=o.q_target.0 as u16;r[2]=bit(o.c_condition);}
            CX|CZ=>{r[1]=o.q_control1.0 as u16;r[2]=o.q_target.0 as u16;r[3]=bit(o.c_condition);}
            CCX=>{r[1]=o.q_control2.0 as u16;r[2]=o.q_control1.0 as u16;r[3]=o.q_target.0 as u16;}
            Hmr=>{r[1]=o.q_target.0 as u16;r[2]=bit(o.c_target);}
            PushCondition=>r[1]=bit(o.c_condition),PopCondition=>(),_=>panic!("unsupported history operation"),
        }r
    }
    fn append(&mut self,row:[u16;4]){self.0.push(operation(row));}
}
pub fn build()->Vec<Op>{
    const COUNT:usize=include!("gate_count.rs");
    let mut reader=zstd::stream::read::Decoder::new(&include_bytes!("gates.zst")[..]).expect("literal circuit stream");
    reader.window_log_max(30).expect("literal window");
    let plan=zstd::stream::decode_all(&include_bytes!("schedule.zst")[..]).expect("circuit schedule");
    // room for the merge step, which adds two CX per merged Toffoli before later steps shrink the list again
    let mut out=Circuit(Vec::with_capacity(COUNT+2_000_000));
    let n=schedule::expand(reader,&plan,&mut out).expect("invalid complete gate schedule");
    assert_eq!(n,COUNT);
    let mut ops=out.0;
    // Offline results of our cancellation + merging pass, round 1 (on the decoded list)
    prune(&mut ops,&include_bytes!("prune1.zst")[..],1824056597);
    merge(&mut ops,&include_bytes!("merge1.zst")[..],1988984);
    // RealAdii's exact peephole (unmodified), one pass at build time, as in 4fa40ba2
    let blocks={let mut v=OpRows(&mut ops,Vec::new());peephole::run(&mut v,1);v.1};
    materialize(&mut ops,&blocks);
    assert_eq!(ops.len(),1823888564);
    // Our pass again, round 2 (computed offline on the list as it stands here)
    prune(&mut ops,&include_bytes!("prune2.zst")[..],1822577498);
    merge(&mut ops,&include_bytes!("merge2.zst")[..],294850);
    assert_eq!(ops.len(),1823167198);
    ops
}
// Removes gates that provably cancel: pairs of identical self-inverse gates (CCX/CX/X) in the same condition-block
// instance with only commuting gates between them on their wires. `data` is a zstd stream of LEB128 run lengths
// over the current op list, alternating kept / deleted, starting with kept.
fn prune(ops:&mut Vec<Op>,data:&[u8],kept:usize){
    let runs=zstd::stream::decode_all(data).expect("prune mask");
    let (mut p,mut r,mut w,mut del)=(0usize,0usize,0usize,false);
    while p<runs.len(){
        let (mut len,mut sh)=(0usize,0u32);
        loop{let b=runs[p];p+=1;len|=((b&127) as usize)<<sh;if b&128==0{break;}sh+=7;}
        if !del{if w!=r{ops.copy_within(r..r+len,w);}w+=len;}
        r+=len;del=!del;
    }
    assert_eq!(r,ops.len());ops.truncate(w);assert_eq!(w,kept);
}
// Toffoli merging. prune() also deleted the first gate of each mergeable pair
//   CCX(a,b,t1) .. CCX(a,b,t)  ==  CX(t,t1) CCX(a,b,t) CX(t,t1)      (same controls)
//   CCX(x,b1,t) .. CCX(x,c,t)  ==  CX(b1,c) CCX(x,c,t) CX(b1,c)      (same target, one shared control)
// (the first gate commutes forward to the second). Here the surviving gate gets its two CX gates.
// `data`: per merge, LEB128 delta of the gate index in the pruned list, then CX control and target (u16 LE).
fn merge(ops:&mut Vec<Op>,data:&[u8],merges:usize){
    let raw=zstd::stream::decode_all(data).expect("merge list");
    let mut list:Vec<(usize,u16,u16)>=Vec::with_capacity(merges);
    let (mut p,mut idx)=(0usize,0usize);
    while p<raw.len(){
        let (mut d,mut sh)=(0usize,0u32);
        loop{let b=raw[p];p+=1;d|=((b&127) as usize)<<sh;if b&128==0{break;}sh+=7;}
        idx+=d;
        list.push((idx,u16::from_le_bytes([raw[p],raw[p+1]]),u16::from_le_bytes([raw[p+2],raw[p+3]])));p+=4;
    }
    assert_eq!(list.len(),merges);
    let n=ops.len();let (mut r,mut w)=(n,n+2*merges);
    ops.resize(w,Op::empty());
    for &(i,a,b) in list.iter().rev(){
        assert!(i<r&&ops[i].kind==OperationType::CCX);
        let len=r-(i+1);ops.copy_within(i+1..r,w-len);w-=len;
        let cx=operation([8,a,b,65535]);
        ops[w-1]=cx;ops[w-2]=ops[i];ops[w-3]=cx;w-=3;r=i;
    }
    assert_eq!(w,r);
}
