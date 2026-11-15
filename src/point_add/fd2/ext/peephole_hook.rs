// Self-contained exact build() peephole hook (RealAdii rows 72ac5500, 6aef5188): wraps any build() that returns Vec<Op>.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_REG};
use super::peephole;
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
/// Packaged-row view of the decoded op list for the exact peephole pass (removed ops are DEBUG_PRINT
/// placeholders until the final compaction drops them).
struct OpRows<'a>(&'a mut Vec<Op>,Vec<(usize,[[u16;4];3])>);
impl peephole::Rows for OpRows<'_>{
    fn len(&self)->usize{self.0.len()}
    fn get(&self,i:usize)->[u16;4]{
        use OperationType::*;
        let o=self.0[i];
        let bit=|x:BitId|if x==NO_BIT{65535}else{assert!(x.0<65535,"peephole: bit id exceeds u16 rows");x.0 as u16};
        let qb=|q:QubitId|{assert!(q.0<65535,"peephole: qubit id exceeds u16 rows");q.0 as u16};
        match o.kind{
            DebugPrint=>if o.r_target==NO_REG{[peephole::TOMB,65535,65535,65535]}else{[peephole::BLOCK,65535,65535,65535]},
            Register=>[1,o.r_target.0 as u16,65535,65535],
            AppendToRegister=>if o.c_target!=NO_BIT{[18,o.r_target.0 as u16,bit(o.c_target),65535]}else{[2,o.r_target.0 as u16,qb(o.q_target),65535]},
            BitInvert=>[3,bit(o.c_target),bit(o.c_condition),65535],
            BitStore0=>[4,bit(o.c_target),bit(o.c_condition),65535],
            BitStore1=>[5,bit(o.c_target),bit(o.c_condition),65535],
            X=>[6,qb(o.q_target),bit(o.c_condition),65535],
            Z=>[7,qb(o.q_target),bit(o.c_condition),65535],
            CX=>[8,qb(o.q_control1),qb(o.q_target),bit(o.c_condition)],
            CZ=>[9,qb(o.q_control1),qb(o.q_target),bit(o.c_condition)],
            Swap=>[10,qb(o.q_control1),qb(o.q_target),bit(o.c_condition)],
            Hmr=>{assert!(o.c_condition==NO_BIT);[12,qb(o.q_target),bit(o.c_target),65535]}
            CCX=>{assert!(o.c_condition==NO_BIT);[13,qb(o.q_control2),qb(o.q_control1),qb(o.q_target)]}
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
pub fn apply(mut ops:Vec<Op>)->Vec<Op>{
    let blocks={let mut v=OpRows(&mut ops,Vec::new());peephole::run(&mut v,1);v.1};
    materialize(&mut ops,&blocks);
    ops
}
