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
/// M2E_SHELL (ob-shell): `apply` when every op fits the peephole's u16 rows (the base stream: unchanged). Otherwise the stream is
/// cut into windows at condition depth 0: at most 60,000 distinct bits per window (renumbered into 0.. for the pass and mapped
/// back), and a window holding an op the rows cannot carry (CCZ, conditioned CCX / HMR, ...) is passed through unchanged; such a
/// window closes once 10,000 ops pass without one, so the long walk regions are peepholed. Exact: every peephole rewrite is an
/// identity on every basis state of the ops it sees (no initial-state use), and windows start outside every condition block.
fn peep_ok(o:&Op)->bool{
    use OperationType::*;
    match o.kind{
        DebugPrint|Register|AppendToRegister|BitInvert|BitStore0|BitStore1|X|Z|CX|CZ|Swap|PushCondition|PopCondition=>true,
        Hmr|CCX=>o.c_condition==NO_BIT,
        _=>false,
    }
}
pub fn apply_windowed(ops:Vec<Op>)->Vec<Op>{
    let bits=|o:&Op|[o.c_target,o.c_condition];
    if ops.iter().all(|o|peep_ok(o)&&bits(o).iter().all(|b|*b==NO_BIT||b.0<65535)){return apply(ops);}
    let mut out:Vec<Op>=Vec::with_capacity(ops.len());
    let mut win:Vec<Op>=Vec::new();
    let mut map:std::collections::HashMap<u64,u64>=std::collections::HashMap::new();
    let mut back:Vec<u64>=Vec::new();
    let (mut depth,mut nwin,mut npass,mut dirty,mut since)=(0i64,0usize,0usize,false,0usize);
    let flush=|win:&mut Vec<Op>,map:&mut std::collections::HashMap<u64,u64>,back:&mut Vec<u64>,out:&mut Vec<Op>,dirty:bool|{
        let w=if dirty{std::mem::take(win)}else{apply(std::mem::take(win))};
        for mut o in w{
            if o.c_target!=NO_BIT{o.c_target=BitId(back[o.c_target.0 as usize]);}
            if o.c_condition!=NO_BIT{o.c_condition=BitId(back[o.c_condition.0 as usize]);}
            out.push(o);
        }
        map.clear();back.clear();
    };
    for mut o in ops{
        let ok=peep_ok(&o);
        if depth==0&&!win.is_empty()&&(map.len()>=60_000||(!dirty&&!ok)||(dirty&&since>=10_000)){
            flush(&mut win,&mut map,&mut back,&mut out,dirty);nwin+=1;if dirty{npass+=1;}dirty=false;since=0;
        }
        if !ok{dirty=true;since=0;}else{since+=1;}
        for f in [&mut o.c_target,&mut o.c_condition]{
            if *f!=NO_BIT{
                let n=back.len() as u64;
                let l=*map.entry(f.0).or_insert_with(||{back.push(f.0);n});
                *f=BitId(l);
            }
        }
        match o.kind{OperationType::PushCondition=>depth+=1,OperationType::PopCondition=>depth-=1,_=>{}}
        win.push(o);
    }
    if dirty{npass+=1;}
    flush(&mut win,&mut map,&mut back,&mut out,dirty);
    eprintln!("peephole_hook: windowed: {} windows, {} passed through (ops the rows cannot carry)",nwin+1,npass);
    out
}
