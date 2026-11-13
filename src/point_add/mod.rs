use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};
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
#[path="compile/optimize.rs"] mod base;
#[path="compile/cleanup.rs"] mod cleanup;
#[path="compile/pass.rs"] mod pass;
#[path="compile/affine.rs"] mod affine;
#[path="compile/values.rs"] mod values;
#[path="compile/cache.rs"] mod cache;
#[path="compile/mirror.rs"] mod mirror;
#[path="compile/factor.rs"] mod factor;
#[path="compile/ladder.rs"] mod ladder;
mod gadget_merge;

type Row = [u16;4];
struct Native(Vec<Row>);
impl schedule::RecordTarget for Native {
    fn read_prior(&mut self,index:usize)->Row {self.0[index]}
    fn append(&mut self,row:Row){self.0.push(row);}
}

pub fn build()->Vec<Op> {
    const ORIGINAL:usize=include!("gate_count.rs");
    const FINAL:usize=include!("optimized_count.rs");
    const CONFIG:(usize,usize,usize,bool)=include!("config.rs");
    let (width,extra,block,mirror_on)=CONFIG;
    let mut literals=zstd::stream::read::Decoder::new(&include_bytes!("gates.zst")[..]).expect("gate literals");
    literals.window_log_max(30).expect("gate window");
    let plan=zstd::stream::decode_all(&include_bytes!("schedule.zst")[..]).expect("gate schedule");
    let mut native=Native(Vec::with_capacity(ORIGINAL));
    assert_eq!(schedule::expand(literals,&plan,&mut native).expect("gate schedule"),ORIGINAL);
    let mut out=Vec::with_capacity(FINAL);
    let mut first=pass::Pass::new(width,12000,2);
    let mut affine=affine::Affine::new();
    let mut mirror=mirror::Mirror::new(width);
    let mut cache=cache::Cache::new(width,extra,12001);
    let mut post=factor::Factor::new(width+extra,8192);
    let mut ladders=ladder::Ladder::new(width+extra,8192);
    let mut emit=|row|out.push(operation(row));
    let mut after_factor=|row|ladders.push(row,&mut emit);
    let mut pending=Vec::with_capacity(block);
    let mut reordered=Vec::with_capacity(block);
    let mut finish_block=|rows:&[Row]|{
        let selected=if mirror_on {mirror.chunk(rows,&mut reordered);&reordered[..]} else {rows};
        cache.chunk(selected,|row|post.push(row,&mut after_factor));
    };
    let mut push=|row|{
        pending.push(row);
        if pending.len()==block {finish_block(&pending);pending.clear();}
    };
    for chunk in native.0.chunks(base::CHUNK){first.chunk(chunk.to_vec(),|row|affine.push(row,&mut push));}
    first.finish();affine.flush(&mut push);drop(push);
    if !pending.is_empty(){finish_block(&pending);}
    drop(finish_block);cache.finish();
    post.finish(&mut after_factor);
    drop(after_factor);
    ladders.finish(&mut emit);
    assert_eq!(out.len(),FINAL);
    // Added by almond-lab, after the parent's own passes (everything above is the parent's build, unchanged).
    // 1. Gadget merging: adjacent dirty-borrow toggle gadgets on the same toggle are merged (see gadget_merge.rs).
    let (chains,removed)=gadget_merge::gadget_merge(&mut out,row_of,operation);
    assert_eq!((chains,removed,out.len()),(1399008,5596032,1317831613));
    // Offline result of our exact whole-circuit cancellation + merging pass on the list as it stands here.
    // prune() shrinks the list and merge() grows it by two CX per merge; it stays below its capacity FINAL.
    prune(&mut out,&include_bytes!("prune1.zst")[..],1316294144);
    merge(&mut out,&include_bytes!("merge1.zst")[..],19863);
    assert_eq!(out.len(),1316333870);
    out
}
// The packaged record [kind, a, b, c] of an op (inverse of operation()).
fn row_of(o:&Op)->[u16;4]{
    use OperationType::*;
    let bit=|x:BitId|if x==NO_BIT{65535u16}else{x.0 as u16};
    let mut r=[0u16,65535,65535,65535];
    match o.kind{
        Register=>{r[0]=1;r[1]=o.r_target.0 as u16;}
        AppendToRegister=>{r[1]=o.r_target.0 as u16;if o.c_target!=NO_BIT{r[0]=18;r[2]=bit(o.c_target);}else{r[0]=2;r[2]=o.q_target.0 as u16;}}
        BitInvert=>{r[0]=3;r[1]=bit(o.c_target);r[2]=bit(o.c_condition);}
        BitStore0=>{r[0]=4;r[1]=bit(o.c_target);r[2]=bit(o.c_condition);}
        BitStore1=>{r[0]=5;r[1]=bit(o.c_target);r[2]=bit(o.c_condition);}
        X=>{r[0]=6;r[1]=o.q_target.0 as u16;r[2]=bit(o.c_condition);}
        Z=>{r[0]=7;r[1]=o.q_target.0 as u16;r[2]=bit(o.c_condition);}
        CX=>{r[0]=8;r[1]=o.q_control1.0 as u16;r[2]=o.q_target.0 as u16;r[3]=bit(o.c_condition);}
        CZ=>{r[0]=9;r[1]=o.q_control1.0 as u16;r[2]=o.q_target.0 as u16;r[3]=bit(o.c_condition);}
        Hmr=>{r[0]=12;r[1]=o.q_target.0 as u16;r[2]=bit(o.c_target);}
        CCX=>{r[0]=13;r[1]=o.q_control2.0 as u16;r[2]=o.q_control1.0 as u16;r[3]=o.q_target.0 as u16;}
        PushCondition=>{r[0]=15;r[1]=bit(o.c_condition);}
        PopCondition=>{r[0]=16;}
        _=>panic!("row_of: unsupported operation"),
    }
    r
}
// Removes gates that provably cancel: pairs of identical self-inverse gates (CCX/CX/X) in the same condition-block
// instance with only commuting gates between them on their wires. The data is a zstd stream of LEB128 run lengths
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

