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
    let mut pending=Vec::with_capacity(block);
    let mut reordered=Vec::with_capacity(block);
    let mut finish_block=|rows:&[Row]|{
        let selected=if mirror_on {mirror.chunk(rows,&mut reordered);&reordered[..]} else {rows};
        cache.chunk(selected,|r|out.push(operation(r)));
    };
    let mut push=|row|{
        pending.push(row);
        if pending.len()==block {finish_block(&pending);pending.clear();}
    };
    for chunk in native.0.chunks(base::CHUNK){first.chunk(chunk.to_vec(),|row|affine.push(row,&mut push));}
    first.finish();affine.flush(&mut push);drop(push);
    if !pending.is_empty(){finish_block(&pending);}
    drop(finish_block);cache.finish();
    assert_eq!(out.len(),FINAL);
    out
}
