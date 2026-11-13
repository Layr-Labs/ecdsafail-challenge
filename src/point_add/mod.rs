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

// These modules are the same width-preserving passes used to replay the complete five-helper point.
mod first_pass;
#[path="compile/post.rs"] mod post;
#[path="compile/passes.rs"] mod passes;
type Row = [u16; 4];
const ORIGINAL: usize = 2_005_557_255;
const FINAL: usize = 1_974_368_957;

struct Native(Vec<Row>);
impl schedule::RecordTarget for Native {
    fn read_prior(&mut self, index: usize) -> Row { self.0[index] }
    fn append(&mut self, row: Row) { self.0.push(row); }
}

fn parent_rows(native: impl IntoIterator<Item=Row>, mut emit: impl FnMut(Row)) {
    let mut prune = first_pass::FirstPass::new(include_bytes!("prune1.zst"), include_bytes!("merge1.zst"));
    let mut branch = pass::Pass::new(646, 65530, 2);
    let mut affine = affine::Affine::new();
    let mut mirror = mirror::Mirror::new(646);
    let mut cache = cache::Cache::new(646, 0, 65531);
    let mut factor = factor::Factor::new(646, 8192);
    let mut ladder = ladder::Ladder::new(646, 8192);
    let mut after_factor = |row| ladder.push(row, &mut emit);
    let mut reordered = Vec::with_capacity(8192);
    let mut cached_block = |rows: &[Row]| {
        mirror.chunk(rows, &mut reordered);
        cache.chunk(&reordered, |row| factor.push(row, &mut after_factor));
    };
    let mut pending = Vec::with_capacity(8192);
    let mut after_affine = |row| {
        pending.push(row);
        if pending.len() == 8192 { cached_block(&pending); pending.clear(); }
    };
    let mut block = Vec::with_capacity(base::CHUNK);
    let mut after_prune = |row| {
        block.push(row);
        if block.len() == base::CHUNK {
            let full = std::mem::replace(&mut block, Vec::with_capacity(base::CHUNK));
            branch.chunk(full, |r| affine.push(r, &mut after_affine));
        }
    };
    let mut n = 0;
    for row in native { prune.push(row, &mut after_prune); n += 1; }
    assert_eq!(n, ORIGINAL);
    assert_eq!(prune.finish(), (2_002_420_545, 2_209_146));
    drop(after_prune);
    if !block.is_empty() { branch.chunk(block, |r| affine.push(r, &mut after_affine)); }
    branch.finish();
    affine.flush(&mut after_affine);
    drop(after_affine);
    if !pending.is_empty() { cached_block(&pending); }
    drop(cached_block);
    cache.finish();
    factor.finish(&mut after_factor);
    drop(after_factor);
    ladder.finish(&mut emit);
}

pub(super) fn optimized_rows(native: impl IntoIterator<Item=Row>, mut emit: impl FnMut(Row)) {
    let mut pass = passes::Passes::new(646, 8192);
    let mut parent_count = 0usize;
    parent_rows(native, |r| { parent_count += 1; pass.push(r, &mut emit); });
    assert_eq!(parent_count, 1_980_680_566);
    pass.finish(&mut emit);
    assert_eq!(pass.output, FINAL as u64);
}

pub fn build() -> Vec<Op> {
    let mut literals = zstd::stream::read::Decoder::new(&include_bytes!("gates.zst")[..]).expect("gate literals");
    literals.window_log_max(30).expect("gate window");
    let plan = zstd::stream::decode_all(&include_bytes!("schedule.zst")[..]).expect("gate schedule");
    let mut native = Native(Vec::with_capacity(ORIGINAL));
    assert_eq!(schedule::expand(literals, &plan, &mut native).expect("native point"), ORIGINAL);
    let mut output = Vec::with_capacity(FINAL);
    optimized_rows(native.0, |row| output.push(operation(row)));
    assert_eq!(output.len(), FINAL);
    output
}
