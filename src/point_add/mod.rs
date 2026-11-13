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
mod gadget_merge;
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
    // Added by almond-lab, after the parent's own passes (everything above is the parent's build, unchanged).
    // Gadget merging: adjacent dirty-borrow toggle gadgets on the same toggle are merged (see gadget_merge.rs).
    // It runs in place on the final list, which only shrinks, so nothing is reallocated.
    let (chains,removed)=gadget_merge::gadget_merge(&mut output,row_of,operation);
    assert_eq!((chains,removed,output.len()),(977675,3910700,1972413607));
    output
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

