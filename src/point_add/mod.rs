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
#[path = "compile/optimize.rs"]
mod base;
#[path = "compile/cleanup.rs"]
mod cleanup;
#[path = "compile/pass.rs"]
mod pass;
#[path = "compile/affine.rs"]
mod affine;

struct Native(Vec<[u16; 4]>);
impl schedule::RecordTarget for Native {
    fn read_prior(&mut self, i: usize) -> [u16; 4] { self.0[i] }
    fn append(&mut self, row: [u16; 4]) { self.0.push(row); }
}

fn build_base()->Vec<Op>{
    const ORIGINAL: usize = include!("gate_count.rs");
    const FINAL: usize = include!("optimized_count.rs");
    const MEASUREMENT_BIT: u16 = include!("measurement_bit.rs");
    let mut literals = zstd::stream::read::Decoder::new(&include_bytes!("gates.zst")[..])
        .expect("gate literals");
    literals.window_log_max(30).expect("gate window");
    let plan = zstd::stream::decode_all(&include_bytes!("schedule.zst")[..]).expect("gate schedule");
    let mut raw = Native(Vec::with_capacity(ORIGINAL));
    assert_eq!(schedule::expand(literals, &plan, &mut raw).expect("gate schedule"), ORIGINAL);
    let mut gates = Vec::with_capacity(FINAL);
    let mut compiler = pass::Pass::new(648, MEASUREMENT_BIT, 2);
    let mut affine = affine::Affine::new();
    for chunk in raw.0.chunks(base::CHUNK) {
        compiler.chunk(chunk.to_vec(), |row| affine.push(row, |gate| gates.push(operation(gate))));
    }
    compiler.finish();
    affine.flush(|gate| gates.push(operation(gate)));
    assert_eq!(gates.len(), FINAL);
    gates
}

mod rpeephole;
mod rpeephole_hook;
/// Exact CCX peephole (RealAdii 72ac5500/6aef5188) over the finished op list.
pub fn build()->Vec<Op>{rpeephole_hook::apply(build_base())}
