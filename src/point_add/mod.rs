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
use schedule::RecordTarget;
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
    let mut out=Circuit(Vec::with_capacity(COUNT));
    let n=schedule::expand(reader,&plan,&mut out).expect("invalid complete gate schedule");
    assert_eq!(n,COUNT);out.0
}
