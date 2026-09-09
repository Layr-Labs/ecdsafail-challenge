//! Rank5 physical inversion lifecycle. Complete point-add validation is separate.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType,NO_QUBIT,QubitId};
const FIELD_WIDTH:usize=257;const VALUE_WIDTH:usize=256;const WORK_WIDTH:usize=259;
const HALF_PLUS_ONE_LE:[u8;33]={let mut b=[0xff;33];b[0]=0x18;b[1]=0xfe;b[3]=0x7f;b[31]=0x7f;b[32]=0;b};
struct Core {rank:Vec<QReg>,a:Vec<QReg>,c:Vec<QReg>,sm:Vec<QReg>,phase1:QReg,phase2:QReg,iteration:QReg,work1:Vec<QReg>,work2:Vec<QReg>}
struct Terminal {iteration:QReg,work2:Vec<QReg>,history:Vec<QReg>}
fn free_clean(circ: &mut Circuit, register: Vec<QReg>) {
    for lane in register {
        circ.zero_and_free(lane);
    }
}
fn allocate_work1(circ:&mut Circuit,name:&str)->Vec<QReg>{
    if super::q796_parity::enabled(){let mut word=circ.alloc_qreg_bits(name,258);word.push(QReg::omitted_lane_marker());word}else{circ.alloc_qreg_bits(name,259)}
}
fn free_work1(circ:&mut Circuit,mut word:Vec<QReg>){
    if super::q796_parity::enabled(){let hole=word.pop().unwrap();assert_eq!(hole.id(),u32::MAX);drop(hole);}free_clean(circ,word);
}

fn toggle_constant(circ: &mut Circuit, register: &[QReg], value: usize) {
    for (index, lane) in register.iter().enumerate() {
        if (value >> index) & 1 != 0 {
            circ.x(lane);
        }
    }
}

fn toggle_initial_work1(circ: &mut Circuit, work1: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    assert_eq!(work1.len(), WORK_WIDTH);
    circ.x(&work1[0]);
    for bit in 0..VALUE_WIDTH {
        if (SECP256K1_P_LE[bit / 8] >> (bit % 8)) & 1 != 0 {
            if bit!=0||!super::q796_parity::enabled(){circ.x(&work1[WORK_WIDTH - 1 - bit]);}
        }
    }
}

fn toggle_terminal_work1(circ: &mut Circuit, work1: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    assert_eq!(work1.len(), WORK_WIDTH);
    for bit in 0..VALUE_WIDTH {
        if (SECP256K1_P_LE[bit / 8] >> (bit % 8)) & 1 != 0 {
            circ.x(&work1[bit]);
        }
    }
    if !super::q796_parity::enabled(){circ.x(&work1[WORK_WIDTH - 1]);}
}


fn ids(core:&Core)->Vec<usize> {
    let mut out:Vec<_>=core.rank.iter().chain(&core.a).chain(&core.c).chain(&core.sm).map(|q|q.id()as usize).collect();
    out.extend([core.phase1.id(),core.phase2.id(),core.iteration.id()].into_iter().map(|i|i as usize));
    out.extend(core.work1.iter().chain(&core.work2).map(|q|q.id()as usize));assert_eq!(out.len(),542);out
}
fn dual_phase()->bool{super::metadata_muxlease::active("Q795_PHASE_LOAN")}
fn initialize(circ:&mut Circuit,mut dx:Vec<QReg>,phase_passenger:&QReg,second_passenger:&QReg)->Core {
    use super::shrunken_pz_state_machine::controlled_field_neg;
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    assert_eq!(dx.len(),257);let iteration=circ.alloc_qreg("rank5.iteration");
    compare_geq_const(circ,&dx,&HALF_PLUS_ONE_LE,&iteration);controlled_field_neg(circ,&iteration,&dx);
    dx.push(circ.alloc_qreg("rank5.work2-pad0"));dx.push(circ.alloc_qreg("rank5.work2-pad1"));dx.reverse();
    let work1=allocate_work1(circ,"rank5.work1");toggle_initial_work1(circ,&work1);
    let phase2=phase_passenger.borrowed_alias();
    circ.cx(&phase2,&work1[0]);circ.cx(&work1[0],&phase2);circ.cx(&phase2,&work1[0]);circ.x(&phase2);
    let phase1=if dual_phase(){let p=second_passenger.borrowed_alias();circ.cx(&p,&dx[2]);circ.cx(&dx[2],&p);circ.cx(&p,&dx[2]);p}else{circ.alloc_qreg("rank5.P1")};
    Core {rank:circ.alloc_qreg_bits("rank5.rank",5),a:circ.alloc_qreg_bits("rank5.a",6),c:circ.alloc_qreg_bits("rank5.c",6),sm:circ.alloc_qreg_bits("rank5.sm",4),phase1,phase2,iteration,work1,work2:dx}
}
fn release_terminal(circ:&mut Circuit,mut core:Core)->Terminal {
    // Terminal phase00: return the passenger carried in the coefficient head.
    circ.x(&core.phase2);circ.cx(&core.phase2,&core.work1[255]);circ.cx(&core.work1[255],&core.phase2);circ.cx(&core.phase2,&core.work1[255]);
    if dual_phase(){circ.cx(&core.phase1,&core.work2[257]);circ.cx(&core.work2[257],&core.phase1);circ.cx(&core.phase1,&core.work2[257]);}
    toggle_terminal_work1(circ,&core.work1);free_work1(circ,core.work1);
    toggle_constant(circ,&core.rank,29);free_clean(circ,core.rank);toggle_constant(circ,&core.a,63);free_clean(circ,core.a);
    let high=core.sm.split_off(2);free_clean(circ,high);let mut history=core.c;history.extend(core.sm);assert_eq!(history.len(),8);
    if dual_phase(){drop(core.phase1);}else{circ.zero_and_free(core.phase1);}drop(core.phase2); // non-owning passenger views
    Terminal {iteration:core.iteration,work2:core.work2,history}
}
fn rebuild_terminal(circ:&mut Circuit,mut terminal:Terminal,phase_passenger:&QReg,second_passenger:&QReg)->Core {
    let work1=allocate_work1(circ,"rank5.work1.rebuilt");toggle_terminal_work1(circ,&work1);
    let rank=circ.alloc_qreg_bits("rank5.rank.rebuilt",5);toggle_constant(circ,&rank,29);
    let a=circ.alloc_qreg_bits("rank5.a.rebuilt",6);toggle_constant(circ,&a,63);
    let mut sm=terminal.history.split_off(6);sm.extend(circ.alloc_qreg_bits("rank5.sm.high.rebuilt",2));
    let phase2=phase_passenger.borrowed_alias();
    circ.cx(&phase2,&work1[255]);circ.cx(&work1[255],&phase2);circ.cx(&phase2,&work1[255]);circ.x(&phase2);
    let phase1=if dual_phase(){let p=second_passenger.borrowed_alias();circ.cx(&p,&terminal.work2[257]);circ.cx(&terminal.work2[257],&p);circ.cx(&p,&terminal.work2[257]);p}else{circ.alloc_qreg("rank5.P1.rebuilt")};
    Core {rank,a,c:terminal.history,sm,phase1,phase2,iteration:terminal.iteration,work1,work2:terminal.work2}
}
fn finish(circ:&mut Circuit,mut core:Core)->Vec<QReg> {
    use super::shrunken_pz_state_machine::controlled_field_neg;
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    circ.x(&core.phase2);circ.cx(&core.phase2,&core.work1[0]);circ.cx(&core.work1[0],&core.phase2);circ.cx(&core.phase2,&core.work1[0]);
    if dual_phase(){circ.cx(&core.phase1,&core.work2[2]);circ.cx(&core.work2[2],&core.phase1);circ.cx(&core.phase1,&core.work2[2]);drop(core.phase1);}else{circ.zero_and_free(core.phase1);}drop(core.phase2);
    toggle_initial_work1(circ,&core.work1);free_work1(circ,core.work1);free_clean(circ,core.rank);free_clean(circ,core.a);free_clean(circ,core.c);free_clean(circ,core.sm);
    core.work2.reverse();circ.zero_and_free(core.work2.pop().unwrap());circ.zero_and_free(core.work2.pop().unwrap());assert_eq!(core.work2.len(),257);
    controlled_field_neg(circ,&core.iteration,&core.work2);compare_geq_const(circ,&core.work2,&HALF_PLUS_ONE_LE,&core.iteration);circ.zero_and_free(core.iteration);core.work2
}
fn toggle_inverse_sign(circ:&mut Circuit,terminal:&Terminal) {
    use super::shrunken_pz_state_machine::controlled_field_neg;
    circ.x(&terminal.iteration);controlled_field_neg(circ,&terminal.iteration,&terminal.work2[..257]);circ.x(&terminal.iteration);
}
/// Logical primitive template; physical remapping preserves every alias relation.
fn template(block:usize,j:usize)->Vec<Op> {
    let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("borrowed_phase");let iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("other_borrowed",23);assert_eq!(circ.b.next_qubit,565);
    if dual_phase(){super::q795_step::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&iter,&w1,&w2,&helpers,j,block);}else{super::q797_step_transport::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&iter,&w1,&w2,&helpers,j,block);}assert_eq!(circ.b.next_qubit,565);
    let b=circ.into_builder();assert!(b.ops.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
    if super::q796_parity::enabled(){let hole=w1[258].id()as u64;assert!(b.ops.iter().all(|o|o.q_target.0!=hole&&o.q_control1.0!=hole&&o.q_control2.0!=hole),"omitted r0 still emitted");}b.ops
}
pub fn sprint_census(){
 let mut total_ops=0usize;let mut total_t=0usize;let mut compressed=0u64;
 let sample=std::env::var("Q799_COMPRESS_SAMPLE").ok().as_deref()==Some("1");
 let only=std::env::var("Q799_CENSUS_BLOCK").ok().map(|s|s.parse::<usize>().unwrap());
 for block in 0..26 {if only.is_some_and(|b|b!=block){continue;}
  for j in 0..4 {let ops=template(block,j);let t=ops.iter().filter(|o|o.kind==OperationType::CCX).count();let copies=if block==25{4}else{16};total_ops+=copies*ops.len();total_t+=copies*t;eprintln!("Q799_TEMPLATE block={block} j={j} ops={} T={t} copies={copies}",ops.len());if sample{compressed+=copies as u64*compressed_sample(&ops);}}
 }
 eprintln!("Q799_CENSUS_TOTAL traversal_ops={total_ops} traversal_T={total_t} complete={}",only.is_none());
 if sample{eprintln!("Q799_COMPRESSION_SAMPLE weighted_four_traversal_bytes={} core_raw_bytes={} complete={} level=3 scope=independent_template_frames_not_actual_remapped_whole_upload; no file written",compressed*4,total_ops as u64*4*56,only.is_none());}
}
fn compressed_sample(ops:&[Op])->u64{
 use std::io::Write;struct Counter(u64);impl Write for Counter{fn write(&mut self,b:&[u8])->std::io::Result<usize>{self.0+=b.len()as u64;Ok(b.len())}fn flush(&mut self)->std::io::Result<()>{Ok(())}}
 let mut encoder=zstd::stream::write::Encoder::new(Counter(0),3).unwrap();let mut record=[0u8;56];
 for op in ops{record[..4].copy_from_slice(&(op.kind as u32).to_le_bytes());for(i,v)in[op.q_control2.0,op.q_control1.0,op.q_target.0,op.c_target.0,op.c_condition.0,op.r_target.0].into_iter().enumerate(){record[8+8*i..16+8*i].copy_from_slice(&v.to_le_bytes());}encoder.write_all(&record).unwrap();}encoder.finish().unwrap().0
}
fn remap(mut ops:Vec<Op>,core_ids:&[usize],passenger:&[QReg],inverse:bool)->Vec<Op> {
    assert_eq!(core_ids.len(),542);let first=if dual_phase(){assert_eq!(core_ids[21],passenger[1].id()as usize);2}else{1};assert!(passenger.len()>=first+23);assert_eq!(core_ids[22],passenger[0].id()as usize);let mut mapping=core_ids.to_vec();mapping.extend(passenger[first..first+23].iter().map(|q|q.id()as usize));
    let mut unique=mapping.clone();unique.sort_unstable();unique.dedup();assert_eq!(unique.len(),565);
    for op in &mut ops {for q in [&mut op.q_control1,&mut op.q_control2,&mut op.q_target] {if *q!=NO_QUBIT{let physical=mapping[q.0 as usize];assert_ne!(physical,u32::MAX as usize,"omitted lane appeared in emitted stream");*q=QubitId(physical as u64);}}op.validate();}
    if inverse{ops.reverse();}ops
}
#[path="rank5_lifecycle_check.rs"]pub mod check;

struct CanonicalTopLoan {
    restored: bool,
    context: &'static str,
}

impl Drop for CanonicalTopLoan {
    fn drop(&mut self) {
        assert!(
            self.restored || std::thread::panicking(),
            "{} canonical top loan dropped without restore",
            self.context
        );
    }
}

/// Lend a canonical field register's known-zero extension lane to the EEA.
/// The replacement lane need not retain physical identity because the 257th
/// lane is internal, canonical zero state rather than ABI-visible data.
fn loan_canonical_top(
    circ: &mut Circuit,
    register: &mut Vec<QReg>,
    context: &'static str,
) -> CanonicalTopLoan {
    assert_eq!(
        register.len(),
        FIELD_WIDTH,
        "{context} canonical register width"
    );
    let live_before = circ.b.active_qubits;
    let top = register.pop().expect("canonical top lane");
    circ.zero_and_free(top);
    assert_eq!(register.len(), FIELD_WIDTH - 1);
    assert_eq!(
        circ.b.active_qubits + 1,
        live_before,
        "{context} canonical top loan must free one qubit"
    );
    circ.lowq_passenger_top_releases += 1;
    CanonicalTopLoan {
        restored: false,
        context,
    }
}

fn restore_canonical_top(circ: &mut Circuit, register: &mut Vec<QReg>, mut loan: CanonicalTopLoan) {
    assert_eq!(
        register.len(),
        FIELD_WIDTH - 1,
        "{} shortened canonical register width",
        loan.context
    );
    let live_before = circ.b.active_qubits;
    register.push(circ.alloc_qreg(&format!("{}.restored", loan.context)));
    assert_eq!(register.len(), FIELD_WIDTH);
    assert_eq!(
        circ.b.active_qubits,
        live_before + 1,
        "{} canonical top restore must allocate one clean qubit",
        loan.context
    );
    assert!(
        circ.lowq_passenger_top_releases > 0,
        "passenger top loan state underflow"
    );
    circ.lowq_passenger_top_releases -= 1;
    loan.restored = true;
}


pub fn enabled()->bool {std::env::var("LOWQ_RANK5_EEA").ok().as_deref()==Some("1")}
pub(crate) const CANDIDATE_OPS:usize=1_000_830_129;
pub(crate) const CANDIDATE_TOFFOLI:usize=587_431_812;
pub(crate) fn candidate_configuration()->bool{
    ["Q799_MUX_LEASE","Q799_MUX_QUOTIENT","Q799_XOR_LO","Q799_PREFIX_TREE","Q799_T11_FIRST","Q799_HEAD_TREE"].iter().all(|s|super::metadata_muxlease::active(s))
    && !super::metadata_muxlease::active("Q799_T11_COMPARE") && std::env::var("Q799_CANCEL_WINDOW").ok().as_deref()==Some("2048")
    && super::q796_parity::enabled()
    && dual_phase() && super::metadata_muxlease::active("Q795_COMPARE_PEBBLE")
    && ["Q796_R01_CACHE","Q796_R01_CLEAN","Q796_PREFIX_MASK_LOAN","Q796_DECODER_TRANSITION","Q796_DECODER_ANF","Q796_R00_CACHE","Q796_R00_SUPPORT"].iter().all(|s|super::metadata_muxlease::active(s))
    && ["Q796_PREFIX_SUPPORT","Q796_PREFIX_FACTORS","Q796_MUX_POLARITY"].iter().all(|s|std::env::var(s).ok().as_deref()!=Some("0"))
    && std::env::var("Q795_CORE_CANCEL").ok().as_deref()==Some("4096")
    && ["Q795_SIGN_TRANSITION","Q796_SIGN_MASK_LOAN","Q795_ENTRY_FACTOR"].iter().all(|s|super::metadata_muxlease::active(s))
    && ["Q795_CARGO_PAIR","Q795_R01_GUARD_NARROW","Q795_T11_DIRECT_CARRY","Q795_T10_QUOTIENT_PAIR","Q795_DECODER_DERIVATIVE","Q795_DECODER_FACTOR","Q795_DECODER_UNGUARDED"].iter().all(|s|super::metadata_muxlease::active(s))
    && std::env::var("Q795_R01_LOW_PREFIX").ok().as_deref()==Some("2")
    && std::env::var("Q795_R00_PREFIX").ok().as_deref()==Some("1")
    && ["Q795_C1_PREFIX_TRANSITION","Q795_SIGN_PAIR_UNGUARDED","Q795_R00_PAIR_UNGUARDED","Q795_R00_DATA_CLEAN_EXTENSION","Q795_AUPDATE_PREFIX_TRANSITION","Q795_AUPDATE_PERM_UNGUARDED","Q795_R01_DATA_UNGUARDED","Q795_EXIT_PERM_CLEAN","Q795_R00_PREFIX_TRANSITION","Q795_R01_PREFIX_TRANSITION","Q795_ENTRY_OUTPUT_ERASE"].iter().all(|s|super::metadata_muxlease::active(s))
    && [("Q795_C1_ACTIVE_PREFIX","8"),("Q795_R00_CACHE_CLEAN","2"),("Q795_R00_LOWER_BITS","2"),("Q795_R00_UPPER_BITS","3"),("Q795_EXIT_PREFIX","5"),("Q795_AUPDATE_PREFIX","6")].iter().all(|&(s,v)|std::env::var(s).ok().as_deref()==Some(v))
    && ["Q795_R00_TWO_PASS","Q795_SIGN_TWO_PASS","Q795_R01_BASIS_CLEAN_EXTENSION"].iter().all(|s|super::metadata_muxlease::active(s))
    && ["Q795_C1_TWO_PASS","Q795_R01_TWO_PASS","Q795_R01_LOWER_CONDITIONAL_SCRATCH","Q795_SIGN_G_SCRATCH_DATA","Q795_SIGN_G_SCRATCH_MASK","Q795_T10_TOP_TWO_PASS"].iter().all(|s|super::metadata_muxlease::active(s))
    && ["Q795_SIGN_JOINT_PREFIX","Q795_R01_JOINT_LOW"].iter().all(|s|std::env::var(s).ok().is_none_or(|v|v=="0"))
    && !super::metadata_muxlease::active("Q795_PAIR_TWO")
    && ["Q795_T10_TOP_MASK_CLEAN","Q795_R01_CACHE_RANK_CLEAN","Q795_R01_CACHE_CARRY_CLEAN","Q795_T10_FUSED"].iter().all(|s|super::metadata_muxlease::active(s))
    && super::metadata_muxlease::active("Q795_R01_FUSED")
    && ["Q795_SIGN_TOP_LOAN_FUSION","Q795_SIGN_SUM_SUPPORT","Q795_AFFINE_TRUTH_SWAP"].iter().all(|s|super::metadata_muxlease::active(s))
}
fn emit_schedule(circ:&mut Circuit,core:&Core,passenger:&[QReg],inverse:bool) {
    assert!(circ.b.count_only_capture_stack.is_empty());circ.b.flush_compact_block();let mapping=ids(core);
    for z in 0..26 {let block=if inverse{25-z}else{z};let mut cached=Vec::new();
        for j in 0..4 {let ops=remap(template(block,j),&mapping,passenger,inverse);let mut kinds=[0usize;18];for op in &ops{kinds[op.kind as usize]+=1;}cached.push((std::sync::Arc::new(ops),kinds));}
        let first=block*64;let end=(first+64).min(1616);
        for i in 0..end-first {let step=if inverse{end-1-i}else{first+i};let (ops,kinds)=&cached[(step+1)%4];
            if circ.b.compact_blocks.is_some(){assert!(circ.b.ops.is_empty());circ.b.compact_blocks.as_mut().unwrap().push(ops.clone());for kind in [OperationType::X,OperationType::CX,OperationType::CCX]{circ.b.add_counted_kind(kind,kinds[kind as usize]);}}
            else if circ.b.count_only&&circ.b.fiat_hash.is_none(){if let Some(check)=&mut circ.b.sprint_sim{check.apply(ops);}for kind in [OperationType::X,OperationType::CX,OperationType::CCX]{circ.b.add_counted_kind(kind,kinds[kind as usize]);}}
            else{for &op in ops.iter(){circ.b.push_op(op);}}
        }
    }
}
fn emit_forward(circ:&mut Circuit,core:&Core,passenger:&[QReg]){emit_schedule(circ,core,passenger,false);}
fn emit_reverse(circ:&mut Circuit,core:&Core,passenger:&[QReg]){emit_schedule(circ,core,passenger,true);}
fn canonicalize_terminal_work2(_circ:&mut Circuit,_terminal:&Terminal){}
fn restore_terminal_work2_rotation(_circ:&mut Circuit,_terminal:&Terminal){}

// Canonical Work2 is coefficient ||000. Keep the257-bit field view and
// temporarily release its two unused high zeros during outer multiplication.
fn release_terminal_padding(circ:&mut Circuit,terminal:&mut Terminal){
    assert_eq!(terminal.work2.len(),259);for _ in 0..2{circ.zero_and_free(terminal.work2.pop().unwrap());}
}
fn restore_terminal_padding(circ:&mut Circuit,terminal:&mut Terminal){
    assert_eq!(terminal.work2.len(),257);terminal.work2.extend(circ.alloc_qreg_bits("rank5.terminal-padding.restored",2));
}
pub fn divide_forward(
    circ: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>, Vec<QReg>) {
    use super::shrunken_pz_state_machine::{
        release_q955_canonical_lambda_top, restore_q955_canonical_lambda_top,
    };
    use crate::point_add::trailmix_port::arith::rfold_mbu::mod_mul_canonical_mbu;

    assert_eq!(dx.len(), FIELD_WIDTH);
    assert_eq!(dy.len(), FIELD_WIDTH);
    let released_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 forward dy");
    let core = initialize(circ, dx,&dy[0],&dy[1]);
    emit_forward(circ, &core, &dy);
    let mut terminal = release_terminal(circ, core);
    release_terminal_padding(circ,&mut terminal);
    canonicalize_terminal_work2(circ, &terminal);
    toggle_inverse_sign(circ, &terminal);

    restore_canonical_top(circ, &mut dy, released_dy_top);
    let mut lambda = circ.alloc_qreg_bits("paper2607.lambda", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &lambda, &terminal.work2[..FIELD_WIDTH], &dy);
    toggle_inverse_sign(circ, &terminal);
    restore_terminal_work2_rotation(circ, &terminal);
    release_q955_canonical_lambda_top(circ, &mut lambda);

    let dy_ghosts: Vec<_> = dy.iter().map(|lane| circ.hmr_ghost(lane)).collect();
    free_clean(circ, dy);
    restore_terminal_padding(circ,&mut terminal);
    let core = rebuild_terminal(circ, terminal,&lambda[0],&lambda[1]);
    emit_reverse(circ, &core, &lambda);
    let dx = finish(circ, core);

    restore_q955_canonical_lambda_top(circ, &mut lambda);
    let dy = circ.alloc_qreg_bits("paper2607.dy-restored", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &dy, &lambda, &dx);
    for (ghost, lane) in dy_ghosts.into_iter().zip(&dy) {
        circ.resolve_ghost(ghost, lane);
    }
    (dx, dy, lambda)
}

pub fn divide_cancel(
    circ: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
    lambda: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::rfold_mbu::{
        mod_mul_canonical_mbu, mod_mul_canonical_mbu_undo,
    };

    assert_eq!(dx.len(), FIELD_WIDTH);
    assert_eq!(dy.len(), FIELD_WIDTH);
    assert_eq!(lambda.len(), FIELD_WIDTH);
    let lambda_ghosts: Vec<_> = lambda.iter().map(|lane| circ.hmr_ghost(lane)).collect();
    free_clean(circ, lambda);

    let released_forward_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 cancel-forward dy");
    let core = initialize(circ, dx,&dy[0],&dy[1]);
    emit_forward(circ, &core, &dy);
    let mut terminal = release_terminal(circ, core);
    release_terminal_padding(circ,&mut terminal);
    canonicalize_terminal_work2(circ, &terminal);
    toggle_inverse_sign(circ, &terminal);

    restore_canonical_top(circ, &mut dy, released_forward_dy_top);
    let quotient = circ.alloc_qreg_bits("paper2607.quotient-check", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &quotient, &terminal.work2[..FIELD_WIDTH], &dy);
    for (ghost, lane) in lambda_ghosts.into_iter().zip(&quotient) {
        circ.resolve_ghost(ghost, lane);
    }
    mod_mul_canonical_mbu_undo(circ, &quotient, &terminal.work2[..FIELD_WIDTH], &dy);
    free_clean(circ, quotient);

    toggle_inverse_sign(circ, &terminal);
    restore_terminal_work2_rotation(circ, &terminal);
    let released_reverse_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 cancel-reverse dy");
    restore_terminal_padding(circ,&mut terminal);
    let core = rebuild_terminal(circ, terminal,&dy[0],&dy[1]);
    emit_reverse(circ, &core, &dy);
    let dx = finish(circ, core);
    restore_canonical_top(circ, &mut dy, released_reverse_dy_top);
    (dx, dy)
}
