//! Native register-transfer primitive for the l_q/l_rp shared-state experiment.
//! This is not yet a complete EEA transition or a reduced point-add circuit.
use super::length_recompute::{xor_eea_suffix_length,xor_eea_coefficient_length};
use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

/// Controlled modular addition/subtraction with restored dirty helpers.
/// Reversing the whole shifted-increment sequence implements subtraction.
fn add_shift(
    circ:&mut Circuit, shift:&[QReg], target:&[QReg], enable:&QReg,
    helpers:&[QReg], subtract:bool,
) {
    assert_eq!(shift.len(),target.len());
    let dirty:Vec<_>=helpers.iter().collect();
    let mut cells=Vec::new();
    for i in 0..shift.len() {
        for j in (i..target.len()).rev() {cells.push((i,j));}
    }
    if subtract {cells.reverse();}
    for (i,j) in cells {
        let mut controls=vec![enable,&shift[i]];
        controls.extend(target[i..j].iter());
        mcx_dirty_ladder(circ,&controls,&target[j],&dirty);
    }
}

/// Under `enable`, convert the empty quotient code (-1) into l_rp's code.
/// The context must establish that the first set bit after lt_raw+2 belongs
/// to r', and that 1 <= its physical length - l_s <= 255. Outside enable,
/// the complete operation is the identity, including on arbitrary target bits.
/// Inverse restores the empty quotient code from the corresponding l_rp code.
/// No clean wire is allocated. All supplied source/metadata/lenders survive.
pub fn transfer(
    circ:&mut Circuit, work2:&[QReg], lt_raw:&[QReg], shift:&[QReg], length:&[QReg],
    enable:&QReg, prefix_dirty:&[QReg], helpers:&[QReg], inverse:bool,
) {
    transfer_with_parity(circ,work2,lt_raw,shift,length,enable,prefix_dirty,helpers,inverse,None);
}

fn transfer_with_parity(
    circ:&mut Circuit,work2:&[QReg],lt_raw:&[QReg],shift:&[QReg],length:&[QReg],
    enable:&QReg,prefix_dirty:&[QReg],helpers:&[QReg],inverse:bool,step_parity:Option<bool>,
) {
    assert_eq!(shift.len(),length.len());
    // Validate the complete interface, including shift (which the suffix
    // oracle itself does not see), before any operation can be emitted.
    let mut ids:Vec<_>=work2.iter().chain(lt_raw).chain(shift).chain(length)
        .chain(prefix_dirty).chain(helpers).map(QReg::id).collect();
    ids.push(enable.id());ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"shared length transfer aliases");
    if inverse {add_shift(circ,shift,length,enable,helpers,false);}
    else {for q in length {circ.cx(enable,q);}}
    if let Some(known)=step_parity {
        super::length_recompute::xor_eea_controlled_loan(circ,work2,lt_raw,length,&[enable],prefix_dirty,helpers,false,enable,&shift[0],known);
    } else {xor_eea_suffix_length(circ,work2,lt_raw,length,Some(enable),prefix_dirty,helpers);}
    if inverse {for q in length {circ.cx(enable,q);}}
    else {add_shift(circ,shift,length,enable,helpers,true);}
}

/// After the work-register swap, update lt and erase the old residual length
/// from the shared register. On enabled inputs shift is exactly zero and the
/// shared register still contains the old nonzero residual's length. Work1
/// now contains the new coefficient and the old residual; Work2 contains the
/// old coefficient and the new residual (which may be zero at termination).
/// The inverse is the exact reversed network. No clean workspace is allocated.
pub fn finish_iteration(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    enable:&QReg,helpers:&[QReg],inverse:bool,
) {
    if inverse {transfer(circ,work1,lt,shift,shared,enable,work2,helpers,false);}
    if inverse {
        xor_eea_coefficient_length(circ,work1,shared,lt,Some(enable),work2,helpers);
        xor_eea_coefficient_length(circ,work2,shared,lt,Some(enable),work1,helpers);
    } else {
        xor_eea_coefficient_length(circ,work2,shared,lt,Some(enable),work1,helpers);
        xor_eea_coefficient_length(circ,work1,shared,lt,Some(enable),work2,helpers);
    }
    if !inverse {transfer(circ,work1,lt,shift,shared,enable,work2,helpers,true);}
}

/// End of an ACTIVE Algorithm-3 step, after the physical post-shift. This
/// replaces the phase update and end-iteration metadata block together.
/// Shared holds l_q except in phase 11, where it holds l_rp. LT is still the
/// old coefficient length. Terminal padding is the caller's separate route.
/// Uses existing phase/sign/iteration wires and restored passenger lenders.
/// No additional clean control flag or length register is allocated.
pub fn active_step_boundary(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg],
) {
    scheduled_boundary(circ,work1,work2,lt,shift,shared,phase1,phase2,sign,iteration,helpers,true);
}

/// Scheduled boundary including already-terminal counter states. On quarter
/// steps their counter has already advanced to a nonzero value. Other steps
/// cannot end an EEA cycle and must suppress LS-zero flips on terminal LT.
pub fn scheduled_boundary(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg],quarter:bool,
) {
    scheduled_boundary_with_parity(circ,work1,work2,lt,shift,shared,phase1,phase2,sign,iteration,helpers,quarter,None);
}

pub(super) fn scheduled_boundary_with_parity(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg],quarter:bool,step_parity:Option<bool>,
) {
    use super::length_recompute::{xor_eea_coefficient_controlled,xor_eea_suffix_controlled,xor_eea_controlled_loan};
    assert_eq!(lt.len(),8);assert_eq!(shift.len(),8);assert_eq!(shared.len(),8);
    assert!(helpers.len()>=24);
    let mut ids:Vec<_>=work1.iter().chain(work2).chain(lt).chain(shift).chain(shared)
        .chain(helpers).map(QReg::id).collect();
    ids.extend([phase1.id(),phase2.id(),sign.id(),iteration.id()]);ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"active boundary aliases");
    let dirty:Vec<_>=helpers.iter().collect();
    // On phase-11 inputs Sign==1 at this point. Consequently Sign xor
    // Phase1 is zero and the omitted implicit-q-zero term cannot flip P2.
    // In all other phases shared is exactly the old quotient length.
    let nonterminal=|circ:&mut Circuit,controls:&[&QReg],target:&QReg| {
        mcx_dirty_ladder(circ,controls,target,&dirty);
        let mut terminal=controls.to_vec();terminal.extend(lt.iter());
        mcx_dirty_ladder(circ,&terminal,target,&dirty);
    };
    // The quotient length 256 shares raw code 255 with length zero.
    // It occurs only with LT=1. Work1[2] is then the leading quotient one;
    // with empty quotient and LT=1 this position is the leading padding zero.
    let cancel_full_quotient=|circ:&mut Circuit,controls:&[&QReg],target:&QReg| {
        for q in lt {circ.x(q);}
        let mut full=controls.to_vec();full.extend(lt.iter());full.push(&work1[2]);
        mcx_dirty_ladder(circ,&full,target,&dirty);
        for q in lt {circ.x(q);}
    };
    for q in [sign,phase1] {
        let mut controls:Vec<_>=shared.iter().collect();controls.push(q);
        nonterminal(circ,&controls,phase2);
        cancel_full_quotient(circ,&controls,phase2);
    }
    // Q==0 is implicit in phase 11. The two cubes below are disjoint.
    nonterminal(circ,&[phase1,phase2],sign);
    circ.x(phase1);
    let mut controls=vec![phase1,phase2];controls.extend(shared.iter());
    nonterminal(circ,&controls,sign);
    cancel_full_quotient(circ,&controls,sign);
    circ.x(phase1);
    // Sign now marks the unique transition into phase 11. This register is
    // otherwise zero on active step boundaries, including iteration exits.
    transfer_with_parity(circ,work2,lt,shift,shared,sign,work1,helpers,false,step_parity);

    // Before the LS==0 phase flips, P1=P2=1 and LS==0 identify the cycle
    // exit. Keep these controls unchanged through the swap and erasure.
    for q in shift {circ.x(q);}
    // A new phase-11 entry with LS=256 also has raw LS=0. Sign=1
    // distinguishes it from a genuine iteration exit.
    circ.x(sign);
    if quarter {
    let mut exit=vec![phase1,phase2,sign];exit.extend(shift.iter());
    let exit_gate=|circ:&mut Circuit,controls:&[&QReg],out:&QReg| {
        if let Some(parity)=step_parity {
            assert!(!parity,"quarter-step parity");
            let others:Vec<_>=controls.iter().filter(|q|q.id()!=phase1.id() && q.id()!=shift[0].id()).map(|&q|(q,true)).collect();
            super::conditional_mcx::guarded(circ,phase1,&others,out,&shift[0],true,&helpers[0]);
        } else {mcx_dirty_ladder(circ,controls,out,&dirty);}
    };
    for (a,b) in work1.iter().zip(work2) {
        circ.cx(b,a);let mut controls=exit.clone();controls.push(a);
        exit_gate(circ,&controls,b);circ.cx(b,a);
    }
    if step_parity.is_some() {
        xor_eea_controlled_loan(circ,work2,shared,lt,&exit,work1,helpers,true,phase1,&shift[0],true);
        xor_eea_controlled_loan(circ,work1,shared,lt,&exit,work2,helpers,true,phase1,&shift[0],true);
    } else {
        xor_eea_coefficient_controlled(circ,work2,shared,lt,&exit,work1,helpers);
        xor_eea_coefficient_controlled(circ,work1,shared,lt,&exit,work2,helpers);
    }
    // LS is known zero on enabled branches, so no add/subtract of LS is
    // needed when erasing the residual code to the empty quotient code.
    if step_parity.is_some() {xor_eea_controlled_loan(circ,work1,lt,shared,&exit,work2,helpers,false,phase1,&shift[0],true);}
    else {xor_eea_suffix_controlled(circ,work1,lt,shared,&exit,work2,helpers);}
    for q in shared {exit_gate(circ,&exit,q);}
    exit_gate(circ,&exit,iteration);
    }
    let mut zero:Vec<_>=shift.iter().collect();zero.push(sign);
    mcx_dirty_ladder(circ,&zero,phase1,&dirty);
    mcx_dirty_ladder(circ,&zero,phase2,&dirty);
    if !quarter {
        let mut terminal=zero.clone();terminal.extend(lt.iter());
        mcx_dirty_ladder(circ,&terminal,phase1,&dirty);
        mcx_dirty_ladder(circ,&terminal,phase2,&dirty);
    }
    // The other raw-zero exception is the first R ascent at true LS=256:
    // LT=1 and LQ=0. After a genuine cycle swap LT is at least 2, because
    // the input was normalized to x<=p/2 and the first quotient is >=2.
    // Thus the unchanged (LTraw=0,Lshared=255) cube cancels only that peak.
    for q in lt {circ.x(q);}
    circ.x(&work1[2]);
    let mut peak=zero;peak.extend(lt.iter());peak.extend(shared.iter());peak.push(&work1[2]);
    mcx_dirty_ladder(circ,&peak,phase1,&dirty);
    mcx_dirty_ladder(circ,&peak,phase2,&dirty);
    circ.x(&work1[2]);
    for q in lt {circ.x(q);}
    circ.x(sign);
    for q in shift {circ.x(q);}
}

pub mod verification {
    use super::*;
    use crate::circuit::{OperationType,QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn set(words:&mut[u64],q:&QReg,lane:usize,bit:bool) {
        let x=&mut words[q.id() as usize];*x=(*x&!(1<<lane))|(u64::from(bit)<<lane);
    }
    pub fn run() {
        let mut circ=Circuit::new();
        let work=circ.alloc_qreg_bits("transfer.work2",259);
        let lt=circ.alloc_qreg_bits("transfer.lt",8);
        let shift=circ.alloc_qreg_bits("transfer.shift",8);
        let length=circ.alloc_qreg_bits("transfer.shared_lq_lrp",8);
        let enable=circ.alloc_qreg("transfer.enable");
        let dirty=circ.alloc_qreg_bits("transfer.borrowed_work1",259);
        let helpers=circ.alloc_qreg_bits("transfer.borrowed_passenger",8);
        let owned=circ.b.next_qubit;
        transfer(&mut circ,&work,&lt,&shift,&length,&enable,&dirty,&helpers,false);
        let split=circ.b.ops.len();
        transfer(&mut circ,&work,&lt,&shift,&length,&enable,&dirty,&helpers,true);
        assert_eq!(owned,circ.b.next_qubit,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..128 {
            let mut random=0x693a214e5d8fb70cu64^batch;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=[0u64;8];
            for lane in 0..64 {
                let k=batch as usize*64+lane;let on=k&1!=0;
                let first=2+(k/2)%257;
                let low=if first==2 {0}else{(rnd(&mut random) as usize)%(first-1)};
                let min_shift=(259usize-first).saturating_sub(255);
                let max_shift=(258-first).min(255);
                let s=min_shift+(rnd(&mut random) as usize)%(max_shift-min_shift+1);
                let raw=259-first-s-1;
                for (j,q) in work.iter().enumerate() {
                    let value=if j<low+2 || j>first {rnd(&mut random)&1!=0}else{j==first};
                    set(&mut before,q,lane,value);
                }
                for (qs,value) in [(&lt,low),(&shift,s)] {
                    for (bit,q) in qs.iter().enumerate(){set(&mut before,q,lane,(value>>bit)&1!=0);}
                }
                set(&mut before,&enable,lane,on);
                for (bit,q) in length.iter().enumerate() {
                    if on {set(&mut before,q,lane,true);}
                    let value=if on {(raw>>bit)&1}else{((before[q.id() as usize]>>lane)&1) as usize};
                    expected[bit]|=(value as u64)<<lane;
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&value) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=value;}
            sim.apply_iter(b.ops[..split].iter());
            assert_eq!(sim.phase,0);
            for q in work.iter().chain(&lt).chain(&shift).chain(&dirty).chain(&helpers).chain(std::iter::once(&enable)) {
                assert_eq!(sim.qubit(QubitId(q.id() as u64)),before[q.id() as usize],"forward restore");
            }
            for (bit,q) in length.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q.id() as u64)),expected[bit],"forward output batch={batch}");}
            sim.apply_iter(b.ops[split..].iter());
            assert_eq!(sim.phase,0);
            for (q,&value) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),value,"inverse restore batch={batch}");}
            tested+=64;
        }
        let t=b.ops[..split].iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata transfer PASS {tested} lanes; forward T={t}, inverse T={t}, no clean allocation, all dirty registers restored, phase zero");
    }

    pub fn run_exits() {
        let path=std::env::var("LOWQ_EXIT_CAPSULE").expect("explicit scalar exit capsule path");
        let data=std::fs::read(path).expect("read exit capsule");
        assert_eq!(&data[..8],b"LQEXIT1\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*521);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("exit.work1",259);
        let breg=circ.alloc_qreg_bits("exit.work2",259);
        let lt=circ.alloc_qreg_bits("exit.lt",8);
        let shift=circ.alloc_qreg_bits("exit.shift",8);
        let shared=circ.alloc_qreg_bits("exit.shared",8);
        let enable=circ.alloc_qreg("exit.enable");
        let helpers=circ.alloc_qreg_bits("exit.borrowed_passenger",8);
        let owned=circ.b.next_qubit;
        finish_iteration(&mut circ,&a,&breg,&lt,&shift,&shared,&enable,&helpers,false);
        let split=circ.b.ops.len();
        finish_iteration(&mut circ,&a,&breg,&lt,&shift,&shared,&enable,&helpers,true);
        assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..(2*count).div_ceil(64) {
            let mut random=0x51376bad9f82ce40u64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected_lt=[0u64;8];let mut expected_shared=[0u64;8];
            for lane in 0..64 {
                let k=batch*64+lane;let on=k&1!=0;
                let row=&data[12+((k/2)%count)*521..][..521];
                for (j,q) in a.iter().chain(&breg).enumerate(){assert!(row[j]<=1);set(&mut before,q,lane,row[j]!=0);}
                set(&mut before,&enable,lane,on);
                for (bit,q) in lt.iter().enumerate(){
                    if on {set(&mut before,q,lane,(row[518]>>bit)&1!=0);}
                    expected_lt[bit]|=(if on {((row[520]>>bit)&1) as u64}else{(before[q.id() as usize]>>lane)&1})<<lane;
                }
                for (bit,q) in shared.iter().enumerate(){
                    if on {set(&mut before,q,lane,(row[519]>>bit)&1!=0);}
                    expected_shared[bit]|=(if on {1}else{(before[q.id() as usize]>>lane)&1})<<lane;
                }
                for q in &shift {if on {set(&mut before,q,lane,false);}}
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops[..split].iter());assert_eq!(sim.phase,0);
            for (qs,expected) in [(&lt,&expected_lt),(&shared,&expected_shared)] {
                for (bit,q) in qs.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q.id() as u64)),expected[bit],"exit output batch={batch}");}
            }
            for q in a.iter().chain(&breg).chain(&shift).chain(&helpers).chain(std::iter::once(&enable)) {
                assert_eq!(sim.qubit(QubitId(q.id() as u64)),before[q.id() as usize],"exit restored data");
            }
            sim.apply_iter(b.ops[split..].iter());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"exit inverse batch={batch}");}
            tested+=64;
        }
        let t=b.ops[..split].iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata exit PASS {tested} lanes / {count} reference states, forward T={t}, no clean allocation, phase and dirty state restored");
    }
    pub fn run_boundaries() {
        let path=std::env::var("LOWQ_BOUNDARY_CAPSULE").expect("explicit boundary capsule path");
        let data=std::fs::read(path).expect("read boundary capsule");
        assert_eq!(&data[..8],b"LQBND1\0\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*1050);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("boundary.work1",259);
        let breg=circ.alloc_qreg_bits("boundary.work2",259);
        let lt=circ.alloc_qreg_bits("boundary.lt",8);
        let shift=circ.alloc_qreg_bits("boundary.shift",8);
        let shared=circ.alloc_qreg_bits("boundary.shared",8);
        let flags=circ.alloc_qreg_bits("boundary.existing_flags",4);
        assert_eq!(circ.b.next_qubit,546,"owned inversion state");
        let helpers=circ.alloc_qreg_bits("boundary.borrowed_passenger",24);
        let owned=circ.b.next_qubit;
        active_step_boundary(&mut circ,&a,&breg,&lt,&shift,&shared,
            &flags[0],&flags[1],&flags[2],&flags[3],&helpers);
        assert_eq!(circ.b.next_qubit,owned,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..count.div_ceil(64) {
            let mut random=0xb1e4359cfa62178du64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=before.clone();
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                    for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                    for (j,qs) in [&lt,&shift,&shared].iter().enumerate() {
                        for (bit,q) in qs.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}
                    }
                    for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
            for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary output batch={batch} wire={q}");}
            // The emitted block consists exclusively of self-inverse X/CX/CCX.
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary inverse batch={batch} wire={q}");}
            tested+=64;
        }
        let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata active boundary PASS {count} reference records / {tested} lanes, T={t}, 546 owned inversion wires + 24 restored passenger wires, no new clean control, phase zero; NOT a complete inversion or point-add circuit");
    }

    pub fn run_coefficients() {
        let path=std::env::var("LOWQ_COEFFICIENT_CAPSULE").expect("explicit boundary capsule path");
        let data=std::fs::read(path).expect("read boundary capsule");
        assert_eq!(&data[..8],b"LQCOF1\0\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*1050);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("boundary.work1",259);
        let breg=circ.alloc_qreg_bits("boundary.work2",259);
        let lt=circ.alloc_qreg_bits("boundary.lt",8);
        let shift=circ.alloc_qreg_bits("boundary.shift",8);
        let shared=circ.alloc_qreg_bits("boundary.shared",8);
        let flags=circ.alloc_qreg_bits("boundary.existing_flags",4);
        assert_eq!(circ.b.next_qubit,546,"owned inversion state");
        let helpers=circ.alloc_qreg_bits("boundary.borrowed_passenger",24);
        let owned=circ.b.next_qubit;
        super::super::shared_arithmetic::coefficient_block(&mut circ,&a,&breg,&lt,&shift,&shared,
            &flags[0],&flags[1],&flags[2],&helpers);
        assert_eq!(circ.b.next_qubit,owned,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..count.div_ceil(64) {
            let mut random=0xb1e4359cfa62178du64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=before.clone();
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                    for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                    for (j,qs) in [&lt,&shift,&shared].iter().enumerate() {
                        for (bit,q) in qs.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}
                    }
                    for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
            for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary output batch={batch} wire={q}");}
            // The emitted block consists exclusively of self-inverse X/CX/CCX.
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary inverse batch={batch} wire={q}");}
            tested+=64;
        }
        let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata coefficient block PASS {count} reference records / {tested} lanes, T={t}, 546 owned inversion wires + 24 restored passenger wires, no new clean control, phase zero; NOT a complete inversion or point-add circuit");
    }

    pub fn run_remainders() {
        let path=std::env::var("LOWQ_REMAINDER_CAPSULE").expect("explicit boundary capsule path");
        let data=std::fs::read(path).expect("read boundary capsule");
        assert_eq!(&data[..8],b"LQREM1\0\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*1050);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("boundary.work1",259);
        let breg=circ.alloc_qreg_bits("boundary.work2",259);
        let lt=circ.alloc_qreg_bits("boundary.lt",8);
        let shift=circ.alloc_qreg_bits("boundary.shift",8);
        let shared=circ.alloc_qreg_bits("boundary.shared",8);
        let flags=circ.alloc_qreg_bits("boundary.existing_flags",4);
        assert_eq!(circ.b.next_qubit,546,"owned inversion state");
        let helpers=circ.alloc_qreg_bits("boundary.borrowed_passenger",24);
        let owned=circ.b.next_qubit;
        super::super::shared_remainder::remainder_block(&mut circ,&a,&breg,&lt,&shift,&shared,
            &flags[0],&flags[1],&flags[2],&helpers);
        assert_eq!(circ.b.next_qubit,owned,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..count.div_ceil(64) {
            let mut random=0xb1e4359cfa62178du64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=before.clone();
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                    for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                    for (j,qs) in [&lt,&shift,&shared].iter().enumerate() {
                        for (bit,q) in qs.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}
                    }
                    for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
            for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary output batch={batch} wire={q}");}
            // The emitted block consists exclusively of self-inverse X/CX/CCX.
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary inverse batch={batch} wire={q}");}
            tested+=64;
        }
        let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata remainder block PASS {count} reference records / {tested} lanes, T={t}, 546 owned inversion wires + 24 restored passenger wires, no new clean control, phase zero; NOT a complete inversion or point-add circuit");
    }

    pub fn run_active_steps() {
        let path=std::env::var("LOWQ_ACTIVE_STEP_CAPSULE").expect("explicit boundary capsule path");
        let data=std::fs::read(path).expect("read boundary capsule");
        assert_eq!(&data[..8],b"LQSTP1\0\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*1050);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("boundary.work1",259);
        let breg=circ.alloc_qreg_bits("boundary.work2",259);
        let lt=circ.alloc_qreg_bits("boundary.lt",8);
        let shift=circ.alloc_qreg_bits("boundary.shift",8);
        let shared=circ.alloc_qreg_bits("boundary.shared",8);
        let flags=circ.alloc_qreg_bits("boundary.existing_flags",4);
        assert_eq!(circ.b.next_qubit,546,"owned inversion state");
        let helpers=circ.alloc_qreg_bits("boundary.borrowed_passenger",24);
        let owned=circ.b.next_qubit;
        super::super::shared_step::active_step(&mut circ,&a,&breg,&lt,&shift,&shared,
            &flags[0],&flags[1],&flags[2],&flags[3],&helpers);
        assert_eq!(circ.b.next_qubit,owned,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..count.div_ceil(64) {
            let mut random=0xb1e4359cfa62178du64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=before.clone();
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                    for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                    for (j,qs) in [&lt,&shift,&shared].iter().enumerate() {
                        for (bit,q) in qs.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}
                    }
                    for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
            for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary output batch={batch} wire={q}");}
            // The emitted block consists exclusively of self-inverse X/CX/CCX.
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary inverse batch={batch} wire={q}");}
            tested+=64;
        }
        let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata whole active step PASS {count} reference records / {tested} lanes, T={t}, 546 owned inversion wires + 24 restored passenger wires, no new clean control, phase zero; NOT a complete inversion or point-add circuit");
    }


    pub fn run_scheduled_steps() {
        let quarter=std::env::var("LOWQ_SCHEDULE_QUARTER").expect("explicit quarter flag")=="1";
        let path=std::env::var("LOWQ_SCHEDULED_CAPSULE").expect("explicit boundary capsule path");
        let data=std::fs::read(path).expect("read boundary capsule");
        assert_eq!(&data[..8],b"LQSCH1\0\0");
        let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
        assert!(count>0 && count<=1_000_000);assert_eq!(data.len(),12+count*1050);
        let mut circ=Circuit::new();
        let a=circ.alloc_qreg_bits("boundary.work1",259);
        let breg=circ.alloc_qreg_bits("boundary.work2",259);
        let lt=circ.alloc_qreg_bits("boundary.lt",8);
        let shift=circ.alloc_qreg_bits("boundary.shift",8);
        let shared=circ.alloc_qreg_bits("boundary.shared",8);
        let flags=circ.alloc_qreg_bits("boundary.existing_flags",4);
        assert_eq!(circ.b.next_qubit,546,"owned inversion state");
        let helpers=circ.alloc_qreg_bits("boundary.borrowed_passenger",24);
        let owned=circ.b.next_qubit;
        super::super::shared_step::scheduled_step(&mut circ,&a,&breg,&lt,&shift,&shared,
            &flags[0],&flags[1],&flags[2],&flags[3],&helpers,quarter);
        assert_eq!(circ.b.next_qubit,owned,"new clean allocation");
        let b=circ.into_builder();let mut tested=0;
        for batch in 0..count.div_ceil(64) {
            let mut random=0xb1e4359cfa62178du64^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
            let mut expected=before.clone();
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                    for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                    for (j,qs) in [&lt,&shift,&shared].iter().enumerate() {
                        for (bit,q) in qs.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}
                    }
                    for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
                }
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
            for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
            for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary output batch={batch} wire={q}");}
            // The emitted block consists exclusively of self-inverse X/CX/CCX.
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
            for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"boundary inverse batch={batch} wire={q}");}
            tested+=64;
        }
        let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        eprintln!("shared metadata scheduled step quarter={quarter} PASS {count} reference records / {tested} lanes, T={t}, 546 owned inversion wires + 24 restored passenger wires, no new clean control, phase zero; NOT a complete inversion or point-add circuit");
    }


}
