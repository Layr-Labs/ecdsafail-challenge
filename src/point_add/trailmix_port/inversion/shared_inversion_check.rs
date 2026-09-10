//! Development verification of the complete1616-step native inversion core.
//! Loads independent scalar input/output capsules. Not a submitted point-adder.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{OperationType,QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed;
impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0xa7);}}
fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn set(words:&mut[u64],q:&QReg,lane:usize,bit:bool) {
    let x=&mut words[q.id() as usize];*x=(*x&!(1<<lane))|(u64::from(bit)<<lane);
}
pub fn run() {
    let began=std::time::Instant::now();
    let path=std::env::var("LOWQ_FULL_INVERSION_CAPSULE").expect("explicit independent inversion capsule");
    let data=std::fs::read(path).expect("read inversion capsule");assert_eq!(&data[..8],b"LQINV1\0\0");
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
    assert!(count>0 && count<=65536);assert_eq!(data.len(),12+count*1050);
    let mut circ=Circuit::new();
    let a=circ.alloc_qreg_bits("inversion.work1",259);let breg=circ.alloc_qreg_bits("inversion.work2",259);
    let lt=circ.alloc_qreg_bits("inversion.lt",8);let shift=circ.alloc_qreg_bits("inversion.shift",8);
    let shared=circ.alloc_qreg_bits("inversion.shared",8);let flags=circ.alloc_qreg_bits("inversion.flags",4);
    assert_eq!(circ.b.next_qubit,546);let helpers=circ.alloc_qreg_bits("inversion.borrowed_passenger",24);
    let owned=circ.b.next_qubit;
    let windowed=std::env::var_os("LOWQ_INVERSION_WINDOWS").is_some();
    let supports=if windowed {super::shared_step::SCHEDULE_SUPPORTS.to_vec()}else{vec![(0,259)]};
    let mut templates=Vec::new();let mut traversal_ops=0usize;let mut traversal_t=0usize;
    for (group,&(r_first,t_end)) in supports.iter().enumerate() {
        let steps=if windowed {(1616-64*group).min(64)}else{1616};
        for quarter in [false,true] {
            super::shared_step::scheduled_step_with_support(&mut circ,&a,&breg,&lt,&shift,&shared,&flags[0],&flags[1],&flags[2],&flags[3],&helpers,quarter,r_first,t_end,None);
            assert_eq!(circ.b.next_qubit,owned);let ops=std::mem::take(&mut circ.b.ops);
            assert!(ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let t=ops.iter().filter(|op|op.kind==OperationType::CCX).count();
            let repeats=if quarter {steps/4}else{3*steps/4};
            traversal_ops+=repeats*ops.len();traversal_t+=repeats*t;
            eprintln!("inversion template group={group} quarter={quarter} Rfirst={r_first} Tend={t_end} ops={} T={t}",ops.len());
            templates.push(ops);
        }
    }
    eprintln!("inversion templates ready windowed={windowed} traversal_ops={traversal_ops} traversal_T={traversal_t} owned=546 borrowed=24 elapsed={:.3}",began.elapsed().as_secs_f64());
    let template_index=|step:usize| if windowed {2*((step-1)/64)+usize::from(step%4==0)}else{usize::from(step%4==0)};
    for batch in 0..count.div_ceil(64) {
        let mut random=0x897bed52103ca6f4u64^batch as u64;
        let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut expected=before.clone();
        for lane in 0..64 {
            let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
            for (words,record) in [(&mut before,&row[..525]),(&mut expected,&row[525..])] {
                for (j,q) in a.iter().chain(&breg).enumerate(){assert!(record[j]<=1);set(words,q,lane,record[j]!=0);}
                for (j,reg) in [&lt,&shift,&shared].iter().enumerate(){for (bit,q) in reg.iter().enumerate(){set(words,q,lane,(record[518+j]>>bit)&1!=0);}}
                for (j,q) in flags.iter().enumerate(){assert!(record[521+j]<=1);set(words,q,lane,record[521+j]!=0);}
            }
        }
        let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
        for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
        for step in 1..=1616 {
            sim.apply_iter(templates[template_index(step)].iter());
            if step%256==0 || step==1616 {assert_eq!(sim.phase,0);eprintln!("inversion forward batch={batch} step={step}/1616 elapsed={:.3}",began.elapsed().as_secs_f64());}
        }
        for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"full inversion terminal batch={batch} wire={q}");}
        assert_eq!(sim.phase,0);eprintln!("inversion terminal PASS batch={batch} all state/dirty/phase checked");
        for step in (1..=1616).rev() {
            sim.apply_iter(templates[template_index(step)].iter().rev());
            if step%256==0 || step==1 {assert_eq!(sim.phase,0);eprintln!("inversion reverse batch={batch} step={step}/1616 elapsed={:.3}",began.elapsed().as_secs_f64());}
        }
        for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"full inversion reverse batch={batch} wire={q}");}
        eprintln!("inversion reverse PASS batch={batch} all input/dirty/phase restored");
    }
    eprintln!("shared inversion core PASS {count} independent reference records,1616 forward and1616 reverse steps,546 owned+24 borrowed, traversal_T={}, elapsed={:.3}; NOT a point-add or official9024-shot validation",traversal_t,began.elapsed().as_secs_f64());
}
