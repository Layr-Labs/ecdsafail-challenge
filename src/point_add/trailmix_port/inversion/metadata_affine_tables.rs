// Offline-pinned LOCAL affine conjugations. No rank encoding or caller changes.
// Full primitive proof: phaseframe/check-hot-affine-gates.mjs, 73,728 states.
struct AffineSwapPlan { width:usize, key:u64, frame:&'static [(i8,usize)], terms:&'static [usize] }
const AFFINE_SWAP_PLANS:&[AffineSwapPlan]=&[
    // cs_sum_0: 29 CCX, 56 primitive operations including frame + inverse.
    AffineSwapPlan{width:6,key:0x3a94b5a5c56b4a5a,frame:&[(3,2),(4,1),(4,5),(-1,2),(3,4),(0,5),(-1,1),(1,0),(4,3),(4,5),(3,5),(2,5)],terms:&[0,13,23,26,32]},
    // cs_sum_1: 87 CCX, 131 primitive operations including frame + inverse.
    AffineSwapPlan{width:6,key:0xdf16c1361a7d8b6c,frame:&[(2,1),(3,2),(4,0),(0,3),(3,4),(0,3),(5,4),(5,2),(4,1),(0,5),(-1,4),(3,2),(5,3),(3,0),(-1,0),(1,0),(5,3),(5,1),(4,0),(4,1),(-1,1)],terms:&[2,8,12,14,20,26,29,32,43,48,49,52,55]},
    // cs_sum_2: 72 CCX, 98 primitive operations including frame + inverse.
    AffineSwapPlan{width:6,key:0x691ec800001480,frame:&[(-1,4),(1,3),(1,0),(3,2),(-1,2),(2,0),(1,3),(0,1),(2,5),(1,5),(-1,5),(2,5)],terms:&[21,23,30,34,42,51,61]},
    // ac_sum_0: 25 CCX, 43 primitive operations including frame + inverse.
    AffineSwapPlan{width:6,key:0x93ce070f6c31f8f0,frame:&[(-1,3),(1,3),(2,3),(3,4),(3,5),(2,5),(4,1),(-1,1)],terms:&[11,23,24,32]},
    // ac_sum_1: 78 CCX, 112 primitive operations including frame + inverse.
    AffineSwapPlan{width:6,key:0x38fe7f06fbe1f00,frame:&[(5,3),(2,3),(2,3),(2,3),(2,1),(5,3),(5,2),(3,5),(3,2),(4,3),(1,4),(2,0),(3,0),(3,5),(-1,3),(5,3)],terms:&[4,12,24,26,29,32,38,47,48,49,53]},
    // ac_zero_0: 26 CCX, 40 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x6c31f8f0,frame:&[(-1,3),(1,3),(2,3),(3,4),(4,1),(-1,1)],terms:&[4,8,11,23,24]},
    // ac_zero_1: 42 CCX, 60 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x6fbe1f00,frame:&[(4,2),(-1,0),(1,0),(-1,1),(4,3),(-1,2),(2,0),(0,4)],terms:&[1,11,12,16,20,21,31]},
    // axis_0_0: 29 CCX, 39 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0xe07fe000,frame:&[(3,1),(3,0),(2,4),(-1,3)],terms:&[4,7,24,31]},
    // axis_1_0: 41 CCX, 80 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x8c4e18f0,frame:&[(-1,2),(4,2),(3,4),(4,2),(1,2),(-1,2),(0,3),(1,4),(4,1),(0,4),(2,0),(3,4),(-1,1),(2,1),(-1,3),(-1,1),(3,0),(0,4)],terms:&[0,5,10,14,16,21,31]},
    // axis_1_1: 29 CCX, 39 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x10701f00,frame:&[(3,1),(3,0),(2,3),(2,4)],terms:&[7,8,24,31]},
    // axis_2_0: 42 CCX, 54 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x492552aa,frame:&[(3,0),(-1,2),(2,4),(2,1),(1,3)],terms:&[1,4,6,14,20,25,31]},
    // axis_2_1: 36 CCX, 70 primitive operations including frame + inverse.
    AffineSwapPlan{width:5,key:0x20984cc,frame:&[(0,3),(1,4),(3,0),(1,3),(4,3),(-1,1),(4,2),(-1,4),(4,0),(-1,3),(2,3),(4,3),(3,4),(-1,1),(1,3),(1,0)],terms:&[11,18,28,31]},
];
fn affine_truth_swap(circ:&mut Circuit,controls:&[&QReg],truth:&[bool],left:&QReg,right:&QReg,helpers:&[QReg])->bool {
    if !active("Q795_AFFINE_TRUTH_SWAP") || controls.len()>6 || truth.len()!=1usize<<controls.len() {return false;}
    let key=truth.iter().enumerate().fold(0u64,|key,(i,&b)|key|((b as u64)<<i));
    let Some(plan)=AFFINE_SWAP_PLANS.iter().find(|p|p.width==controls.len()&&p.key==key) else{return false;};
    // Keep the original generic fallback when this local frame cannot borrow
    // its four disjoint arbitrary lenders. No new caller precondition.
    if helpers.len()<4 {return false;}
    let wires:Vec<_>=controls.iter().copied().chain([left,right]).chain(helpers[..4].iter()).map(|q|q.id()).collect();
    if wires.iter().enumerate().any(|(i,id)|wires[..i].contains(id)){return false;}
    let gate=|circ:&mut Circuit,(c,t):(i8,usize)|{if c<0{circ.x(controls[t]);}else{circ.cx(controls[c as usize],controls[t]);}};
    for &g in plan.frame{gate(circ,g);}
    circ.cx(right,left);
    for &m in plan.terms{let mut cs=vec![(left,true)];cs.extend((0..controls.len()).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));mixed_mcx(circ,&cs,right,helpers);}
    circ.cx(right,left);
    for &g in plan.frame.iter().rev(){gate(circ,g);}
    true
}

/// Dedicated diagnostic; does not alter any existing evaluator or assertion.
pub fn run_affine_unit(){
    use crate::{sim::Simulator,circuit::OperationType};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    assert!(active("Q795_AFFINE_TRUTH_SWAP"));
    let mut total=0usize;
    for plan in AFFINE_SWAP_PLANS{
        let mut circ=Circuit::new();let controls=circ.alloc_qreg_bits("controls",plan.width);let left=circ.alloc_qreg("left");let right=circ.alloc_qreg("right");let helpers=circ.alloc_qreg_bits("dirty",5);let n=circ.b.next_qubit;
        let truth=(0..1usize<<plan.width).map(|i|plan.key>>i&1!=0).collect();
        truth_swap(&mut circ,&controls.iter().collect::<Vec<_>>(),truth,&left,&right,&helpers);assert_eq!(n,circ.b.next_qubit);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let cases=1usize<<(plan.width+7);
        for base in (0..cases).step_by(64){let mut before=vec![0u64;n as usize];let mut wanted=before.clone();
            for lane in 0..64{let s=base+lane;let f=plan.key>>(s&((1<<plan.width)-1))&1!=0;let unequal=((s>>plan.width)^(s>>(plan.width+1)))&1!=0;let out=s^if f&&unequal{3<<plan.width}else{0};for i in 0..n as usize{before[i]|=(((s>>i)&1)as u64)<<lane;wanted[i]|=(((out>>i)&1)as u64)<<lane;}}
            let mut fixed=Fixed;let mut sim=Simulator::new(n as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,wanted,"affine key={:x} base={base}",plan.key);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
        }
        total+=cases;eprintln!("AFFINE_TABLE_PASS key={:x} width={} cases={cases} ops={} T={}",plan.key,plan.width,b.ops.len(),b.ops.iter().filter(|o|o.kind==OperationType::CCX).count());
    }
    eprintln!("AFFINE_ALL_PASS tables={} cases={total}",AFFINE_SWAP_PLANS.len());
}
