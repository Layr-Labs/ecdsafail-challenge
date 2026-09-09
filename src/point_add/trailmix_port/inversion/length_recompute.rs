//! Exact XOR length oracle for the shared-metadata experiment.
//!
//! `source` is big endian. XOR (bit_length(source)-1) modulo 2^output.len()
//! into the little-endian output, optionally controlled. Zero has the all-one
//! encoding. No clean ancillas are allocated: all supplied dirty lenders and
//! the source are restored. This component is not yet in the main EEA route.
//! The dirty zero-prefix conjugation follows the length-update construction
//! of Luo et al., arXiv:2607.13816v2; this lowering replaces its clean unary
//! selector workspace with exact disjoint mixed-control cubes.

use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

// Disjoint prefix cubes for an unsigned register being strictly below a
// classical bound. Each pair is (bit index, required value).
pub(super) fn below_cubes(width: usize, bound: usize) -> Vec<Vec<(usize,bool)>> {
    if bound >= 1usize<<width { return vec![Vec::new()]; }
    let mut prefix=Vec::new(); let mut cubes=Vec::new();
    for bit in (0..width).rev() {
        let one=(bound>>bit)&1!=0;
        if one { let mut cube=prefix.clone();cube.push((bit,false));cubes.push(cube); }
        prefix.push((bit,one));
    }
    cubes
}

pub(super) fn above_cubes(width: usize, bound: usize) -> Vec<Vec<(usize,bool)>> {
    if bound >= (1usize<<width)-1 { return Vec::new(); }
    let mut prefix=Vec::new(); let mut cubes=Vec::new();
    for bit in (0..width).rev() {
        let one=(bound>>bit)&1!=0;
        if !one { let mut cube=prefix.clone();cube.push((bit,true));cubes.push(cube); }
        prefix.push((bit,one));
    }
    cubes
}

pub(super) fn mixed_mcx(circ: &mut Circuit, controls: &[(&QReg,bool)], target: &QReg, helpers: &[QReg]) {
    for &(q,positive) in controls { if !positive {circ.x(q);} }
    let mut refs: Vec<_> = controls.iter().map(|&(q,_)|q).collect();
    // Control factors commute. Reversing their ladder order can expose shared
    // metadata-prefix cancellations; experimental mode changes no predicate.
    static REVERSE_ORDER:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
    if *REVERSE_ORDER.get_or_init(||std::env::var("LOWQ_MCX_REVERSE_ORDER").ok().as_deref()==Some("1")) {refs.reverse();}
    let dirty: Vec<_> = helpers.iter().collect();
    if dirty.len()>=refs.len().saturating_sub(2) {mcx_dirty_ladder(circ,&refs,target,&dirty);}
    else {
        // A restored dirty echo funds rare wide predicates with fewer lenders.
        // A toggles d by the first half product; B toggles target by d*second.
        // ABAB cancels the arbitrary incoming d and restores all lenders.
        let split=refs.len()/2;let d=dirty[0];let rest=&dirty[1..];
        let mut right=refs[split..].to_vec();right.push(d);
        assert!(rest.len()>=split.saturating_sub(2)&&rest.len()>=right.len().saturating_sub(2),"split MCX lender shortage");
        for _ in 0..2{mcx_dirty_ladder(circ,&refs[..split],d,rest);mcx_dirty_ladder(circ,&right,target,rest);}
    }
    for &(q,positive) in controls.iter().rev() { if !positive {circ.x(q);} }
}

/// XOR the physical encoded length of the first set bit in [lo,hi).
/// Both endpoints are quantum little-endian registers. An empty window or
/// all-zero window produces -1 modulo output width. Bits outside the window
/// are ignored. The length is source.len()-first_index, not window length.
///
/// All source/endpoints, prefix_dirty and helpers are restored; no clean
/// workspace is allocated. A triangular conjugation toggles dirty prefix
/// registers by controlled zero-prefix predicates. Two such maps around
/// linear output writes cancel all incoming dirty values exactly.
pub fn xor_window_length(
    circ: &mut Circuit, source: &[QReg], lo: &[QReg], hi: &[QReg], output: &[QReg],
    enable: Option<&QReg>, prefix_dirty: &[QReg], helpers: &[QReg],
) {
    window_impl(circ,source,lo,hi,output,&enable.into_iter().collect::<Vec<_>>(),prefix_dirty,helpers,false,false,None);
}

/// First set bit at physical positions j >= lt_raw+2. This is the EEA
/// coefficient guard convention. The result is the physical position length,
/// so a caller recovering l_rp must still subtract l_s reversibly. No upper
/// bound is imposed: using this to recover r' requires a proven nonterminal
/// phase-1/2/3 context, where r' precedes any wrapped t' bits.
pub fn xor_eea_suffix_length(
    circ: &mut Circuit, source: &[QReg], lt_raw: &[QReg], output: &[QReg],
    enable: Option<&QReg>, prefix_dirty: &[QReg], helpers: &[QReg],
) {
    window_impl(circ,source,lt_raw,&[],output,&enable.into_iter().collect::<Vec<_>>(),prefix_dirty,helpers,true,false,None);
}

/// XOR the bit length minus one of the little-endian coefficient preceding
/// the residual field. The residual has truth length rp_raw+1; positions
/// j < source.len()-(rp_raw+1) belong to the coefficient/padding region.
/// This oracle is used only while that residual is nonzero and rp_raw<255.
pub fn xor_eea_coefficient_length(
    circ:&mut Circuit,source:&[QReg],rp_raw:&[QReg],output:&[QReg],
    enable:Option<&QReg>,prefix_dirty:&[QReg],helpers:&[QReg],
) {
    window_impl(circ,source,rp_raw,&[],output,&enable.into_iter().collect::<Vec<_>>(),prefix_dirty,helpers,true,true,None);
}

/// Multi-controlled forms share the same dirty-prefix construction. Controls
/// enter only at the root and the constant output term; all lenders restore.
pub fn xor_eea_suffix_controlled(
    circ:&mut Circuit,source:&[QReg],lt:&[QReg],out:&[QReg],
    controls:&[&QReg],dirty:&[QReg],helpers:&[QReg],
) {window_impl(circ,source,lt,&[],out,controls,dirty,helpers,true,false,None);}

pub fn xor_eea_coefficient_controlled(
    circ:&mut Circuit,source:&[QReg],rp:&[QReg],out:&[QReg],
    controls:&[&QReg],dirty:&[QReg],helpers:&[QReg],
) {window_impl(circ,source,rp,&[],out,controls,dirty,helpers,true,true,None);}

/// Control every elementary gate by a guard already present in the oracle
/// enable. The original oracle is identity when guard=0, so this refinement
/// preserves its complete unitary. Scratch need be known only on guard=1.
pub(super) fn xor_eea_controlled_loan(
    circ:&mut Circuit,source:&[QReg],boundary:&[QReg],out:&[QReg],
    controls:&[&QReg],dirty:&[QReg],helpers:&[QReg],coefficient:bool,
    guard:&QReg,scratch:&QReg,known:bool,
) {
    assert!(controls.iter().any(|q|q.id()==guard.id()));
    window_impl(circ,source,boundary,&[],out,controls,dirty,helpers,true,coefficient,Some((guard,scratch,known)));
}

fn window_impl(
    circ: &mut Circuit, source: &[QReg], lo: &[QReg], hi: &[QReg], output: &[QReg],
    enable: &[&QReg], prefix_dirty: &[QReg], helpers: &[QReg], eea_suffix: bool, coefficient:bool,
    parity_loan:Option<(&QReg,&QReg,bool)>,
) {
    assert!(!source.is_empty() && !lo.is_empty() && (eea_suffix || !hi.is_empty()) && !output.is_empty());
    assert!(lo.len()<usize::BITS as usize && hi.len()<usize::BITS as usize && output.len()<usize::BITS as usize);
    assert_eq!(source.len(),prefix_dirty.len());
    assert!(helpers.len()>=lo.len()+hi.len()+enable.len().saturating_sub(1));
    let mut ids: Vec<_> = source.iter().chain(lo).chain(hi).chain(output).chain(prefix_dirty).chain(helpers).map(QReg::id).collect();
    ids.extend(enable.iter().map(|q|q.id()));
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"window length alias");
    let n=source.len();let mask=(1usize<<output.len())-1;
    let low: Vec<_>=(0..n).map(|j|below_cubes(lo.len(),if coefficient {j} else if eea_suffix {j.saturating_sub(1)} else {j+1})).collect();
    let high: Vec<_>=(0..n).map(|j|if eea_suffix {vec![Vec::new()]} else {above_cubes(hi.len(),j)}).collect();

    let gate=|circ:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg| {
        if let Some((guard,scratch,known))=parity_loan {
            let mut others=Vec::new();
            for &(q,value) in controls {
                if q.id()==guard.id() {assert!(value);}
                else if q.id()==scratch.id() {assert_eq!(value,known,"loan contradicts oracle enable");}
                else {others.push((q,value));}
            }
            super::conditional_mcx::guarded(circ,guard,&others,out,scratch,known,&helpers[0]);
        } else {mixed_mcx(circ,controls,out,helpers);}
    };
    let cell=|circ: &mut Circuit,j:usize| {
        let parent:Vec<_>=if j==0 {enable.to_vec()} else {vec![&prefix_dirty[j-1]]};
        gate(circ,&parent.iter().map(|&q|(q,true)).collect::<Vec<_>>(),&prefix_dirty[j]);
        for lc in &low[j] {for hc in &high[j] {
            let mut controls: Vec<_>=parent.iter().map(|&q|(q,true)).collect();
            controls.push((&source[if coefficient {n-1-j}else{j}],true));
            controls.extend(lc.iter().map(|&(bit,value)|(&lo[bit],value)));
            controls.extend(hc.iter().map(|&(bit,value)|(&hi[bit],value)));
            gate(circ,&controls,&prefix_dirty[j]);
        }}
    };
    let zero_map=|circ: &mut Circuit| {
        for j in (1..n).rev() {cell(circ,j);}
        cell(circ,0);
        for j in 1..n {cell(circ,j);}
    };
    let writes=|circ: &mut Circuit| {
        for j in 0..n {
            let delta=if j+1<n {(n-j-1)^(n-j-2)}else{mask};
            for (bit,q) in output.iter().enumerate() {
                if (delta>>bit)&1!=0 {gate(circ,&[(&prefix_dirty[j],true)],q);}
            }
        }
    };
    for (bit,q) in output.iter().enumerate() {
        if ((n-1)>>bit)&1!=0 {
            gate(circ,&enable.iter().map(|&q|(q,true)).collect::<Vec<_>>(),q);
        }
    }
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
}

pub fn xor_encoded_length(
    circ: &mut Circuit,
    source: &[QReg],
    output: &[QReg],
    enable: Option<&QReg>,
    dirty: &[QReg],
) {
    assert!(!output.is_empty() && output.len() < usize::BITS as usize);
    let mut ids: Vec<_> = source.iter().chain(output).chain(dirty).map(QReg::id).collect();
    if let Some(q) = enable { ids.push(q.id()); }
    ids.sort_unstable();
    assert!(ids.windows(2).all(|pair| pair[0] != pair[1]), "length oracle alias");
    assert!(dirty.len() >= (source.len()+usize::from(enable.is_some())).saturating_sub(2));
    let mask = (1usize << output.len()) - 1;
    let scratch: Vec<_> = dirty.iter().collect();

    // The default (no set bit) is encoded as -1. The mutually exclusive
    // first-set predicates below change this to the corresponding length.
    for q in output {
        if let Some(c) = enable { circ.cx(c, q); } else { circ.x(q); }
    }
    for j in 0..source.len() {
        let toggle = mask ^ ((source.len()-j-1) & mask);
        if toggle != 0 {
            let mut controls: Vec<_> = enable.into_iter().collect();
            controls.extend(source[..=j].iter());
            let carrier = toggle.trailing_zeros() as usize;
            // Reversible fanout conjugation shares one MCX among all output
            // toggles, even when the output register is initially dirty.
            for bit in 0..output.len() {
                if bit != carrier && ((toggle >> bit)&1) != 0 {
                    circ.cx(&output[carrier], &output[bit]);
                }
            }
            mcx_dirty_ladder(circ, &controls, &output[carrier], &scratch);
            for bit in (0..output.len()).rev() {
                if bit != carrier && ((toggle >> bit)&1) != 0 {
                    circ.cx(&output[carrier], &output[bit]);
                }
            }
        }
        // At the next position all preceding controls require original zero.
        circ.x(&source[j]);
    }
    for q in source.iter().rev() { circ.x(q); }
}

pub mod verification {
    use super::*;
    use crate::circuit::{analyze_ops, OperationType, QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed { fn read(&mut self, b: &mut [u8]) { b.fill(0x96); } }
    fn rnd(state: &mut u64) -> u64 {
        *state ^= *state << 13; *state ^= *state >> 7; *state ^= *state << 17; *state
    }
    pub fn run() {
        let mut tested=0;
        for n in [1usize,2,3,4,5,6,7,8,16,32,64,128,255,256,259] {
            for controlled in [false,true] {
                let mut circ=Circuit::new();
                let source=circ.alloc_qreg_bits("length.source",n);
                let width=if n<=256 {8} else {9};
                let output=circ.alloc_qreg_bits("length.output",width);
                let enable=controlled.then(||circ.alloc_qreg("length.enable"));
                let dirty=circ.alloc_qreg_bits("length.dirty",n);
                let owned=circ.b.next_qubit;
                xor_encoded_length(&mut circ,&source,&output,enable.as_ref(),&dirty);
                assert_eq!(circ.b.next_qubit,owned,"oracle allocated a clean wire");
                let b=circ.into_builder();
                let (nq,nb,_,_)=analyze_ops(b.ops.iter());
                let batches=if n<=8 {(1usize<<(n+1)).div_ceil(64)*8} else {(2*(n+1)).div_ceil(64)};
                for batch in 0..batches {
                    assert!(nq <= owned as u64);
                    let mut fixed=Fixed;
                    let mut sim=Simulator::new(owned as usize,nb as usize,&mut fixed);
                    let mut random=0xa273_b6c9_d417_593du64 ^ batch as u64;
                    let mut before=vec![0u64;owned as usize];
                    for word in &mut before { *word=rnd(&mut random); }
                    let mut expected=vec![0u64;width];
                    for lane in 0..64 {
                        let k=batch*64+lane;
                        let mut length=0;
                        for (j,q) in source.iter().enumerate() {
                            let bit=if n<=8 { ((k>>1)>>(n-1-j))&1 != 0 }
                                else { let first=(k/2)%(n+1);j==first || (j>first && rnd(&mut random)&1!=0) };
                            before[q.id() as usize] = (before[q.id() as usize]&!(1u64<<lane)) | (u64::from(bit)<<lane);
                            if bit && length==0 { length=n-j; }
                        }
                        let on=!controlled || k&1!=0;
                        if let Some(q)=&enable {
                            before[q.id() as usize]=(before[q.id() as usize]&!(1u64<<lane)) | (u64::from(on)<<lane);
                        }
                        for (bit,q) in output.iter().enumerate() {
                            let old=(before[q.id() as usize]>>lane)&1;
                            let delta=if on { (length.wrapping_sub(1)>>bit)&1 } else {0};
                            expected[bit]|=(old^delta as u64)<<lane;
                        }
                    }
                    for (q,&word) in before.iter().enumerate() { *sim.qubit_mut(QubitId(q as u64))=word; }
                    sim.apply_iter(b.ops.iter().filter(|op|op.kind!=OperationType::R));
                    assert_eq!(sim.phase,0,"n={n} controlled={controlled} batch={batch}");
                    for q in source.iter().chain(&dirty).chain(enable.iter()) {
                        assert_eq!(sim.qubit(QubitId(q.id() as u64)),before[q.id() as usize],"restore n={n}");
                    }
                    for (bit,q) in output.iter().enumerate() {
                        assert_eq!(sim.qubit(QubitId(q.id() as u64)),expected[bit],"length n={n} batch={batch}");
                    }
                    tested+=64;
                }
            }
        }
        eprintln!("length recomputation PASS {tested} lanes; dirty output, restored source/lenders, phase zero, no clean allocation");
    }

    pub fn run_windows() {
        let mut tested=0;
        for n in [1usize,2,3,4,5,6,8,16,32,64,128,256,259] {
          for suffix in [false,true] {
            let width=(usize::BITS-(n as usize).leading_zeros()) as usize;
            let mut circ=Circuit::new();
            let source=circ.alloc_qreg_bits("window.source",n);
            let lo=circ.alloc_qreg_bits("window.lo",width);
            let hi=circ.alloc_qreg_bits("window.hi",width);
            let output=circ.alloc_qreg_bits("window.output",width);
            let enable=circ.alloc_qreg("window.enable");
            let prefix=circ.alloc_qreg_bits("window.prefix_dirty",n);
            let helpers=circ.alloc_qreg_bits("window.helpers_dirty",2*width);
            let owned=circ.b.next_qubit;
            if suffix {xor_eea_suffix_length(&mut circ,&source,&lo,&output,Some(&enable),&prefix,&helpers);}
            else {xor_window_length(&mut circ,&source,&lo,&hi,&output,Some(&enable),&prefix,&helpers);}
            assert_eq!(circ.b.next_qubit,owned);
            let b=circ.into_builder();let (_,nb,_,_)=analyze_ops(b.ops.iter());
            let batches=if n<=6 {(1usize<<(n+2*width+1)).div_ceil(64)*2}else{32};
            for batch in 0..batches {
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,nb as usize,&mut fixed);
                let mut random=0x5f317ea2b493860du64 ^ batch as u64;
                let mut before:Vec<u64>=(0..owned).map(|_|rnd(&mut random)).collect();
                let mut expected=vec![0u64;width];
                for lane in 0..64 {
                    let k=batch*64+lane;
                    let mask=(1usize<<width)-1;
                    let lower=if n<=6 {(k>>(n+1))&mask}else{(rnd(&mut random) as usize)&mask};
                    let upper=if n<=6 {(k>>(n+width+1))&mask}else{(rnd(&mut random) as usize)&mask};
                    let mut length=0;
                    for (j,q) in source.iter().enumerate() {
                        let bit=if n<=6 {(k>>(j+1))&1!=0}else{(rnd(&mut random)&7)==0};
                        before[q.id() as usize]=(before[q.id() as usize]&!(1<<lane))|(u64::from(bit)<<lane);
                        if j >= if suffix {lower+2} else {lower}
                            && j < if suffix {n} else {upper} && bit && length==0 {length=n-j;}
                    }
                    for (qs,v) in [(&lo,lower),(&hi,upper)] {
                        for (bit,q) in qs.iter().enumerate() {
                            before[q.id() as usize]=(before[q.id() as usize]&!(1<<lane))|((((v>>bit)&1) as u64)<<lane);
                        }
                    }
                    let on=k&1!=0;
                    before[enable.id() as usize]=(before[enable.id() as usize]&!(1<<lane))|(u64::from(on)<<lane);
                    for (bit,q) in output.iter().enumerate() {
                        let delta=if on {(length.wrapping_sub(1)>>bit)&1}else{0};
                        expected[bit]|=(((before[q.id() as usize]>>lane)&1)^delta as u64)<<lane;
                    }
                }
                for (q,&v) in before.iter().enumerate() {*sim.qubit_mut(QubitId(q as u64))=v;}
                sim.apply_iter(b.ops.iter().filter(|op|op.kind!=OperationType::R));
                assert_eq!(sim.phase,0);
                for q in source.iter().chain(&lo).chain(&hi).chain(&prefix).chain(&helpers).chain(std::iter::once(&enable)) {
                    assert_eq!(sim.qubit(QubitId(q.id() as u64)),before[q.id() as usize],"window restore n={n} batch={batch}");
                }
                for (bit,q) in output.iter().enumerate() {
                    assert_eq!(sim.qubit(QubitId(q.id() as u64)),expected[bit],"window result n={n} batch={batch}");
                }
                tested+=64;
            }
            let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
            eprintln!("window length n={n} suffix={suffix} Toffoli={t} new_clean=0");
          }
        }
        eprintln!("window length PASS {tested} lanes; quantum endpoints, dirty output/prefix/helpers, exact phase, no clean allocation");
    }
}
