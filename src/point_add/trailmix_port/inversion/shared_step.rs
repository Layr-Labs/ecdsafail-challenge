//! Shared-register EEA steps, including reversible terminal padding.
//! Whole-inversion initialization/cleanup are integrated separately.
use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

fn increment(circ:&mut Circuit,word:&[QReg],controls:&[&QReg],helpers:&[QReg],subtract:bool) {
    let dirty:Vec<_>=helpers.iter().collect();
    let js:Vec<_>=if subtract {(0..word.len()).collect()}else{(0..word.len()).rev().collect()};
    for j in js {let mut cs=controls.to_vec();cs.extend(word[..j].iter());mcx_dirty_ladder(circ,&cs,&word[j],&dirty);}
}
fn add_word(circ:&mut Circuit,source:&[QReg],target:&[QReg],helpers:&[QReg],subtract:bool) {
    assert_eq!(source.len(),target.len());let dirty:Vec<_>=helpers.iter().collect();
    let mut cells=Vec::new();for i in 0..source.len(){for j in (i..target.len()).rev(){cells.push((i,j));}}
    if subtract {cells.reverse();}
    for (i,j) in cells {let mut cs=vec![&source[i]];cs.extend(target[i..j].iter());mcx_dirty_ladder(circ,&cs,&target[j],&dirty);}
}
fn swap(circ:&mut Circuit,a:&QReg,b:&QReg,controls:&[&QReg],helpers:&[QReg]) {
    circ.cx(b,a);let mut cs=controls.to_vec();cs.push(a);
    mcx_dirty_ladder(circ,&cs,b,&helpers.iter().collect::<Vec<_>>());circ.cx(b,a);
}
fn rotate(circ:&mut Circuit,word:&[QReg],controls:&[&QReg],helpers:&[QReg],right:bool) {
    let js:Vec<_>=if right {(1..word.len()).rev().collect()}else{(1..word.len()).collect()};
    for j in js {swap(circ,&word[j-1],&word[j],controls,helpers);}
}

/// The pre/post physical shift pair, with the ordinary modulo-256 shift word.
/// The caller must disable the pre-shift for already-terminal states.
pub fn shift_block(circ:&mut Circuit,work2:&[QReg],shift:&[QReg],p1:&QReg,p2:&QReg,helpers:&[QReg],post:bool) {
    if !post {circ.x(p1);}
    rotate(circ,work2,&[p1],helpers,false);increment(circ,shift,&[p1],helpers,false);
    rotate(circ,work2,&[p1,p2],helpers,true);rotate(circ,work2,&[p1,p2],helpers,true);
    increment(circ,&shift[1..],&[p1,p2],helpers,true);
    if !post {circ.x(p1);}
}

/// Quotient-bit insertion/removal using L as the quotient-length register.
/// During phase11 L instead holds LR, but all operations are disabled there.
/// Position minus2 is LTraw+LQraw, including the quotient-length256 case.
pub fn quotient_exchange(circ:&mut Circuit,work1:&[QReg],lt:&[QReg],shared:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,helpers:&[QReg]) {
    quotient_exchange_with_parity(circ,work1,lt,shared,p1,p2,sign,helpers,None);
}

fn quotient_exchange_with_parity(circ:&mut Circuit,work1:&[QReg],lt:&[QReg],shared:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,helpers:&[QReg],parity_loan:Option<(&QReg,bool)>) {
    assert_eq!(work1.len(),259);assert_eq!(lt.len(),8);assert_eq!(shared.len(),8);
    let dirty:Vec<_>=helpers.iter().collect();
    circ.x(p1);increment(circ,shared,&[p1,p2],helpers,false);circ.x(p1);
    add_word(circ,lt,shared,helpers,false);
    // The quotient is exchanged only in phases01/10. Encode their XOR in
    // P2 once, instead of lowering two equal controlled exchanges per bit.
    if let Some((scratch,parity))=parity_loan {circ.cx(p1,scratch);if parity {circ.x(scratch);}}
    circ.cx(p1,p2);
    for j in 2..258 {
        let code=j-2;
        for (bit,q) in shared.iter().enumerate(){if (code>>bit)&1==0 {circ.x(q);}}
        circ.cx(&work1[j],sign);
        if let Some((scratch,_))=parity_loan {
            let mut others=vec![(sign,true)];others.extend(shared.iter().map(|q|(q,true)));
            super::conditional_mcx::guarded(circ,p2,&others,&work1[j],scratch,false,&helpers[0]);
        } else {
            let mut cs=vec![p2,sign];cs.extend(shared.iter());
            mcx_dirty_ladder(circ,&cs,&work1[j],&dirty);
        }
        circ.cx(&work1[j],sign);
        for (bit,q) in shared.iter().enumerate(){if (code>>bit)&1==0 {circ.x(q);}}
    }
    circ.cx(p1,p2);
    if let Some((scratch,parity))=parity_loan {if parity {circ.x(scratch);}circ.cx(p1,scratch);}
    add_word(circ,lt,shared,helpers,true);
    circ.x(p2);increment(circ,shared,&[p1,p2],helpers,true);circ.x(p2);
}

/// One ACTIVE reference step on the complete 546-wire inversion state.
/// Passenger helpers may contain arbitrary quantum data and are restored.
/// This route must not yet be applied to already-terminal padding states.
pub fn active_step(circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg]) {
    assert_eq!(work1.len(),259);assert_eq!(work2.len(),259);assert_eq!(lt.len(),8);assert_eq!(shift.len(),8);assert_eq!(shared.len(),8);assert!(helpers.len()>=24);
    let mut ids:Vec<_>=work1.iter().chain(work2).chain(lt).chain(shift).chain(shared).chain(helpers).map(QReg::id).collect();
    ids.extend([p1.id(),p2.id(),sign.id(),iteration.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"shared active step aliases");
    shift_block(circ,work2,shift,p1,p2,helpers,false);
    super::shared_remainder::remainder_block(circ,work1,work2,lt,shift,shared,p1,p2,sign,helpers);
    quotient_exchange(circ,work1,lt,shared,p1,p2,sign,helpers);
    super::shared_arithmetic::coefficient_block(circ,work1,work2,lt,shift,shared,p1,p2,sign,helpers);
    shift_block(circ,work2,shift,p1,p2,helpers,true);
    super::shared_metadata::active_step_boundary(circ,work1,work2,lt,shift,shared,p1,p2,sign,iteration,helpers);
}

/// One scheduled step, including already-terminal states. At steps divisible
/// by four, terminal LS increments once and Work2 stays unrotated. A completed
/// secp cycle requires >=1024 steps, so the1616-step schedule pads at most148
/// times. LS never wraps in this terminal representation.
pub fn scheduled_step(circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg],quarter:bool) {
    scheduled_step_with_support(circ,work1,work2,lt,shift,shared,p1,p2,sign,iteration,helpers,quarter,0,259,None);
}

pub(super) fn scheduled_step_with_support(circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,helpers:&[QReg],quarter:bool,r_first:usize,t_end:usize,step_parity:Option<bool>) {
    assert_eq!(work1.len(),259);assert_eq!(work2.len(),259);assert_eq!(lt.len(),8);assert_eq!(shift.len(),8);assert_eq!(shared.len(),8);assert!(helpers.len()>=24);
    let mut ids:Vec<_>=work1.iter().chain(work2).chain(lt).chain(shift).chain(shared).chain(helpers).map(QReg::id).collect();
    ids.extend([p1.id(),p2.id(),sign.id(),iteration.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"scheduled step aliases");
    let terminal:Vec<_>=lt.iter().collect();let dirty:Vec<_>=helpers.iter().collect();
    if quarter {increment(circ,shift,&terminal,helpers,false);}
    mcx_dirty_ladder(circ,&terminal,p1,&dirty);
    shift_block(circ,work2,shift,p1,p2,helpers,false);
    mcx_dirty_ladder(circ,&terminal,p1,&dirty);
    super::shared_remainder::remainder_block_with_support(circ,work1,work2,lt,shift,shared,p1,p2,sign,helpers,r_first,step_parity);
    quotient_exchange_with_parity(circ,work1,lt,shared,p1,p2,sign,helpers,step_parity.map(|p|(&shift[0],p)));
    super::shared_arithmetic::coefficient_block_with_support(circ,work1,work2,lt,shift,shared,p1,p2,sign,helpers,t_end,step_parity.map(|p|!p));
    shift_block(circ,work2,shift,p1,p2,helpers,true);
    let metadata_parity=if std::env::var("LOWQ_METADATA_PARITY_LOAN").ok().as_deref()==Some("1") {step_parity}else{None};
    super::shared_metadata::scheduled_boundary_with_parity(circ,work1,work2,lt,shift,shared,p1,p2,sign,iteration,helpers,quarter,metadata_parity);
}

/// Appendix-A.2 analytic bounds, pinned primary source e64aa3c1198d96aeb389e64bc7ae48edbb9712ec:
/// eea_circuit_updated.py::active_windows. Fixed n=256, outward-rounded over
/// blocks of64 scheduled steps; R lower bound at block start, T upper at end.
/// Values come from the analytic formula, never from measured sample extents.
pub(super) const SCHEDULE_BLOCK:usize=32;
pub(super) const SCHEDULE_BLOCKS:usize=51;
pub(super) const SCHEDULE_SUPPORTS:[(usize,usize);51]=[
    (2,10), // steps 1..32
    (2,18), // steps 33..64
    (2,26), // steps 65..96
    (2,34), // steps 97..128
    (2,42), // steps 129..160
    (2,50), // steps 161..192
    (2,58), // steps 193..224
    (2,66), // steps 225..256
    (2,74), // steps 257..288
    (7,82), // steps 289..320
    (13,90), // steps 321..352
    (19,98), // steps 353..384
    (25,106), // steps 385..416
    (31,114), // steps 417..448
    (37,122), // steps 449..480
    (43,130), // steps 481..512
    (49,138), // steps 513..544
    (55,146), // steps 545..576
    (61,154), // steps 577..608
    (67,162), // steps 609..640
    (73,170), // steps 641..672
    (79,178), // steps 673..704
    (85,186), // steps 705..736
    (91,194), // steps 737..768
    (97,202), // steps 769..800
    (103,210), // steps 801..832
    (109,218), // steps 833..864
    (115,226), // steps 865..896
    (121,234), // steps 897..928
    (127,242), // steps 929..960
    (133,250), // steps 961..992
    (139,257), // steps 993..1024
    (145,257), // steps 1025..1056
    (151,257), // steps 1057..1088
    (157,257), // steps 1089..1120
    (163,257), // steps 1121..1152
    (170,257), // steps 1153..1184
    (176,257), // steps 1185..1216
    (182,257), // steps 1217..1248
    (188,257), // steps 1249..1280
    (194,257), // steps 1281..1312
    (200,257), // steps 1313..1344
    (206,257), // steps 1345..1376
    (212,257), // steps 1377..1408
    (218,257), // steps 1409..1440
    (224,257), // steps 1441..1472
    (230,257), // steps 1473..1504
    (236,257), // steps 1505..1536
    (242,257), // steps 1537..1568
    (248,257), // steps 1569..1600
    (254,257), // steps 1601..1616
];
