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
/// Scheduled steps per window block. Every consumer derives its block index from this,
/// so the two support tables and all reference filters cannot drift apart.
/// MUST stay a multiple of 4: emit_schedule selects cached[(step+1)%4], so each block
/// must contain all four j-phases. 1616 = 202 x 8.
pub(super) const SCHEDULE_BLOCK:usize=8;
pub(super) const SCHEDULE_BLOCKS:usize=202;

pub(super) const SCHEDULE_SUPPORTS:[(usize,usize);202]=[
    (2,4), // steps 1..8
    (2,6), // steps 9..16
    (2,8), // steps 17..24
    (2,10), // steps 25..32
    (2,12), // steps 33..40
    (2,14), // steps 41..48
    (2,16), // steps 49..56
    (2,18), // steps 57..64
    (2,20), // steps 65..72
    (2,22), // steps 73..80
    (2,24), // steps 81..88
    (2,26), // steps 89..96
    (2,28), // steps 97..104
    (2,30), // steps 105..112
    (2,32), // steps 113..120
    (2,34), // steps 121..128
    (2,36), // steps 129..136
    (2,38), // steps 137..144
    (2,40), // steps 145..152
    (2,42), // steps 153..160
    (2,44), // steps 161..168
    (2,46), // steps 169..176
    (2,48), // steps 177..184
    (2,50), // steps 185..192
    (2,52), // steps 193..200
    (2,54), // steps 201..208
    (2,56), // steps 209..216
    (2,58), // steps 217..224
    (2,60), // steps 225..232
    (2,62), // steps 233..240
    (2,64), // steps 241..248
    (2,66), // steps 249..256
    (2,68), // steps 257..264
    (2,70), // steps 265..272
    (4,72), // steps 273..280
    (5,74), // steps 281..288
    (7,76), // steps 289..296
    (8,78), // steps 297..304
    (10,80), // steps 305..312
    (11,82), // steps 313..320
    (13,84), // steps 321..328
    (14,86), // steps 329..336
    (16,88), // steps 337..344
    (18,90), // steps 345..352
    (19,92), // steps 353..360
    (21,94), // steps 361..368
    (22,96), // steps 369..376
    (24,98), // steps 377..384
    (25,100), // steps 385..392
    (27,102), // steps 393..400
    (28,104), // steps 401..408
    (30,106), // steps 409..416
    (31,108), // steps 417..424
    (33,110), // steps 425..432
    (34,112), // steps 433..440
    (36,114), // steps 441..448
    (37,116), // steps 449..456
    (39,118), // steps 457..464
    (40,120), // steps 465..472
    (42,122), // steps 473..480
    (43,124), // steps 481..488
    (45,126), // steps 489..496
    (46,128), // steps 497..504
    (48,130), // steps 505..512
    (49,132), // steps 513..520
    (51,134), // steps 521..528
    (52,136), // steps 529..536
    (54,138), // steps 537..544
    (55,140), // steps 545..552
    (57,142), // steps 553..560
    (58,144), // steps 561..568
    (60,146), // steps 569..576
    (61,148), // steps 577..584
    (63,150), // steps 585..592
    (64,152), // steps 593..600
    (66,154), // steps 601..608
    (67,156), // steps 609..616
    (69,158), // steps 617..624
    (70,160), // steps 625..632
    (72,162), // steps 633..640
    (73,164), // steps 641..648
    (75,166), // steps 649..656
    (76,168), // steps 657..664
    (78,170), // steps 665..672
    (79,172), // steps 673..680
    (81,174), // steps 681..688
    (82,176), // steps 689..696
    (84,178), // steps 697..704
    (85,180), // steps 705..712
    (87,182), // steps 713..720
    (88,184), // steps 721..728
    (90,186), // steps 729..736
    (91,188), // steps 737..744
    (93,190), // steps 745..752
    (94,192), // steps 753..760
    (96,194), // steps 761..768
    (97,196), // steps 769..776
    (99,198), // steps 777..784
    (100,200), // steps 785..792
    (102,202), // steps 793..800
    (103,204), // steps 801..808
    (105,206), // steps 809..816
    (106,208), // steps 817..824
    (108,210), // steps 825..832
    (109,212), // steps 833..840
    (111,214), // steps 841..848
    (112,216), // steps 849..856
    (114,218), // steps 857..864
    (115,220), // steps 865..872
    (117,222), // steps 873..880
    (118,224), // steps 881..888
    (120,226), // steps 889..896
    (121,228), // steps 897..904
    (123,230), // steps 905..912
    (124,232), // steps 913..920
    (126,234), // steps 921..928
    (127,236), // steps 929..936
    (129,238), // steps 937..944
    (130,240), // steps 945..952
    (132,242), // steps 953..960
    (133,244), // steps 961..968
    (135,246), // steps 969..976
    (136,248), // steps 977..984
    (138,250), // steps 985..992
    (139,252), // steps 993..1000
    (141,254), // steps 1001..1008
    (142,256), // steps 1009..1016
    (144,257), // steps 1017..1024
    (145,257), // steps 1025..1032
    (147,257), // steps 1033..1040
    (148,257), // steps 1041..1048
    (150,257), // steps 1049..1056
    (151,257), // steps 1057..1064
    (153,257), // steps 1065..1072
    (154,257), // steps 1073..1080
    (156,257), // steps 1081..1088
    (157,257), // steps 1089..1096
    (159,257), // steps 1097..1104
    (160,257), // steps 1105..1112
    (162,257), // steps 1113..1120
    (163,257), // steps 1121..1128
    (165,257), // steps 1129..1136
    (166,257), // steps 1137..1144
    (168,257), // steps 1145..1152
    (170,257), // steps 1153..1160
    (171,257), // steps 1161..1168
    (173,257), // steps 1169..1176
    (174,257), // steps 1177..1184
    (176,257), // steps 1185..1192
    (177,257), // steps 1193..1200
    (179,257), // steps 1201..1208
    (180,257), // steps 1209..1216
    (182,257), // steps 1217..1224
    (183,257), // steps 1225..1232
    (185,257), // steps 1233..1240
    (186,257), // steps 1241..1248
    (188,257), // steps 1249..1256
    (189,257), // steps 1257..1264
    (191,257), // steps 1265..1272
    (192,257), // steps 1273..1280
    (194,257), // steps 1281..1288
    (195,257), // steps 1289..1296
    (197,257), // steps 1297..1304
    (198,257), // steps 1305..1312
    (200,257), // steps 1313..1320
    (201,257), // steps 1321..1328
    (203,257), // steps 1329..1336
    (204,257), // steps 1337..1344
    (206,257), // steps 1345..1352
    (207,257), // steps 1353..1360
    (209,257), // steps 1361..1368
    (210,257), // steps 1369..1376
    (212,257), // steps 1377..1384
    (213,257), // steps 1385..1392
    (215,257), // steps 1393..1400
    (216,257), // steps 1401..1408
    (218,257), // steps 1409..1416
    (219,257), // steps 1417..1424
    (221,257), // steps 1425..1432
    (222,257), // steps 1433..1440
    (224,257), // steps 1441..1448
    (225,257), // steps 1449..1456
    (227,257), // steps 1457..1464
    (228,257), // steps 1465..1472
    (230,257), // steps 1473..1480
    (231,257), // steps 1481..1488
    (233,257), // steps 1489..1496
    (234,257), // steps 1497..1504
    (236,257), // steps 1505..1512
    (237,257), // steps 1513..1520
    (239,257), // steps 1521..1528
    (240,257), // steps 1529..1536
    (242,257), // steps 1537..1544
    (243,257), // steps 1545..1552
    (245,257), // steps 1553..1560
    (246,257), // steps 1561..1568
    (248,257), // steps 1569..1576
    (249,257), // steps 1577..1584
    (251,257), // steps 1585..1592
    (252,257), // steps 1593..1600
    (254,257), // steps 1601..1608
    (255,257), // steps 1609..1616
];
