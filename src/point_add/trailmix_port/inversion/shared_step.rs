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
pub(super) const SCHEDULE_BLOCK:usize=4;
pub(super) const SCHEDULE_BLOCKS:usize=404;
pub(super) const SCHEDULE_SUPPORTS:[(usize,usize);404]=[
    (2,3), // steps 1..4
    (2,4), // steps 5..8
    (2,5), // steps 9..12
    (2,6), // steps 13..16
    (2,7), // steps 17..20
    (2,8), // steps 21..24
    (2,9), // steps 25..28
    (2,10), // steps 29..32
    (2,11), // steps 33..36
    (2,12), // steps 37..40
    (2,13), // steps 41..44
    (2,14), // steps 45..48
    (2,15), // steps 49..52
    (2,16), // steps 53..56
    (2,17), // steps 57..60
    (2,18), // steps 61..64
    (2,19), // steps 65..68
    (2,20), // steps 69..72
    (2,21), // steps 73..76
    (2,22), // steps 77..80
    (2,23), // steps 81..84
    (2,24), // steps 85..88
    (2,25), // steps 89..92
    (2,26), // steps 93..96
    (2,27), // steps 97..100
    (2,28), // steps 101..104
    (2,29), // steps 105..108
    (2,30), // steps 109..112
    (2,31), // steps 113..116
    (2,32), // steps 117..120
    (2,33), // steps 121..124
    (2,34), // steps 125..128
    (2,35), // steps 129..132
    (2,36), // steps 133..136
    (2,37), // steps 137..140
    (2,38), // steps 141..144
    (2,39), // steps 145..148
    (2,40), // steps 149..152
    (2,41), // steps 153..156
    (2,42), // steps 157..160
    (2,43), // steps 161..164
    (2,44), // steps 165..168
    (2,45), // steps 169..172
    (2,46), // steps 173..176
    (2,47), // steps 177..180
    (2,48), // steps 181..184
    (2,49), // steps 185..188
    (2,50), // steps 189..192
    (2,51), // steps 193..196
    (2,52), // steps 197..200
    (2,53), // steps 201..204
    (2,54), // steps 205..208
    (2,55), // steps 209..212
    (2,56), // steps 213..216
    (2,57), // steps 217..220
    (2,58), // steps 221..224
    (2,59), // steps 225..228
    (2,60), // steps 229..232
    (2,61), // steps 233..236
    (2,62), // steps 237..240
    (2,63), // steps 241..244
    (2,64), // steps 245..248
    (2,65), // steps 249..252
    (2,66), // steps 253..256
    (2,67), // steps 257..260
    (2,68), // steps 261..264
    (2,69), // steps 265..268
    (2,70), // steps 269..272
    (4,71), // steps 273..276
    (4,72), // steps 277..280
    (5,73), // steps 281..284
    (5,74), // steps 285..288
    (7,75), // steps 289..292
    (7,76), // steps 293..296
    (8,77), // steps 297..300
    (8,78), // steps 301..304
    (10,79), // steps 305..308
    (10,80), // steps 309..312
    (11,81), // steps 313..316
    (11,82), // steps 317..320
    (13,83), // steps 321..324
    (13,84), // steps 325..328
    (14,85), // steps 329..332
    (14,86), // steps 333..336
    (16,87), // steps 337..340
    (16,88), // steps 341..344
    (18,89), // steps 345..348
    (18,90), // steps 349..352
    (19,91), // steps 353..356
    (19,92), // steps 357..360
    (21,93), // steps 361..364
    (21,94), // steps 365..368
    (22,95), // steps 369..372
    (22,96), // steps 373..376
    (24,97), // steps 377..380
    (24,98), // steps 381..384
    (25,99), // steps 385..388
    (25,100), // steps 389..392
    (27,101), // steps 393..396
    (27,102), // steps 397..400
    (28,103), // steps 401..404
    (28,104), // steps 405..408
    (30,105), // steps 409..412
    (30,106), // steps 413..416
    (31,107), // steps 417..420
    (31,108), // steps 421..424
    (33,109), // steps 425..428
    (33,110), // steps 429..432
    (34,111), // steps 433..436
    (34,112), // steps 437..440
    (36,113), // steps 441..444
    (36,114), // steps 445..448
    (37,115), // steps 449..452
    (37,116), // steps 453..456
    (39,117), // steps 457..460
    (39,118), // steps 461..464
    (40,119), // steps 465..468
    (40,120), // steps 469..472
    (42,121), // steps 473..476
    (42,122), // steps 477..480
    (43,123), // steps 481..484
    (43,124), // steps 485..488
    (45,125), // steps 489..492
    (45,126), // steps 493..496
    (46,127), // steps 497..500
    (46,128), // steps 501..504
    (48,129), // steps 505..508
    (48,130), // steps 509..512
    (49,131), // steps 513..516
    (49,132), // steps 517..520
    (51,133), // steps 521..524
    (51,134), // steps 525..528
    (52,135), // steps 529..532
    (52,136), // steps 533..536
    (54,137), // steps 537..540
    (54,138), // steps 541..544
    (55,139), // steps 545..548
    (55,140), // steps 549..552
    (57,141), // steps 553..556
    (57,142), // steps 557..560
    (58,143), // steps 561..564
    (58,144), // steps 565..568
    (60,145), // steps 569..572
    (60,146), // steps 573..576
    (61,147), // steps 577..580
    (61,148), // steps 581..584
    (63,149), // steps 585..588
    (63,150), // steps 589..592
    (64,151), // steps 593..596
    (64,152), // steps 597..600
    (66,153), // steps 601..604
    (66,154), // steps 605..608
    (67,155), // steps 609..612
    (67,156), // steps 613..616
    (69,157), // steps 617..620
    (69,158), // steps 621..624
    (70,159), // steps 625..628
    (70,160), // steps 629..632
    (72,161), // steps 633..636
    (72,162), // steps 637..640
    (73,163), // steps 641..644
    (73,164), // steps 645..648
    (75,165), // steps 649..652
    (75,166), // steps 653..656
    (76,167), // steps 657..660
    (76,168), // steps 661..664
    (78,169), // steps 665..668
    (78,170), // steps 669..672
    (79,171), // steps 673..676
    (79,172), // steps 677..680
    (81,173), // steps 681..684
    (81,174), // steps 685..688
    (82,175), // steps 689..692
    (82,176), // steps 693..696
    (84,177), // steps 697..700
    (84,178), // steps 701..704
    (85,179), // steps 705..708
    (85,180), // steps 709..712
    (87,181), // steps 713..716
    (87,182), // steps 717..720
    (88,183), // steps 721..724
    (88,184), // steps 725..728
    (90,185), // steps 729..732
    (90,186), // steps 733..736
    (91,187), // steps 737..740
    (91,188), // steps 741..744
    (93,189), // steps 745..748
    (93,190), // steps 749..752
    (94,191), // steps 753..756
    (94,192), // steps 757..760
    (96,193), // steps 761..764
    (96,194), // steps 765..768
    (97,195), // steps 769..772
    (97,196), // steps 773..776
    (99,197), // steps 777..780
    (99,198), // steps 781..784
    (100,199), // steps 785..788
    (100,200), // steps 789..792
    (102,201), // steps 793..796
    (102,202), // steps 797..800
    (103,203), // steps 801..804
    (103,204), // steps 805..808
    (105,205), // steps 809..812
    (105,206), // steps 813..816
    (106,207), // steps 817..820
    (106,208), // steps 821..824
    (108,209), // steps 825..828
    (108,210), // steps 829..832
    (109,211), // steps 833..836
    (109,212), // steps 837..840
    (111,213), // steps 841..844
    (111,214), // steps 845..848
    (112,215), // steps 849..852
    (112,216), // steps 853..856
    (114,217), // steps 857..860
    (114,218), // steps 861..864
    (115,219), // steps 865..868
    (115,220), // steps 869..872
    (117,221), // steps 873..876
    (117,222), // steps 877..880
    (118,223), // steps 881..884
    (118,224), // steps 885..888
    (120,225), // steps 889..892
    (120,226), // steps 893..896
    (121,227), // steps 897..900
    (121,228), // steps 901..904
    (123,229), // steps 905..908
    (123,230), // steps 909..912
    (124,231), // steps 913..916
    (124,232), // steps 917..920
    (126,233), // steps 921..924
    (126,234), // steps 925..928
    (127,235), // steps 929..932
    (127,236), // steps 933..936
    (129,237), // steps 937..940
    (129,238), // steps 941..944
    (130,239), // steps 945..948
    (130,240), // steps 949..952
    (132,241), // steps 953..956
    (132,242), // steps 957..960
    (133,243), // steps 961..964
    (133,244), // steps 965..968
    (135,245), // steps 969..972
    (135,246), // steps 973..976
    (136,247), // steps 977..980
    (136,248), // steps 981..984
    (138,249), // steps 985..988
    (138,250), // steps 989..992
    (139,251), // steps 993..996
    (139,252), // steps 997..1000
    (141,253), // steps 1001..1004
    (141,254), // steps 1005..1008
    (142,255), // steps 1009..1012
    (142,256), // steps 1013..1016
    (144,257), // steps 1017..1020
    (144,257), // steps 1021..1024
    (145,257), // steps 1025..1028
    (145,257), // steps 1029..1032
    (147,257), // steps 1033..1036
    (147,257), // steps 1037..1040
    (148,257), // steps 1041..1044
    (148,257), // steps 1045..1048
    (150,257), // steps 1049..1052
    (150,257), // steps 1053..1056
    (151,257), // steps 1057..1060
    (151,257), // steps 1061..1064
    (153,257), // steps 1065..1068
    (153,257), // steps 1069..1072
    (154,257), // steps 1073..1076
    (154,257), // steps 1077..1080
    (156,257), // steps 1081..1084
    (156,257), // steps 1085..1088
    (157,257), // steps 1089..1092
    (157,257), // steps 1093..1096
    (159,257), // steps 1097..1100
    (159,257), // steps 1101..1104
    (160,257), // steps 1105..1108
    (160,257), // steps 1109..1112
    (162,257), // steps 1113..1116
    (162,257), // steps 1117..1120
    (163,257), // steps 1121..1124
    (163,257), // steps 1125..1128
    (165,257), // steps 1129..1132
    (165,257), // steps 1133..1136
    (166,257), // steps 1137..1140
    (166,257), // steps 1141..1144
    (168,257), // steps 1145..1148
    (168,257), // steps 1149..1152
    (170,257), // steps 1153..1156
    (170,257), // steps 1157..1160
    (171,257), // steps 1161..1164
    (171,257), // steps 1165..1168
    (173,257), // steps 1169..1172
    (173,257), // steps 1173..1176
    (174,257), // steps 1177..1180
    (174,257), // steps 1181..1184
    (176,257), // steps 1185..1188
    (176,257), // steps 1189..1192
    (177,257), // steps 1193..1196
    (177,257), // steps 1197..1200
    (179,257), // steps 1201..1204
    (179,257), // steps 1205..1208
    (180,257), // steps 1209..1212
    (180,257), // steps 1213..1216
    (182,257), // steps 1217..1220
    (182,257), // steps 1221..1224
    (183,257), // steps 1225..1228
    (183,257), // steps 1229..1232
    (185,257), // steps 1233..1236
    (185,257), // steps 1237..1240
    (186,257), // steps 1241..1244
    (186,257), // steps 1245..1248
    (188,257), // steps 1249..1252
    (188,257), // steps 1253..1256
    (189,257), // steps 1257..1260
    (189,257), // steps 1261..1264
    (191,257), // steps 1265..1268
    (191,257), // steps 1269..1272
    (192,257), // steps 1273..1276
    (192,257), // steps 1277..1280
    (194,257), // steps 1281..1284
    (194,257), // steps 1285..1288
    (195,257), // steps 1289..1292
    (195,257), // steps 1293..1296
    (197,257), // steps 1297..1300
    (197,257), // steps 1301..1304
    (198,257), // steps 1305..1308
    (198,257), // steps 1309..1312
    (200,257), // steps 1313..1316
    (200,257), // steps 1317..1320
    (201,257), // steps 1321..1324
    (201,257), // steps 1325..1328
    (203,257), // steps 1329..1332
    (203,257), // steps 1333..1336
    (204,257), // steps 1337..1340
    (204,257), // steps 1341..1344
    (206,257), // steps 1345..1348
    (206,257), // steps 1349..1352
    (207,257), // steps 1353..1356
    (207,257), // steps 1357..1360
    (209,257), // steps 1361..1364
    (209,257), // steps 1365..1368
    (210,257), // steps 1369..1372
    (210,257), // steps 1373..1376
    (212,257), // steps 1377..1380
    (212,257), // steps 1381..1384
    (213,257), // steps 1385..1388
    (213,257), // steps 1389..1392
    (215,257), // steps 1393..1396
    (215,257), // steps 1397..1400
    (216,257), // steps 1401..1404
    (216,257), // steps 1405..1408
    (218,257), // steps 1409..1412
    (218,257), // steps 1413..1416
    (219,257), // steps 1417..1420
    (219,257), // steps 1421..1424
    (221,257), // steps 1425..1428
    (221,257), // steps 1429..1432
    (222,257), // steps 1433..1436
    (222,257), // steps 1437..1440
    (224,257), // steps 1441..1444
    (224,257), // steps 1445..1448
    (225,257), // steps 1449..1452
    (225,257), // steps 1453..1456
    (227,257), // steps 1457..1460
    (227,257), // steps 1461..1464
    (228,257), // steps 1465..1468
    (228,257), // steps 1469..1472
    (230,257), // steps 1473..1476
    (230,257), // steps 1477..1480
    (231,257), // steps 1481..1484
    (231,257), // steps 1485..1488
    (233,257), // steps 1489..1492
    (233,257), // steps 1493..1496
    (234,257), // steps 1497..1500
    (234,257), // steps 1501..1504
    (236,257), // steps 1505..1508
    (236,257), // steps 1509..1512
    (237,257), // steps 1513..1516
    (237,257), // steps 1517..1520
    (239,257), // steps 1521..1524
    (239,257), // steps 1525..1528
    (240,257), // steps 1529..1532
    (240,257), // steps 1533..1536
    (242,257), // steps 1537..1540
    (242,257), // steps 1541..1544
    (243,257), // steps 1545..1548
    (243,257), // steps 1549..1552
    (245,257), // steps 1553..1556
    (245,257), // steps 1557..1560
    (246,257), // steps 1561..1564
    (246,257), // steps 1565..1568
    (248,257), // steps 1569..1572
    (248,257), // steps 1573..1576
    (249,257), // steps 1577..1580
    (249,257), // steps 1581..1584
    (251,257), // steps 1585..1588
    (251,257), // steps 1589..1592
    (252,257), // steps 1593..1596
    (252,257), // steps 1597..1600
    (254,257), // steps 1601..1604
    (254,257), // steps 1605..1608
    (255,257), // steps 1609..1612
    (255,257), // steps 1613..1616
];
