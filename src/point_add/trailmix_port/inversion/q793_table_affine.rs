//! W5 affine-frame winners (lane-kimi-w45), baked from research/w5 scorer
//! output (w5-winners-v1, accept=true only). Each entry was independently
//! re-verified by check_winners.py and is re-verified exhaustively at every
//! emission by metadata_muxlease::swap_plan; the emission-time accept rule
//! (strictly smaller T actual, ops not up, site-exact external controls) can
//! still decline. Generator: research/gen_affine_table.py.
pub struct AffineEntry{pub width:usize,pub truth:u64,pub g_rows:[u32;6],pub polarity:u32,pub terms:u64}
pub static AFFINE_WINNERS:&[AffineEntry]=&[
    AffineEntry{width:5,truth:0x00000000e07fe000,g_rows:[9,10,4,8,20,0],polarity:8,terms:0x0000000081000090}, // dT=-24 calls=163981 weighted=-3935544
    AffineEntry{width:5,truth:0x000000006381e00f,g_rows:[29,10,6,14,7,0],polarity:5,terms:0x0000000080240814}, // dT=-52 calls=21816 weighted=-1134432
    AffineEntry{width:5,truth:0x00000000b4d22911,g_rows:[29,26,25,24,13,0],polarity:2,terms:0x0000000082030044}, // dT=-22 calls=12120 weighted=-266640
    AffineEntry{width:6,truth:0x93ce070f6c31f8f0,g_rows:[1,30,28,24,16,32],polarity:2,terms:0x0000000100258110}, // dT=-26 calls=51624 weighted=-1342224
    AffineEntry{width:6,truth:0x038fe7f06fbe1f00,g_rows:[1,2,4,14,28,44],polarity:40,terms:0x0380041021542145}, // dT=-87 calls=25800 weighted=-2244600
    AffineEntry{width:5,truth:0x000000006fbe1f00,g_rows:[15,18,28,23,16,0],polarity:19,terms:0x0000000090110821}, // dT=-37 calls=9696 weighted=-358752
    AffineEntry{width:5,truth:0x000000006c301800,g_rows:[27,26,6,8,16,0],polarity:0,terms:0x0000000008402000}, // dT=-21 calls=22668 weighted=-476028
    AffineEntry{width:5,truth:0x0000000060000000,g_rows:[3,2,4,8,16,0],polarity:0,terms:0x0000000020000000}, // dT=-12 calls=9696 weighted=-116352
    AffineEntry{width:6,truth:0x00691ec800001480,g_rows:[47,14,36,24,16,32],polarity:30,terms:0x02600202840c0000}, // dT=-68 calls=7104 weighted=-483072
    AffineEntry{width:5,truth:0x0000000000001480,g_rows:[1,7,5,9,16,0],polarity:16,terms:0x0000000084000000}, // dT=-40 calls=4680 weighted=-187200
    AffineEntry{width:5,truth:0x0000000000000a48,g_rows:[5,2,3,8,21,0],polarity:0,terms:0x0000000020080000}, // dT=-32 calls=10920 weighted=-349440
    AffineEntry{width:5,truth:0x0000000000000124,g_rows:[1,11,14,8,16,0],polarity:16,terms:0x0000000080400000}, // dT=-40 calls=6240 weighted=-249600
    AffineEntry{width:5,truth:0x000000008c4e18f0,g_rows:[31,22,20,8,14,0],polarity:4,terms:0x0000000091080019}, // dT=-36 calls=5208 weighted=-187488
    AffineEntry{width:5,truth:0x0000000010701f00,g_rows:[9,10,4,12,20,0],polarity:0,terms:0x0000000081000180}, // dT=-29 calls=2610 weighted=-75690
    AffineEntry{width:5,truth:0x0000000020802001,g_rows:[5,14,4,8,16,0],polarity:27,terms:0x0000000008000080}, // dT=-40 calls=10302 weighted=-412080
    AffineEntry{width:6,truth:0x3a94b5a5c56b4a5a,g_rows:[31,10,12,24,16,32],polarity:5,terms:0x0000000104208007}, // dT=-40 calls=22872 weighted=-914880
    AffineEntry{width:6,truth:0xdf16c1361a7d8b6c,g_rows:[1,3,6,11,16,47],polarity:7,terms:0x2152881404805114}, // dT=-80 calls=11472 weighted=-917760
    AffineEntry{width:5,truth:0x00000000fc70180f,g_rows:[9,30,26,22,14,0],polarity:16,terms:0x0000000082014050}, // dT=-53 calls=3276 weighted=-173628
];
pub fn lookup(width:usize,truth:u64)->Option<&'static AffineEntry>{
    AFFINE_WINNERS.iter().find(|e|e.width==width&&e.truth==truth)
}
