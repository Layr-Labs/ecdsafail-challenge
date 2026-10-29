//! Compiled snapshot of the generated prefix before comparison passes, with six verified exact reductions.
//! The decoded pre-tail stream is pinned by count and SHA3 in prefix().
//! This replaces repeated emission/optimization of the same fixed prefix.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use sha3::{Digest, Sha3_256};
use std::io::Read;

const DATA: &[u8] = include_bytes!("divide_prefix.bin");
const PREFIX_LEN: usize = 10233017;
const PREFIX_SHA3: &str = "9547dcc9618ef1e1893f898baf05e2edb8f6e7f0157dc18dff05b16b0f36b26d";
fn kind(k: u32) -> K {
    match k {
        0=>K::Neg,1=>K::Register,2=>K::AppendToRegister,3=>K::BitInvert,
        4=>K::BitStore0,5=>K::BitStore1,6=>K::X,7=>K::Z,8=>K::CX,
        9=>K::CZ,10=>K::Swap,11=>K::R,12=>K::Hmr,13=>K::CCX,
        14=>K::CCZ,15=>K::PushCondition,16=>K::PopCondition,17=>K::DebugPrint,
        _=>panic!("divide prefix: invalid kind {k}"),
    }
}

pub(super) fn prefix() -> Vec<Op> {
    assert_eq!(&DATA[..8], b"QECCOPSZ");
    assert_eq!(u64::from_le_bytes(DATA[8..16].try_into().unwrap()) as usize, PREFIX_LEN+96);
    let mut dec=zstd::stream::read::Decoder::new(&DATA[16..]).expect("divide prefix zstd");
    let mut ops=Vec::with_capacity(PREFIX_LEN+96);
    let mut buf=[0u8;56*256];
    let mut hash=Sha3_256::new();
    while ops.len()<PREFIX_LEN {
        let n=(PREFIX_LEN-ops.len()).min(256);
        dec.read_exact(&mut buf[..n*56]).expect("divide prefix data");
        hash.update(&buf[..n*56]);
        for r in buf[..n*56].chunks_exact(56) {
            assert_eq!(&r[4..8], &[0u8;4]);
            let u=|i:usize|u64::from_le_bytes(r[i..i+8].try_into().unwrap());
            ops.push(Op{kind:kind(u32::from_le_bytes(r[..4].try_into().unwrap())),
                q_control2:QubitId(u(8)),q_control1:QubitId(u(16)),q_target:QubitId(u(24)),
                c_target:BitId(u(32)),c_condition:BitId(u(40)),r_target:RegisterId(u(48))});
        }
    }
    assert_eq!(format!("{:x}",hash.finalize()),PREFIX_SHA3,"divide prefix hash");
    ops
}
