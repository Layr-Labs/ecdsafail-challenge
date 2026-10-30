// Generated source-edit applicator. Do not edit.
use crate::circuit::{Op,OperationType as K};
use sha3::{Digest,Sha3_256};
fn rec(o:&Op)->[u64;7]{[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]}
fn mk(v:&[u64])->Op{let kinds=[K::Neg,K::Register,K::AppendToRegister,K::BitInvert,K::BitStore0,K::BitStore1,K::X,K::Z,K::CX,K::CZ,K::Swap,K::R,K::Hmr,K::CCX,K::CCZ,K::PushCondition,K::PopCondition,K::DebugPrint];let mut o=Op::empty();o.kind=kinds[v[0]as usize];o.q_control2.0=v[1];o.q_control1.0=v[2];o.q_target.0=v[3];o.c_target.0=v[4];o.c_condition.0=v[5];o.r_target.0=v[6];o.validate();o}
pub(super) fn run(v:Vec<Op>)->Vec<Op>{
let mut lines=include_str!("copy_elision.txt").lines();let h:Vec<&str>=lines.next().unwrap().split_whitespace().collect();assert_eq!(v.len(),h[0].parse::<usize>().unwrap());let mut hash=Sha3_256::new();for o in &v{for x in rec(o){hash.update(x.to_le_bytes());}}assert_eq!(format!("{:x}",hash.finalize()),h[1],"source-edit complete-prefix hash");
let mut out=Vec::new();let mut at=0;for l in lines{let a:Vec<u64>=l.split_whitespace().map(|s|s.parse().unwrap()).collect();let(i,n,z)=(a[0]as usize,a[1]as usize,a[2]as usize);out.extend_from_slice(&v[at..i]);assert_eq!(a.len(),3+7*(n+z));for j in 0..n{assert_eq!(rec(&v[i+j]),a[3+7*j..3+7*j+7]);}for r in a[3+7*n..].chunks(7){out.push(mk(r));}at=i+n;}out.extend_from_slice(&v[at..]);out}
