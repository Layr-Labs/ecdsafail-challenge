// Source-bound operation edits.
use crate::circuit::{Op,OperationType as K};
use sha3::{Digest,Sha3_256};
fn rec(o:&Op)->[u64;7]{[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]}
fn mk(v:&[u64])->Op{let kinds=[K::Neg,K::Register,K::AppendToRegister,K::BitInvert,K::BitStore0,K::BitStore1,K::X,K::Z,K::CX,K::CZ,K::Swap,K::R,K::Hmr,K::CCX,K::CCZ,K::PushCondition,K::PopCondition,K::DebugPrint];let mut o=Op::empty();o.kind=kinds[v[0]as usize];o.q_control2.0=v[1];o.q_control1.0=v[2];o.q_target.0=v[3];o.c_target.0=v[4];o.c_condition.0=v[5];o.r_target.0=v[6];o.validate();o}
fn nums(l:&str)->Vec<u64>{l.split_whitespace().map(|s|s.parse().unwrap()).collect()}
// Checks the header `<stream length> <SHA3-256>` against the stream and returns the body length.
// The hash binds the stream without its last 96 ops, the X-only nonce tail, so the table does not depend on TAIL_NONCE.
fn bound_body(v:&[Op],header:&str)->usize{
let h:Vec<&str>=header.split_whitespace().collect();assert_eq!(v.len(),h[0].parse::<usize>().unwrap());
let body=v.len()-96;assert!(v[body..].iter().all(|o|o.kind==K::X),"nonce tail");
let mut hash=Sha3_256::new();for o in &v[..body]{for x in rec(o){hash.update(x.to_le_bytes());}}assert_eq!(format!("{:x}",hash.finalize()),h[1],"pre-tail stream hash");
body}
// Context table: rows `index n z`, then the n ops expected at `index` and the z ops that replace them (7 fields each).
pub(super) fn run(v:Vec<Op>,table:&str)->Vec<Op>{
let mut lines=table.lines();let body=bound_body(&v,lines.next().unwrap());
let mut out=Vec::new();let mut at=0;for l in lines{let a=nums(l);let(i,n,z)=(a[0]as usize,a[1]as usize,a[2]as usize);assert!(i>=at&&i+n<=body);out.extend_from_slice(&v[at..i]);assert_eq!(a.len(),3+7*(n+z));for j in 0..n{assert_eq!(rec(&v[i+j]),a[3+7*j..3+7*j+7]);}out.extend(a[3+7*n..].chunks(7).map(mk));at=i+n;}out.extend_from_slice(&v[at..]);out}
// Position table: every edit removes one CCX of the body. Line 2 lists the positions of the CCX that are deleted
// (the first one absolute, then the gap to the previous one). Each later line is `position` followed by the ops
// (7 fields each) that replace the CCX at that position. The edited ops are not repeated in the table: the header
// hash already fixes every op of the stream.
pub(super) fn run_positions(v:Vec<Op>,table:&str)->Vec<Op>{
let mut lines=table.lines();let body=bound_body(&v,lines.next().unwrap());
let mut edits:Vec<(usize,Vec<Op>)>=Vec::new();
let mut at=0;for gap in nums(lines.next().unwrap()){at+=gap as usize;edits.push((at,Vec::new()));}
for l in lines{let a=nums(l);assert!(a.len()>1&&a.len()%7==1,"replacement row");edits.push((a[0]as usize,a[1..].chunks(7).map(mk).collect()));}
edits.sort_by_key(|e|e.0);
let mut out=Vec::with_capacity(v.len());let mut at=0;
for(i,new)in edits{assert!(i>=at&&i<body,"positions are distinct and inside the body");assert!(v[i].kind==K::CCX,"edited op is a CCX");out.extend_from_slice(&v[at..i]);out.extend(new);at=i+1;}
out.extend_from_slice(&v[at..]);out}
