//! New harness qualification of the frozen physical R01 implementation.
//! V1's test had an obsolete W2[A+1]=0 assertion on the special A1/S1 branch.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::q793_r01_dynamic_v1::signless;
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
#[path="q793_r01_dynamic_v2_check.rs"] mod check;
pub fn run(){check::run();}
