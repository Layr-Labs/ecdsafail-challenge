//! All104 supported-loop qualification of the frozen dynamic R01 emitter.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::q793_r01_dynamic_v1::signless;
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn support(block:usize)->(usize,usize){super::shared_step::SCHEDULE_SUPPORTS[block]}
#[path="q793_r01_supported_v3_check.rs"] mod check;
pub fn run(){check::run();}
