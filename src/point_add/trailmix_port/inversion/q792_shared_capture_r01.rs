//! Diagnostic-only contiguous output-function groups. No circuit mutation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use std::cell::RefCell;
#[derive(Clone)]struct Item{word:Vec<u32>,prefix:Vec<(u32,bool)>,out:u32,truth:u64,start:usize,end:usize,t:usize}
thread_local!{static STATE:RefCell<(bool,Vec<Item>)>=const{RefCell::new((false,Vec::new()))};}
fn flush(v:&mut Vec<Item>){if v.len()>1{let a=&v[0];let fs=v.iter().map(|x|format!("{:x}",x.truth)).collect::<Vec<_>>().join(",");let ts=v.iter().map(|x|x.t.to_string()).collect::<Vec<_>>().join(",");let key=format!("n={} k={} f={} T={}",a.word.len(),a.prefix.len(),fs,ts);static SEEN:std::sync::OnceLock<std::sync::Mutex<std::collections::BTreeMap<String,usize>>>=std::sync::OnceLock::new();let mut seen=SEEN.get_or_init(||std::sync::Mutex::new(std::collections::BTreeMap::new())).lock().unwrap();let count=seen.entry(key.clone()).or_default();*count+=1;eprintln!("GPU_OUTPUT_GROUP {key} occurrence={count}");}v.clear();}
pub(super)fn begin(){STATE.with(|s|{let mut s=s.borrow_mut();flush(&mut s.1);s.0=std::env::var_os("FOLD20_GPU_CAPTURE").is_some();});}
pub(super)fn end(){STATE.with(|s|{let mut s=s.borrow_mut();flush(&mut s.1);s.0=false;});}
pub(super)fn record(c:&Circuit,word:&[&QReg],truth:&[bool],prefix:&[(&QReg,bool)],out:&QReg,start:usize){STATE.with(|s|{let mut s=s.borrow_mut();if !s.0{return;}if !(4..=6).contains(&word.len())||super::q792_passive_r01::active()||super::q792_rank4_lower_r01::capture_active(){flush(&mut s.1);return;}
 let item=Item{word:word.iter().map(|q|q.id()).collect(),prefix:prefix.iter().map(|(q,b)|(q.id(),*b)).collect(),out:out.id(),truth:truth.iter().enumerate().fold(0,|a,(i,&b)|a|((b as u64)<<i)),start,end:c.b.ops.len(),t:c.b.ops[start..].iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count()};
 if let Some(a)=s.1.last(){if a.end!=item.start||a.word!=item.word||a.prefix!=item.prefix||s.1.iter().any(|a|a.out==item.out)||s.1.len()==8{flush(&mut s.1);}}
 if item.word.contains(&item.out)||item.prefix.iter().any(|(q,_)|*q==item.out){flush(&mut s.1);return;}s.1.push(item);
});}
