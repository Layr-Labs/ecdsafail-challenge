//! Bounded performance measurement on this candidate's actual primitive templates.
use crate::circuit::{Op,OperationType as K};
use std::io::{Write,Read};
use std::time::Instant;
fn record(o:&Op)->[u8;56]{let mut r=[0;56];r[..4].copy_from_slice(&(o.kind as u32).to_le_bytes());for(i,v)in[o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0].into_iter().enumerate(){r[8+8*i..16+8*i].copy_from_slice(&v.to_le_bytes());}r}
pub fn run(){
 let mut cache=crate::point_add::q793_runtime_r01::Cache::default();cache.synchronize();let started=Instant::now();let mut ops_count=0;let mut template_secs=0f64;let mut check_secs=0f64;
 for block in 0..super::shared_step::SCHEDULE_BLOCKS{for j in 0..4{let at=Instant::now();let ops=super::q793_lifecycle_r03::template(block,j);template_secs+=at.elapsed().as_secs_f64();ops_count+=ops.len();let at=Instant::now();cache.insert((block,j),&ops);assert_eq!(cache.get((block,j)).unwrap(),ops);check_secs+=at.elapsed().as_secs_f64();}}
 let first_secs=started.elapsed().as_secs_f64();let at=Instant::now();for _ in 0..3{for block in 0..super::shared_step::SCHEDULE_BLOCKS{for j in 0..4{let ops=cache.get((block,j)).unwrap();std::hint::black_box(ops);}}}let reuse_secs=at.elapsed().as_secs_f64();
 eprintln!("Q793_RUNTIME_CACHE_PROBE templates=104 stored_ops={ops_count} compressed_bytes={} generation_s={template_secs:.6} encode_decode_check_s={check_secs:.6} first_s={first_secs:.6} three_reuses_s={reuse_secs:.6} cache_all104_exact=true",cache.bytes());
 let ops=cache.get((12,0)).unwrap();let mut kinds=[0usize;18];for o in &ops{kinds[o.kind as usize]+=1;}
 let copies=64;let n=ops.len()*copies;let mut a=crate::point_add::B::new();let mut b=crate::point_add::B::new();a.ops.reserve_exact(n);b.ops.reserve_exact(n);
 let at=Instant::now();for _ in 0..copies{for &o in &ops{a.push_op(o);}}let scalar_s=at.elapsed().as_secs_f64();
 let at=Instant::now();for _ in 0..copies{b.append_nct_template(&ops,&kinds);}let bulk_s=at.elapsed().as_secs_f64();assert_eq!(a.ops,b.ops);assert_eq!(a.counted_ops,b.counted_ops);assert_eq!(a.counted_kind_ops,b.counted_kind_ops);assert_eq!(a.counted_phase_kind_ops,b.counted_phase_kind_ops);
 eprintln!("Q793_RUNTIME_APPEND_PROBE template_block=12 clock=0 copies={copies} expanded_ops={n} bytes={} scalar_s={scalar_s:.6} bulk_s={bulk_s:.6} complete_stream_and_counters_equal=true",n*56);drop(a);drop(b);
 for level in [3,1]{
  let copies=32;let at=Instant::now();let mut enc=zstd::stream::write::Encoder::new(Vec::new(),level).unwrap();for _ in 0..copies{for o in &ops{enc.write_all(&record(o)).unwrap();}}let bytes=enc.finish().unwrap();let encode_s=at.elapsed().as_secs_f64();let compressed=bytes.len();
  let at=Instant::now();let decoder=zstd::stream::read::Decoder::new(std::io::Cursor::new(bytes)).unwrap();let mut decoder=std::io::BufReader::new(decoder);let mut rec=[0u8;56];for _ in 0..copies{for o in &ops{decoder.read_exact(&mut rec).unwrap();assert_eq!(rec,record(o));}}assert_eq!(decoder.read(&mut rec).unwrap(),0);let decode_check_s=at.elapsed().as_secs_f64();
  eprintln!("Q793_RUNTIME_ZSTD_PROBE level={level} expanded_ops={} raw_bytes={} compressed_bytes={compressed} encode_s={encode_s:.6} decode_check_s={decode_check_s:.6} exact_record_stream=true",copies*ops.len(),copies*ops.len()*56);
 }
 assert!(kinds[K::CCX as usize]>0);eprintln!("Q793_RUNTIME_PROBE_R01_PASS bounded_actual_templates=true whole_ordinary_not_materialized=true");
}
