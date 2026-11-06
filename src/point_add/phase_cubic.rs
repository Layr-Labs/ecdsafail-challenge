pub(super) fn run(ops:Vec<crate::circuit::Op>)->Vec<crate::circuit::Op>{
if std::env::var("YP8_VETO").is_ok_and(|v|v=="1"){ops}else{super::phase_cubic_base::run(ops)}}
