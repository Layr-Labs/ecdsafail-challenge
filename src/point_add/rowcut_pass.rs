pub(super) fn run(ops:Vec<crate::circuit::Op>)->Vec<crate::circuit::Op>{
if std::env::var("YP8_VETO").is_ok_and(|v|v=="1"){
if std::env::var("YP8_VETO_PAD").is_ok_and(|v|v=="1"){super::rowcut_veto_pad::run(ops)}else{super::rowcut_veto::run(ops)}
}else{super::rowcut_base::run(ops)}}
