//! Paid parked signed rails <-> positive odd cofactor interface.
//! Public ecdsa.fail resource research; no real-world ECDSA key target.
use super::{builder::Builder,QubitId};
use super::pingpong::heo_hooks as h7;
use super::width_composition as wc;

pub(crate) struct Frame {
    pub a:Vec<QubitId>, pub b:Vec<QubitId>, pub signs:[QubitId;2],
    orient:QubitId, original_r1_width:usize, fused:bool,
}
fn room(c:&Builder)->usize{h7::cap().saturating_sub(c.active_qubits()as usize)}
fn add(c:&mut Builder,source:&[QubitId],target:&[QubitId],incoming:Option<QubitId>,subtract:bool){
    assert_eq!(source.len(),target.len());let zero=incoming.unwrap_or_else(||c.alloc_qubit());
    let map:Vec<_>=source.iter().map(|&q|vec![q]).collect();
    let plan=wc::direct_plan(target.len(),room(c)).expect("adapter carry plan");
    if subtract{c.x_all(target);}wc::direct_add(c,&map,target,zero,&plan);if subtract{c.x_all(target);}
    if incoming.is_none(){c.free(zero);}
}
fn increment(c:&mut Builder,target:&[QubitId],incoming:QubitId){
    let map=vec![Vec::new();target.len()];let p=wc::direct_plan(target.len(),room(c)).expect("adapter increment plan");
    wc::direct_add(c,&map,target,incoming,&p);
}
fn negate(c:&mut Builder,target:&[QubitId],sign:QubitId){c.cx_all(sign,target);increment(c,target,sign);}
fn left(c:&mut Builder,r:&[QubitId]){for i in(0..r.len()-1).rev(){c.swap(r[i],r[i+1]);}}
fn right(c:&mut Builder,r:&[QubitId]){for i in 0..r.len()-1{c.swap(r[i],r[i+1]);}}
fn route(c:&mut Builder,a:&[QubitId],b:&[QubitId],q:QubitId){for(&u,&v)in a.iter().zip(b){h7::cswap(c,q,u,v);}}

// Difference's carry into bit1, after complementing each input by its sign:
// carry = sg XOR ((NOT S0) AND (1 XOR sg XOR ss)). Original G0=NOT S0.
fn difference_carry(c:&mut Builder,s0:QubitId,sg:QubitId,ss:QubitId)->(QubitId,QubitId){
    let mix=c.alloc_qubit();c.x(mix);c.cx(sg,mix);c.cx(ss,mix);
    let carry=c.alloc_qubit();c.cx(sg,carry);c.x(s0);c.ccx(s0,mix,carry);c.x(s0);(carry,mix)
}
fn clear_difference_carry(c:&mut Builder,s0:QubitId,sg:QubitId,ss:QubitId,carry:QubitId,mix:QubitId){
    let m=c.alloc_bit();c.hmr(carry,m);c.z_if(sg,m);c.z_if(mix,m);c.cz_if(s0,mix,m);c.free_bit(m);c.free(carry);
    c.cx(ss,mix);c.cx(sg,mix);c.x(mix);c.free(mix);
}
fn folded_source(c:&mut Builder,s:&[QubitId],sign:QubitId){c.cx_all(sign,s);c.x_all(s);}
fn fused_forward(c:&mut Builder,g:&[QubitId],s:&[QubitId],sg:QubitId,ss:QubitId){
    let(carry,mix)=difference_carry(c,s[0],sg,ss);
    c.cx(s[0],g[0]); // G0 XOR S0 =1, the known odd difference bit.
    c.cx_all(sg,&g[1..]);folded_source(c,&s[1..],ss);
    add(c,&s[1..],&g[1..],Some(carry),false);
    folded_source(c,&s[1..],ss);clear_difference_carry(c,s[0],sg,ss,carry,mix);
    // S^ss has a zero top bit because S is the smaller magnitude. Fold its
    // absolute-value increment into the carry of the following high-word add.
    c.cx_all(ss,s);left(c,s);c.x(s[0]);add(c,&g[1..],&s[1..],Some(ss),false);
}
fn fused_inverse(c:&mut Builder,d:&[QubitId],k:&[QubitId],sg:QubitId,ss:QubitId){
    add(c,&d[1..],&k[1..],Some(ss),true);c.x(k[0]);right(c,k);c.cx_all(ss,k);
    let(carry,mix)=difference_carry(c,k[0],sg,ss);
    folded_source(c,&k[1..],ss);add(c,&k[1..],&d[1..],Some(carry),true);folded_source(c,&k[1..],ss);
    c.cx_all(sg,&d[1..]);c.cx(k[0],d[0]);clear_difference_carry(c,k[0],sg,ss,carry,mix);
}

pub(crate) fn forward(c:&mut Builder,r1:&[QubitId],r2_parked:&[QubitId],orient:QubitId,fused:bool)->Frame{
    let width=r2_parked.len()+1;assert!(r1.len()==width||r1.len()+1==width);
    let parity=c.alloc_qubit();c.x(parity);c.cx(r1[0],parity);let mut b=vec![parity];b.extend_from_slice(r2_parked);
    let mut a=r1.to_vec();if a.len()<width{let q=c.alloc_qubit();c.cx(*a.last().unwrap(),q);a.push(q);}
    route(c,&a,&b,orient);let signs=[c.alloc_qubit(),c.alloc_qubit()];c.cx(a[width-1],signs[0]);c.cx(b[width-1],signs[1]);
    if fused{fused_forward(c,&a,&b,signs[0],signs[1]);}
    else{negate(c,&a,signs[0]);negate(c,&b,signs[1]);add(c,&b,&a,None,true);left(c,&b);add(c,&a,&b,None,false);}
    // D top=0; D0=K0=1. This includes signed-min boundaries by opposite parity.
    c.x(a[0]);c.x(b[0]);c.free(a[width-1]);c.free(a[0]);c.free(b[0]);
    Frame{a,b,signs,orient,original_r1_width:r1.len(),fused}
}
pub(crate) fn inverse(c:&mut Builder,f:&Frame){
    let w=f.a.len();for q in[f.a[w-1],f.a[0],f.b[0]]{c.reacquire(q);}c.x(f.a[0]);c.x(f.b[0]);
    if f.fused{fused_inverse(c,&f.a,&f.b,f.signs[0],f.signs[1]);}
    else{add(c,&f.a,&f.b,None,true);right(c,&f.b);add(c,&f.b,&f.a,None,false);negate(c,&f.a,f.signs[0]);negate(c,&f.b,f.signs[1]);}
    c.cx(f.a[w-1],f.signs[0]);c.cx(f.b[w-1],f.signs[1]);c.free_vec(&f.signs);
    route(c,&f.a,&f.b,f.orient);
    if f.original_r1_width<w{c.cx(f.a[w-2],f.a[w-1]);c.free(f.a[w-1]);}
    c.cx(f.a[0],f.b[0]);c.x(f.b[0]);c.free(f.b[0]);
}

pub(crate) fn probe(){
    use std::io::Write;
    std::env::set_var("HEO_RESEARCH","1");std::env::set_var("HEO_PHASE_REPORT","1");std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS","1175");
    std::fs::create_dir_all("adapter-gates").unwrap();
    for(w,aw,room)in[(4usize,3usize,8usize),(5,5,8),(8,7,16),(99,99,60),(136,135,74),(136,135,32)]{
        for fused in[false,true]{for mode in["forward","inverse","roundtrip"]{
            let mut c=Builder::new();let r1=c.alloc_qubits(aw);let r2=c.alloc_qubits(w-1);let orient=c.alloc_qubit();
            let _pad=c.alloc_qubits(h7::cap()-c.active_qubits()as usize-room);let entry=c.active_qubits();
            let mut start=c.op_count();let f=forward(&mut c,&r1,&r2,orient,fused);
            let forward_cost=c.report_totals().unwrap().1;let middle=c.active_qubits();let mut cost=forward_cost;
            let mut peak=c.take_win_peak();
            if mode!="forward"{
                if mode=="inverse"{start=c.op_count();}
                inverse(&mut c,&f);let ip=c.take_win_peak();peak=if mode=="inverse"{ip}else{peak.max(ip)};
                cost=c.report_totals().unwrap().1-if mode=="inverse"{forward_cost}else{0.0};
            }
            let end=c.active_qubits();let(nq,nb)=c.i13_dims();let ops=c.take_ops();
            let name=format!("w{w}-a{aw}-room{room}-{}-{mode}",if fused{"fused"}else{"control"});let path=format!("adapter-gates/{name}.json");
            let ids=|qs:&[QubitId]|qs.iter().map(|q|q.0.to_string()).collect::<Vec<_>>().join(",");
            let mut out=std::io::BufWriter::new(std::fs::File::create(&path).unwrap());
            writeln!(out,"{{\"nq\":{nq},\"nb\":{nb},\"input_start\":{start},\"r1\":[{}],\"r2_parked\":[{}],\"orient\":{},\"D_high\":[{}],\"K_high\":[{}],\"signs\":[{}],\"ops\":[",ids(&r1),ids(&r2),orient.0,ids(&f.a[1..w-1]),ids(&f.b[1..]),ids(&f.signs)).unwrap();
            for(i,o)in ops.iter().enumerate(){writeln!(out,"{}[{},{},{},{},{},{},{}]",if i==0{""}else{","},o.kind as u32,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0).unwrap();}writeln!(out,"]}}").unwrap();
            println!("{{\"name\":\"{name}\",\"w\":{w},\"r1_width\":{aw},\"room\":{room},\"fused\":{fused},\"mode\":\"{mode}\",\"T\":{cost},\"Q\":{peak},\"native_entry_live\":{entry},\"cofactor_live\":{middle},\"end_live\":{end},\"artifact\":\"{path}\"}}");
        }}
    }
}
