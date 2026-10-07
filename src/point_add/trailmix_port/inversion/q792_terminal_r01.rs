//! Eight-bit terminal history in the disjoint folded20 marker.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

// All actual metadata owners must be live and from this Circuit, with pending
// frees flushed by the caller. Numeric IDs cannot authenticate a foreign Rc.
fn terminal88_preflight(c:&Circuit,m:&[QReg]) {
    let mut ids:Vec<_>=m.iter().map(QReg::id).collect();
    assert!(ids.iter().all(|&id|id!=u32::MAX&&id<c.b.next_qubit),"terminal omitted/outside metadata");
    assert!(ids.iter().all(|id|!c.b.free_qubits.contains(id)),"terminal freed metadata");
    ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]),"terminal metadata alias");
    assert!(!super::q792_passive_r01::active(),"terminal is outside passive lowering");
    // This query records no gates. It rejects active virtual-rank capture on
    // every participating low-ID rank rail; the actual caller uses m0..19.
    let controls:Vec<_>=m.iter().map(|q|(q,true)).collect();
    assert!(super::q792_rank4_lower_r01::pair_begin(c,&controls).is_none(),"terminal is outside rank lowering");
}
fn terminal88_order()->bool {
    static REVERSE_ORDER:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
    *REVERSE_ORDER.get_or_init(||std::env::var("LOWQ_MCX_REVERSE_ORDER").ok().as_deref()==Some("1"))
}
// Explicit MAJ/carry/UMA adder or its literal inverse, arbitrary high bit.
fn terminal88_arithmetic(c:&mut Circuit,a:&[&QReg;8],v:&[&QReg;9],carry:&QReg,subtract:bool) {
    for i in 0..8 {let previous=if i==0{carry}else{a[i-1]};
        c.cx(if subtract{previous}else{a[i]},v[i]);c.cx(a[i],previous);c.ccx(previous,v[i],a[i]);}
    c.cx(a[7],v[8]);
    for i in (0..8).rev(){let previous=if i==0{carry}else{a[i-1]};
        c.ccx(previous,v[i],a[i]);c.cx(a[i],previous);c.cx(if subtract{a[i]}else{previous},v[i]);}
}
fn terminal88_increment(c:&mut Circuit,m:&[QReg],inverse:bool) {
    let a=[&m[0],&m[1],&m[2],&m[3],&m[5],&m[6],&m[7],&m[8]];
    let v=[&m[4],&m[10],&m[11],&m[12],&m[13],&m[14],&m[15],&m[16],&m[17]];
    let carry=&m[9];
    for &q in &v{c.cx(carry,q);}
    if !inverse {
        terminal88_arithmetic(c,&a,&v,carry,true);for &q in &a{c.x(q);}
        terminal88_arithmetic(c,&a,&v,carry,true);for &q in a.iter().rev(){c.x(q);}c.x(v[8]);
    }else {
        c.x(v[8]);for &q in &a{c.x(q);}terminal88_arithmetic(c,&a,&v,carry,false);
        for &q in a.iter().rev(){c.x(q);}terminal88_arithmetic(c,&a,&v,carry,false);
    }
    for &q in v.iter().rev(){c.cx(carry,q);}
}
fn terminal88_u(c:&mut Circuit,m:&[QReg],inverse:bool) {
    if inverse{c.x(&m[4]);terminal88_increment(c,m,true);}
    else{terminal88_increment(c,m,false);c.x(&m[4]);}
}
// Same five-control enough-dirty ladder as the donor, with explicit inverse.
// Each cascade is palindromic; inverse reverses seeded/unseeded cascade order.
fn terminal88_f(c:&mut Circuit,m:&[QReg],reverse_order:bool,inverse:bool) {
    let a=&m[4];let d=[&m[6],&m[7],&m[8]];
    let mut controls=[&m[0],&m[1],&m[2],&m[3],&m[5]];
    if reverse_order{controls.reverse();}
    for q in &m[10..18]{c.cx(a,q);}
    for seed in if inverse{[false,true]}else{[true,false]} {
        if seed{c.ccx(controls[0],controls[1],d[0]);}
        for i in 1..3{c.ccx(d[i-1],controls[i+1],d[i]);}
        c.ccx(d[2],controls[4],a);
        for i in (1..3).rev(){c.ccx(d[i-1],controls[i+1],d[i]);}
        if seed{c.ccx(controls[0],controls[1],d[0]);}
    }
    for q in m[10..18].iter().rev(){c.cx(a,q);}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],d:&[QReg],quarter:bool,inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);
    terminal88_preflight(c,m);if !quarter{return;}
    let reverse_order=terminal88_order();
    let owned=(c.b.next_qubit,c.b.active_qubits,c.b.peak_qubits,c.b.next_bit,c.b.next_register,c.b.allocation_serial);
    // U;F;U^-1;F gives h+=E. The other arm is its full literal inverse.
    if inverse{terminal88_f(c,m,reverse_order,true);terminal88_u(c,m,false);
        terminal88_f(c,m,reverse_order,true);terminal88_u(c,m,true);}
    else{terminal88_u(c,m,false);terminal88_f(c,m,reverse_order,false);
        terminal88_u(c,m,true);terminal88_f(c,m,reverse_order,false);}
    assert_eq!((c.b.next_qubit,c.b.active_qubits,c.b.peak_qubits,c.b.next_bit,c.b.next_register,c.b.allocation_serial),owned);
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x99)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut total=0;for quarter in [false,true]{let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let d=c.alloc_qreg_bits("d",20);let n=c.b.next_qubit;emit(&mut c,&m,&d,quarter,false);assert_eq!(c.b.next_qubit,n);let ops=c.into_builder().ops;
        eprintln!("FOLD20_TERMINAL_BUILT quarter={quarter} T={} ops={}",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len());
        for first in (0..1usize<<20).step_by(64){let mut seed=0x7927e4d1u64^first as u64;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[bit]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}let mut after=before.clone();
            for lane in 0..64{let code=first+lane;let mut out=code;if quarter&&code&15==15&&code>>5&1!=0{let h=(code>>10)&255;out=(code&!(255<<10))|(((h+1)&255)<<10);}for bit in 0..20{let mask=1u64<<lane;after[bit]=(after[bit]&!mask)|(((out>>bit&1)as u64)<<lane);}}
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
    }eprintln!("FOLD20_TERMINAL_NATIVE_PASS lanes={total} all20bit_physical_codes=true history8=true inverse=true phase=0");
}
