//! Standalone exact fused restoring-R01 bridge for a modulo-four chart.
//! Not a production cargo adapter and not a whole-Q794 claim.
//! There are no physical y0/y1 rails and no separately allocated borrow-out.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use super::length_recompute::mixed_mcx;

const S0: &[usize] = &[23,28,35,37,40,41,49,51,52,55,57,87,89,97,113,117,149,177,209];
const S1: &[usize] = &[23,24,53,85,113,145];

fn residual(code: usize) -> usize {
    let (t,b,v,q)=(code&3,code>>2&3,code>>4&3,code>>6&3);
    if t&1!=0 {(3usize.wrapping_sub(b*v).wrapping_mul(t).wrapping_sub(q*v))&3} else {b}
}
fn valid(code:usize)->bool {code&1!=0 || code&16!=0}

fn seed(circ:&mut Circuit,word:[&QReg;8],ha:&QReg,dirty:&[QReg],shift:usize){
    if shift>=2{return;}
    let (polarity,terms)=if shift==0{(204,S0)}else{(108,S1)};
    for code in 0..256 {
        let want=residual(code)<(((code>>4&3)<<shift)&3);
        let got=terms.iter().filter(|&&m|(code^polarity)&m==m).count()&1!=0;
        assert_eq!(got,want,"fixed-polarity seed truth table");
    }
    for i in 0..8{if polarity>>i&1!=0{circ.x(word[i]);}}
    for &m in terms{
        let cs:Vec<_>=(0..8).filter(|&i|m>>i&1!=0).map(|i|(word[i],true)).collect();
        mixed_mcx(circ,&cs,ha,dirty);
    }
    for i in (0..8).rev(){if polarity>>i&1!=0{circ.x(word[i]);}}
}

fn maj(circ:&mut Circuit,s:&QReg,y:&QReg,ha:&QReg,inverse:bool){
    if inverse {circ.ccx(y,s,ha);circ.cx(ha,s);circ.cx(s,y);}
    else {circ.cx(s,y);circ.cx(ha,s);circ.ccx(y,s,ha);}
}

/// word=[t0,t1,b0,b1,v0,v1,qpre0,qpre1]. source is the already shifted X,
/// n bits, with an implicit zero bit n; target_high is physical y[2..n].
/// source low bits equal (v*2^shift)mod4. It may alias v0/v1 at positions
/// shift/shift+1; all other aliases are forbidden. This unit updates the
/// supplied qpre rails by decision*2^shift mod4 AFTER unseeding HA.
///
/// Under g=1, HA must start zero and decision starts the old high bit h.
/// q_out=h XOR [y>=X]; y_out=y-q_out*X mod2^n. Under g=0, HA and h are
/// arbitrary and the entire operation is identity. Three dirty rails suffice.
pub(super) fn emit(circ:&mut Circuit,word:[&QReg;8],source:&[QReg],target_high:&[QReg],
    decision:&QReg,g:&QReg,ha:&QReg,dirty:&[QReg],shift:usize){
    let n=source.len();assert!(n>=3 && shift<=2 && target_high.len()==n-2);
    assert!(dirty.len()>=3);
    let mut unique:Vec<_>=source.iter().chain(target_high).chain(dirty).map(QReg::id).collect();
    unique.extend([decision.id(),g.id(),ha.id()]);
    for (i,q) in word.iter().enumerate(){
        if i==4||i==5{
            if let Some(at)=source.iter().position(|s|s.id()==q.id()) {assert_eq!(at,shift+i-4);continue;}
        }
        unique.push(q.id());
    }
    unique.sort_unstable();assert!(unique.windows(2).all(|x|x[0]!=x[1]),"R01 low bridge alias");
    let before=circ.b.next_qubit;let active=circ.b.active_qubits;
    let start=circ.b.ops.len();seed(circ,word,ha,dirty,shift);
    let unseed=circ.b.ops[start..].to_vec();
    // F is allowed to move arbitrary off-guard data: its paired inverse and
    // disabled center/SUM restore it. In particular HA need not be clean g0.
    for i in 2..n {maj(circ,&source[i],&target_high[i-2],ha,false);}
    circ.cx(g,decision);circ.ccx(g,ha,decision);
    for i in (2..n).rev(){
        maj(circ,&source[i],&target_high[i-2],ha,true);
        circ.cx(ha,&source[i]);
        mixed_mcx(circ,&[(g,true),(decision,true),(&source[i],true)],&target_high[i-2],dirty);
        circ.cx(ha,&source[i]);
    }
    // Lower chart and unshifted v are still their INPUT values here.
    circ.b.ops.extend(unseed.into_iter().rev());
    if shift==0 {
        mixed_mcx(circ,&[(g,true),(decision,true),(word[0],false),(word[4],true)],word[2],dirty);
        mixed_mcx(circ,&[(g,true),(decision,true),(word[0],false),(word[5],true)],word[3],dirty);
        mixed_mcx(circ,&[(g,true),(decision,true),(word[0],false),(word[4],true),(word[2],true)],word[3],dirty);
        mixed_mcx(circ,&[(g,true),(decision,true),(word[6],true)],word[7],dirty);
        circ.ccx(g,decision,word[6]);
    } else if shift==1 {
        mixed_mcx(circ,&[(g,true),(decision,true),(word[0],false),(word[4],true)],word[3],dirty);
        circ.ccx(g,decision,word[7]);
    }
    assert_eq!(circ.b.next_qubit,before,"no new borrow/decode rails");
    assert_eq!(circ.b.active_qubits,active);
}

pub fn run(){verification::run();}

mod verification {
    use super::*;
    use crate::{circuit::{Op,OperationType as K},sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],id:usize,lane:usize,b:bool){if b{w[id]|=1u64<<lane;}else{w[id]&=!(1u64<<lane);}}
    fn bitword(w:&mut[u64],ids:&[usize],lane:usize,value:usize){for(i,&q)in ids.iter().enumerate(){put(w,q,lane,value>>i&1!=0);}}
    struct Program{ops:Vec<Op>,source:Vec<usize>,target:Vec<usize>,word:[usize;8],decision:usize,g:usize,ha:usize,dirty:Vec<usize>,nq:usize,t:usize}
    fn program(n:usize,shift:usize)->Program{
        assert!(n>=shift+2);
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
        let source=circ.alloc_qreg_bits("q794.low.source_shifted",n);
        let chart=circ.alloc_qreg_bits("q794.low.t_b_qpre",6);
        let word=[&chart[0],&chart[1],&chart[2],&chart[3],&source[shift],&source[shift+1],&chart[4],&chart[5]];
        let target=circ.alloc_qreg_bits("q794.low.yhigh",n-2);
        let decision=circ.alloc_qreg("q794.low.existing_h");let g=circ.alloc_qreg("q794.low.g");
        let ha=circ.alloc_qreg("q794.low.existing_HA");let dirty=circ.alloc_qreg_bits("q794.low.dirty",3);
        let nq=circ.b.next_qubit as usize;assert_eq!(nq,2*n+10);
        emit(&mut circ,word,&source,&target,&decision,&g,&ha,&dirty,shift);
        assert_eq!(circ.b.next_qubit as usize,nq);
        let ops=circ.b.ops.clone();for o in &ops{o.validate();assert!(matches!(o.kind,K::X|K::CX|K::CCX));}
        let t=ops.iter().filter(|o|o.kind==K::CCX).count();
        Program{ops,source:source.iter().map(|q|q.id()as usize).collect(),target:target.iter().map(|q|q.id()as usize).collect(),word:word.map(|q|q.id()as usize),decision:decision.id()as usize,g:g.id()as usize,ha:ha.id()as usize,dirty:dirty.iter().map(|q|q.id()as usize).collect(),nq,t}
    }
    fn lane(p:&Program,n:usize,shift:usize,index:usize,small:bool,codes:&[usize],seed:&mut u64,before:&mut[u64],after:&mut[u64],l:usize){
        let mut z=index;
        let code=if small{let x=codes[z%codes.len()];z/=codes.len();x}else{codes[rnd(seed)as usize%codes.len()]};
        let mut x=vec![false;n];let mut y=vec![false;n];
        for i in 0..2{x[shift+i]=(code>>(4+i))&1!=0;y[i]=residual(code)>>i&1!=0;}
        for q in &mut x[shift+2..]{*q=if small{let v=z&1!=0;z>>=1;v}else{rnd(seed)&1!=0};}
        for q in &mut y[2..]{*q=if small{let v=z&1!=0;z>>=1;v}else{rnd(seed)&1!=0};}
        let h=if small{let v=z&1!=0;z>>=1;v}else{rnd(seed)&1!=0};
        let guard_state=if small{let v=z%3;z/=3;v}else{rnd(seed)as usize%3};
        let(g,ha)=match guard_state{0=>(true,false),1=>(false,false),_=>(false,true)};
        let dirty=if small{z&7}else{rnd(seed)as usize&7};
        if !small && index<8 {
            // Deterministic high-limb extremes retain the chosen valid chart.
            for i in shift+2..n{x[i]=index&1!=0;}
            for i in 2..n{y[i]=index&2!=0;}
        }
        let ge=(0..n).rev().find(|&i|x[i]!=y[i]).map(|i|y[i]).unwrap_or(true);
        let q=if g{h^ge}else{h};let take=g&&q;
        let mut out=y.clone();let mut borrow=false;
        if take{for i in 0..n{out[i]=y[i]^x[i]^borrow;borrow=(!y[i]&&(x[i]||borrow))||(x[i]&&borrow);}}
        let b=code>>2&3;let amount=((code>>4&3)<<shift)&3;
        let bnext=if take&&code&1==0{b.wrapping_sub(amount)&3}else{b};
        let qnext=if take{((code>>6&3)+(1<<shift))&3}else{code>>6&3};
        let next=(code&0x33)|(bnext<<2)|(qnext<<6);
        assert_eq!(residual(next),usize::from(out[0])+2*usize::from(out[1]));
        for i in 0..n{put(before,p.source[i],l,x[i]);put(after,p.source[i],l,x[i]);}
        for i in 0..8{put(before,p.word[i],l,code>>i&1!=0);put(after,p.word[i],l,next>>i&1!=0);}
        for i in 2..n{put(before,p.target[i-2],l,y[i]);put(after,p.target[i-2],l,out[i]);}
        for(w,d)in[(&mut *before,h),(&mut *after,q)]{put(w,p.decision,l,d);put(w,p.g,l,g);put(w,p.ha,l,ha);bitword(w,&p.dirty,l,dirty);}
    }
    fn check(n:usize,shift:usize)->(usize,String){
        let p=program(n,shift);let small=n<=6;let codes:Vec<_>=(0..256).filter(|&c|valid(c)).collect();assert_eq!(codes.len(),192);
        let cases=if small{192*(1usize<<(n-shift-2))*(1usize<<(n-2))*2*3*8}else{8192};
        assert_eq!(cases%64,0);let mut fixed=Fixed;let mut sim=Simulator::new(p.nq,0,&mut fixed);let mut seed=0xd794fa01d37ac329u64^n as u64^((shift as u64)<<32);
        for first in (0..cases).step_by(64){
            let mut before=vec![0u64;p.nq];let mut after=before.clone();
            for l in 0..64{lane(&p,n,shift,first+l,small,&codes,&mut seed,&mut before,&mut after,l);}
            sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(p.ops.iter());
            assert_eq!(sim.qubits,after,"fused low forward n={n} shift={shift} first={first}");assert_eq!(sim.phase,0);
            // A coherent consumer changes one dirty rail by the decoded output
            // decision. The literal inverse must retain precisely that effect.
            let effect=sim.qubits[p.decision];sim.qubits[p.dirty[0]]^=effect;before[p.dirty[0]]^=effect;
            sim.apply_iter(p.ops.iter().rev());assert_eq!(sim.qubits,before,"literal inverse/dirty consumer n={n} shift={shift} first={first}");assert_eq!(sim.phase,0);
        }
        assert_eq!(sim.stats.toffoli_gates,2*cases as u64*p.t as u64);
        eprintln!("Q794_R01_FUSED_LOW_CASE_PASS n={n} shift={shift} lanes={cases} Q={} ops={} forwardT={} allocations=0",p.nq,p.ops.len(),p.t);
        (cases,format!("{{\"n\":{n},\"shift\":{shift},\"lanes\":{cases},\"all_valid_chart_and_high_inputs\":{small},\"all_three_dirty_bits\":{small},\"g0_arbitrary_HA\":true,\"physical_interface_q\":{},\"forward_ccx\":{},\"ops\":{},\"extra_allocations\":0}}",p.nq,p.t,p.ops.len()))
    }
    pub(super) fn run(){
        let mut total=0;let mut rows=Vec::new();
        for n in [3,4,5,6,256]{for shift in 0..=2{if n<shift+2{continue;}let(count,row)=check(n,shift);total+=count;rows.push(row);}}
        println!("{{\"kind\":\"native fused R01 low-chart primitive\",\"lanes\":{total},\"results\":[{}],\"production_cargo_integrated\":false,\"whole_q794_proven\":false}}",rows.join(","));
        eprintln!("Q794_R01_FUSED_LOW_PASS lanes={total}; seeded existingHA, virtual low2, physical high ripple, h-to-decision, qpre update, allphase/dirty/literalinverse; NOT cargo or wholeQ794");
    }
}
