//! Low seed shares paid singleton selectors and factors exact data ANFs.
//! R02 adds A253/shift2 cargo correction. t>=2^253, r<8 and 2v<=r imply v2=0.
//! R00 low3 reader in the post-pre-rotation production physical frame.
//! Required contract supplied by the root boundary/cargo audit; no allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::paired_clean_mcx;

fn gate(circ:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg,scratch:&QReg) {
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v)in controls{assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){
            if old!=v{return;}
        }else{unique.push((q,v));}
    }paired_clean_mcx::toggle(circ,&unique,out,scratch);
}

// Paid reversible linear chart frames factor the exact nine-bit ANF.
// The transform substitutes x_t = y_t XOR y_s; Boolean x_s^2 = x_s.
// Each data port and every borrowed helper is returned before class erase.
fn data_polynomial(circ:&mut Circuit,chart:&[&QReg;9],terms:&[usize],base:&QReg,carry:&QReg,scratch:&QReg,j:usize,group:usize){
    let frame:&[(usize,usize)]=match (j,group){
        (0,0)=>&[(7, 1), (7, 5), (6, 3), (6, 7), (2, 5), (0, 2), (6, 8)],
        (0,1)=>&[(7, 1), (7, 5), (6, 3), (6, 7), (2, 5), (0, 2), (6, 8)],
        (0,2)=>&[(0, 3), (7, 5), (1, 4), (0, 1), (7, 4), (1, 4), (2, 5)],
        (0,3)=>&[(0, 2), (1, 4), (4, 7), (0, 3), (7, 4)],
        (0,4)=>&[(7, 4)],
        (0,5)=>&[],
        (1,0)=>&[(1, 4), (2, 8), (7, 1), (7, 2), (0, 2), (6, 5), (1, 4), (1, 8)],
        (1,1)=>&[(1, 4), (2, 8), (7, 1), (7, 2), (0, 2), (6, 5), (1, 4), (1, 8)],
        (1,2)=>&[(0, 1), (4, 7), (0, 7)],
        (1,3)=>&[(0, 2), (0, 3)],
        (1,4)=>&[(4, 1)],
        (1,5)=>&[],
        _=>panic!("invalid low seed group"),
    };
    let mut polynomial=vec![false;512];for &m in terms{polynomial[m&511]^=true;}
    for &(source,target) in frame{
        circ.cx(chart[source],chart[target]);
        let mut next=polynomial.clone();
        for (m,&on) in polynomial.iter().enumerate(){if on&&m>>target&1!=0{
            next[(m&!(1<<target))|(1<<source)]^=true;
        }}polynomial=next;
    }
    for (m,on) in polynomial.into_iter().enumerate(){if on{
        let mut cs=vec![(base,true)];cs.extend((0..9).filter(|&i|m>>i&1!=0).map(|i|(chart[i],true)));
        gate(circ,&cs,carry,scratch);
    }}
    for &(source,target) in frame.iter().rev(){circ.cx(chart[source],chart[target]);}
}

/// Only bit2's active mask can select S0 (j0) or S1 (j1); C=0 then.
/// Other j have no low seed. Thus flag A0/A1/A2 uses exact rank0, and A254
/// uses exact rank3. Those selectors are exact on the required active
/// domain; outside it this is a pure carry-XOR extension undone by W^-1.
///
/// Normalization contract in this R00 internal frame:
/// A0: logical t=1,b=0; A1: t1=1,t2=0; A2: t2=1.
/// A254/shift1: v2=0; A254/shift2: v1=v2=0 (v=1).
/// Raw shortword/cargo bits remain untouched, even when they contain loans.
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],w2:&[QReg],mask:&QReg,carry:&QReg,scratch:&QReg,loan:&QReg,j:usize) {
    assert!(j<4);if j>=2{return;}let shift=j+1;
    assert_eq!(rank.len(),4);assert_eq!(a.len(),6);assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);
    let chart=[&w1[0],&w1[1],&w1[2],
        &w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],
        &w2[258-shift],&w2[257-shift],&w2[256-shift]];
    let mut anf:Vec<_>=(0..16384).map(|z|{
        let mut t=z&7;let mut b=(z>>3)&7;let mut v=(z>>6)&7;
        if z>>9&1!=0{t=1;b=0;}else if z>>10&1!=0{t=(t&1)|2;}else if z>>11&1!=0{t=(t&3)|4;}
        if z>>12&1!=0{v&=if shift==1{3}else{1};}
        if shift==2&&z>>13&1!=0{v&=3;} // A253 second cargo occupies raw v2.
        let r=if t&1!=0{(7usize.wrapping_sub(b*v).wrapping_mul(t))&7}else{b};
        (r>>shift)<(v&((1usize<<(3-shift))-1))
    }).collect();
    for bit in 0..14{for m in 0..16384{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    // Generic polynomial uses the active-clean C3, returning it per term.
    // Each supported singleton correction shares one mask*metadata selector.
    // X(loan) makes the actual R00 guard zero on phase00 while these local
    // maps run. It is returned before any other W cell and before Sign's
    // external center. Off phase all primitives remain target-XOR extensions
    // with every borrowed rail restored, so the literal W inverse closes.
    let generic:Vec<_>=anf.iter().enumerate().filter_map(|(m,&on)|if on&&m>>9==0{Some(m)}else{None}).collect();
    data_polynomial(circ,&chart,&generic,mask,carry,scratch,j,0);
    for f in 0..5{
        let av=[0usize,1,2,254,253][f];
        if circ.q797_a_support.is_some_and(|(lo,hi)|!(lo..hi).contains(&av)){continue;}
        let terms:Vec<_>=anf.iter().enumerate().filter_map(|(m,&on)|if on&&m>>9==1<<f{Some(m)}else{None}).collect();
        if terms.is_empty(){continue;}
        let rv=if f>=3{3}else{0};let mut cs=vec![(mask,true)];
        cs.extend((0..4).map(|i|(&rank[i],rv>>i&1!=0)));
        cs.extend((0..6).map(|i|(&a[i],av>>i&1!=0)));
        circ.x(loan);
        paired_clean_mcx::toggle(circ,&cs,scratch,loan);
        data_polynomial(circ,&chart,&terms,scratch,carry,loan,j,f+1);
        paired_clean_mcx::toggle(circ,&cs,scratch,loan);
        circ.x(loan);
    }
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"dynamic R00 seed touched hole{h}");
    }}
}
