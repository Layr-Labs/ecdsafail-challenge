//! Direct twenty-wire C/S counter composition. Own component, not wholeQ792.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::q792_counter_sign_loan_r02::mixed_mcx;
#[path="q792_fold20_counter_plan_r02.rs"]mod plan;
#[path="q794_counter_reflection.rs"]mod phase_reflection;
fn exchange(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],x:usize,y:usize,free:usize){
    let delta=x^y;let fixed=((1usize<<20)-1)^free;let pivot=(delta&fixed).trailing_zeros()as usize;assert!(pivot<20);
    let base=if x>>pivot&1==0{x}else{y};
    for i in 0..20{if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
    let mut cs=prefix.to_vec();cs.extend((0..20).filter(|&i|i!=pivot&&fixed>>i&1!=0).map(|i|(&m[i],base>>i&1!=0)));mixed_mcx(c,&cs,&m[pivot],dirty);
    for i in (0..20).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
}
// Equal affine transpositions on disjoint coarse-code cylinders commute.
// Share their linear conjugation and synthesize the exact union predicate.
fn exchange_group(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],group:&[(usize,usize,usize)]){
    if group.len()==1{let(x,y,free)=group[0];exchange(c,m,prefix,dirty,x,y,free);return;}
    let(x,y,free)=group[0];let fixed=((1usize<<20)-1)^free;let delta=x^y;let pivot=(delta&fixed).trailing_zeros()as usize;let mut bases=Vec::new();
    for &(x,y,f)in group{assert_eq!(f,free);assert_eq!(x^y,delta);let base=if x>>pivot&1==0{x}else{y};assert!(!bases.iter().any(|b|b&fixed==base&fixed));bases.push(base);}
    let varying=bases.iter().fold(0usize,|v,b|v|(b^bases[0]))&fixed;let positions:Vec<_>=(0..20).filter(|&i|varying>>i&1!=0).collect();
    if positions.len()>6{for &(x,y,f)in group{exchange(c,m,prefix,dirty,x,y,f);}return;}
    let mut truth=vec![false;1<<positions.len()];for b in &bases{let code=positions.iter().enumerate().fold(0usize,|v,(i,p)|v|((b>>p&1)<<i));assert!(!truth[code]);truth[code]=true;}
    for i in 0..20{if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
    let mut cs=prefix.to_vec();cs.extend((0..20).filter(|&i|i!=pivot&&(fixed^varying)>>i&1!=0).map(|i|(&m[i],bases[0]>>i&1!=0)));
    super::q792_counter_sign_loan_r02::table(c,&positions.iter().map(|&i|&m[i]).collect::<Vec<_>>(),truth,&cs,&m[pivot],dirty);
    for i in (0..20).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
}
fn branch(c:&mut Circuit,m:&[QReg],target:usize,forced:usize,d:&QReg,dirty:&[QReg]){
    let positions=[8usize,9,14,15,18,19];let live:Vec<_>=positions.iter().copied().filter(|&p|p!=target).collect();
    let mut truth=Vec::new();for code in 0..1usize<<live.len(){let mut value=0usize;for (i,&p)in positions.iter().enumerate(){let bit=if p==target{forced}else{code>>live.iter().position(|&x|x==p).unwrap()&1};value|=bit<<i;}truth.push((value&3)+(value>>2&3)+(value>>4&3)>=5);}
    super::q792_counter_sign_loan_r02::table(c,&live.iter().map(|&p|&m[p]).collect::<Vec<_>>(),truth,&[],d,dirty);
}
fn atomic(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],field:usize,bit:usize,c0:Option<usize>){
    let offset=if field==0{10}else{16};let target=offset+bit;let mut base=prefix.to_vec();base.extend((0..bit).map(|i|(&m[offset+i],false)));if let Some(v)=c0{base.push((&m[10],v!=0));}
    mixed_mcx(c,&base,&m[target],dirty);
    let mut terminal=base.clone();terminal.extend(m[..4].iter().map(|q|(q,true)));terminal.push((&m[5],true));mixed_mcx(c,&terminal,&m[target],dirty);
    if bit==0&&c0.is_none(){return;}
    let d=&dirty[0];let rest=&dirty[1..];let tag:Vec<_>=m[..4].iter().collect();
    // Away from the six side-test coordinates, both target cofactors are B.
    // C0 and C1 are complete XORs into the same target with restored lenders.
    // Replace C0 B C0 B C1 B C1 B by C0 C1 B C0 C1 B; never cross a bit update.
    if ![8usize,9,14,15,18,19].contains(&target){
        for _ in 0..2{
            for reflected in [false,true]{
                let mut controls=prefix.to_vec();controls.push((d,true));controls.extend((0..bit).map(|i|(&m[offset+i],reflected)));if let Some(v)=c0{controls.push((&m[10],(v!=0)^reflected));}
                super::q792_counter_sign_loan_r02::table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&controls,&m[target],rest);
            }
            branch(c,m,target,0,d,rest);
        }
        return;
    }
    // The normal branch uses the maximum target cofactor, the reflected
    // branch the minimum. Admitted flips have both endpoints in the same
    // half. False carry cases remain false even beside the unused gap.
    for reflected in [false,true]{
        let mut controls=prefix.to_vec();controls.push((d,true));controls.extend((0..bit).map(|i|(&m[offset+i],reflected)));if let Some(v)=c0{controls.push((&m[10],(v!=0)^reflected));}
        let consume=|c:&mut Circuit|super::q792_counter_sign_loan_r02::table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&controls,&m[target],rest);
        consume(c);branch(c,m,target,usize::from(!reflected),d,rest);consume(c);branch(c,m,target,usize::from(!reflected),d,rest);
    }
}
// The side-test coordinates do not change through C's low four bits or S's
// low two bits. Conjugate the complete low-word increment by their reflected
// chart, with both selector lenders arbitrary and literally restored. The S
// conditional C0 control belongs to the same reflected frame, so normalize it
// alongside the S low word. No coarse-code or terminal-domain assumption.
fn low_word(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],field:usize,c0:Option<usize>){
    let offset=if field==0{10}else{16};let low=if field==0{4}else{2};
    let d=&dirty[0];let e=&dirty[1];let rest=&dirty[2..];let held_rest=&dirty[1..];
    let normalize=|c:&mut Circuit|{
        let mut cs=prefix.to_vec();cs.push((d,true));
        for bit in 0..low{mixed_mcx(c,&cs,&m[offset+bit],held_rest);}
        if c0.is_some(){mixed_mcx(c,&cs,&m[10],held_rest);}
    };
    normalize(c);
    let flag_at=c.b.ops.len();let tag:Vec<_>=m[..4].iter().collect();
    // ABAB removes e's unknown value: d ^= e*tag; e ^= B; repeat.
    for _ in 0..2{
        super::q792_counter_sign_loan_r02::table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[(e,true)],d,rest);
        branch(c,m,offset,0,e,rest);
    }
    let flag=c.b.ops[flag_at..].to_vec();
    normalize(c);
    for bit in 0..low{
        let mut base=prefix.to_vec();base.extend((0..bit).map(|i|(&m[offset+i],false)));if let Some(v)=c0{base.push((&m[10],v!=0));}
        mixed_mcx(c,&base,&m[offset+bit],held_rest);
        let mut terminal=base;terminal.extend(m[..4].iter().map(|q|(q,true)));terminal.push((&m[5],true));
        mixed_mcx(c,&terminal,&m[offset+bit],held_rest);
    }
    normalize(c);c.b.ops.extend(flag.into_iter().rev());normalize(c);
}
fn word(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],field:usize,c0:Option<usize>,subtract:bool){
    let at=c.b.ops.len();let n=if field==0{6}else{4};
    low_word(c,m,prefix,dirty,field,c0);
    for bit in (if field==0{4}else{2})..n{atomic(c,m,prefix,dirty,field,bit,c0);}
    let hi=if field==0{0}else{1+c0.map(|x|x+1).unwrap_or(0)};
    let high=plan::HIGHS[hi];let mut start=0;while start<high.len(){let mut end=start+1;while end<high.len()&&high[end].2==high[start].2&&(high[end].0^high[end].1)==(high[start].0^high[start].1){end+=1;}exchange_group(c,m,prefix,dirty,&high[start..end]);start=end;}
    if subtract{c.b.ops[at..].reverse();}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,dirty:&[QReg],j:usize){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20&&j<4);let n=c.b.next_qubit;let at=c.b.ops.len();
    if j==3{word(c,m,&[(p1,false),(p2,false)],dirty,1,None,false);}
    if j%2==0{word(c,m,&[(p1,false),(p2,true)],dirty,1,Some(j/2),true);}
    word(c,m,&[(p1,false),(p2,true)],dirty,0,None,false);
    word(c,m,&[(p1,true),(p2,false)],dirty,0,None,true);
    if j%2==1{word(c,m,&[(p1,true),(p2,false)],dirty,1,Some(usize::from(j==1)),false);}
    if j==0{word(c,m,&[(p1,true),(p2,true)],dirty,1,None,true);}
    // Simultaneous modulo wraps cannot be decomposed through the simplex:
    // phase10 at j1: (C,S)=(0,255)->(255,0); phase01 at j2 is inverse.
    // Endpoint admissibility gives A<=2. Repair this COMPLETE scalar domain,
    // independent of EEA input points, test vectors and schedule sampling.
    if j==1||j==2{
        use crate::circuit::{OperationType as K,NO_QUBIT};
        use super::q792_fold20_rank_r01 as codec;
        let ts=codec::triples();let phase=if j==1{2}else{1};
        let (old_c,old_s,new_c,new_s)=if j==1{(0,255,255,0)}else{(255,0,0,255)};
        for a in 0..=2{
            let old_r=ts.iter().position(|t|*t==[0,old_c>>6,old_s>>6]).unwrap();
            let new_r=ts.iter().position(|t|*t==[0,new_c>>6,new_s>>6]).unwrap();
            let before=codec::encode(old_r,a,old_c&63,old_s>>2&15,&ts);
            let expected=codec::encode(new_r,a,new_c&63,new_s>>2&15,&ts);
            let mut bits=vec![false;n as usize];for i in 0..20{bits[m[i].id()as usize]=before>>i&1!=0;}
            bits[p1.id()as usize]=phase&2!=0;bits[p2.id()as usize]=phase&1!=0;
            for op in &c.b.ops[at..]{let target=op.q_target.0 as usize;assert_ne!(op.q_target,NO_QUBIT);match op.kind{K::X=>bits[target]^=true,K::CX=>bits[target]^=bits[op.q_control1.0 as usize],K::CCX=>bits[target]^=bits[op.q_control1.0 as usize]&bits[op.q_control2.0 as usize],_=>panic!("counter primitive type")}}
            assert!(dirty.iter().all(|q|!bits[q.id()as usize]));assert_eq!(bits[p1.id()as usize],phase&2!=0);assert_eq!(bits[p2.id()as usize],phase&1!=0);
            let got=(0..20).fold(0usize,|v,i|v|usize::from(bits[m[i].id()as usize])<<i);
            if got!=expected{exchange(c,m,&[(p1,phase&2!=0),(p2,phase&1!=0)],dirty,got,expected,0);}
        }
    }
    assert_eq!(n,c.b.next_qubit);
}
fn canonical_small(c:&mut Circuit,word:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],subtract:bool){
    for k in 0..word.len(){let bit=if subtract{k}else{word.len()-1-k};let mut cs=prefix.to_vec();cs.extend(word[..bit].iter().map(|q|(q,true)));super::length_recompute::mixed_mcx(c,&cs,&word[bit],dirty);}
}
fn canonical_high(c:&mut Circuit,rank:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],axis:usize,subtract:bool){
    let at=c.b.ops.len();let d=&dirty[0];let rest=&dirty[1..];
    // A complete rank rotation is R1 R0. Each rank reflection is an exact
    // involution, permitting this fully paid arbitrary-lender commutator.
    for offset in 0..2{
        phase_reflection::emit(c,rank,d,rest,axis,offset);
        super::length_recompute::mixed_mcx(c,prefix,d,rest);
        phase_reflection::emit(c,rank,d,rest,axis,offset);
        super::length_recompute::mixed_mcx(c,prefix,d,rest);
    }
    if subtract{c.b.ops[at..].reverse();}
}
fn canonical_pair(c:&mut Circuit,m:&[QReg],rank:&[QReg],guard:&QReg,sign:&QReg,dirty:&[QReg],j:usize){
    let cl=&m[10..16];let sm=&m[16..20];let even=j%2==0;
    let prefix=[(guard,true),(sign,false)];
    // Resolve implicit S1 from OLD C0. On odd clocks the retained physical
    // implementation tests POST-decrement C0, hence the complemented literal.
    let needed_c0=if even{j/2!=0}else{j==3};
    let mut scarry=prefix.to_vec();scarry.extend(sm.iter().map(|q|(q,!even)));scarry.push((&cl[0],needed_c0));
    let mut ccarry=prefix.to_vec();ccarry.extend(cl.iter().map(|q|(q,even)));
    if even{canonical_high(c,rank,&scarry,dirty,2,true);canonical_high(c,rank,&ccarry,dirty,1,false);}
    else{canonical_high(c,rank,&ccarry,dirty,1,true);canonical_high(c,rank,&scarry,dirty,2,false);}
    // Exact simultaneous modulo wrap, before either low word changes.
    if j==1||j==2{
        let mut both=ccarry;both.extend(sm.iter().map(|q|(q,!even)));
        let(left,right)=if even{(1,3)}else{(4,11)};
        super::metadata_rank5::affine_transposition(c,rank,&both,dirty,left,right);
    }
    let scontrol=[(guard,true),(sign,false),(&cl[0],needed_c0)];
    canonical_small(c,sm,&scontrol,dirty,even);
    canonical_small(c,cl,&prefix,dirty,!even);
    // The same even-clock chart also covers phase11. Its sole S-mid borrow
    // is clock0; no C motion occurs in that phase.
    if j==0{
        let mut carry=vec![(guard,true),(sign,true)];carry.extend(sm.iter().map(|q|(q,false)));
        canonical_high(c,rank,&carry,dirty,2,true);
        canonical_small(c,sm,&[(guard,true),(sign,true)],dirty,true);
    }
}
fn phase_chart(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,dirty:&[QReg],j:usize){
    let(guard,lease)=if j%2==0{(p2,p1)}else{(p1,p2)};
    // Sign=P1*P2 on every nonzero phase. Under guard, lease XOR Sign=0;
    // on guard0 Sign is arbitrary and the entire chart is literally returned.
    c.cx(sign,lease);
    super::q792_unfold_lease_r01::emit(c,m,lease,guard,dirty,false);
    let rank:Vec<_>=m[..4].iter().chain(std::iter::once(lease)).map(QReg::borrowed_alias).collect();
    canonical_pair(c,m,&rank,guard,sign,dirty,j);
    super::q792_unfold_lease_r01::emit(c,m,lease,guard,dirty,true);
    c.cx(sign,lease);
}
pub(super) fn emit_with_phase_lease(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,dirty:&[QReg],j:usize){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20&&j<4);let n=c.b.next_qubit;
    let chart=|c:&mut Circuit|{
        // The caller owns the original Sign=P1*P2 shortcut scope. Suspend it
        // throughout the leased phase coordinate; that relation is temporarily
        // false on original phase11. Reinstall only after full fold and return.
        super::q792_counter_sign_loan_r02::end();
        phase_chart(c,m,p1,p2,sign,dirty,j);
        super::q792_counter_sign_loan_r02::begin(c,p1,p2,sign);
    };
    if j==3{word(c,m,&[(p1,false),(p2,false)],dirty,1,None,false);}
    if j%2==0{
        chart(c);
        word(c,m,&[(p1,true),(p2,false)],dirty,0,None,true);
    }else{
        word(c,m,&[(p1,false),(p2,true)],dirty,0,None,false);
        chart(c);
    }
    assert_eq!(n,c.b.next_qubit);
}
fn check_phase_chart_offguard(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut total=0;
    for j in [0usize,1]{
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
        let m=c.alloc_qreg_bits("metadata",20);let p1=c.alloc_qreg("p1");let p2=c.alloc_qreg("p2");let sign=c.alloc_qreg("Sign");let dirty=c.alloc_qreg_bits("arbitrary_lenders",20);let n=c.b.next_qubit;
        phase_chart(&mut c,&m,&p1,&p2,&sign,&dirty,j);let ops=c.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let(guard,lease)=if j==0{(&p2,&p1)}else{(&p1,&p2)};
        for pattern in 0..4{for first in (0..1usize<<20).step_by(64){
            let mut seed=0x7925_21ca_7af0u64^(first as u64)^((j as u64)<<40)^((pattern as u64)<<32);
            let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
            for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0u64,|v,l|v|((((first+l)>>bit&1)as u64)<<l));}
            before[guard.id()as usize]=0;before[lease.id()as usize]=if pattern&1!=0{u64::MAX}else{0};before[sign.id()as usize]=if pattern&2!=0{u64::MAX}else{0};
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,before,"phase chart offguard j={j} first={first} pattern={pattern}");assert_eq!(sim.phase,0);
            sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }
    eprintln!("FOLD20_SHARED_COUNTER_CHART_OFFGUARD_PASS lanes={total} all_physical_metadata=true arbitrary_Sign_and_phase_lease=true literal_inverse=true");
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    use super::q792_fold20_rank_r01 as codec;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    check_phase_chart_offguard();let ts=codec::triples();let mut total=0u64;let mut active=0u64;
    for j in 0..4{
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
        let m=circ.alloc_qreg_bits("fold20.metadata",20);let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let sign=circ.alloc_qreg("existing.counter.Sign");let dirty=circ.alloc_qreg_bits("arbitrary_lenders",20);let n=circ.b.next_qubit;
        super::q792_counter_sign_loan_r02::begin(&mut circ,&p1,&p2,&sign);
        emit_with_phase_lease(&mut circ,&m,&p1,&p2,&sign,&dirty,j);
        super::q792_counter_sign_loan_r02::end();
        let ops=circ.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        eprintln!("FOLD20_COUNTER_R02_BUILT j={j} metadata=20 scratch_allocated=0 shared_phase_chart=true ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
        for phase in 0..4{
            let mut cases=Vec::new();
            for code in 0..1usize<<20{
                if let Some((r,a,cl,sm))=codec::decode(code,&ts){
                    let av=64*ts[r][0]+a;let cv=64*ts[r][1]+cl;
                    let base=if phase<2{j}else{(4-j)%4};let s1=(base/2)^if [1,2].contains(&phase){cv&1}else{0};
                    let sv=64*ts[r][2]+4*sm+2*s1+(j&1);
                    let cn=if phase==1{(cv+1)&255}else if phase==2{(cv+255)&255}else{cv};
                    let sn=if phase==0||phase==2{(sv+1)&255}else{(sv+255)&255};
                    if av+cv+sv>257||av+cn+sn>257{continue;}
                    let nr=ts.iter().position(|t|*t==[av>>6,cn>>6,sn>>6]).unwrap();
                    let next=codec::encode(nr,a,cn&63,sn>>2&15,&ts);
                    assert_eq!(codec::encode(r,a,cl,sm,&ts),code);cases.push((code,next));
                }
            }
            for pattern in 0..2{for first in (0..cases.len()).step_by(64){
                let mut seed=0x7925_c7af_9971u64^(first as u64)^((phase as u64)<<40)^((j as u64)<<44)^((pattern as u64)<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
                for w in [&mut before,&mut after]{w[p1.id()as usize]=if phase&2!=0{u64::MAX}else{0};w[p2.id()as usize]=if phase&1!=0{u64::MAX}else{0};if phase!=0{w[sign.id()as usize]=if phase==3{u64::MAX}else{0};}}
                for lane in 0..64{let(code,next)=cases[(first+lane)%cases.len()];for bit in 0..20{for(w,value)in[(&mut before,code),(&mut after,next)]{let mask=1u64<<lane;w[m[bit].id()as usize]=(w[m[bit].id()as usize]&!mask)|(((value>>bit&1)as u64)<<lane);}}}
                let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());
                if sim.qubits!=after{let differences=sim.qubits.iter().zip(&after).fold(0u64,|mask,(x,y)|mask|(x^y));let lane=differences.trailing_zeros()as usize;let (input,expected)=cases[(first+lane)%cases.len()];let got=(0..20).fold(0usize,|v,i|v|(((sim.qubits[m[i].id()as usize]>>lane)&1)as usize)<<i);panic!("counter j={j} phase={phase} input={input} expected={expected} got={got} decoded={:?} expected_decoded={:?} actual_decoded={:?}",codec::decode(input,&ts),codec::decode(expected,&ts),codec::decode(got,&ts));}
                assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;active+=64;
            }}
            eprintln!("FOLD20_COUNTER_R02_CLASS_PASS j={j} phase={phase} cases={}",cases.len());
        }
    }
    eprintln!("FOLD20_COUNTER_R02_NATIVE_PASS metadata=20 lanes={total} active={active} scratch_allocated=0 whole_Q792=false");
}
