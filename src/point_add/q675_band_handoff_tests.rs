//! Coherent five-slot transport only: quotient search/repayment is not implemented.
use super::builder::{B,G};
use super::frogdrop_col::{Fd,ColScr};
use crate::circuit::{QubitId,OperationType};
pub(crate) use super::q675_support::{CUTS,park};
fn bit(q:&mut[u64],id:QubitId,lane:usize,v:bool){if v{q[id.0 as usize]|=1<<lane;}}
#[test]
fn q675_five_band_handoff_all_channels(){
    super::bake_knobs();let(mut count,mut negative)=(0usize,0usize);
    for parity in 0..2 {for fam in 0..5 {
        let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
        if parity!=0{std::mem::swap(&mut fd.sy,&mut fd.sx);}
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        b.begin();park(&mut b,&fd,&sc,fam);let r=b.end();b.play(&r,false);let off=b.ops.len();let t=b.tof;b.play(&r,true);
        assert!(b.ops.iter().all(|o|matches!(o.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
        let cases:Vec<_>=(1..=128).flat_map(|sy|{let len=CUTS[sy-1][fam+1]-CUTS[sy-1][fam];(0..1usize<<len).map(move|v|(sy,len,v))}).collect();
        for batch in cases.chunks(64){for mask in [u64::MAX,0,0x5555555555555555]{for noise in 0..2 {
            let mut q=vec![0u64;675];q[sc.g.0 as usize]=mask;
            for(i,&d)in dirty.iter().enumerate(){q[d.0 as usize]=if noise==0{0}else{0x9e3779b97f4a7c15u64.rotate_left(i as u32)};}
            for(lane,&(sy,len,v))in batch.iter().enumerate(){
                for i in 0..8{bit(&mut q,fd.sy[i],lane,sy>>i&1!=0);}
                for i in 0..sy{bit(&mut q,fd.q[i],lane,i==sy-1||(i*13+lane*7)%3==0);}
                for i in 0..len{bit(&mut q,fd.sx[1+i],lane,v>>i&1!=0);}
            }
            let mut want=q.clone();
            for(lane,&(sy,len,_))in batch.iter().enumerate(){if mask>>lane&1==0{continue;}
                for i in 0..len{let a=fd.sx[1+i];let z=if sy+i<128{fd.q[sy+i]}else{sc.bq};let v=((want[a.0 as usize]^want[z.0 as usize])>>lane)&1;want[a.0 as usize]^=v<<lane;want[z.0 as usize]^=v<<lane;}
            }
            let f=super::tests_frogdrop::run(&b.ops[..off],675,&|x|*x=q.clone());assert_eq!(f.q,want);assert_eq!(f.phase,0);
            let rt=super::tests_frogdrop::run(&b.ops,675,&|x|*x=q.clone());assert_eq!(rt.q,q);assert_eq!(rt.phase,0);
            if mask==u64::MAX&&noise==1{for lane in 0..batch.len(){if fd.sx[1..6].iter().any(|a|((want[a.0 as usize]^q[a.0 as usize])>>lane)&1!=0){negative+=1;}}}
            count+=batch.len();
        }}}
        eprintln!("Q675_HANDOFF family={fam} parity={parity} forward_ops={off} T={t} actual_fixture_Q=675 cases={}",cases.len());
    }}
    assert!(negative>0);eprintln!("Q675_HANDOFF_PASS lanes={count} omitted_inverse_detected={negative} phase=0 dirty=restored absent_slots_supported_by_zero=conditional arithmetic_search=unimplemented");
}
