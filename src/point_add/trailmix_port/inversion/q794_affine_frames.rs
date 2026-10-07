//! Closed CNOT frames for exact endpoint transpositions, including offguard.
//! No allocation, no persistent encoding change, no data-word access.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

pub(super) fn swap(circ:&mut Circuit,word:&[&QReg],guard:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],left:usize,right:usize,scratch:Option<&[QReg]>) {
    let width=word.len();assert!((2..=7).contains(&width));assert!(left<1usize<<width&&right<1usize<<width&&left!=right);
    if let Some(s)=scratch{assert!(extras.is_empty());assert_eq!(s.len(),4);}
    let needed=if scratch.is_some(){usize::from(width==7)}else{width+extras.len()-2};assert!(helpers.len()>=needed);
    let mut live:Vec<_>=word.iter().map(|q|q.id()).collect();live.push(guard.id());live.extend(extras.iter().map(|(q,_)|q.id()));if let Some(s)=scratch{live.extend(s.iter().map(QReg::id));}
    let mut unique=live.clone();unique.sort_unstable();unique.dedup();assert_eq!(unique.len(),live.len(),"affine live alias");
    let mut used:Vec<_>=helpers[..needed].iter().map(QReg::id).collect();assert!(used.iter().all(|id|!live.contains(id)),"affine lender alias");used.sort_unstable();used.dedup();assert_eq!(used.len(),needed);
    let diff=left^right;let pivot=diff.trailing_zeros()as usize;let targets:Vec<_>=(0..width).filter(|&i|i!=pivot&&diff>>i&1!=0).collect();let mut value=left;
    for &i in &targets{circ.cx(word[pivot],word[i]);if left>>pivot&1!=0{value^=1<<i;}}
    let controls:Vec<_>=(0..width).filter(|&i|i!=pivot).map(|i|(word[i],value>>i&1!=0)).collect();
    if let Some(s)=scratch{super::metadata_transfer5_compact::exit_guarded_toggle(circ,guard,&controls,word[pivot],s,helpers);}
    else{let mut all=vec![(guard,true)];all.extend_from_slice(extras);all.extend(controls);mixed_mcx(circ,&all,word[pivot],helpers);}
    for &i in targets.iter().rev(){circ.cx(word[pivot],word[i]);}
}

pub(super) fn counter_swap(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],left:usize,right:usize){
    if super::metadata_muxlease::active("Q794_COUNTER_AFFINE"){swap(circ,&rank.iter().collect::<Vec<_>>(),guard,extras,helpers,left,right,None);}
    else{super::metadata_rank5::basis_swap(circ,rank,guard,extras,helpers,left,right);}
}

/// Actual emitted full-wire tests, including all dirty and offguard scratch
/// charts for boundaries. This does not build or allocate whole-circuit ops.
pub fn run(){
    use crate::circuit::OperationType;use crate::sim::Simulator;use sha3::digest::XofReader;
    #[path="metadata_transfer5_compact_programs.rs"] mod maps;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    let mut total=0usize;
    for width in [5usize,7]{for exit in [false,true]{
        let swaps=if width==5{maps::UNPACK_SWAPS}else{maps::PACK_SWAPS};let map=if width==5{maps::UNPACK_MAP}else{maps::PACK_MAP};
        for affine in [false,true]{
            let mut circ=Circuit::new();let word=circ.alloc_qreg_bits("word",width);let g=circ.alloc_qreg("guard");let scratch=circ.alloc_qreg_bits("S",4);let helpers=circ.alloc_qreg_bits("dirty",5);let owned=circ.b.next_qubit;let refs:Vec<_>=word.iter().collect();
            for &(left,right) in swaps{
                if affine{swap(&mut circ,&refs,&g,&[],&helpers,left,right,if exit{Some(&scratch)}else{None});}
                else{
                    let mut value=left;let mut edges=Vec::new();for bit in 0..width{if(left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
                    for(bit,value)in edges{let cs:Vec<_>=(0..width).filter(|&i|i!=bit).map(|i|(&word[i],value>>i&1!=0)).collect();if exit{super::metadata_transfer5_compact::exit_guarded_toggle(&mut circ,&g,&cs,&word[bit],&scratch,&helpers);}else{let mut all=vec![(&g,true)];all.extend(cs);mixed_mcx(&mut circ,&all,&word[bit],&helpers);}}
                }
            }
            assert_eq!(circ.b.next_qubit,owned);let mut b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}let raw=b.ops.clone();
            super::shared_optimize::cancel_nct(&mut b.ops,256,8);super::shared_optimize::cancel_nct_live(&mut b.ops,256);
            eprintln!("Q794_AFFINE_BOUNDARY_BUILT width={width} exit={exit} affine={affine} raw_T={} raw_ops={} T={} ops={}",raw.iter().filter(|o|o.kind==OperationType::CCX).count(),raw.len(),b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
            let cases=(1usize<<width)*32*if exit{17}else{2};
            for ops in [&raw,&b.ops]{for batch in 0..cases.div_ceil(64){let mut before=vec![0u64;owned as usize];let mut expected=before.clone();
                for lane in 0..64{let k=(batch*64+lane)%cases;let value=k&((1<<width)-1);let dirty=k>>width&31;let chart=k>>(width+5);let on=if exit{chart==16}else{chart==1};let sc=if exit{if on{0}else{chart}}else{(value^dirty)&15};let want=if on{map[value]}else{value};
                    for i in 0..width{before[word[i].id()as usize]|=u64::from(value>>i&1!=0)<<lane;expected[word[i].id()as usize]|=u64::from(want>>i&1!=0)<<lane;}
                    for w in [&mut before,&mut expected]{w[g.id()as usize]|=u64::from(on)<<lane;for i in 0..4{w[scratch[i].id()as usize]|=u64::from(sc>>i&1!=0)<<lane;}for i in 0..5{w[helpers[i].id()as usize]|=u64::from(dirty>>i&1!=0)<<lane;}}
                }
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            }}
        }
    }}
    eprintln!("Q794_AFFINE_BOUNDARY_PASS states={total}; old/new raw/cancelled total maps; all dirty and offguard scratch; inverse/phase/noallocation");
}
