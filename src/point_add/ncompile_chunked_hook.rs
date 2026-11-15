// nasqret's exact record passes (1e9efad8, src/point_add/compile: peephole rounds, measurement-based
// uncompute of provable ANDs, affine Toffoli sharing) applied to a finished op list.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};
#[path = "ncompile_w/optimize.rs"]
mod base;
#[path = "ncompile_w/cleanup.rs"]
mod cleanup;
#[path = "ncompile_w/pass.rs"]
mod pass;
#[path = "ncompile_w/affine.rs"]
mod affine;
fn ob(x: u16) -> BitId { if x == u16::MAX { NO_BIT } else { BitId(x as u64) } }
fn operation([kind, a, b, c]: [u16; 4]) -> Op {
    use OperationType::*;
    let qa = QubitId(a as u64); let qb = QubitId(b as u64);
    let mut op = Op::empty();
    op.kind = match kind {
        1 => { op.r_target = RegisterId(a as u64); Register }
        2 => { op.r_target = RegisterId(a as u64); op.q_target = qb; AppendToRegister }
        18 => { op.r_target = RegisterId(a as u64); op.c_target = BitId(b as u64); AppendToRegister }
        3 | 4 | 5 => { op.c_target = BitId(a as u64); op.c_condition = ob(b); if kind == 3 { BitInvert } else if kind == 4 { BitStore0 } else { BitStore1 } }
        6 | 7 => { op.q_target = qa; op.c_condition = ob(b); if kind == 6 { X } else { Z } }
        8 | 9 => { op.q_control1 = qa; op.q_target = qb; op.c_condition = ob(c); if kind == 8 { CX } else { CZ } }
        12 => { op.q_target = qa; op.c_target = ob(b); Hmr }
        13 => { op.q_control2 = qa; op.q_control1 = qb; op.q_target = QubitId(c as u64); CCX }
        14 => { op.q_control2 = qa; op.q_control1 = qb; op.q_target = QubitId(c as u64); CCZ }
        15 => { op.c_condition = BitId(a as u64); PushCondition }
        16 => PopCondition,
        _ => panic!("ncompile: unsupported record {}", kind),
    };
    op
}
fn row(o: &Op) -> [u16; 4] { row_j(o, 65535) }
fn row_j(o: &Op, junk: u16) -> [u16; 4] {
    use OperationType::*;
    let bit = |x: BitId| if x == NO_BIT { 65535 } else { assert!(x.0 < 65535); x.0 as u16 };
    let q = |x: QubitId| { assert!(x.0 < 65535); x.0 as u16 };
    match o.kind {
        Register => [1, o.r_target.0 as u16, 65535, 65535],
        AppendToRegister => if o.c_target != NO_BIT { [18, o.r_target.0 as u16, bit(o.c_target), 65535] } else { [2, o.r_target.0 as u16, q(o.q_target), 65535] },
        BitInvert => [3, bit(o.c_target), bit(o.c_condition), 65535],
        BitStore0 => [4, bit(o.c_target), bit(o.c_condition), 65535],
        BitStore1 => [5, bit(o.c_target), bit(o.c_condition), 65535],
        X => [6, q(o.q_target), bit(o.c_condition), 65535],
        Z => [7, q(o.q_target), bit(o.c_condition), 65535],
        CX => [8, q(o.q_control1), q(o.q_target), bit(o.c_condition)],
        CZ => [9, q(o.q_control1), q(o.q_target), bit(o.c_condition)],
        Hmr => { assert!(o.c_condition == NO_BIT); [12, q(o.q_target), bit(o.c_target), 65535] }
        CCX => { assert!(o.c_condition == NO_BIT); [13, q(o.q_control2), q(o.q_control1), q(o.q_target)] }
        CCZ => { assert!(o.c_condition == NO_BIT); [14, q(o.q_control2), q(o.q_control1), q(o.q_target)] }
        // Reset is defined as an HMR whose result is ignored: record it into a junk bit nobody reads.
        R => { assert!(o.c_condition == NO_BIT && junk != 65535); [12, q(o.q_target), junk, 65535] }
        PushCondition => [15, bit(o.c_condition), 65535, 65535],
        PopCondition => [16, 65535, 65535, 65535],
        _ => panic!("ncompile: unsupported operation {:?}", o.kind),
    }
}

use std::collections::{HashMap,HashSet};

#[path="rowhunter_rpeephole.rs"] mod first;
struct FirstTape {rows:Vec<[u16;4]>,blocks:Vec<[[u16;4];3]>}
impl first::Rows for FirstTape {
 fn len(&self)->usize{self.rows.len()}
 fn get(&self,i:usize)->[u16;4]{self.rows[i]}
 fn set(&mut self,i:usize,row:[u16;4]){self.rows[i]=row;}
 fn expand(&mut self,i:usize,block:[[u16;4];3]){
  let j=u32::try_from(self.blocks.len()).unwrap();self.blocks.push(block);
  self.rows[i]=[first::BLOCK,j as u16,(j>>16) as u16,65535];
 }
 fn block(&self,i:usize)->[[u16;4];3]{let r=self.rows[i];self.blocks[usize::from(r[1])+(usize::from(r[2])<<16)]}
}
impl FirstTape {
 fn flatten(self)->Vec<[u16;4]>{
  let mut out=Vec::with_capacity(self.rows.len()+self.blocks.len());
  for (i,r) in self.rows.iter().copied().enumerate(){match r[0]{
   first::TOMB=>(),first::BLOCK=>out.extend(<Self as first::Rows>::block(&self,i)),_=>out.push(r),
  }}out
 }
}
fn first_layer(data:Vec<[u16;4]>,entering:usize,leaving:usize)->Vec<[u16;4]>{
 const SYNTHETIC:u16=65534;
 let mut rows=vec![[15,SYNTHETIC,65535,65535];entering];rows.extend(data);
 rows.resize(rows.len()+leaving,[16,65535,65535,65535]);
 for _ in 0..3 {
  let before=rows.len();let mut tape=FirstTape{rows,blocks:Vec::new()};
  first::run(&mut tape,1);let expanded=!tape.blocks.is_empty();rows=tape.flatten();
  if rows.len()==before&&!expanded{break;}
 }
 assert!(rows.iter().take(entering).all(|r|r[0]==15&&r[1]==SYNTHETIC));
 assert!(rows.iter().rev().take(leaving).all(|r|r[0]==16));
 rows.truncate(rows.len()-leaving);rows.drain(..entering);rows
}

const PHASE: u16 = 65531;
const JUNK: u16 = 65532;
const SCRATCH: u16 = 65533;
const LIMIT: usize = PHASE as usize;
struct EncodedChunk { rows: Vec<[u16;4]>, names: Vec<u64>, map: HashMap<u64,u16> }
impl EncodedChunk {
    fn new()->Self {Self {rows:Vec::new(),names:Vec::new(),map:HashMap::new()}}
    fn bit(&mut self,b:BitId)->BitId {
        if b==NO_BIT {return b;}
        let n=self.names.len() as u16;
        let alias=*self.map.entry(b.0).or_insert_with(||{self.names.push(b.0);n});
        BitId(u64::from(alias))
    }
}
fn decode_bit(b:BitId,names:&[u64],private:[u64;3])->BitId {
    if b==NO_BIT {return b;}
    BitId(match b.0 {
        x if x==u64::from(SCRATCH)=>private[0],
        x if x==u64::from(JUNK)=>private[1],
        x if x<u64::from(PHASE)=>names[x as usize],
        _=>panic!("alias compiler: unexpected internal classical operand {}",b.0),
    })
}
fn decode_row(g:[u16;4],names:&[u64],private:[u64;3])->Op {
    if g[0]==3 && g[1]==PHASE {
        let mut o=Op::empty();o.kind=OperationType::Neg;
        o.c_condition=decode_bit(ob(g[2]),names,private);return o;
    }
    let mut o=operation(g);
    o.c_target=decode_bit(o.c_target,names,private);
    o.c_condition=decode_bit(o.c_condition,names,private);
    o
}
pub fn apply(ops:Vec<Op>,width:usize)->Vec<Op>{apply_inner(ops,width,base::CHUNK)}
#[cfg(test)]
pub fn apply_for_probe(ops:Vec<Op>,width:usize,chunk:usize)->Vec<Op>{apply_inner(ops,width,chunk)}
fn apply_inner(ops:Vec<Op>,width:usize,chunk:usize)->Vec<Op>{
    let started=std::time::Instant::now();
    assert!(width<=1536 && chunk>0);
    let mut used=HashSet::new();
    for o in &ops {for b in [o.c_target,o.c_condition] {if b!=NO_BIT {used.insert(b.0);}}}
    let mut free=(0u64..).filter(|b|*b!=u64::MAX && !used.contains(b));
    let private=[free.next().unwrap(),free.next().unwrap(),free.next().unwrap()];
    let mut chunks=Vec::new();let mut current=EncodedChunk::new();
    // Match the existing widened adapter's declaration ordering.
    for declarations in [true,false] {
        for original in &ops {
            use OperationType::*;
            if original.kind==DebugPrint {continue;}
            if matches!(original.kind,Register|AppendToRegister)!=declarations {continue;}
            let need=[original.c_target,original.c_condition].iter().filter(|b|**b!=NO_BIT && !current.map.contains_key(&b.0)).count();
            if !current.rows.is_empty() && (current.rows.len()>=chunk || current.names.len()+need>LIMIT) {
                current.map=HashMap::new();chunks.push(current);current=EncodedChunk::new();
            }
            assert!(original.r_target==crate::circuit::NO_REG || original.r_target.0<u64::from(PHASE));
            let mut o=*original;
            o.c_target=current.bit(o.c_target);o.c_condition=current.bit(o.c_condition);
            if o.kind==Neg {
                current.rows.push([3,PHASE,if o.c_condition==NO_BIT {65535}else{o.c_condition.0 as u16},65535]);
            } else if o.kind==Swap {
                assert!(o.q_control1.0<65531 && o.q_target.0<65531);
                let (a,b)=(o.q_control1.0 as u16,o.q_target.0 as u16);
                let c=if o.c_condition==NO_BIT {65535}else{o.c_condition.0 as u16};
                current.rows.extend([[8,a,b,c],[8,b,a,c],[8,a,b,c]]);
            } else if o.c_condition!=NO_BIT && matches!(o.kind,CCX|CCZ|Hmr|R) {
                let c=o.c_condition.0 as u16;o.c_condition=NO_BIT;
                current.rows.push([15,c,65535,65535]);current.rows.push(row_j(&o,JUNK));current.rows.push([16,65535,65535,65535]);
            } else {current.rows.push(row_j(&o,JUNK));}
        }
    }
    if !current.rows.is_empty(){current.map=HashMap::new();chunks.push(current);}
    let n=ops.len();drop(ops);drop(used);
    let mut out=Vec::with_capacity(n);
    let mut compiler=pass::Pass::new(width,SCRATCH,2);
    let mut aff=affine::Affine::new();
    let mut depth=0usize;let mut completed=0usize;let total=chunks.len();
    eprintln!("NCOMPILE_CHUNKED encoded_chunks={total} encode_s={:.1}",started.elapsed().as_secs_f64());
    for encoded in chunks {
        let leaving=base::stack_after(depth,&encoded.rows);
        let rows=first_layer(encoded.rows,depth,leaving);depth=leaving;
        compiler.chunk(rows,|r|aff.push(r,|g|out.push(decode_row(g,&encoded.names,private))));
        // No encoded classical operand is retained across a change of alias table.
        aff.flush(|g|out.push(decode_row(g,&encoded.names,private)));
        completed+=1;
        if completed%128==0{eprintln!("NCOMPILE_CHUNKED chunks={completed}/{total} elapsed_s={:.1}",started.elapsed().as_secs_f64());}
    }
    compiler.finish();assert_eq!(depth,0);
    eprintln!("NCOMPILE_ALIAS private={private:?} input={n} output={}",out.len());
    out
}
