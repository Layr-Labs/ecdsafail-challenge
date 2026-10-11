use super::{builder::B,arith::{up_m,down_m,Dm},mask::{Dec,mc_xor}};
use crate::circuit::QubitId;
// Caller contract: active implies C>0, headers give original positive C/Y
// widths <=m, physical C above its header is0, and Y's low header prefix is
// the remainder. Higher Y lanes are arbitrary foreign data. Quotient fits q.
// Inactive permits arbitrary source/target/header values, with zero outputs.
// All target/source/header/output/work roles are disjoint. work >=20 isGLOBAL0.
pub fn divmod(b:&mut B,y:&[QubitId],c:&[QubitId],hy:&[QubitId],hc:&[QubitId],q:&[QubitId],active:QubitId,work:&[QubitId]){
 assert_eq!(y.len(),c.len());assert_eq!(hy.len(),8);assert_eq!(hc.len(),8);assert!(work.len()>=20&&q.len()<=y.len());
 let mut seen=std::collections::BTreeSet::new();for w in y.iter().chain(c).chain(hy).chain(hc).chain(q).chain(&work[..20]).chain(std::iter::once(&active)){assert!(seen.insert(w.0));}
 let(c0,one,ge,valid,tmp)=(work[0],work[1],work[2],work[3],work[4]);let pre=&work[5..12];let constanc=&work[12..19];
 for j in(0..q.len()).rev(){
  // Headers are immutable metadata of ORIGINAL Y and C through all rounds.
  b.begin();super::frogdrop::reg_add_const(b,hc,j as i64,one,constanc);let add=b.end();
  b.begin();b.play(&add,false);let up=up_m(b,hy,hc,c0,true);b.play(&up,false);b.x(hc[7]);b.cx(hc[7],ge);b.x(hc[7]);b.play(&up,true);b.play(&add,true);let predicate=b.end();
  b.play(&predicate,false);b.and_c(active,ge,valid);
  let up=up_m(b,&y[j..],&c[..y.len()-j],c0,true);let down=down_m(b,&y[j..],&c[..y.len()-j],c0,Dm::Cond(q[j]),true);b.play(&up,false);
  // Stored source at k−1 is c_k XOR original C_k. Under valid, C_k=0
  // at k=header(Y)−j, so it is the exact prefix borrow even with dirty tail.
  // Active care licenses hy<=m; low header bits are complete there.
  // valid is a held top decoder bit, so every boundary summary is0 on
  // arbitrary inactive headers and needs only one final CCX with carry.
  let hb=(usize::BITS-y.len().leading_zeros())as usize;
  let mut bounded_header=hy[..hb].to_vec();bounded_header.push(valid);
  let mut dec=Dec::new(&bounded_header,pre);for i in 0..y.len()-j{let mut lits=dec.ctrls(b,(1usize<<hb)|(i+j+1));lits.push((c[i],true));mc_xor(b,&lits,q[j],&[],&[]);}dec.clear(b);
  b.play(&down,false);b.and_u(active,ge,valid);b.play(&predicate,true);
 }
}


