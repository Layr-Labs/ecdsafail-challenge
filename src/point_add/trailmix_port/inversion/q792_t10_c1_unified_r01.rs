//! Share C1 arithmetic across S<=2 and S>=3. All rank classes use the same body.
//! C3 is zero on the held C1 guard and stores the small-S selector.
//! Off that guard, the codec is an arbitrary U followed by its exact inverse:
//! its q0 is live C0, which changes only inside the guarded arithmetic.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub(super) fn branch(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize){
 let g=&helpers[0];let d=&helpers[1..];let low=&cl[3];
 // C1 fixes low S mod4: j0->2,j1->1,j2->0,j3->3.
 let at=c.b.ops.len();if j!=3{let ts=super::q792_fold20_rank_r01::triples();let cs:Vec<_>=sm.iter().map(|q|(q,false)).collect();super::q792_fold20_r01::table(c,&rank.iter().collect::<Vec<_>>(),ts.iter().map(|t|t[2]==0).collect(),&cs,low,d);}let selector=c.b.ops[at..].to_vec();
 if j!=3{super::q792_t10_c1_codec_r01::flags(c,rank,a,cl,low,&sm[1],&sm[2],d);super::q792_t10_c1_codec_r01::emit(c,rank,a,cl,sm,p1,p2,low,w1,w2,d,j,false,true);}
 let mut source:Vec<_>=w1[..256].iter().map(QReg::borrowed_alias).collect();source.push(sm[3].borrowed_alias());
 let move_g=|c:&mut Circuit|{let(l,ls)=super::q794_handoffs::gather_a(c,rank,a,&source,1,d);let(r,rs)=super::q794_handoffs::gather_a(c,rank,a,w2,2,d);c.cswap(g,l,r);c.b.ops.extend(rs.into_iter().rev());c.b.ops.extend(ls.into_iter().rev());};
 // Original target A+2 funds carry directly; no global passenger relocation.
 super::q792_t10_c1_fused_r01::add_and_clear(c,rank,&source,w2,a,g,&cl[2],&cl[1],&cl[0],d,n,cl,sm,j,true,true);
 // Original target A+2 funds carry directly; no global passenger relocation.
 if j!=3{super::q792_t10_c1_codec_r01::emit(c,rank,a,cl,sm,p1,p2,low,w1,w2,d,j,true,true);super::q792_t10_c1_codec_r01::flags(c,rank,a,cl,low,&sm[1],&sm[2],d);}
 c.cx(g,&cl[0]);c.b.ops.extend(selector.into_iter().rev());
}
