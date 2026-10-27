//! SOURCE-ONLY full boundary exchange using one exact Z-1 byte epoch.
//! All original ring[129..257] / reversed Q lanes and full tails retained.
//! Exactly the existing cut, toggle and prefix owners are used.
use super::builder::{B,G};
use super::mask::mc_xor;
use super::outer_size::Roles;
use super::sum_size::SumSize;
use crate::circuit::QubitId;

struct Prefix<'a>{word:&'a[QubitId],port:QubitId,old:Option<usize>}
impl Prefix<'_>{
    fn cell(&self,b:&mut B,value:usize){
        if value&64==0{b.x(self.word[6]);}if value&32==0{b.x(self.word[5]);}
        b.ccx(self.word[6],self.word[5],self.port);
        if value&32==0{b.x(self.word[5]);}if value&64==0{b.x(self.word[6]);}
    }
    fn controls(&mut self,b:&mut B,value:usize)->Vec<(QubitId,bool)>{
        if self.old.map(|v|v>>5)!=Some(value>>5){
            self.clear(b);self.cell(b,value);self.old=Some(value);
        }
        std::iter::once((self.port,false))
            .chain((0..5).map(|i|(self.word[i],value>>i&1==0))).collect()
    }
    fn clear(&mut self,b:&mut B){if let Some(v)=self.old{self.cell(b,v);}self.old=None;}
}

/// Care: 98<=Z<=256, E=Y-1,S=Z+Y-226 and the three helpers are0.
/// The optional immutable gate is outside all helpers/metadata/data.
/// With gate0 every swap and running-mask query is exactly disabled;
/// the byte and its clean decoder are still completely reversed.
pub(crate) fn record(b:&mut B,size:&SumSize,roles:Roles,ring:&[QubitId],q:&[QubitId],
    extra:&[(QubitId,bool)],dirty:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),q.len()),(257,128));assert!(extra.len()<=1);
    assert!(extra.iter().all(|p|p.0==roles.tag));
    let address=super::direct_frame::z_byte_record(b,size,roles.toggle,dirty);
    b.begin();b.play(&address,false);
    let mut dec=Prefix{word:&size.y,port:roles.prefix,old:None};
    // At the top physical lane every admissible Z is below the cut.
    mc_xor(b,extra,roles.cut,&[],dirty);
    for lane in(129..257).rev(){
        if lane<256{
            // Remove precisely Z=lane+1 from the retained Z<=lane mask.
            // All such codes129..255 have high byte bit1; no low alias.
            let mut c=dec.controls(b,lane&127);
            c.push((roles.toggle,false));c.extend_from_slice(extra);
            mc_xor(b,&c,roles.cut,&[],dirty);
        }
        b.cswap(roles.cut,ring[lane],q[256-lane]);
    }
    // Remaining mask is extra & (Z<=129). Its exact byte expression is
    // extra XOR extra*high XOR extra*high*[low7=0].
    mc_xor(b,extra,roles.cut,&[],dirty);
    let mut high=extra.to_vec();high.push((roles.toggle,false));
    mc_xor(b,&high,roles.cut,&[],dirty);
    let mut last=dec.controls(b,0);last.extend(high);
    mc_xor(b,&last,roles.cut,&[],dirty);
    dec.clear(b);b.play(&address,true);b.end()
}
