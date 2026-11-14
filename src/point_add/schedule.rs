use std::io::{self, Read};
use super::decoder::decode_records;

pub trait RecordTarget {
    fn read_prior(&mut self, index: usize) -> [u16;4];
    fn append(&mut self, row: [u16;4]);
}
fn bad(s:&'static str)->io::Error {io::Error::new(io::ErrorKind::InvalidData,s)}
struct Reader<'a>{data:&'a[u8],pos:usize}
impl Reader<'_>{
    fn byte(&mut self)->io::Result<u8>{let x=*self.data.get(self.pos).ok_or_else(||bad("short schedule"))?;self.pos+=1;Ok(x)}
    fn number(&mut self)->io::Result<usize>{
        let mut x=0u64;
        for shift in (0..64).step_by(7){let b=self.byte()?;
            if shift==63&&b>1{return Err(bad("schedule number overflow"));}
            x|=u64::from(b&127)<<shift;
            if b<128{return usize::try_from(x).map_err(|_|bad("schedule number too large"));}
        }Err(bad("bad schedule number"))
    }
}
#[derive(Clone,Copy)]
struct Piece{start:u16,base:u16,minus:bool}
struct Rename([Vec<Piece>;3]);
fn namespace(kind:u16,j:usize)->Option<usize>{
    match kind {
        1=>(j==0).then_some(2),2=>[Some(2),Some(0),None][j],18=>[Some(2),Some(1),None][j],
        3..=5=>(j<2).then_some(1),6|7|12=>[Some(0),Some(1),None][j],
        8|9=>Some(if j<2{0}else{1}),13=>Some(0),15=>(j==0).then_some(1),16=>None,
        _=>panic!("unsupported semantic gate {}",kind),
    }
}
impl Rename{
    fn apply(&self,mut row:[u16;4])->[u16;4]{
        let k=row[0];for j in 0..3{let w=row[j+1];if w==u16::MAX{continue;}
            if let Some(ns)=namespace(k,j){let runs=&self.0[ns];if !runs.is_empty(){
                let p=runs[runs.partition_point(|p|p.start<=w)-1];
                row[j+1]=if p.minus{p.base.wrapping_sub(w)}else{p.base.wrapping_add(w)};
            }}
        }row
    }
}
struct Action{size:usize,src:usize,map:usize,mode:u8}
struct Schedule{items:Vec<Action>,maps:Vec<Rename>,total:usize,literals:usize}
impl Schedule {
    fn parse(data:&[u8])->io::Result<Self>{
        if data.len()<24||&data[..8]!=b"GIRPLAN1"{return Err(bad("incorrect schedule version"));}
        let total=usize::try_from(u64::from_le_bytes(data[8..16].try_into().unwrap())).map_err(|_|bad("schedule length"))?;
        let literals=usize::try_from(u64::from_le_bytes(data[16..24].try_into().unwrap())).map_err(|_|bad("schedule literals"))?;
        let mut rd=Reader{data,pos:24};let nm=rd.number()?;if nm>data.len(){return Err(bad("too many wire maps"));}
        let mut maps=Vec::with_capacity(nm);
        for _ in 0..nm{let mut m=Rename([Vec::new(),Vec::new(),Vec::new()]);
            for bank in &mut m.0{let nr=rd.number()?;if nr>65535{return Err(bad("too many wire ranges"));}
                let mut start=0usize;
                for i in 0..nr{if i!=0{let d=rd.number()?;if d==0{return Err(bad("unordered wire map"));}
                    start=start.checked_add(d).ok_or_else(||bad("wire range overflow"))?;}
                    let encoded=rd.number()?;if start>=65535||encoded>=131072{return Err(bad("wire map outside u16"));}
                    let z=(encoded>>1)as u16;bank.push(Piece{start:start as u16,base:(z>>1)^0u16.wrapping_sub(z&1),minus:encoded&1!=0});
                }
            }maps.push(m);
        }
        let nc=rd.number()?;if nc>data.len(){return Err(bad("too many schedule commands"));}
        let mut items=Vec::with_capacity(nc);let mut pos=0usize;let mut lit=0usize;
        for _ in 0..nc{
            let mode=rd.byte()?;let size=rd.number()?;if size==0||size>total-pos{return Err(bad("invalid schedule chunk"));}
            let (src,map)=match mode{
                0=>{lit+=size;(0,0)}
                1|2=>{let distance=rd.number()?;let map=rd.number()?;
                    if distance==0||distance>pos||map>=maps.len(){return Err(bad("illegal history reference"));}
                    let src=pos-distance;
                    if mode==1&&size>distance||mode==2&&size>src+1{return Err(bad("overlapping history reference"));}
                    (src,map)}
                _=>return Err(bad("unknown schedule command"))
            };items.push(Action{size,src,map,mode});pos+=size;
        }
        if rd.pos!=data.len()||pos!=total||lit!=literals{return Err(bad("inconsistent schedule totals"));}
        Ok(Self{items,maps,total,literals})
    }
}
pub fn expand(input:impl Read,plan:&[u8],output:&mut impl RecordTarget)->io::Result<usize>{
    let s=Schedule::parse(plan)?;let mut next=0usize;let mut remaining=0usize;
    let drain=|next:&mut usize,remaining:&mut usize,output:&mut _| {
        while *remaining==0&&*next<s.items.len(){
            let a=&s.items[*next];*next+=1;
            if a.mode==0{*remaining=a.size;break;}
            let m=&s.maps[a.map];
            for k in 0..a.size{
                let source=if a.mode==1{a.src+k}else{a.src-k};
                let row=RecordTarget::read_prior(output,source);RecordTarget::append(output,m.apply(row));
            }
        }
    };
    let mut excess=false;
    let n=decode_records(input,|record|{
        drain(&mut next,&mut remaining,output);
        if remaining==0{excess=true;return;}output.append(record);remaining-=1;
    })?;
    drain(&mut next,&mut remaining,output);
    if excess||remaining!=0||next!=s.items.len()||n!=s.literals{return Err(bad("incorrect literal stream length"));}
    Ok(s.total)
}
