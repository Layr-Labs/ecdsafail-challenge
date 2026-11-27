//! Deterministic post-pass at final physical row coordinates.
use super::{budget630, codek630, inner630, layer630, lowerr630, stack630, ureg630, Row};
mod config;
mod columns;
mod cap;
mod walks;
mod scans;
mod liveness;
#[path = "budget630_windows.rs"]
mod budget_windows;

pub(super) fn arity(k:u16)->usize{match k{13=>3,8|9=>2,6|7|12=>1,_=>0}}

pub(super) fn varint(b:&mut &[u8])->usize {
    let mut n=0;
    for shift in (0..63).step_by(7){
        let (&x,rest)=b.split_first().expect("truncated varint");*b=rest;
        n|=usize::from(x&127)<<shift;
        if x<128{return n;}
    }
    panic!("invalid varint")
}

fn patch(base:&[Row],bytes:&[u8],expected:usize,masked:bool)->Vec<Row>{
    let unpacked=super::lzma::decode(bytes).expect("decode row patch");
    let mut b=unpacked.as_slice();
    let mut cursor=0usize;let mut out=Vec::with_capacity(expected);
    while !b.is_empty(){
        let token=varint(&mut b);
        let (n,kind)=if masked{(token>>2,token&3)}else{(token>>1,token&1)};
        assert!(n>0&&n<=expected-out.len());
        if kind==1{
            let (data,rest)=b.split_at(n*8);b=rest;
            out.extend(data.chunks_exact(8).map(|r|std::array::from_fn(|i|u16::from_le_bytes([r[2*i],r[2*i+1]]))));
        }else if kind==0{
            let z=varint(&mut b);let shift=(z as isize>>1)^-((z&1) as isize);
            let p=cursor.checked_add_signed(shift).unwrap();
            out.extend_from_slice(&base[p..p+n]);cursor=p+n;
        }else{
            assert_eq!(kind,2);
            out.resize(out.len()+n,[0;4]);
        }
    }
    assert_eq!(out.len(),expected);out
}

pub fn segments(input:impl Iterator<Item=Row>,mut output:impl FnMut(&str,Vec<Row>)){
    let mut src=input;
    let mut forward=Vec::new();
    let mut fp_tail=None;
    let cuts=super::lzma::decode(include_bytes!("budget2-cuts.lzma")).expect("budget2 windows");
    for &(name,n,release_len) in config::BLOCKS{
        let raw=if name=="s26_tail"{Vec::new()}else{
            let v:Vec<_>=src.by_ref().take(n).collect();assert_eq!(v.len(),n);v
        };
        let rows=match name{
            "s02_upper"|"s18_upper"=>{
                let result=walks::upper(&raw,usize::from(name=="s18_upper"));
                assert!(forward.is_empty());forward=raw;result
            },
            "s13_early"|"s29_early"=>{
                let result=walks::adjoint(&raw,&forward,usize::from(name=="s29_early"));
                forward=Vec::new();result
            },
            "s02_col1"|"s18_col1"|"s02_capped"|"s18_capped"=>walks::front(name.starts_with("s18") as usize,name.ends_with("capped")),
            "s03"=>scans::b(raw),"s19"=>scans::bp(raw),
            "s06"|"s10"|"s23"=>liveness::prune(raw),
            "s26_sweep"=>{
                let (_,n_tail,_)=*config::BLOCKS.iter().find(|b|b.0=="s26_tail").unwrap();
                let mut whole=raw;
                whole.reserve_exact(n_tail);whole.extend(src.by_ref().take(n_tail));
                assert_eq!(whole.len(),n+n_tail);
                let mut kept=liveness::prune(whole);
                fp_tail=Some(kept.split_off(release_len));kept
            }
            "s26_tail"=>fp_tail.take().unwrap(),
            "s08" => patch(&raw,include_bytes!("composition/s08-original.lzma"),102_344_358,false),
            "s25" => patch(&raw,include_bytes!("composition/s25-original.lzma"),99_447_038,false),
            "s05" => patch(&raw,include_bytes!("composition/s05-retained.lzma"),release_len,true),
            "s21" => patch(&raw,include_bytes!("composition/s21-retained.lzma"),release_len,true),
            "s12"|"s28"|"s29_late"=>patch(&raw,config::blob(name),release_len,false),
            _=>raw
        };
        if !matches!(name,"s08"|"s25"){assert_eq!(rows.len(),release_len,"release segment {name}");}
        let rows=match name{
            "s05"|"s21"=>lowerr630::generate(name,rows),
            "s12"|"s28"=>ureg630::generate(name,rows),
            "s08"|"s25"=>{
                let item=if name=="s08"{4}else{12};
                let stack=stack630::generate(item,rows);
                let inner=inner630::generate(item,&stack);
                codek630::generate(item,inner,&stack)
            }
            "s00"|"s03"|"s06"|"s10"|"s13_early"|"s14"|"s19"|"s23"|"s26_sweep"|"s26_tail"|"s29_early"|"s30"=>
                budget630::certified(name,rows),
            _=>rows,
        };
        let rows=match budget_windows::WINDOWS.iter().find(|w|w.0==name){
            Some(&(_,start,end))=>budget630::windowed(rows,&cuts[start..end]),
            None=>rows,
        };
        output(name,rows);
    }
    assert!(src.next().is_none());
}

pub fn output(src:impl Iterator<Item=Row>,sink:impl FnMut(Row)){
    let mut writer=layer630::Writer::new(sink);
    segments(src,|_,rows|for r in rows{writer.row(r);});
    writer.finish();
}
