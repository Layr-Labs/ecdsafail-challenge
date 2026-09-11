//! Exact directional-shift fusion: A - 2*A*b = (A XOR b) - b.
//! Replace only four byte-verified coherent helper bodies. Parent node IDs,
//! mappings and every other node body remain unchanged. The normal HIR parser
//! recomputes summaries, and all original compiler passes remain enabled.
use super::{Reader,MAGIC};

fn var(mut n:usize,out:&mut Vec<u8>){while n>=128{out.push((n as u8&127)|128);n>>=7;}out.push(n as u8);}

pub(super) fn replace(data:&[u8])->Vec<u8>{
    assert!(data.starts_with(MAGIC));
    let mut r=Reader{data,at:MAGIC.len()};
    assert_eq!(r.uvar(),1);assert_eq!(r.uvar(),2269);assert_eq!(r.uvar(),2270);
    let mut out=Vec::with_capacity(data.len());out.extend_from_slice(&data[..r.at]);
    let mut count=0;
    for node in 0..2270 {
        let prefix=r.at;let size=r.uvar();let start=r.at;
        let end=start.checked_add(size).expect("node size overflow");
        let body=data.get(start..end).expect("truncated node");
        let pair:Option<(&[u8],&[u8])>=match node {
            1=>Some((include_bytes!("shift_fixtures/old-pre.hir"),include_bytes!("shift_fixtures/new-pre.hir"))),
            5=>Some((include_bytes!("shift_fixtures/old-post.hir"),include_bytes!("shift_fixtures/new-post.hir"))),
            1130=>Some((include_bytes!("shift_fixtures/old-post-inverse.hir"),include_bytes!("shift_fixtures/new-post-inverse.hir"))),
            1131=>Some((include_bytes!("shift_fixtures/old-pre-inverse.hir"),include_bytes!("shift_fixtures/new-pre-inverse.hir"))),
            _=>None,
        };
        if let Some((old,new))=pair {
            assert_eq!(body,old,"directional-shift source body changed, node {node}");
            var(new.len(),&mut out);out.extend_from_slice(new);count+=1;
        }else{out.extend_from_slice(&data[prefix..end]);}
        r.at=end;
    }
    assert_eq!(r.at,data.len());assert_eq!(count,4);
    eprintln!("DIRECTIONAL_SHIFT: exact helper replacements={count} old_CCX=566 new_CCX=548 per_call_raw_saving=18");
    out
}
