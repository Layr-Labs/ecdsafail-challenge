//! Physical replacements for AL3 segments 7–10 and 20–23, before peephole.
use super::{Row, i1, lzma, qubits, b5gen};
#[path="fd_alloc.rs"] mod fd_alloc;
#[path="fd_machine.rs"] mod fd_machine;
#[path="fd_pressure.rs"] mod fd_pressure;
#[path="fd_dp.rs"] mod fd_dp;
const N:u16=u16::MAX;

fn var(data:&[u8],at:&mut usize)->usize{
    let mut value=0;
    for shift in (0..usize::BITS).step_by(7) {
        let b=data[*at];*at+=1;value|=((b&127) as usize)<<shift;
        if b<128 {return value;}
    }
    panic!("bad FD varint")
}
fn row(bytes:&[u8])->Row{std::array::from_fn(|j|u16::from_le_bytes([bytes[2*j],bytes[2*j+1]]))}
fn u32at(s:&[u8])->usize{u32::from_le_bytes(s[..4].try_into().unwrap()) as usize}
fn u16at(s:&[u8])->u16{u16::from_le_bytes(s[..2].try_into().unwrap())}
fn frame(data:&[u8])->(fd_machine::Frame,Vec<usize>,Vec<usize>){
    let bytes=lzma::decode(data).unwrap();let mut at=0;
    let mut col=|width|{
        let n=u32at(&bytes[at..]);at+=4;
        let v=&bytes[at..at+n*width];at+=n*width;v
    };
    let u16s=|s:&[u8]|s.chunks_exact(2).map(u16at).collect::<Vec<_>>();
    let lanes=|s:&[u8]|s.chunks_exact(2).map(|p|u16at(p) as usize).collect::<Vec<_>>();
    let live=lanes(col(2));let ones=lanes(col(2));
    let bits_zero=u16s(col(2));let bits_one=u16s(col(2));
    let guards=u16s(col(2)).into_iter().map(|v|v as u8).collect();
    let bypass=col(8).chunks_exact(80).map(|line|line.chunks_exact(8)
        .map(|p|u64::from_le_bytes(p.try_into().unwrap())).collect()).collect();
    let entry=lanes(col(2));let exit=lanes(col(2));assert_eq!(at,bytes.len());
    (fd_machine::Frame{live,ones,bits_zero,bits_one,guards,bypass},entry,exit)
}
fn place(rows:&mut Vec<Row>,start:usize,data:&[u8],moves:usize){
    let (f,e,x)=frame(data);
    fd_alloc::assign(rows,start,&f,&e,&x,631,moves);
}

// Undo only the original i1 lane transpositions inside this physical scan.
// The last eighteen repaired high bits are emitted by the replacement.
fn native(parent:&[Row],start:usize,n:usize)->Vec<Row>{
    let table=i1::table().expect("graded i1 table");
    let mut out=Vec::with_capacity(n+18);
    let mut pos=0;
    let mut offset=0;
    let mut hide=table.h0;
    for (idx,next,flags) in table.ent {
        let physical=idx as usize+offset;
        let moves=i1::moves(hide,next,flags);offset+=moves.len();
        if physical>=start+parent.len(){break;}
        if physical>=start {
            let end=physical-start;
            out.extend(parent[pos..end].iter().map(|&r|i1::sigma(r,hide)));
            assert_eq!(&parent[end..end+moves.len()],moves.as_slice());
            pos=end+moves.len();
        }
        hide=next;
    }
    out.extend(parent[pos..].iter().map(|&r|i1::sigma(r,hide)));
    assert_eq!(out.len(),n+18);out.truncate(n);out
}

fn gaps(input:Vec<Row>,commands:&[u8],literals:&[u8],expected:usize)->Vec<Row>{
    let commands=lzma::decode(commands).unwrap();
    let literals=lzma::decode(literals).unwrap();
    let mut out=Vec::with_capacity(expected);
    let (mut at,mut pos,mut lit)=(0,0,0);
    while at<commands.len(){
        let keep=var(&commands,&mut at);let skip=var(&commands,&mut at);let add=var(&commands,&mut at);
        out.extend_from_slice(&input[pos..pos+keep]);pos+=keep+skip;
        out.extend(literals[lit..lit+8*add].chunks_exact(8).map(row));lit+=8*add;
    }
    out.extend_from_slice(&input[pos..]);assert_eq!(lit,literals.len());assert_eq!(out.len(),expected);
    out
}

fn fperm(mut r:Row)->Row{
    for j in 1..=qubits(r[0]){
        r[j]=match r[j]{632=>614,614=>632,631=>613,613=>631,x=>x};
    }r
}
fn half(parent:&[Row])->Vec<Row>{
    let base=native(parent,626414271,257057665);
    let dict=lzma::decode(include_bytes!("data/half.dict.lzma")).unwrap();
    let mut templates=Vec::new();let mut at=0;
    while at<dict.len(){
        let n=var(&dict,&mut at);
        templates.push(dict[at..at+8*n].chunks_exact(8).map(|p|fperm(row(p))).collect::<Vec<_>>());
        at+=8*n;
    }
    let cmds=lzma::decode(include_bytes!("data/half.cmd.lzma")).unwrap();
    let mut out=Vec::with_capacity(457566104);at=0;let mut prev=0i64;
    while at<cmds.len(){
        let op=var(&cmds,&mut at);
        if op&1!=0 {out.extend_from_slice(&templates[op/2]);}
        else {
            let z=var(&cmds,&mut at) as i64;
            let from=(prev+((z>>1)^-(z&1))) as usize;
            let end=from+op/2;out.extend(base[from..end].iter().copied().map(fperm));prev=end as i64;
        }
    }
    assert_eq!(out.len(),457566104);out
}

// Build the odd comparator from the balanced KG ladder used by half.cpp.
fn comparator(biased:bool)->Vec<Row>{
    let mut a:Vec<u16>=(69..73).chain(129..171).collect();a[4+135-129]=249;
    let mut bank=vec![230];bank.extend_from_slice(&a[if biased{12}else{13}..43]);
    let mut free=vec![false;bank.len()];free[0]=true;
    let mut ladder=Vec::new();
    for _ in 0..bank.len(){
        let mut chosen=None;
        for t in (0..bank.len()).rev().filter(|&t|free[t]){
            let mut src=(t+1..bank.len()).filter(|&k|!free[k]);
            if let (Some(x),Some(y))=(src.next(),src.next()){chosen=Some((t,x,y));break;}
        }
        let Some((t,x,y))=chosen else{break};
        ladder.push([13,bank[x],bank[y],bank[t]]);
        if t!=0{ladder.push([6,bank[t],N,N]);}
        free[x]=true;free[y]=true;free[t]=false;
    }
    let live:Vec<_>=bank.iter().enumerate().filter(|(i,_)|!free[*i]).map(|(_,x)|*x).collect();
    assert_eq!(live.len(),2);
    let fan=[8,234,631,N];
    let bias=[[8,a[10],a[12],N],[8,a[11],a[12],N],[13,a[10],a[11],a[12]]];
    let mut out=vec![fan];if biased{out.extend(bias);}
    out.extend(&ladder);out.push([13,live[0],live[1],234]);out.extend(ladder.iter().rev());
    if biased{out.extend(bias.iter().rev());}out.push(fan);out
}

pub(super) fn f(parent:&[Row])->Vec<Row>{
    const PREFIX:usize=18+115733069+29674;
    assert_eq!(parent.len(),372821296);
    let input=half(&parent[PREFIX..]);
    let input=fd_pressure::apply(input,include_bytes!("data/closed.ranges"),
        &[236,234,164,165,250,235,138,163],461288297);
    let input=fd_pressure::apply(input,include_bytes!("data/narrow.ranges"),
        &[137,138,139,136,165,164,163,162,235,234,250,236],461527636);
    let draw=gaps(input,include_bytes!("data/Frest.cmd.lzma"),include_bytes!("data/Frest.lit.lzma"),462020078);
    let mut out=Vec::with_capacity(115762750+464641518+12);
    let loans=lzma::decode(include_bytes!("data/f.loans")).unwrap();
    let mut groups=loans.chunks_exact(10).peekable();
    for (i,&p) in parent[..PREFIX].iter().enumerate(){
        let mut r=p;
        let item=i.saturating_sub(18);
        if groups.peek().is_some_and(|g|item==u32at(&g[4..])){groups.next();}
        for j in 1..=qubits(r[0]){
            if r[j]==613 && i>=18 {
                let g=groups.peek().expect("F loan");
                assert!(u32at(g)<=item && item<u32at(&g[4..]));r[j]=u16at(&g[8..]);
            }else if r[j]==631 {r[j]=if i<18 {180}else{613};}
        }
        out.push(r);if i==17{out.push([12,613,65001,N]);}
    }
    assert!(groups.next().is_none());
    place(&mut out,0,include_bytes!("data/fpre.frame"),0);let start=out.len();assert_eq!(start,115762750);
    let old=comparator(false);let new=comparator(true);
    let mut pos=0;let mut count=0;
    while pos<draw.len(){
        if draw[pos]==old[0] && draw[pos..].starts_with(&old){
            out.extend_from_slice(&new);pos+=old.len();count+=1;
        } else {out.push(draw[pos]);pos+=1;}
    }
    drop(draw);assert_eq!(count,262144);assert_eq!(out.len()-start,464641518);
    place(&mut out,start,include_bytes!("data/fscan.frame"),6);
    assert_eq!(out.len(),575720034);
    place(&mut out,0,include_bytes!("data/fwhole.frame"),0);
    assert_eq!(out.len(),575221183);out
}
pub(super) fn dp(parent:&[Row])->Vec<Row>{fd_dp::emit(parent)}

