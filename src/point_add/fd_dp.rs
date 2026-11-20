//! Two native loads with the original switch schedule, portable classical
//! caches and the 16-visit nine-bit pulse schedule of zc-Dp.
use super::{Row,N,b5gen,fd_machine,gaps,lzma,native,place,u16at,u32at};
fn perm(q:u16)->u16 {match q {618=>631,631=>632,632=>618,_=>q}}
fn map_native(mut r:Row)->Row {
    let n=fd_machine::operands(&r).len();
    for q in &mut r[1..1+n]{*q=perm(*q);}r
}

#[derive(Clone)]
struct Ripple {
    sub:bool,carry:u16,a:[u16;46],b:[u16;46],
}
impl Ripple {
    fn read(data:&[u8])->Self{
        let lane=|i:usize|u16at(&data[2*i..]);
        Self{sub:lane(0)!=0,carry:lane(1),a:std::array::from_fn(|j|lane(2+j)),
             b:std::array::from_fn(|j|lane(48+j))}
    }
    fn emit(&self,cut:usize,source:u8,fine:bool)->Vec<Row>{
        let mut a=self.a;let b=&self.b;
        let carry=if source==255{self.carry}else{a[source as usize]};
        if fine && source==255 {a[cut..9].copy_from_slice(&self.a[..9-cut]);}
        let mut g=Vec::with_capacity(272);
        let cx=|x,y|[8,x,y,N];
        for j in cut..45 {
            let prev=if j==cut{carry}else{a[j-1]};
            g.extend([cx(if self.sub{prev}else{a[j]},b[j]),cx(a[j],prev),[13,prev,b[j],a[j]]]);
        }
        g.extend([cx(a[44],b[45]),cx(a[45],b[45])]);
        for j in (cut..45).rev(){
            let prev=if j==cut{carry}else{a[j-1]};
            g.extend([[13,prev,b[j],a[j]],cx(a[j],prev),cx(if self.sub{a[j]}else{prev},b[j])]);
        }g
    }
}
struct Pair{left:Vec<Row>,right:Vec<Row>,carry:u16,pulses:Vec<(Vec<Row>,Vec<Row>)>}
fn patterns()->Vec<Pair>{
    let specs=lzma::decode(include_bytes!("data/dp.ripples")).unwrap();
    let rules=include_bytes!("data/dp.pulses");
    specs.chunks_exact(376).map(|s|{
        let x=Ripple::read(&s[..188]);let y=Ripple::read(&s[188..]);
        assert_eq!(x.sub,y.sub);
        let left=x.emit(0,255,false);let right=y.emit(0,255,false);
        let pulses=(0..16).map(|i|{
            let at=64*usize::from(x.sub)+4*i;
            let xy=&rules[at..at+4];
            let build=|r:&Ripple|{
                let j=if r.a[0]==41 {2}else{0};
                r.emit(xy[j] as usize,xy[j+1],true)
            };(build(&x),build(&y))
        }).collect();
        Pair{left,right,carry:x.carry,pulses}
    }).collect()
}
fn shorten(input:Vec<Row>)->Vec<Row>{
    let patterns=patterns();
    let mut out=Vec::with_capacity(518450799+78);
    let mut i=76938034;let mut start=0;let mut steps=0;
    while i+545<=input.len(){
        let r=input[i];
        if r[0]==8 {
            if let Some(p)=patterns.iter().find(|p| r==p.left[0] && input[i..].starts_with(&p.left)
                && input[i+272][0]==8 && input[i+272][2]==p.carry && input[i+272][3]==N
                && input[i+273..].starts_with(&p.right)){
                let (x,y)=&p.pulses[steps%16];
                out.extend_from_slice(&input[start..i]);out.extend_from_slice(x);
                out.push(input[i+272]);out.extend_from_slice(y);
                i+=545;start=i;steps+=1;continue;
            }
        }
        i+=1;
    }
    out.extend_from_slice(&input[start..]);assert_eq!(steps,524288);assert_eq!(out.len(),518450799);out
}

pub(super) fn emit(parent:&[Row])->Vec<Row>{
    const ITEM_END:usize=18+76908469;
    const PREFIX:usize=ITEM_END+29674;
    assert_eq!(parent.len(),321829721);
    let switches=lzma::decode(include_bytes!("data/dp.switch")).unwrap();
    let mut sw=switches.chunks_exact(10).peekable();
    let mut map:[u16;634]=std::array::from_fn(|i|i as u16);
    let mut raw=Vec::with_capacity(566216320);
    let mut put=|mut r:Row|{
        while let Some(s)=sw.next_if(|s|u32at(s)==raw.len()) {
            map[u16at(&s[4..]) as usize]=634;
            map[u16at(&s[6..]) as usize]=u16at(&s[8..]);
        }
        let n=fd_machine::operands(&r).len();
        for q in &mut r[1..1+n] {*q=map[*q as usize];}raw.push(r);
    };
    for mut r in parent[..18].iter().copied(){assert_eq!(r[0],12);if r[1]==631{r[1]=248;}put(r);}
    put([12,618,65001,N]);
    for r in b5gen::decode(&parent[18..ITEM_END],include_bytes!("data/dp21.b5")) {put(r);}
    for r in b5gen::decode(&parent[ITEM_END..PREFIX],include_bytes!("data/dp22.b5")) {put(r);}
    let base=native(&parent[PREFIX..],1560224089,244891028);
    let tail=&parent[parent.len()-18..];
    let mut top=[false;634];
    for r in tail {assert_eq!(r[0],7);top[if r[1]==228{632}else{r[1] as usize}]=true;}
    let mut scan=|r|put(map_native(r));
    scan([6,618,N,N]);
    let mut fan=false;let mut matches=0;let mut removed=0;
    for (i,&r) in base.iter().enumerate() {
        if fan && r[0]==8 && r[1]==229 && r[3]==N && top[r[2] as usize] {
            removed+=1;continue;
        }
        fan=i>=4 && r[0]==9 && r[1]==137 && r[2]==138 &&
            base[i-1]==[12,228,r[3],N] && base[i-3][0]==12 &&
            base[i-2][0]==9 && base[i-2][1]==228;
        matches+=usize::from(fan);
        if i==211937423 {
            assert_eq!(r,[6,229,N,N]);scan([8,229,633,N]);scan([8,633,229,N]);
        }else{scan(r);}
    }
    assert_eq!((matches,removed),(262144,503794));
    scan([6,618,N,N]);scan([8,633,618,N]);scan([8,618,633,N]);
    for &r in &base {scan(r);}
    for &r in tail {let mut t=r;if t[1]==228 {t[1]=632;}scan(t);}
    scan([7,618,65001,N]);
    drop(base);
    assert_eq!(raw.len(),566216320);
    let portable=gaps(raw,include_bytes!("data/Dportable.cmd.lzma"),include_bytes!("data/Dportable.lit.lzma"),565046895);
    let mut assigned=shorten(portable);
    place(&mut assigned,0,include_bytes!("data/dp.frame"),39);
    assert_eq!(assigned.len(),516046447);assigned
}

