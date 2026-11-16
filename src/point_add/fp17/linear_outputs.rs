//! Coordinate changes on the lookup OUTPUTS are paid twice: CNOT into basis,
//! an oracle for AF, then A^-1. This works on arbitrary incoming output words.
use super::lutplan::{Gate,Plan,AUX,OUT,NOT_USED as N,cost};
#[derive(Clone,Copy,PartialEq,Eq,PartialOrd,Ord)]
struct Score { weighted:u32, ccx:u32, rows:u32 }
impl Score {
    fn new(rows:u32,ccx:u32,w:u32)->Self{Self{weighted:rows+w*ccx,ccx,rows}}
    fn add(self,b:Self)->Self{Self{weighted:self.weighted+b.weighted,rows:self.rows+b.rows,ccx:self.ccx+b.ccx}}
    fn zero()->Self{Self{weighted:0,rows:0,ccx:0}}
}
fn valid_order(m:u8)->Vec<Vec<u8>> {
    fn go(m:u8,p:&mut Vec<u8>,out:&mut Vec<Vec<u8>>){
        if p.len()==m as usize {out.push(p.clone());return}
        for i in 0..m {if !p.contains(&i){p.push(i);go(m,p,out);p.pop();}}
    }
    let mut r=vec![];go(m,&mut vec![],&mut r);r
}
fn monomials(t:&[u32],flip:usize)->[u16;16]{
    let n=t.len();let mut v=[0u16;16];
    for i in 0..n{v[i]=t[i^flip] as u16;}
    for j in 0..n.ilog2(){let b=1<<j;for i in 0..n {if i&b!=0{v[i]^=v[i^b]}}}
    v
}
#[derive(Clone)]
pub struct Shape { order:Vec<u8>,nodes:Vec<(usize,u16)> }
impl Shape {
    fn new(order:Vec<u8>)->Self{
        let mut nodes=vec![];
        let n=1<<order.len();
        for m in 1usize..n {
            if m.count_ones()<2{continue}
            let last=order.iter().rposition(|&j|m>>j&1!=0).unwrap();
            let mut descendants=0u16;
            for d in 1..n {
                if d==m || d&m!=m {continue}
                if order[..=last].iter().all(|&j|((m^d)>>j)&1==0){descendants|=1<<d;}
            }
            nodes.push((m,descendants));
        }
        Self{order,nodes}
    }
}
pub fn shapes(m:u8)->Vec<Shape>{valid_order(m).into_iter().map(Shape::new).collect()}
fn leaf(h:u32,w:u32)->(Score,u8) {
    if h==0{return(Score::zero(),0)}
    [(Score::new(h,h,w),1),(Score::new(2+h,2,w),2),(Score::new(2*h-1,1,w),3)].into_iter().min().unwrap()
}
fn tally(v:&[u16;16],shape:&Shape,flip:usize,changes:usize,w:u32)->Score{
    let mut alive=0u16;
    for (i,&x) in v.iter().enumerate(){if x!=0{alive|=1u16<<i;}}
    let mut rows=v[0].count_ones()+2*(flip.count_ones()+changes as u32);
    for &i in &shape.order{rows+=v[1<<i].count_ones()}
    let mut total=Score::new(rows,0,w);
    for &(m,descendants) in &shape.nodes {
        let h=v[m].count_ones();
        let price=if descendants&alive!=0 {Score::new(2+h,2,w)} else {leaf(h,w).0};
        total=total.add(price);
    }
    total
}
fn change(v:[u16;16],a:u8,b:u8)->[u16;16]{v.map(|m|m^(((m>>a)&1)<<b))}
fn scatter(p:&mut Plan,mask:u16,a:u8,b:u8){for j in 0..16{if mask>>j&1!=0{p.push(Gate(a,b,OUT+j));}}}
fn emit_node(p:&mut Plan,v:&[u16;16],left:&[u8],prefix:usize,parent:u8,naux:u8,w:u32){
    for (i,&b) in left.iter().enumerate(){
        let mon=prefix|(1<<b);let mask=v[mon];let suffix=&left[i+1..];
        if prefix==0 {
            scatter(p,mask,N,b);emit_node(p,v,suffix,mon,b,naux,w);continue
        }
        let remain=suffix.iter().fold(0,|m,&x|m|1usize<<x);
        let has=(0..16).any(|m|(m&mon)==mon && m!=mon && (m&!mon&!remain)==0 && v[m]!=0);
        let mode=if has{2}else{leaf(mask.count_ones(),w).1};
        match mode {
            0=>{},
            1=>scatter(p,mask,parent,b),
            2=>{let g=Gate(parent,b,AUX+naux);p.push(g);scatter(p,mask,N,AUX+naux);
                emit_node(p,v,suffix,mon,AUX+naux,naux+1,w);p.push(g);}
            3=>{let pivot=mask.trailing_zeros() as u8;let other=mask&!(1<<pivot);
                scatter(p,other,N,OUT+pivot);p.push(Gate(parent,b,OUT+pivot));scatter(p,other,N,OUT+pivot);}
            _=>unreachable!()
        }
    }
}
pub fn choose(t:&[u32],shapes:&[Shape],w:u32,base:Plan,depth:usize)->Plan{
    let m=t.len().ilog2();if m<2||m>4{return base}
    let nout=(32-t.iter().fold(0,|a,&b|a|b).leading_zeros())as u8;
    if nout<2{return base}
    let (r,c)=cost(&base);
    let mut best=Score::new(r as u32,c as u32,w);
    let mut layouts=Vec::new();
    for flip in 0..t.len(){
        let v=monomials(t,flip);
        for (i,s) in shapes.iter().enumerate(){layouts.push((tally(&v,s,flip,0,w),flip,i));}
    }
    layouts.sort_unstable();
    let mut best_data=None;
    for &(_,flip,i) in layouts.iter().take(depth){
        let mut v=monomials(t,flip);
        let s=&shapes[i];let mut score=tally(&v,s,flip,0,w);
        let mut cx=vec![];
        loop {
            let mut next=None;
            for a in 0..nout {for b in 0..nout {if a!=b{
                let nv=change(v,a,b);let ns=tally(&nv,s,flip,cx.len()+1,w);
                if ns<score && next.as_ref().map_or(true,|(z,_,_,_)|ns<*z){next=Some((ns,a,b,nv))}
            }}}
            let Some((ns,a,b,nv))=next else{break};
            score=ns;v=nv;cx.push(Gate(N,OUT+a,OUT+b));
        }
        if score<best{best=score;best_data=Some((v,flip,i,cx));}
    }
    let Some((v,flip,i,changes))=best_data else{return base};
    let mut p=changes.clone();
    let flips=(0..m as u8).filter(|b|flip>>b&1!=0).map(|b|Gate(N,N,b)).collect::<Vec<_>>();
    p.extend(&flips);scatter(&mut p,v[0],N,N);
    emit_node(&mut p,&v,&shapes[i].order,0,N,0,w);
    p.extend(flips.iter().rev());p.extend(changes.iter().rev());
    let (r,c)=cost(&p);assert_eq!((best.rows,best.ccx),(r as u32,c as u32));p
}
// For each address, the implemented map of incoming targets is affine.
// Its offset and every column of its linear part determine the entire map.
pub fn verify(p:&[Gate],t:&[u32]){
    let n=t.len();let mask=(1u32<<n)-1;let m=n.ilog2() as usize;
    let nout=(32-t.iter().fold(0,|a,&b|a|b).leading_zeros()) as usize;
    for e in 0..=nout{
        let mut bits=[0u32;64];for i in 0..m {for j in 0..n{bits[i]|=(((j>>i)&1)as u32)<<j;}}
        if e<nout{bits[OUT as usize+e]=mask;}
        let initial=bits;
        for &Gate(a,b,out) in p {
            assert!(a!=out && b!=out);
            if (AUX..OUT).contains(&out){assert!(((out-AUX)as usize)<m-1);}
            if a!=N{assert!(a<OUT && b<OUT);}
            if b>=OUT && b!=N{assert!(a==N && out>=OUT);}
            let val=|i:u8|if i==N{mask}else{bits[i as usize]};
            bits[out as usize]^=val(a)&val(b);
        }
        assert_eq!(&bits[..OUT as usize],&initial[..OUT as usize]);
        for j in 0..n{for k in 0..16{assert_eq!((bits[OUT as usize+k]>>j)&1,((t[j]>>k)&1)^u32::from(k==e && e<nout));}}
    }
}
