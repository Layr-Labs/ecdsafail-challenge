//! Plan an XOR lookup on disjoint address, clean decode scratch and arbitrary targets.
//! Cost is (printed operations, static CCX), ordered lexicographically.
pub const NOT_USED:u8=255;
pub const AUX:u8=24;
pub const OUT:u8=48;
#[derive(Clone,Copy,Debug)]
pub struct Gate(pub u8,pub u8,pub u8);
pub type Plan=Vec<Gate>;
fn x(t:u8)->Gate { Gate(NOT_USED,NOT_USED,t) }
fn cx(c:u8,t:u8)->Gate { Gate(NOT_USED,c,t) }
fn ccx(a:u8,b:u8,t:u8)->Gate { Gate(a,b,t) }
pub fn cost(p:&[Gate])->(usize,usize) {
    (p.len(),p.iter().filter(|g|g.0!=NOT_USED).count())
}
fn word(mask:u32,c:u8)->Plan {
    (0..16u8).filter(|&i|(mask>>i)&1==1).map(|i|if c==NOT_USED{x(OUT+i)}else{cx(c,OUT+i)}).collect()
}
fn append(mut a:Plan,b:&[Gate])->Plan { a.extend_from_slice(b);a }
fn best(a:Plan,b:Plan)->Plan { if cost(&b)<cost(&a){b}else{a} }
// Add a controlled XOR oracle. Negative uses c AND NOT b if there is a parent.
fn child(table:&[u32],d:u8,c:u8,b:u8,next:u8,negative:bool)->Plan {
    if table.iter().all(|&w|w==0){return vec![]}
    if c==NOT_USED {
        let v=solve(table,d,b,next);
        if !negative {return v}
        return append(append(vec![x(b)],&v),&[x(b)]);
    }
    let h=AUX+next;
    let g=ccx(c,b,h);
    let prep=if negative{vec![g,cx(c,h)]}else{vec![g]};
    let mut via=append(prep.clone(),&solve(table,d,h,next+1));
    via.extend(prep.iter().rev());
    // A constant controlled by two inputs can scatter directly to its target bits.
    if table.iter().all(|&w|w==table[0]){
        let mut direct=Vec::new();
        for i in 0..16u8 { if (table[0]>>i)&1!=0 {
            if negative{direct.push(cx(c,OUT+i))}
            direct.push(ccx(c,b,OUT+i))
        }}
        via=best(via,direct);
    }
    via
}
fn solve(table:&[u32],bits:u8,c:u8,next:u8)->Plan {
    if table.iter().all(|&v|v==table[0]) {return word(table[0],c)}
    let common=table.iter().fold(u32::MAX,|x,&y|x&y);
    if common!=0 {
        let rest=table.iter().map(|&x|x^common).collect::<Vec<_>>();
        return append(word(common,c),&solve(&rest,bits,c,next));
    }
    let b=bits-1;
    let (lo,hi)=table.split_at(table.len()/2);
    if lo==hi {return solve(lo,b,c,next)}
    let delta=lo.iter().zip(hi).map(|(x,y)|x^y).collect::<Vec<_>>();
    let mut base=append(solve(lo,b,c,next),&child(&delta,b,c,b,next,false));
    base=best(base,append(solve(hi,b,c,next),&child(&delta,b,c,b,next,true)));
    // Shannon with both sides sharing the same unwind, as in the frozen Rns::sel.
    if !lo.iter().all(|&w|w==0) && !hi.iter().all(|&w|w==0) {
        let mut sh=Vec::new();
        if c==NOT_USED {
            sh.push(x(b));sh.extend(solve(lo,b,b,next));sh.push(x(b));sh.extend(solve(hi,b,b,next));
        } else {
            let h=AUX+next;
            sh.extend([ccx(c,b,h),cx(c,h)]);sh.extend(solve(lo,b,h,next+1));sh.push(cx(c,h));
            sh.extend(solve(hi,b,h,next+1));sh.push(ccx(c,b,h));
        }
        base=best(base,sh);
    }
    base
}
pub fn plan(table:&[u32])->Plan {
    assert!(table.len().is_power_of_two() && table.len()<=16 && table.iter().all(|&x|x<65536));
    solve(table,table.len().ilog2() as u8,NOT_USED,0)
}
// Check every address in parallel on bit masks. Gate targets in the output are
// never used as controls, so zeroed targets suffice for arbitrary initial targets.
pub fn verify(p:&[Gate],table:&[u32]) {
    let n=table.len();
    let mask=(1u32<<n)-1;
    let m=n.ilog2() as usize;
    let mut a=[0u32;64];
    for i in 0..m {for j in 0..n {a[i]|=(((j>>i)&1)as u32)<<j;}}
    let initial=a;
    for &Gate(x,y,t) in p {
        let c=if x==NOT_USED{mask}else{assert!(x<OUT);a[x as usize]};
        let d=if y==NOT_USED{mask}else{assert!(y<OUT);a[y as usize]};
        assert!(x!=t && y!=t);
        if (AUX..OUT).contains(&t) {assert!((t-AUX) < (m as u8).saturating_sub(1))}
        a[t as usize]^=c&d;
    }
    assert_eq!(&a[..OUT as usize],&initial[..OUT as usize]);
    for bit in 0..16 {
        let wanted=table.iter().enumerate().fold(0,|x,(i,&w)|x|(((w>>bit)&1)<<i));
        assert_eq!(a[OUT as usize+bit],wanted);
    }
}
