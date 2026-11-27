//! Two-bit classical liveness for the four scans, one bit per value of bit 768.
use super::super::Row;
const N:u16=u16::MAX;
type Guard=(u8,u8);
fn condition((may,must):Guard,bit:u16)->Guard{
    match bit{768=>(may&1,must&1),N=>(may,must),_=>(may,0)}
}
pub fn prune(mut src:Vec<Row>)->Vec<Row>{
    let mut top=(1u8,1u8);
    let mut stack=vec![(3,3)];
    let mut events=Vec::new();
    for &[k,a,b,_] in &src{
        assert!(!((matches!(k,3..=5)&&a==768)||(k==12&&b==768)));
        match k{
            15=>{events.push(top);stack.push(top);top=condition(top,a);}
            16=>{events.push(top);top=stack.pop().expect("scope underflow");}
            _=>()
        }
    }
    assert_eq!(stack.len(),1);
    let mut live=vec![3u8;65536];
    for r in src.iter_mut().rev(){
        let [k,a,b,c]=*r;
        match k{
            15|16=>{top=events.pop().unwrap();if k==15&&a!=N{live[a as usize]|=top.0;}}
            3..=5=>{
                let (may,must)=condition(top,b);
                if live[a as usize]&may==0{r[0]=0;continue;}
                if k!=3{live[a as usize]&=!must;}
                if b!=N{live[b as usize]|=top.0;}
            }
            12 if b!=N=>live[b as usize]&=!top.1,
            6|7 if b!=N=>live[b as usize]|=top.0,
            8|9 if c!=N=>live[c as usize]|=top.0,
            _=>()
        }
    }
    assert!(events.is_empty());
    src.retain(|r|r[0]!=0);src
}
