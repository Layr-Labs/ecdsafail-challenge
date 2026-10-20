use super::builder::Builder;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
pub(super) fn cap()->usize{std::env::var("PEBBLE_HARD_CAP").expect("Independent phase-pebble cap").parse().unwrap()}
pub(super) fn source_ok(acc:&[QubitId],rows:&[Vec<QubitId>],cin:QubitId)->bool{
    if acc.len()!=rows.len(){return false;}let mut used=BTreeSet::from([cin.0]);if !acc.iter().all(|q|used.insert(q.0)){return false;}
    rows.iter().all(|r|{let mut seen=BTreeSet::new();r.iter().all(|q|!used.contains(&q.0)&&seen.insert(q.0))})
}
fn rank(a:&[QubitId],b:&[QubitId])->usize{if a.is_empty()||b.is_empty()||a.iter().map(|q|q.0).collect::<BTreeSet<_>>()==b.iter().map(|q|q.0).collect::<BTreeSet<_>>(){1}else{2}}
#[derive(Clone)]struct State{cost:usize,drops:Vec<usize>}
fn put(dst:&mut Option<State>,next:State){if dst.as_ref().is_none_or(|old|(next.cost,&next.drops)<(old.cost,&old.drops)){*dst=Some(next);}}
pub(super) fn choose(rows:&[Vec<QubitId>],need:usize,paused:bool,allowed:&[bool])->Option<Vec<usize>>{
    let n=rows.len();if n<3||allowed.len()!=n{return None;}let m=n-2+usize::from(paused);if need>m{return None;}if need==0{return Some(Vec::new());}let room=m-need;
    let mut dp=vec![vec![None::<State>;2];need+1];dp[0][0]=Some(State{cost:0,drops:Vec::new()});
    for j in 1..m{
        let mut next=vec![vec![None::<State>;2];need+1];
        for k in 0..=need{for last in 0..2{if let Some(state)=&dp[k][last]{put(&mut next[k][0],state.clone());if k<need&&last==0&&allowed[j]&&j+1-k<=room{let mut s=state.clone();s.cost+=rank(&rows[j-1],&rows[j]);s.drops.push(j);put(&mut next[k+1][1],s);}}}}
        dp=next;
    }
    dp[need].iter().flatten().min_by(|a,b|(a.cost,&a.drops).cmp(&(b.cost,&b.drops))).map(|s|s.drops.clone())
}
pub(super) fn plain(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
    let n=acc.len();if cap()>=1234||n<3||ones.len()!=n||!source_ok(acc,rows,cin){return false;}
    let need=(c.active_qubits()as usize+n-2).saturating_sub(cap());if need==0{return false;}
    let Some(drops)=choose(rows,need,false,&vec![true;n])else{return false;};let before=c.op_count();let active=c.active_qubits();
    assert!(super::phase_pebble::add_with_hook(c,acc,rows,ones,cin,&drops,hook));
    eprintln!("PHASE_PEBBLE_PLAIN\t{}\t{before}\t{}\t{active}\t{n}\t{need}\t{drops:?}",c.current_phase(),c.op_count());true
}

#[cfg(test)]mod tests{
    use super::*;
    #[test]fn dynamic_program_matches_independent_enumerated_lifetime_peak_and_cost(){
        for n in 3usize..=12{for paused in[false,true]{let m=n-2+usize::from(paused);for pattern in 0..3{let rows:Vec<_>=(0..n).map(|i|if pattern==0{vec![QubitId(100)]}else if pattern==1&&i%3==0{vec![]}else{vec![QubitId((100+i)as u64)]}).collect();
            for mask_kind in 0..3{let allowed:Vec<_>=(0..n).map(|i|mask_kind==0||mask_kind==1&&i%2==0||mask_kind==2&&i%3!=1).collect();for need in 1..=m{
                let mut expected:Option<(usize,Vec<usize>)>=None;
                for mask in 1usize..1<<(m-1){let ds:Vec<_>=(1..m).filter(|&i|mask>>(i-1)&1!=0).collect();if ds.len()!=need||ds.iter().any(|&i|!allowed[i])||ds.windows(2).any(|p|p[1]==p[0]+1){continue;}
                    let(mut active,mut peak)=(0usize,0usize);for i in 1..=m{active+=1;peak=peak.max(active);if ds.contains(&(i-1)){active-=1;}}if peak>m-need{continue;}
                    let candidate=(ds.iter().map(|&j|rank(&rows[j-1],&rows[j])).sum(),ds);if expected.as_ref().is_none_or(|old|&candidate<old){expected=Some(candidate);}
                }
                assert_eq!(choose(&rows,need,paused,&allowed),expected.map(|x|x.1),"n={n} paused={paused} pattern={pattern} mask={mask_kind} need={need}");
            }}
        }}}
    }
}
pub(super) fn plain_optional(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:Option<QubitId>,hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
    if cap()>=1234||acc.len()!=rows.len()||acc.len()!=ones.len(){return false;}
    let trim=if cin.is_none(){rows.iter().zip(ones).take_while(|(r,one)|r.is_empty()&&!**one).count()}else{0};
    let acc=&acc[trim..];let rows=&rows[trim..];let ones=&ones[trim..];let n=acc.len();if n<3{return false;}
    let need=(c.active_qubits()as usize+n-2).saturating_sub(cap());if need==0{return false;}
    let drops=if let Some(q)=cin{
        if !super::phase_pebble::valid_mode(acc,rows,ones,q,&[],false){return false;}
        let Some(ds)=choose(rows,need,false,&vec![true;n])else{return false;};ds
    }else{
        if !super::zero_carry::valid(acc,rows,ones,&[]){return false;}
        let Some(ds)=choose(&rows[1..],need,false,&vec![true;n-1])else{return false;};ds
    };
    let before=c.op_count();let active=c.active_qubits();
    if let Some(q)=cin{assert!(super::phase_pebble::add_with_hook(c,acc,rows,ones,q,&drops,&mut|c,i,q|hook(c,i+trim,q)));}
    else{assert!(super::zero_carry::add(c,acc,rows,ones,&drops,&mut|c,i,q|hook(c,i+trim,q)));}
    eprintln!("PHASE_OPTIONAL\t{}\t{before}\t{}\t{active}\t{n}\t{need}\t{}\t{drops:?}",c.current_phase(),c.op_count(),usize::from(cin.is_some()));true
}
