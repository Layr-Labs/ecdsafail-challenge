use std::collections::HashMap;
pub type Key=(u8,u64,u64,u64);
pub struct CancelIndex {
    alive:Vec<bool>,writes:Vec<Vec<usize>>,reads:Vec<Vec<usize>>,keys:HashMap<Key,Vec<usize>>,
}
impl CancelIndex {
    pub fn new()->Self{Self{alive:Vec::new(),writes:Vec::new(),reads:Vec::new(),keys:HashMap::new()}}
    pub fn reset(&mut self){self.alive.clear();for v in self.writes.iter_mut().chain(self.reads.iter_mut()){v.clear();}self.keys.clear();}
    fn top(v:&mut Vec<usize>,alive:&[bool])->Option<usize>{while v.last().is_some_and(|&j|!alive[j]){v.pop();}v.last().copied()}
    pub fn observe(&mut self,k:Key)->Option<usize>{
        // Extra opportunity barrier controls memory only; never deletes a gate.
        if self.alive.len()>=262144{self.reset();}
        let n=(k.1.max(if k.0>0{k.2}else{0}).max(if k.0>1{k.3}else{0})+1)as usize;
        self.writes.resize_with(n.max(self.writes.len()),Vec::new);self.reads.resize_with(n.max(self.reads.len()),Vec::new);
        let prior=Self::top(self.keys.entry(k).or_default(),&self.alive);
        if let Some(j)=prior{
            let mut blocked=Self::top(&mut self.reads[k.1 as usize],&self.alive).is_some_and(|p|p>j);
            for c in [k.2,k.3].iter().take(k.0 as usize){blocked|=Self::top(&mut self.writes[*c as usize],&self.alive).is_some_and(|p|p>j);}
            if !blocked{self.alive[j]=false;self.keys.get_mut(&k).unwrap().pop();return Some(j);}
        }
        let id=self.alive.len();self.alive.push(true);self.keys.get_mut(&k).unwrap().push(id);self.writes[k.1 as usize].push(id);
        for c in [k.2,k.3].iter().take(k.0 as usize){self.reads[*c as usize].push(id);}
        None
    }
}
