/// Fixed 512-bit exact truth tables; unused rows are always zero.
#[derive(Clone,Copy,Debug,PartialEq,Eq,Hash)]
struct Table([u64;8]);
impl Table {
 fn low(x:u64)->Self{let mut v=[0;8];v[0]=x;Self(v)}
 fn bit(&self,row:usize)->u64{assert!(row<512);self.0[row/64]>>(row%64)&1}
 fn set(&mut self,row:usize,value:u64){assert!(row<512&&value<2);self.0[row/64]|=value<<(row%64);}
 fn mask(count:usize)->Self{assert!(count<=9);let mut t=Self::low(0);for row in 0..1usize<<count{t.set(row,1);}t}
 fn xor(self,other:Self)->Self{Self(std::array::from_fn(|i|self.0[i]^other.0[i]))}
 fn and(self,other:Self)->Self{Self(std::array::from_fn(|i|self.0[i]&other.0[i]))}
}
fn support_cap()->usize{9}

impl Truth {
 fn row_mask(count:usize)->Table{Table::mask(count)}
 fn constant(value:bool)->Self{Self{atoms:vec![],table:Table::low(value as u64)}}
 fn is_zero(&self)->bool{self.atoms.is_empty()&&self.table==Table::low(0)}
 fn is_one(&self)->bool{self.atoms.is_empty()&&self.table==Table::low(1)}
 fn complement(&self)->Self{Self{atoms:self.atoms.clone(),table:self.table.xor(Self::row_mask(self.atoms.len()))}}
 fn complements(&self,other:&Self)->bool{self.atoms==other.atoms&&self.table.xor(other.table)==Self::row_mask(self.atoms.len())}
 fn canonical(mut atoms:Vec<u64>,mut table:Table)->Self{
  assert!(atoms.len()<=SUPPORT_CAP);assert!(atoms.windows(2).all(|p|p[0]<p[1]));
  table=table.and(Self::row_mask(atoms.len()));let mut position=0;
  while position<atoms.len(){let bit=1usize<<position;
   let essential=(0..1usize<<atoms.len()).any(|row|row&bit==0&&table.bit(row)!=table.bit(row|bit));
   if essential{position+=1;continue;}
   let mut reduced=Table::low(0);
   for row in 0..1usize<<(atoms.len()-1){let original=(row&(bit-1))|((row&!(bit-1))<<1);reduced.set(row,table.bit(original));}
   atoms.remove(position);table=reduced;
  }Self{atoms,table}
 }
 fn value_in_union(&self,positions:&[usize],row:usize)->u64{let mut own=0;for(i,&j)in positions.iter().enumerate(){own|=((row>>j)&1)<<i;}self.table.bit(own)}
}
