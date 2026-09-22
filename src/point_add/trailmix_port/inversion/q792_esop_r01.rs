//! Exact ESOP synthesis: optimal four-input cube tables, bounded Davio/Shannon
//! composition for five/six inputs. Every returned truth is exhaustively checked.
use std::collections::HashMap;
type Cubes=Vec<(usize,usize)>;
const TABLE:&[u8;3997696]=include_bytes!("q792_esop4_r01.bin");
fn cube(i:usize)->(usize,usize,u16){let(mut n,mut m,mut v)=(i,0,0);for b in 0..4{let t=n%3;n/=3;if t!=0{m|=1<<b;if t==2{v|=1<<b;}}}let truth=(0..16).filter(|&x|x&m==v).fold(0u16,|t,x|t|(1<<x));(m,v,truth)}
fn index(k:usize)->usize{match k{0=>0,1=>1,2=>3,_=>6+(4*k-12)/2}}
fn small(truth:u64,k:usize)->Cubes{let mut t=truth as u16;let mut out=Vec::new();while t!=0{let i=TABLE[65536*index(k)+t as usize]as usize;assert!(i<81);let(m,v,f)=cube(i);out.push((m,v));t^=f;assert!(out.len()<64);}out}
fn cost(p:&[(usize,usize)],k:usize)->usize{p.iter().map(|&(m,v)|{let n=k+m.count_ones()as usize;(if n<=2{1}else{4*n-8})+2*(m^v).count_ones()as usize}).sum()}
fn trim(p:Cubes)->Cubes{let mut p=p;p.sort_unstable();let mut out=Vec::new();for v in p{if out.last()==Some(&v){out.pop();}else{out.push(v);}}out}
fn lift(p:Cubes,bit:usize,value:Option<bool>)->Cubes{p.into_iter().map(|(m,v)|{let lo=(1<<bit)-1;let mut m=(m&lo)|((m&!lo)<<1);let mut v=(v&lo)|((v&!lo)<<1);if let Some(b)=value{m|=1<<bit;if b{v|=1<<bit;}}(m,v)}).collect()}
fn solve(n:usize,t:u64,k:usize,memo:&mut HashMap<(usize,u64,usize),Cubes>)->Cubes{
 if t==0{return Vec::new();}if let Some(p)=memo.get(&(n,t,k)){return p.clone();}let out=if n==4{small(t,k)}else{
  let mut best:Option<Cubes>=None;for b in 0..n{let mut f=[0u64;2];for x in 0..1usize<<(n-1){let low=(1<<b)-1;let y=(x&low)|((x&!low)<<1);for v in 0..2{f[v]|=((t>>(y|(v<<b)))&1)<<x;}}
   for mode in 0..3{let(mut a,bb)=if mode<2{let base=mode;let a=lift(solve(n-1,f[base],k,memo),b,None);let bb=lift(solve(n-1,f[0]^f[1],k+1,memo),b,Some(base==0));(a,bb)}else{(lift(solve(n-1,f[0],k+1,memo),b,Some(false)),lift(solve(n-1,f[1],k+1,memo),b,Some(true)))};a.extend(bb);let p=trim(a);if best.as_ref().is_none_or(|v|cost(&p,k)<cost(v,k)){best=Some(p);}}
  }best.unwrap()
 };memo.insert((n,t,k),out.clone());out
}
pub(super) fn plan(n:usize,truth:&[bool],k:usize)->Option<Cubes>{
 if !(4..=6).contains(&n)||k+n>22{return None;}let t=truth.iter().enumerate().fold(0u64,|t,(i,&b)|t|((b as u64)<<i));

 static CAPTURE:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
 if *CAPTURE.get_or_init(||std::env::var("FOLD20_GPU_CAPTURE").ok().as_deref()==Some("1")) {
  static SEEN:std::sync::OnceLock<std::sync::Mutex<std::collections::BTreeSet<(usize,u64,usize)>>>=std::sync::OnceLock::new();
  if SEEN.get_or_init(||std::sync::Mutex::new(std::collections::BTreeSet::new())).lock().unwrap().insert((n,t,k)){eprintln!("GPU_PREDICATE n={n} k={k} truth={t:016x}");}
 }
 static CACHE:std::sync::OnceLock<std::sync::Mutex<HashMap<(usize,u64,usize),Cubes>>>=std::sync::OnceLock::new();let mut cache=CACHE.get_or_init(||std::sync::Mutex::new(HashMap::new())).lock().unwrap();let p=solve(n,t,k,&mut cache);
 for(x,&want)in truth.iter().enumerate(){assert_eq!(p.iter().fold(false,|v,&(m,b)|v^(x&m==b)),want,"ESOP truth mismatch n={n} x={x}");}Some(p)
}
pub fn run(){
 let mut cases=0usize;for k in 0..=20{for t in 0..65536u64{let p=small(t,k);let mut got=0u64;for x in 0..16{if p.iter().fold(false,|v,&(m,b)|v^(x&m==b)){got|=1<<x;}}assert_eq!(got,t);cases+=1;}}
 let mut seed=0x792e50fu64;let mut more=0;for n in [5,6]{for k in [0,1,2,6,12]{for _ in 0..64{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;let truth:Vec<_>=(0..1<<n).map(|x|seed>>x&1!=0).collect();plan(n,&truth,k).unwrap();more+=1;}}}
 eprintln!("FOLD20_ESOP_TRUTH_PASS exhaustive4={cases} composed5and6={more} every_address=true no_sample_fit=true");
}

pub(super) fn active()->bool{super::q792_lifecycle_r01::enabled()||std::env::var("LOWQ_Q793_NATIVE_MODE").ok().is_some_and(|s|s.starts_with("fold20"))}
/// Pure target XOR on a real zero scratch, or a matched routing extension.
pub(super) fn paired(c:&mut crate::point_add::trailmix_port::circuit::Circuit,word:&[&crate::point_add::trailmix_port::circuit::QReg],truth:Vec<bool>,prefix:&[(&crate::point_add::trailmix_port::circuit::QReg,bool)],out:&crate::point_add::trailmix_port::circuit::QReg,scratch:&crate::point_add::trailmix_port::circuit::QReg){
 let start=c.b.ops.len();let(pol,terms)=super::metadata_muxlease::swap_terms(truth.clone(),word.len());for(i,q)in word.iter().enumerate(){if pol>>i&1!=0{c.x(q);}}for m in terms{let mut cs=prefix.to_vec();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));super::paired_clean_mcx::toggle(c,&cs,out,scratch);}for(i,q)in word.iter().enumerate().rev(){if pol>>i&1!=0{c.x(q);}}let baseline=c.b.ops.split_off(start);
 if let Some(mut cubes)=plan(word.len(),&truth,prefix.len()){
  let mut frame=0usize;while !cubes.is_empty(){let pick=(0..cubes.len()).min_by_key(|&i|{let(m,v)=cubes[i];((frame^(m^v))&m).count_ones()}).unwrap();let(m,v)=cubes.remove(pick);let toggles=(frame^(m^v))&m;for(i,q)in word.iter().enumerate(){if toggles>>i&1!=0{c.x(q);}}frame^=toggles;let mut cs=prefix.to_vec();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));super::paired_clean_mcx::toggle(c,&cs,out,scratch);}for(i,q)in word.iter().enumerate(){if frame>>i&1!=0{c.x(q);}}
  if c.b.ops.len()-start>=baseline.len(){c.b.ops.truncate(start);c.b.ops.extend(baseline);}
 }else{c.b.ops.extend(baseline);}
}
