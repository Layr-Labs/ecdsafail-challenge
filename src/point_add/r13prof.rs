//! R13-delta659 PRIVATE Toffoli attribution. Counting only: a Mark gate emits no
//! operation, is transparent to every cancellation scan, and only switches the
//! accounting bucket at emission time. Enabled only by R13_PROFILE_OUT.
use super::builder::{B,G};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::Write;

#[derive(Default)]
struct St { stack:Vec<u32>, ctx:Option<u32>, last:[u64;5], acc:BTreeMap<(u32,Vec<u32>),[i64;6]>, roles:BTreeMap<(u8,u32,Vec<u32>,u8),[u64;2]> }
thread_local!{ static ST:RefCell<St>=RefCell::new(St::default()); static DIR:std::cell::Cell<u32>=const{std::cell::Cell::new(0)}; }
static ON:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
pub(crate) fn on()->bool { *ON.get_or_init(||std::env::var_os("R13_PROFILE_OUT").is_some()) }
/// Toggle piece `id` (begin on the first occurrence, end on the second; reverse plays are symmetric).
pub(crate) fn mk(b:&mut B,id:u32) { if on() { b.g(G::Mark(id)); } }
/// Traversal pass 1..4 (T1..T4), column (999 = endpoint).
pub(crate) fn ctx(b:&mut B,pass:u32,col:u32) { if on() { b.g(G::Mark(0x8000_0000|(pass<<16)|col)); } }
pub(crate) fn set_dir(inverse:bool) { DIR.with(|d|d.set(u32::from(inverse))); }
/// OFF-path pass id from the software direction and payload presence.
pub(crate) fn off_pass(payload:bool)->u32 {
    let inv=DIR.with(|d|d.get())==1;
    match (inv,payload) { (false,true)=>1,(true,false)=>2,(false,false)=>3,(true,true)=>4 }
}
fn snap(b:&B)->[u64;5] { let s=b.r13_snap(); [s[0],s[1],s[2],s[3],b.r13_nops] }
impl St {
    fn flush(&mut self,now:[u64;5]) {
        let key=(self.ctx.unwrap_or(0),self.stack.clone());
        let e=self.acc.entry(key).or_insert([0;6]);
        for i in 0..5 { e[i]+=now[i] as i64-self.last[i] as i64; }
        self.last=now;
    }
}
pub(crate) fn mark(b:&B,id:u32) {
    let now=snap(b);
    ST.with(|s|{
        let mut s=s.borrow_mut(); s.flush(now);
        if id&0x8000_0000!=0 {
            if s.ctx==Some(id) { assert!(s.stack.is_empty(),"R13 ctx close with open pieces {:?}",s.stack); s.ctx=None; }
            else { assert!(s.ctx.is_none(),"R13 nested ctx {:x} in {:x?}",id,s.ctx); s.ctx=Some(id); }
            let key=(id,vec![]);s.acc.entry(key).or_insert([0;6])[5]+=1;
        } else if s.stack.last()==Some(&id) { s.stack.pop(); }
        else { s.stack.push(id); let key=(s.ctx.unwrap_or(0),s.stack.clone()); s.acc.entry(key).or_insert([0;6])[5]+=1; }
    });
}
pub(crate) fn dump(b:&B) {
    if !on() { return; }
    let path=std::env::var_os("R13_PROFILE_OUT").unwrap();
    let now=snap(b);
    ST.with(|s|{
        let mut s=s.borrow_mut(); s.flush(now);
        assert!(s.stack.is_empty()&&s.ctx.is_none(),"R13 unbalanced profile at end");
        let mut f=std::io::BufWriter::new(std::fs::File::create(&path).unwrap());
        writeln!(f,"pass\tcol\tpath\ttof\tcond1\tcond2\tcond3\tops\tvisits").unwrap();
        for ((c,stack),v) in &s.acc {
            let (pass,col)=if *c==0 {(0,0)} else {((c>>16)&0x7fff,c&0xffff)};
            let p:Vec<String>=stack.iter().map(|x|x.to_string()).collect();
            writeln!(f,"{pass}\t{col}\t/{}\t{}\t{}\t{}\t{}\t{}\t{}",p.join("/"),v[0],v[1],v[2],v[3],v[4],v[5]).unwrap();
        }
        writeln!(f,"TOTAL\t-\t-\t{}\t{}\t{}\t{}\t{}\t-",now[0],now[1],now[2],now[3],now[4]).unwrap();
    });
}
pub(crate) fn census(op:&crate::circuit::Op,pass:u8,roles:[crate::circuit::QubitId;3]) {
    if pass>4{return;} // pass 0 is the interval between traversals while the pool is live
    static ON:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
    if !*ON.get_or_init(||std::env::var_os("R14_CENSUS_OUT").is_some()){return;}
    static WP5:std::sync::OnceLock<bool>=std::sync::OnceLock::new();
    let wp5=*WP5.get_or_init(||std::env::var("C658_WP5").as_deref()==Ok("1"));
    let m6a=std::env::var("C658_WP5_M6A").as_deref()==Ok("1");
    let m6b=std::env::var("C658_WP5_M6B").as_deref()==Ok("1");
    let ports=[op.q_target,op.q_control1,op.q_control2];
    for (role,&wire) in roles.iter().enumerate(){
        if wire==crate::circuit::NO_QUBIT {continue;}
        if ports.contains(&wire){
            if role==2&&(pass==2||pass==3){panic!("R14_T23_POOL2_TOUCH pass={pass} wire={}",wire.0);}
            if role==2&&std::env::var_os("R14_K5_FORBID_POOL2").is_some(){
                panic!("R14_K5_POOL2_TOUCH pass={pass} wire={}",wire.0);
            }
            ST.with(|s|{let mut s=s.borrow_mut();let col=s.ctx.map_or(0,|x|x&0xffff);
                let path=s.stack.clone();
                let finish=path.contains(&4);
                let changed_map=finish&&path.contains(&20)&&(matches!(col,0..=35|41..=81|114..=202)
                    ||m6a&&matches!(col,36..=40|82..=96)||m6b&&matches!(col,97..=113));
                let changed_tail=finish&&path.contains(&21);
                let changed_counter=finish&&path.contains(&22);
                assert!(std::env::var_os("R14_WP5_ASSERT_POOL2").is_none() || role!=2 || !(wp5&&(pass==1||pass==4)&&
                    (changed_map||changed_tail||changed_counter)),
                    "R14_WP5_POOL2_TOUCH pass={pass} col={col} path={path:?} wire={}",wire.0);
                let e=s.roles.entry((pass,col,path,role as u8)).or_default();
                e[0]+=1;e[1]+=u64::from(matches!(op.kind,crate::circuit::OperationType::CCX|crate::circuit::OperationType::CCZ));});
        }
    }
}
pub(crate) fn census_dump(){
    let Some(path)=std::env::var_os("R14_CENSUS_OUT") else{return;};
    ST.with(|s|{let s=s.borrow();let mut f=std::io::BufWriter::new(std::fs::File::create(path).unwrap());
        writeln!(f,"pass\tcol\tpath\trole\tops\tT").unwrap();
        for ((pass,col,stack,role),n) in &s.roles{
            let p:Vec<String>=stack.iter().map(|x|x.to_string()).collect();
            writeln!(f,"{pass}\t{col}\t/{}\t{role}\t{}\t{}",p.join("/"),n[0],n[1]).unwrap();
        }
    });
}
thread_local!{ static MAP_OK:std::cell::Cell<bool>=const{std::cell::Cell::new(false)}; }
/// Map-internal marks only on tapes that are played plainly (never on paired/controlled replays).
pub(crate) fn set_map_ok(v:bool)->bool { MAP_OK.with(|m|m.replace(v)) }
pub(crate) fn mm(b:&mut B,id:u32) { if MAP_OK.with(|m|m.get()) { mk(b,id); } }
