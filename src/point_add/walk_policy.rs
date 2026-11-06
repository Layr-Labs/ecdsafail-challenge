//! Research-only capture of parent planning rooms. The physical cap remains
//! independent: exact adders may borrow operand wires while every approximate
//! boundary and its predicate retain the parent's position.
use std::collections::HashMap;
use std::sync::OnceLock;
thread_local!{static COUNTS:std::cell::RefCell<HashMap<String,usize>>=std::cell::RefCell::new(HashMap::new());}
pub(crate) fn frozen()->bool {std::env::var_os("WALK_POLICY").is_some()}
pub(crate) fn room(tag:&str,key:&str,actual:usize)->usize {
    let i=COUNTS.with(|cs|{let mut cs=cs.borrow_mut();let n=cs.entry(tag.to_string()).or_default();let i=*n;*n+=1;i});
    static TABLE:OnceLock<HashMap<(String,usize),(String,usize)>>=OnceLock::new();
    let table=TABLE.get_or_init(||{
        let mut t=HashMap::new();if let Ok(path)=std::env::var("WALK_POLICY") {
            for line in (if path=="@parent"{include_str!("walk_data/policy.tsv").to_string()}else{std::fs::read_to_string(path).unwrap()}).lines().filter(|s|s.starts_with("WALK_POLICY\t")) {
                let f:Vec<_>=line.split('\t').collect();assert_eq!(f.len(),5);
                assert!(t.insert((f[1].into(),f[2].parse().unwrap()),(f[3].into(),f[4].parse().unwrap())).is_none());
            }
        }t
    });
    let room=if frozen(){
        let site=format!("{tag}:{key}");let occurrence=COUNTS.with(|cs|{let mut cs=cs.borrow_mut();let n=cs.entry(site.clone()).or_default();let i=*n;*n+=1;i});
        let mut matches:Vec<_>=table.iter().filter(|((t,_),(k,_))|t==tag&&k==key).map(|((_,i),(_,r))|(*i,*r)).collect();matches.sort_unstable();
        matches.get(occurrence).unwrap_or_else(||panic!("missing parent site {site} occurrence {occurrence}")).1
    }else{actual};
    eprintln!("WALK_POLICY\t{tag}\t{i}\t{key}\t{room}");room
}
pub(crate) fn physical_cap()->usize {
    static CAP:OnceLock<Option<usize>>=OnceLock::new();
    let requested=*CAP.get_or_init(||std::env::var("WALK_PHYS").ok().map(|s|s.parse().unwrap()));
    let logical=super::pingpong::heo_hooks::cap();
    requested.map_or(logical,|cap|cap.min(logical))
}
