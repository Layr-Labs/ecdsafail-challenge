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

thread_local!{
    static SHIFT:std::cell::Cell<usize>=const{std::cell::Cell::new(0)};
    static LCOUNTS:std::cell::RefCell<HashMap<String,usize>>=std::cell::RefCell::new(HashMap::new());
}
/// Logical-cap shift: while a booked walk component runs with fewer live wires than the parent had at the
/// same site, every room decision sees the parent's room (cap lowered by the live deficit).
pub(crate) fn shift()->usize {SHIFT.with(|s|s.get())}
pub(crate) fn set_shift(v:usize)->usize {SHIFT.with(|s|s.replace(v))}
pub(crate) fn shift_comp(comp:&str,label:&str)->bool {
    std::env::var("WALK_SHIFT").is_ok_and(|v|v.split(',').any(|x|x==comp||label.contains(&x.replace('_'," "))))
}
/// Non-panicking parent lookup by (tag,key) occurrence; records the actual value in every mode.
pub(crate) fn lookup(tag:&str,key:&str,actual:usize)->usize {
    static TABLE:OnceLock<HashMap<String,Vec<usize>>>=OnceLock::new();
    let table=TABLE.get_or_init(||{
        let mut t:HashMap<String,Vec<(usize,usize)>>=HashMap::new();
        if let Ok(path)=std::env::var("WALK_POLICY") {
            let text=if path=="@parent"{include_str!("walk_data/policy.tsv").to_string()}else{std::fs::read_to_string(path).unwrap()};
            for line in text.lines().filter(|s|s.starts_with("WALK_LOOKUP\t")) {
                let f:Vec<_>=line.split('\t').collect();assert_eq!(f.len(),5);
                t.entry(format!("{}\t{}",f[1],f[3])).or_default().push((f[2].parse().unwrap(),f[4].parse().unwrap()));
            }
        }
        t.into_iter().map(|(k,mut v)|{v.sort_unstable();(k,v.into_iter().map(|x|x.1).collect())}).collect()
    });
    let site=format!("{tag}\t{key}");
    let i=LCOUNTS.with(|cs|{let mut cs=cs.borrow_mut();let n=cs.entry(site.clone()).or_default();let i=*n;*n+=1;i});
    eprintln!("WALK_LOOKUP\t{tag}\t{i}\t{key}\t{actual}");
    if frozen(){table.get(&site).and_then(|v|v.get(i)).copied().unwrap_or(actual)}else{actual}
}
