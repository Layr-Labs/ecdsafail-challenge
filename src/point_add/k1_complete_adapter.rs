//! Exact raw-recipe annotations and independent test adapters for complete K1.
use super::*;
use crate::point_add::k1_complete_caller::Layout;
use std::cell::RefCell;
#[derive(Clone)]
pub(crate) struct Tag {pub name:&'static str,pub tape:Vec<G>,pub ports:Vec<QubitId>,pub geometry:Option<Geometry>}
#[derive(Clone)]
pub(crate) struct Geometry {source:Vec<QubitId>,target:Vec<QubitId>,padding:Vec<QubitId>,donors:Vec<QubitId>,controls:Vec<QubitId>}
#[derive(Default)]
struct Collector {tags:Vec<Tag>,index:std::collections::HashMap<u64,Vec<usize>>,gates:usize,ports:usize}
thread_local!{static TAGS:RefCell<Option<Collector>>=const{RefCell::new(None)};}
pub(crate) fn start(){TAGS.with(|x|{assert!(x.borrow().is_none());*x.borrow_mut()=Some(Collector::default());});}
pub(crate) fn take()->Vec<Tag>{TAGS.with(|x|x.borrow_mut().take().expect("annotation capture absent").tags)}
fn intern(name:&'static str,tape:&[G],ports:&[QubitId])->Option<usize>{
    use std::hash::{Hash,Hasher};
    if !enabled()||tape.is_empty(){return None;}
    let mut hash=std::collections::hash_map::DefaultHasher::new();name.hash(&mut hash);
    for g in tape{key(*g).hash(&mut hash);}for q in ports{q.0.hash(&mut hash);}let hash=hash.finish();
    TAGS.with(|x|{let mut x=x.borrow_mut();let c=x.as_mut().unwrap();
        if let Some(bucket)=c.index.get(&hash){if let Some(&i)=bucket.iter().find(|&&i|c.tags[i].name==name&&c.tags[i].tape==tape&&c.tags[i].ports==ports){return Some(i);}}
        assert!(tape.len()<=2_000_000&&c.gates+tape.len()<=4_000_000&&c.ports+ports.len()<=4_000_000,"K1_RESOURCE annotation cap");
        let i=c.tags.len();c.gates+=tape.len();c.ports+=ports.len();
        c.tags.push(Tag{name,tape:tape.to_vec(),ports:ports.to_vec(),geometry:None});c.index.entry(hash).or_default().push(i);Some(i)
    })
}
pub(crate) fn tag(name:&'static str,tape:&[G],ports:&[QubitId]){let _=intern(name,tape,ports);}
pub(crate) fn inv(g:G)->G{match g{G::AndC(a,b,t)=>G::AndU(a,b,t),G::AndU(a,b,t)=>G::AndC(a,b,t),G::RowAdd(id,d)=>G::RowAdd(id,!d),G::DeferredErase(id,d)=>G::DeferredErase(id,!d),x=>x}}
pub(crate) fn inverse(tape:&[G])->Vec<G>{tape.iter().rev().map(|g|inv(*g)).collect()}
fn key(g:G)->[u64;4]{match g{
    G::X(a)=>[0,a.0,0,0],G::Cx(a,b)=>[1,a.0,b.0,0],G::Ccx(a,b,c)=>[2,a.0,b.0,c.0],G::Cz(a,b)=>[3,a.0,b.0,0],G::Swap(a,b)=>[4,a.0,b.0,0],
    G::AndC(a,b,c)=>[5,a.0,b.0,c.0],G::AndU(a,b,c)=>[6,a.0,b.0,c.0],G::XIf(a,b)=>[7,a.0,b.0,0],G::ZIf(a,b)=>[8,a.0,b.0,0],
    G::RowAdd(id,d)=>[9,id as u64,d as u64,0],G::DeferredErase(id,d)=>[10,id as u64,d as u64,0],G::Mark(id)=>[11,id as u64,0,0],}}
#[derive(Clone,Debug)]
pub(crate) struct Span {pub begin:usize,pub end:usize,pub tag:usize,pub back:bool}
pub(crate) fn locate(tape:&[G],tags:&[Tag])->Vec<Span>{locate_inner(tape,tags,false)}
pub(crate) fn locate_boundaries(tape:&[G],tags:&[Tag])->Vec<Span>{locate_inner(tape,tags,true)}
fn locate_inner(tape:&[G],tags:&[Tag],boundary:bool)->Vec<Span>{
    let mut prefixes=std::collections::HashMap::<[u64;4],Vec<(usize,bool)>>::new();
    for(i,t)in tags.iter().enumerate(){if boundary&&!matches!(t.name,"pad"|"donor"|"zero"|"host0"|"host1"){continue;}prefixes.entry(key(t.tape[0])).or_default().push((i,false));prefixes.entry(key(inv(*t.tape.last().unwrap()))).or_default().push((i,true));}
    let mut spans=vec![];let mut seen=std::collections::BTreeSet::new();
    for(i,g)in tape.iter().enumerate(){if let Some(candidates)=prefixes.get(&key(*g)){for &(tag,back)in candidates{
        let r=&tags[tag].tape;if i+r.len()>tape.len(){continue;}
        let same=if back{tape[i..i+r.len()].iter().copied().eq(r.iter().rev().map(|g|inv(*g)))}else{tape[i..i+r.len()]==r[..]};
        if same&&seen.insert((i,i+r.len(),tag)){assert!(spans.len()<2_000_000,"K1_RESOURCE boundary count");spans.push(Span{begin:i,end:i+r.len(),tag,back});}
    }}}spans.sort_by_key(|s|(s.begin,s.end));spans
}
pub(crate) fn entry(b:&mut B,l:&Layout,native:bool,parent:bool)->Vec<G>{
    let scratch:Vec<_>=l.meta.sum.iter().copied().chain([l.pool[1],l.pool[2]]).collect();
    let dirty:Vec<_>=l.fd.ring.iter().chain(&l.fd.q).chain(&l.meta.y).chain(&scratch).copied().collect();
    if parent{
        if native{super::super::super::direct_map_entry_native::record(b,&l.fd.ring,&l.fd.q,&l.meta.y,&scratch,l.pool[3],l.fd.ph,l.pool[0],&dirty)}
        else{super::super::entry_record(b,&l.fd.ring,&l.fd.q,&l.meta.y,&scratch,l.pool[3],128,1,128,&dirty,false)}
    }else{
        let actual=super::entry::entry(b,&l.fd.ring,&l.fd.q,&l.meta.y,&scratch,native.then_some((l.fd.ph,l.pool[0])),&dirty);
        if enabled(){let observed=observed_entry::entry(b,&l.fd.ring,&l.fd.q,&l.meta.y,&scratch,native.then_some((l.fd.ph,l.pool[0])),&dirty);assert_eq!(actual,observed,"literal entry observer identity");}
        actual
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Fault {Virtual,N2Direction,Adjustment,FrameMissing,FrameDirection,FrameRecipe,OuterControl,ProbeReturn,TErase,DReturn,PhBracket,Host,Release}
pub(crate) fn mutate(tape:&[G],tags:&[Tag],fault:Fault,l:&Layout)->Vec<G>{
    let spans=locate(tape,tags);let choose=|name:&str,back:Option<bool>,last:bool|{
        let found:Vec<_>=spans.iter().filter(|s|tags[s.tag].name==name&&back.is_none_or(|b|s.back==b)).collect();
        assert!(!found.is_empty(),"required actual recipe absent: {name} fault={fault:?}");
        (*if last{found.last().unwrap()}else{found.first().unwrap()}).clone()
    };
    let mut result=tape.to_vec();
    match fault{
        Fault::Virtual=>{let mut ranges:Vec<_>=spans.iter().filter(|s|tags[s.tag].name=="virtual"&&!s.back).map(|s|(s.begin,s.end)).collect();ranges.sort();ranges.dedup();assert!(!ranges.is_empty());for(a,z)in ranges.into_iter().rev(){result.drain(a..z);}},
        Fault::N2Direction=>{let s=choose("n2rot",Some(false),false);result.splice(s.begin..s.end,inverse(&tape[s.begin..s.end]));},
        Fault::Adjustment=>{let s=choose("adjust",Some(false),false);result.drain(s.begin..s.end);},
        Fault::FrameMissing=>{let s=choose("frame",Some(true),true);result.drain(s.begin..s.end);},
        Fault::FrameDirection=>{let s=choose("frame",Some(true),true);result.splice(s.begin..s.end,tags[s.tag].tape.clone());},
        Fault::FrameRecipe=>{let s=choose("frame",Some(false),false);result.insert(s.end,G::X(l.fd.ring[0]));},
        Fault::OuterControl=>{
            if spans.iter().any(|s|tags[s.tag].name=="controlled-middle"){
                let s=choose("controlled-middle",Some(false),false);let control=l.pool[0];
                for g in &mut result[s.begin..s.end]{*g=match *g{
                    G::Cx(c,t) if c==control=>G::X(t),G::Ccx(a,c,t) if a==control=>G::Cx(c,t),G::Ccx(a,c,t) if c==control=>G::Cx(a,t),
                    G::AndC(a,c,t)|G::AndU(a,c,t) if a==control=>G::Cx(c,t),G::AndC(a,c,t)|G::AndU(a,c,t) if c==control=>G::Cx(a,t),other=>other};}
            }else{
                let mut ranges:Vec<_>=spans.iter().filter(|s|tags[s.tag].name=="active-off").map(|s|(s.begin,s.end)).collect();
                ranges.sort();ranges.dedup();assert!(!ranges.is_empty());
                for(i,(a,z))in ranges.iter().enumerate(){assert!(i==0||*a>=ranges[i-1].1);assert!(a<z);}
                for(a,z)in ranges.into_iter().rev(){result.drain(a..z);}
            }
        },
        Fault::ProbeReturn=>{let s=choose("probe",Some(true),true);result.drain(s.begin..s.end);},
        Fault::TErase=>{let s=choose("tout",None,true);result.drain(s.begin..s.end);},
        Fault::DReturn=>{let s=choose("dswap",None,true);result.drain(s.begin..s.end);},
        Fault::PhBracket=>{let at=result.iter().position(|g|*g==G::X(l.fd.ph)).expect("actual PH bracket");result.remove(at);},
        Fault::Host=>{result.insert(0,G::Swap(l.fd.q[114],l.p[2]));result.push(G::Swap(l.fd.q[114],l.p[2]));},
        Fault::Release=>{let at=result.iter().rposition(|g|match *g{G::X(t)|G::Cx(_,t)|G::Ccx(_,_,t)|G::AndC(_,_,t)|G::AndU(_,_,t)=>t==l.fd.q[114],_=>false}).expect("actual host release literal");result.remove(at);},
    }
    assert!(result!=tape,"unchanged mutation {fault:?}");result
}
/// Structural controls accept only the exact typed failure. Unrelated panics
/// propagate, and a control must reject before any actual native operation.
pub(crate) fn expect(error:Error,body:impl FnOnce()){
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(body));
    match result{Err(p)=>match p.downcast::<Error>(){Ok(actual)=>assert_eq!(*actual,error),Err(p)=>std::panic::resume_unwind(p)},Ok(())=>panic!("missing structural rejection {error:?}")}
}
thread_local!{static FAULT:std::cell::Cell<Option<Fault>>=const{std::cell::Cell::new(None)};}
pub(crate) fn omits(f:Fault)->bool{FAULT.with(|x|x.get()==Some(f))}
pub(crate) fn with_fault<R>(f:Fault,body:impl FnOnce()->R)->R{
    FAULT.with(|x|assert!(x.replace(Some(f)).is_none()));
    struct Reset;impl Drop for Reset{fn drop(&mut self){FAULT.with(|x|x.set(None));}}
    let _reset=Reset;body()
}
pub(crate) fn enabled()->bool{TAGS.with(|x|x.borrow().is_some())}
pub(crate) fn frame_pair_guard(){
    let mut b=crate::point_add::k1_complete_caller::builder();let l=Layout::allocate(&mut b);
    let g=G::Ccx(l.fd.q[1],l.fd.q[2],l.fd.ring[0]);let bad=Captured{tape:vec![g,G::X(l.fd.ring[0])],frame:vec![g],first:0,second:1};
    expect(Error::FrameRecipe,||paired_clean(&mut b,&bad,l.pool[0],l.fd.ph));assert!(b.ops.is_empty());
}

pub(crate) fn pad_tag(tape:&[G],source:&[QubitId],target:&[QubitId],padding:&[QubitId],donors:&[QubitId],controls:&[QubitId]){
    if !enabled(){return;}
    let ports:Vec<_>=source.iter().chain(padding).chain(donors).chain(controls).copied().collect();
    let i=intern("pad",tape,&ports).unwrap();
    TAGS.with(|x|{let mut x=x.borrow_mut();let t=&mut x.as_mut().unwrap().tags[i];
        t.geometry=Some(Geometry{source:source.to_vec(),target:target.to_vec(),padding:padding.to_vec(),donors:donors.to_vec(),controls:controls.to_vec()});});
}
pub(crate) fn geometry(tags:&[Tag],l:&Layout,column:usize)->usize {
    use sha3::{Digest,Sha3_256};
    let canonical=|q:QubitId|->u64{if let Some(i)=l.fd.ring.iter().position(|x|*x==q){i as u64}
        else if let Some(i)=l.fd.q.iter().position(|x|*x==q){257+i as u64}
        else if q==l.meta.y[6]{649}else{panic!("frame geometry has unexpected owner {}",q.0)}};
    let mut hash=Sha3_256::new();let mut count=0;
    for g in tags.iter().filter_map(|t|t.geometry.as_ref()).filter(|g|g.source.first()==Some(&l.fd.q[1])){
        let n=g.source.len();let h=g.target.len()-n;let i=(canonical(*g.controls.last().unwrap())+1)%257;
        for x in [i,n as u64,h as u64,u64::from(g.controls.len()==2)]{hash.update(x.to_le_bytes());}
        for ports in [&g.source,&g.target,&g.controls,&g.padding,&g.donors]{hash.update((ports.len()as u64).to_le_bytes());for q in ports{hash.update(canonical(*q).to_le_bytes());}}
        let surplus=256-g.target.len()-g.padding.len()-g.donors.len();hash.update((surplus as u64).to_le_bytes());count+=1;
    }
    let expected=FRAME_GEOMETRY.iter().find(|x|x.0==column).expect("missing exact reviewed frame column");
    assert_eq!(count,expected.1);assert_eq!(format!("{:x}",hash.finalize()),expected.2,"runtime full row geometry c{column}");count
}
// SHA3-256 of every ordered row field in the sealed predecessor ledger.
const FRAME_GEOMETRY:&[(usize,usize,&str)]=&[
    (36,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (37,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (38,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (39,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (40,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (41,254,"aaee14e5acb828bc30e8027a5a860271db6a3285b18950f3c47be9194520f264"),
    (42,253,"d0a583da59595f3ff400a8d7d80bca42d3d34a692bce4c548ffbab4bcaf042c0"),
    (43,251,"3b5f989e5b92b8615dceb94cac85023f43de047f9644e0c437980f5b1957ed67"),
    (44,250,"a7a7d31c23af292584b3a5d0813d33ec348458fe212eb11ec196587d812a08c7"),
    (45,249,"72c5845825d1c3cdea06bdec081ae3062ec6fde83fc00c658235711841be5638"),
    (46,248,"7325854721774f5255ca547aa3fb0498f9bc47d24e208a85eb5c48aca7d6d076"),
    (47,246,"d0687ffb93f57b320a8a5ab417092885be0544ed2a608a6f6981bbe36a07d142"),
    (48,246,"d0687ffb93f57b320a8a5ab417092885be0544ed2a608a6f6981bbe36a07d142"),
    (49,245,"04e8343fd32d9db8565111c3b6708899dff914cc574c3293f21922fe0497a319"),
    (50,243,"44d6e194f58b620d2e97cab11eeb979c9f687262c9d086e364d714ac7ab5d7cd"),
    (51,242,"aa41b190b5d51ed96c78b72bd122e3344fb5e1035d2e06079115c54d6de83a2c"),
    (52,242,"aa41b190b5d51ed96c78b72bd122e3344fb5e1035d2e06079115c54d6de83a2c"),
    (53,239,"10e4ab4ef40c942309a9a8301390970ee438129a37565ff5d49f975768d10dbc"),
    (54,238,"3ff3efaf150621ed2163b6fc428dc3c1dd2b9b6709109e874ebb69f5bd8452ba"),
    (55,237,"b8c663bbdcf847aa182808f47f644316229d57a23cd124984e6424e07bc669ac"),
    (56,236,"924c092cc6ef2d93de76230f3c6b9dd07bf8002de0fd6bfac61b54f70f33e96a"),
    (57,236,"924c092cc6ef2d93de76230f3c6b9dd07bf8002de0fd6bfac61b54f70f33e96a"),
    (58,232,"147a6271f3bcf904a25718ff3679af2325876a4925c3f9d78e02376c3e5f0c1b"),
    (59,231,"3326def842865407b8df5fc0bff5bcd4a71b100739bd491369f2438d5cefeea3"),
    (60,230,"1ee818b1e201e9957bdf9a84654380068daacf5d5db5a8736765bd5695611488"),
    (61,230,"1ee818b1e201e9957bdf9a84654380068daacf5d5db5a8736765bd5695611488"),
    (62,228,"521acdb0a90eaeeec31101bdab6b3af071c29ba7e9e98d28bb6d0e04828a55be"),
    (63,226,"2219f74bf88bb171e34126b71c883ff12385726442a546e32e8d90206762de1e"),
    (64,224,"458203dd2a1b8bff62ce8925a975383de2363c583f749fd1c74683701b818d14"),
    (65,223,"2e4d18edbcaf6b40d04d043568dc2af3f250d648cf3f1af27747242bffdf557c"),
    (66,224,"458203dd2a1b8bff62ce8925a975383de2363c583f749fd1c74683701b818d14"),
    (67,225,"f41f044b1a7077b04a8cb5f6b03973f55b04b61d540138b36847eabc8cf6c277"),
    (68,226,"2219f74bf88bb171e34126b71c883ff12385726442a546e32e8d90206762de1e"),
    (69,233,"66f3e136595467d8bd07373515665f5814190da992a1426d0a6d6a9e426201f1"),
    (70,234,"eec558deb7497e806cc5718066c08dce1d99bf7502caf34d921c5ed981091339"),
    (71,235,"49eef6df1aeacc5bf9f87f0fb157bec836766e47256c2e38dd0aa84f4612b12d"),
    (72,235,"49eef6df1aeacc5bf9f87f0fb157bec836766e47256c2e38dd0aa84f4612b12d"),
    (73,240,"840eaa8101bd25685acc163baa743197f243e2196c1f29e0fc78e4238c6f55d3"),
    (74,241,"92e28a7522669275480d78c14f67084081864153daf41c2285c29dc4ff5b3cb2"),
    (75,242,"aa41b190b5d51ed96c78b72bd122e3344fb5e1035d2e06079115c54d6de83a2c"),
    (76,243,"44d6e194f58b620d2e97cab11eeb979c9f687262c9d086e364d714ac7ab5d7cd"),
    (77,245,"04e8343fd32d9db8565111c3b6708899dff914cc574c3293f21922fe0497a319"),
    (78,245,"04e8343fd32d9db8565111c3b6708899dff914cc574c3293f21922fe0497a319"),
    (79,251,"3b5f989e5b92b8615dceb94cac85023f43de047f9644e0c437980f5b1957ed67"),
    (80,253,"d0a583da59595f3ff400a8d7d80bca42d3d34a692bce4c548ffbab4bcaf042c0"),
    (81,254,"aaee14e5acb828bc30e8027a5a860271db6a3285b18950f3c47be9194520f264"),
    (82,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (83,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (84,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (85,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (86,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (87,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (88,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (89,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (90,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (91,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (92,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (93,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (94,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (95,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (96,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (97,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (98,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (99,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (100,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (101,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (102,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (103,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (104,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (105,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (106,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (107,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (108,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (109,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (110,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (111,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (112,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (113,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (114,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (115,255,"6f4c00c217459ab95c335c6ddcab7aaa723d476cadf2d7d1d2f8fc126e3a2da3"),
    (116,255,"af0e81098cdbc5ebf531a39799196d2e015241a8f7ccb170e998e1a60328d00b"),
    (117,255,"6659b5bef7425a86a2a5a3f49ac9f8b207d2be91023a1bd8807b6ed03472e267"),
    (118,255,"37985a7f94e891304e4e4397e2f931c333399f9b6a07de3df514387e1fd7f24c"),
    (119,255,"869f26421fe510be666778a0fd7745df08d59aa9e3b3dba28948b2766ee1ab4f"),
];
pub(crate) fn retained_bytes(tags:&Vec<Tag>)->usize{
    use std::mem::size_of;
    tags.capacity()*size_of::<Tag>()+tags.iter().map(|t|t.tape.capacity()*size_of::<G>()+t.ports.capacity()*size_of::<QubitId>()
        +t.geometry.as_ref().map_or(0,|g|[&g.source,&g.target,&g.padding,&g.donors,&g.controls].iter().map(|p|p.capacity()*size_of::<QubitId>()).sum::<usize>())).sum::<usize>()
}

mod observed_entry {
//! Repaired K1 N1/N2. Clean-output encoders, not arbitrary-output XOR oracles.
use super::*;

fn active_xor(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    lit(b,controls,target,dirty);
    if let Some((ph,c))=nand {
        let mut off=controls.to_vec();off.extend([(ph,false),(c,false)]);
        lit(b,&off,target,dirty);
    }
}

fn binary(b:&mut B,word:&[QubitId],out:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require(word.len()==128&&out.len()==7,Error::Shape);
    record(b,|b|{
        let mut swaps=Vec::new();
        for j in (0..7).rev() {
            let h=1usize<<j;
            if h>1 {active_xor(b,&[],out[j],nand,dirty);}
            let ctl:Vec<_>=word[h..2*h].iter().map(|&q|(q,h>1)).collect();
            active_xor(b,&ctl,out[j],nand,dirty);
            for i in 0..h {b.cswap(out[j],word[i],word[i+h]);swaps.push((out[j],word[i],word[i+h]));}
        }
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
    })
}

/// The existing TTK ladder with only its sum writes gated by NAND(PH,C).
/// This is the k=7 N2 add, with no carry output and no borrowed clean bit.
fn add(b:&mut B,a:&[QubitId],t:&[QubitId],nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    require(a.len()==7&&t.len()==7,Error::Shape);
    for i in 1..7 {b.cx(a[i],t[i]);}
    for i in (1..6).rev() {b.cx(a[i],a[i+1]);}
    for i in 0..6 {b.ccx(t[i],a[i],a[i+1]);}
    for i in (1..7).rev() {
        active_xor(b,&[(a[i],false)],t[i],nand,dirty);
        b.ccx(t[i-1],a[i-1],a[i]);
    }
    for i in 1..6 {b.cx(a[i],a[i+1]);}
    active_xor(b,&[(a[0],false)],t[0],nand,dirty);
    for i in 1..7 {b.cx(a[i],t[i]);}
}

pub(super) fn entry(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G> {
    require((ring.len(),q.len(),y.len(),m.len())==(257,128,7,7),Error::Shape);
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(m).copied()
        .chain(nand.into_iter().flat_map(|(p,c)|[p,c])).collect();
    require(ports.iter().copied().collect::<BTreeSet<_>>().len()==ports.len(),Error::Alias);
    require(nand.is_none_or(|(p,c)|!dirty.contains(&p)&&!dirty.contains(&c)),Error::HeldPort);
    record(b,|b|{
        // N1: highest support of real Q and virtual one at address y.
        let mut swaps=Vec::new();
        for j in (0..7).rev() {
            let h=1usize<<j;
            for l in j+1..7 {b.cx(m[l],y[l]);}
            if h>1||nand.is_some() {
                active_xor(b,&[],m[j],nand,dirty);
                let upper:Vec<_>=q[h..2*h].iter().map(|&q|(q,true)).collect();
                active_xor(b,&upper,m[j],nand,dirty);
            } else {active_xor(b,&[(q[1],false)],m[0],nand,dirty);}
            let virtual_one:Vec<_>=q[h..2*h].iter().map(|&q|(q,true))
                .chain(y[j+1..].iter().map(|&q|(q,true))).chain([(y[j],false)]).collect();
            #[cfg(test)] let mark=b.recording_len();
            active_xor(b,&virtual_one,m[j],nand,dirty);
            #[cfg(test)] if super::enabled(){super::tag("virtual",&b.k1_current_since(mark),&[]);}
            for l in (j+1..7).rev() {b.cx(m[l],y[l]);}
            for i in 0..h {b.cswap(m[j],q[i],q[i+h]);swaps.push((m[j],q[i],q[i+h]));}
        }
        for &(c,a,z) in swaps.iter().rev() {b.cswap(c,a,z);}
        // N2: align the reversed physical window by complement(M), erase y.
        #[cfg(test)] let mark=b.recording_len();
        for &v in m {b.x(v);}add(b,m,y,nand,dirty);for &v in m {b.x(v);}
        #[cfg(test)] if super::enabled(){super::tag("adjust",&b.k1_current_since(mark),&[]);}
        let window:Vec<_>=ring.iter().rev().take(128).copied().collect();
        let rot=record(b,|b|{
            for &v in m {b.x(v);}
            for(k,&v)in m.iter().enumerate() {crate::point_add::frogdrop::crot_up(b,v,&window,1usize<<k);}
            for &v in m {b.x(v);}
        });
        #[cfg(test)] super::tag("n2rot",&rot,&[]);
        b.play(&rot,false);let erase=binary(b,&window,y,nand,dirty);b.play(&erase,true);b.play(&rot,true);
    })
}

}
