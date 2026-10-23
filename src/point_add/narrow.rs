//! narrow: sell compare bits for failing shots (the dual of the phasefix probe). A seeded chunk-boundary compare of
//! `chunked_add` (pingpong.rs) whose seed is the addend bit just below its window reads `bits` fewer bits, the seed
//! moving up with the window: -0.5 T per bit (one CCX under the measured bit) for about twice the site's error rate.
//! Classes are (multiply, width at the site after every other rule). Empty table = the base, gate for gate.
use super::builder::Builder;
use crate::circuit::QubitId;
use std::cell::RefCell;
use std::collections::BTreeMap;

/// (multiply, width, bits taken off).
pub(crate) const NARROW: &[(bool, usize, usize)] = &[
    (false, 21, 1),
    (true, 16, 1),
    (true, 21, 1),
    (true, 22, 2),
];
/// Narrowest window a narrowed compare keeps.
const MIN_WIDTH: usize = 4;

thread_local! {
    /// (multiply, width, form) -> (sites, narrowed). form 0: seeded, seed adjacent; 1: seeded otherwise; 2: unseeded.
    static HIST: RefCell<BTreeMap<(bool, usize, u8), (usize, usize)>> = const { RefCell::new(BTreeMap::new()) };
}

fn bits_for(multiply: bool, width: usize) -> usize {
    NARROW.iter().find(|e| e.0 == multiply && e.1 == width).map_or(0, |e| e.2)
}

/// The window and seed of one chunk-boundary compare at [.., phi) of `addend`, after narrowing.
pub(crate) fn chunk(multiply: bool, phi: usize, compare: usize, addend: &[QubitId], borrow: Option<QubitId>, tie: bool) -> (usize, Option<QubitId>) {
    let adjacent = !tie && phi > compare && borrow.is_some() && borrow == Some(addend[phi - compare - 1]);
    let form = if adjacent { 0 } else if borrow.is_some() { 1 } else { 2 };
    let d = if adjacent { bits_for(multiply, compare) } else { 0 };
    let d = if compare >= MIN_WIDTH + d { d } else { 0 };
    HIST.with(|h| {
        let mut h = h.borrow_mut();
        let e = h.entry((multiply, compare, form)).or_insert((0, 0));
        e.0 += 1;
        e.1 += usize::from(d > 0);
    });
    if d == 0 {
        return (compare, borrow);
    }
    let k = compare - d;
    (k, Some(addend[phi - k - 1]))
}

/// One NARROW_HIST line per class (called once, after the multiply).
pub(crate) fn report() {
    HIST.with(|h| {
        for ((m, w, f), (n, d)) in h.borrow().iter() {
            eprintln!("NARROW_HIST\t{}\t{w}\t{f}\t{n}\t{d}", if *m { "mul" } else { "div" });
        }
    });
}

/// The allocator at the square's entry in a build without divide narrowing (one line `next_bit free_wires free_bits`,
/// comma lists, "-" = empty). Empty: the build prints its own state as a `NARROW_SQ` line (GEN). A narrowed divide
/// leaves the free lists in another order, which the hash-bound square table (y42_bound, rebind.rs) cannot follow.
const SQ: &str = include_str!("narrow_sq.txt");

pub(crate) fn square_entry(c: &mut Builder) {
    let join = |v: &[u32]| if v.is_empty() { "-".to_string() } else { v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",") };
    let list = |s: &str| -> Vec<u32> { if s == "-" { Vec::new() } else { s.split(',').map(|x| x.parse().expect("narrow_sq: id")).collect() } };
    let (q, b, n) = c.y42_alloc_state();
    if SQ.trim().is_empty() {
        eprintln!("NARROW_SQ {n} {} {}", join(&q), join(&b));
        return;
    }
    let f: Vec<&str> = SQ.split_whitespace().collect();
    assert_eq!(f.len(), 3, "narrow_sq: bad line");
    let (rq, rb, rn) = (list(f[1]), list(f[2]), f[0].parse::<u32>().expect("narrow_sq: next bit"));
    let same = rq == q && rb == b && rn == n;
    c.narrow_alloc_set(&rq, &rb, rn);
    eprintln!("NARROW_SQ set (was {})", if same { "equal" } else { "different" });
}

thread_local! {static COMPARE_WINDOW_CALL:std::cell::Cell<usize>=const{std::cell::Cell::new(0)};}
pub(crate)fn compare_window_compare(multiply:bool,round:usize,phi:usize,w:usize,a:&[QubitId],seed:Option<QubitId>)->(usize,usize,Option<QubitId>){
 let id=COMPARE_WINDOW_CALL.with(|x|{let n=x.get();x.set(n+1);n});
 let want=match (multiply as usize,w){(0,16)=>17,(0,18)=>19,(0,19)=>20,(0,20)=>21,(1,15)=>18,(1,18)=>20,_=>w};
 let eligible=want<=phi && (seed.is_none() || w<phi && seed==Some(a[phi-w-1]));
 let base=if eligible{want}else{w};
 let menu=std::env::var("FRAME_MENU").as_deref()==Ok("1");
 let mut k=if menu{match(multiply as usize,base){(0,19)=>21,(0,20)=>21,(0,21)=>20,(1,18)=>17,(1,19)=>18,(1,21)=>18,_=>base}.min(phi)}else{base};
 // Fund the reordered walk with a fixed, stronger whole div16 class.
 // This is chosen before any current qualification outcome.
 if multiply==false&&w==16&&eligible{if let Ok(v)=std::env::var("FRAME_FUND"){k=v.parse::<usize>().unwrap().min(phi).max(base);}}
 if k!=base{assert!(seed.is_none()||w<phi&&seed==Some(a[phi-w-1]));}
 FRAME_COMPARE_FAULT_SITE.with(|v|v.set((k,k!=base&&menu,multiply==false&&w==16&&k>base)));

 // buy-back (31c38da8 sec 2.5) at source: division compare windows 17 -> 18 and 19 -> 20
 if !multiply { let kb=match k {17=>18,19=>20,_=>k}.min(phi); if kb!=k && (seed.is_none()||w<phi&&seed==Some(a[phi-w-1])) { k=kb; } }
 if k==w{return(id,k,seed);}
 (id,k,if seed.is_some()&&k<phi{Some(a[phi-k-1])}else{None})
}

thread_local!{static FRAME_COMPARE_FAULT_SITE:std::cell::Cell<(usize,bool,bool)>=const{std::cell::Cell::new((0,false,false))};}
pub(super)fn frame_fault_site(w:usize,fund:bool)->bool{FRAME_COMPARE_FAULT_SITE.with(|v|{let(k,m,f)=v.get();k==w&&if fund{f}else{m}})}
