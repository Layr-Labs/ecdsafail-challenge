//! Fixed source-only U6 qualification plan. No whole digit or other U-site.
use super::*;
use super::super::maj_virtual_leading::{self as maj,K4BoundaryQuery,K4Mutation,K4Error};
use super::super::size_window::{SizeWindow,WindowDecoder};
use super::super::ttk_virtual_leading::Size;
use crate::circuit::{Op,OperationType as K,NO_BIT};
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput,XofReader},Digest};
type Wide=ruint::Uint<512,8>;
const WIDTH:usize=660;
const SMALL_ROWS:usize=942144;
const FULL_ROWS:usize=147456;
const SEED:u64=0x4b345f55365f2026;
fn mix(mut s:u64)->u64 {
    s=s.wrapping_add(0x9e3779b97f4a7c15);s=(s^(s>>30)).wrapping_mul(0xbf58476d1ce4e5b9);
    s=(s^(s>>27)).wrapping_mul(0x94d049bb133111eb);s^(s>>31)
}
fn mask(n:usize)->Wide {if n==0{Wide::ZERO}else{(Wide::from(1)<<n)-Wide::from(1)}}
fn put(w:&mut[u64],q:QubitId,lane:usize,v:bool) {
    let bit=1u64<<lane;w[q.0 as usize]&=!bit;if v{w[q.0 as usize]|=bit;}
}
fn word(w:&mut[u64],q:&[QubitId],lane:usize,v:Wide) {
    for(i,&q)in q.iter().enumerate(){put(w,q,lane,v.bit(i));}
}
fn read(w:&[u64],q:&[QubitId],lane:usize)->Wide {
    let mut v=Wide::ZERO;for(i,&q)in q.iter().enumerate(){if w[q.0 as usize]>>lane&1!=0{v|=Wide::from(1)<<i;}}v
}
#[derive(Clone,Copy,Debug)]
enum QueryKind { Raw, Window }
#[derive(Clone,Copy,Debug)]
struct Profile { n:usize,lo:usize,hi:usize,kind:QueryKind,reversed_target:bool,optimized:bool }
struct Rig {
    b:B,ring:Vec<QubitId>,q:Vec<QubitId>,raw:Vec<QubitId>,meta:SumSize,
    ph:QubitId,a:QubitId,e:QubitId,sign:QubitId,work:QubitId,
    raw_prefix_seen:bool,window_prefix_seen:bool,
}
impl Rig {
    fn new(optimized:bool)->Self {
        assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
        let mut b=B::new();b.cancel_simple_pairs=optimized;b.cancel_commuting_pairs=optimized;
        b.global_cancel=false;b.force_unitary_and=false;b.no_rows=false;
        let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);
        let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};
        let ph=b.alloc();let a=b.alloc();let e=b.alloc();let sign=b.alloc();let work=b.alloc();
        let raw=p.into_iter().chain([ph]).collect();
        assert_eq!((b.width(),ph.0,work.0),(660,655,659));
        Self{b,ring,q,raw,meta,ph,a,e,sign,work,raw_prefix_seen:false,window_prefix_seen:false}
    }
    fn target(&self,p:Profile)->Vec<QubitId> {
        if p.reversed_target{(0..p.n).map(|i|self.raw[258-i]).collect()}
        else{self.raw[..p.n].to_vec()}
    }
    fn bank(&self)->Vec<QubitId> {
        // Original physical kernel bank order. Metadata/Q/roles are absent.
        self.raw.iter().chain(&self.ring).copied().filter(|q|*q!=self.ph).collect()
    }
    fn capture(&mut self,p:Profile,candidate:bool,mutation:K4Mutation)->(Vec<G>,Option<QubitId>) {
        let t=self.target(p);let s=self.ring[..p.n].to_vec();let d=self.bank();
        let held=[self.ph,self.work];
        let build=|b:&mut B,query:&mut dyn K4BoundaryQuery| {
            // Adapters below use concrete Query wrappers for the original
            // impl-Trait API while retaining the real production decoder.
            struct Dyn<'a>(&'a mut dyn K4BoundaryQuery);
            impl BoundaryQuery for Dyn<'_> {
                fn xor(&mut self,b:&mut B,v:usize,t:QubitId,e:&[(QubitId,bool)],d:&[QubitId]){self.0.xor(b,v,t,e,d);}
                fn clear(&mut self,b:&mut B){self.0.clear(b);}
            }
            impl K4BoundaryQuery for Dyn<'_>{fn k4_contract(&self)->maj::K4QueryContract{self.0.k4_contract()}}
            let mut query=Dyn(query);
            if candidate {
                let r=maj::physical_restoring_record3(b,&t,&s,self.a,self.e,self.sign,self.q[127],
                    p.lo,p.hi,&d,&held,&mut query,mutation).expect("K4 typed record contract");
                assert_eq!(r.parity.1,matches!(p.kind,QueryKind::Window)&&p.lo%2==1);
                (r.tape,Some(r.dirty_lane))
            }else{
                assert_eq!(mutation,K4Mutation::None);
                (physical_restoring_record(b,&t,&s,self.a,self.e,self.work,self.q[127],
                    p.lo,p.hi,&d,&mut query),None)
            }
        };
        let answer=match p.kind {
            QueryKind::Raw=>{
                // The real raw tree planner/Decoder, including sum-cover
                // disambiguation and its actual union of Q/S prefix loans.
                let leaves=tree(0,7,p.lo,p.hi,128,31).leaves;
                let prefix_max=leaves.iter().map(|l|l.prefixes).max().unwrap_or(0);
                self.raw_prefix_seen|=prefix_max>0;
                println!("K4_DECODER kind=raw range={}..{} leaves={} prefix_max={} parity_neg=false",p.lo,p.hi,leaves.len(),prefix_max);
                let mut decoder=Decoder{meta:&self.meta,q:&self.q,activity:self.a,
                    lo:p.lo,hi:p.hi,limit:31,leaves,cur:None};
                build(&mut self.b,&mut decoder)
            },
            QueryKind::Window=>{
                let kind=if p.n<98{Size::Y}else{Size::Z};
                let window=SizeWindow::new(&self.meta,kind,p.lo,p.hi,31);
                let count=window.width.saturating_sub(1).min(window.spares().len());
                let pre:Vec<_>=window.spares().into_iter().take(count).collect();
                self.window_prefix_seen|=count>0;
                println!("K4_DECODER kind=window range={}..{} prefixes={} parity_neg={}",p.lo,p.hi,count,p.lo%2==1);
                let mut decoder=WindowDecoder::new(&window,&pre,self.a);
                build(&mut self.b,&mut decoder)
            },
        };
        assert_eq!(self.b.width(),WIDTH as u64);answer
    }
}
fn emit(b:&mut B,r:&[G],inverse:bool)->Vec<Op> {
    assert!(b.ops.is_empty()&&b.pending_count()==0);
    b.play(r,inverse);b.flush_global();let out=std::mem::take(&mut b.ops);
    for o in &out{assert!(matches!(o.kind,K::X|K::CX|K::CCX));assert_eq!(o.c_condition,NO_BIT);o.validate();}
    assert!(b.c162_audit.is_empty());out
}
fn counts(ops:&[Op])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
fn fingerprint(ops:&[Op])->String {
    let mut h=sha3::Keccak256::new();
    for o in ops{h.update((o.kind as u8).to_le_bytes());for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
    format!("{:x}",h.finalize())
}
struct NoMeasure<R>(R);
impl<R:XofReader>XofReader for NoMeasure<R>{fn read(&mut self,_:&mut[u8]){panic!("unexpected measurement");}}
fn play(ops:&[Op],input:&[u64],phase:u64)->(Vec<u64>,u64){
    let mut xof=NoMeasure(sha3::Shake256::default().finalize_xof());
    let mut sim=Simulator::new(WIDTH,10002,&mut xof);sim.qubits=input.to_vec();sim.phase=phase;
    sim.apply_iter(ops.iter());(sim.qubits,sim.phase)
}
fn diff(a:&[u64],b:&[u64])->u64{a.iter().zip(b).fold(0,|d,(a,b)|d|(a^b))}
fn check(ops:&[Op],input:&[u64],expected:&[u64],phase:u64,label:&str){
    let(out,sign)=play(ops,input,phase);assert_eq!(sign,phase,"signed phase {label}");
    assert!(out==expected,"full660 state {label}, difference={:016x}",diff(&out,expected));
}
// Independent arithmetic oracle: numerical conditional subtraction on the
// low R+1 bits only, never a transcription of MAJ/undo or boundary gates.
fn oracle(rig:&Rig,p:Profile,input:&[u64],rs:&[usize])->Vec<u64>{
    let mut out=input.to_vec();let target=rig.target(p);
    for(lane,&r)in rs.iter().enumerate(){
        assert!((p.lo..=p.hi).contains(&r));
        if input[rig.a.0 as usize]>>lane&1==0{continue;}
        assert_eq!((input[rig.e.0 as usize]>>lane&1,input[rig.q[127].0 as usize]>>lane&1),(0,0));
        let source=read(input,&rig.ring[..p.n],lane)&mask(r);
        assert!(source.bit(r-1));
        let all=read(input,&target,lane);let d=all&mask(r+1);
        assert!(d<source*Wide::from(2),"explicit d<2r care");
        let decision=d>=source;let low=if decision{d-source}else{d};
        word(&mut out,&target,lane,(all&!mask(r+1))|low);
        put(&mut out,rig.e,lane,decision);
    }out
}
struct Tapes{pf:Vec<Op>,pi:Vec<Op>,cf:Vec<Op>,ci:Vec<Op>,w:QubitId}
fn tapes(rig:&mut Rig,p:Profile)->Tapes{
    let(parent,_)=rig.capture(p,false,K4Mutation::None);
    let(disabled,_)=rig.capture(p,false,K4Mutation::None);
    assert!(parent==disabled,"original/default identity before candidate");
    let pf=emit(&mut rig.b,&parent,false);let pi=emit(&mut rig.b,&parent,true);
    let df=emit(&mut rig.b,&disabled,false);let di=emit(&mut rig.b,&disabled,true);
    assert!(pf==df&&pi==di);
    println!("K4_BASELINE {:?} parent={:?} f={} i={}",p,counts(&pf),fingerprint(&pf),fingerprint(&pi));
    let(candidate,w)=rig.capture(p,true,K4Mutation::None);let w=w.unwrap();
    let cf=emit(&mut rig.b,&candidate,false);let ci=emit(&mut rig.b,&candidate,true);
    assert_eq!(counts(&pf),counts(&pi));assert_eq!(counts(&cf),counts(&ci));
    assert!(pf.iter().rev().copied().collect::<Vec<_>>()==pi);
    assert!(cf.iter().rev().copied().collect::<Vec<_>>()==ci);
    for o in cf.iter().chain(&ci){
        assert!(![o.q_control1,o.q_control2,o.q_target].contains(&rig.work));
        if !rig.target(p).contains(&rig.ph){assert!(![o.q_control1,o.q_control2,o.q_target].contains(&rig.ph));}
    }
    assert!(!rig.target(p).contains(&w)&&!rig.ring[..p.n].contains(&w));
    println!("K4_PROFILE {:?} parent={:?} candidate={:?} w={} f={} i={}",p,counts(&pf),counts(&cf),w.0,fingerprint(&cf),fingerprint(&ci));
    Tapes{pf,pi,cf,ci,w}
}
fn batch(rig:&Rig,p:Profile,t:&Tapes,w:&[u64],rs:&[usize],id:usize){
    let expected=oracle(rig,p,w,rs);let sign=mix(SEED^id as u64);
    check(&t.pf,w,&expected,sign,"parent forward independent arithmetic");
    check(&t.cf,w,&expected,sign,"candidate forward independent arithmetic");
    check(&t.pi,&expected,w,sign,"parent inverse independent image");
    check(&t.ci,&expected,w,sign,"candidate inverse independent image");
}

struct Stream{w:Vec<u64>,rs:Vec<usize>,rows:usize,batches:usize,padding:usize}
impl Stream{
    fn new()->Self{Self{w:vec![0;WIDTH],rs:Vec::new(),rows:0,batches:0,padding:0}}
    fn push(&mut self,rig:&Rig,p:Profile,t:&Tapes,r:usize,a:bool,e:bool,carry:bool,
            s:Wide,d:Wide,passengers:usize){
        let lane=self.rs.len();let salt=SEED^self.rows as u64^(r as u64)<<40;
        for wire in 0..WIDTH{put(&mut self.w,QubitId(wire as u64),lane,mix(salt^wire as u64)&1!=0);}
        word(&mut self.w,&rig.ring[..p.n],lane,s);word(&mut self.w,&rig.target(p),lane,d);
        put(&mut self.w,rig.a,lane,a);put(&mut self.w,rig.e,lane,e);
        put(&mut self.w,rig.sign,lane,passengers&2!=0);put(&mut self.w,rig.work,lane,false);
        put(&mut self.w,t.w,lane,passengers&1!=0);
        put(&mut self.w,rig.raw[p.n+1],lane,passengers&4!=0);
        if a {
            for &q in &rig.q{put(&mut self.w,q,lane,false);}
            let address=match p.kind{QueryKind::Raw=>r%128,QueryKind::Window=>r-p.lo};
            word(&mut self.w,&rig.meta.y,lane,Wide::from(address));
            word(&mut self.w,&rig.meta.sum,lane,Wide::ZERO);
        }
        put(&mut self.w,rig.q[127],lane,carry);
        self.rs.push(r);self.rows+=1;
        if self.rs.len()==64{self.flush(rig,p,t);}
    }
    fn flush(&mut self,rig:&Rig,p:Profile,t:&Tapes){
        if self.rs.is_empty(){return;}
        self.padding+=64-self.rs.len();batch(rig,p,t,&self.w,&self.rs,self.batches);
        self.batches+=1;self.rs.clear();self.w.fill(0);
    }
}
fn small()->usize{
    let mut total=0;
    for optimized in [false,true]{for n in 3..=5{for (kind,lo) in
        [(QueryKind::Raw,1),(QueryKind::Window,1),(QueryKind::Window,2)] {
        let p=Profile{n,lo,hi:n-1,kind,reversed_target:false,optimized};
        let mut rig=Rig::new(optimized);let t=tapes(&mut rig,p);let mut stream=Stream::new();
        for r in lo..n {
            // Off-A: exhaustive complete target/source, e, carry, dirty w,
            // retained sign and one independent passenger bit. No rejection.
            for e in [false,true]{for carry in [false,true]{for s in 0..1usize<<n{
                for d in 0..1usize<<n{for passengers in 0..8{
                    stream.push(&rig,p,&t,r,false,e,carry,Wide::from(s),Wide::from(d),passengers);
                }}
            }}}
            // On-A: enumerate leading-one source and ALL d<2r directly;
            // upper source/target bits remain independently exhaustive.
            for low in 1usize<<(r-1)..1usize<<r{for upper_s in 0..1usize<<(n-r){
                for d in 0..2*low{for upper_t in 0..1usize<<(n-r-1){for passengers in 0..8{
                    stream.push(&rig,p,&t,r,true,false,false,
                        Wide::from(low|(upper_s<<r)),Wide::from(d|(upper_t<<(r+1))),passengers);
                }}}
            }}
        }
        stream.flush(&rig,p,&t);total+=stream.rows;
        println!("K4_SMALL {:?} rows={} packed_batches={} padding_lanes={} independent_directions=2",p,stream.rows,stream.batches,stream.padding);
    }}}
    assert_eq!(total,SMALL_ROWS);total
}
fn profiles()->Vec<Profile>{
    let geometry=[(128,98,127,QueryKind::Raw),(128,98,127,QueryKind::Window),
        (128,99,127,QueryKind::Raw),(128,99,127,QueryKind::Window),
        (256,128,255,QueryKind::Raw),(256,128,255,QueryKind::Window),
        (257,129,256,QueryKind::Raw),(257,129,256,QueryKind::Window),
        (257,98,256,QueryKind::Raw)];
    let mut out=Vec::new();for optimized in [false,true]{for reversed_target in [false,true]{
        for &(n,lo,hi,kind)in &geometry{out.push(Profile{n,lo,hi,kind,reversed_target,optimized});}
    }}assert_eq!(out.len(),36);out
}
fn full_input(rig:&Rig,p:Profile,batch:usize)->(Vec<u64>,Vec<usize>){
    let mut w=vec![0;WIDTH];let mut rs=Vec::new();let count=p.hi-p.lo+1;
    for lane in 0..64{
        let id=batch*64+lane;let r=p.lo+id%count;let a=(id/count)%2==0;
        let pattern=(id/(count*2))%6;
        for wire in 0..WIDTH{put(&mut w,QubitId(wire as u64),lane,mix(SEED^(id as u64)<<20^wire as u64)&1!=0);}
        let raw_s=read(&w,&rig.ring[..p.n],lane);
        let source=(raw_s&mask(r))|(Wide::from(1)<<(r-1));
        if a {
            word(&mut w,&rig.ring[..p.n],lane,(raw_s&!mask(r))|source);
            let low=match pattern{0=>Wide::ZERO,1=>source-Wide::from(1),2=>source,
                3=>source+Wide::from(1),4=>source*Wide::from(2)-Wide::from(1),
                _=>source/Wide::from(2)};
            let target=rig.target(p);let upper=read(&w,&target,lane)&!mask(r+1);
            word(&mut w,&target,lane,upper|low);
            for &q in &rig.q{put(&mut w,q,lane,false);}
            put(&mut w,rig.e,lane,false);
            // Original S/Y feasibility makes residue aliases unambiguous.
            // For R98..256: Y=226+S-R in1..128 and S in0..31.
            let sl=r.saturating_sub(225);let sh=31.min(r-98);
            let sum=sl+(id%(sh-sl+1));
            let address=match p.kind{QueryKind::Raw=>r%128,QueryKind::Window=>r-p.lo};
            word(&mut w,&rig.meta.y,lane,Wide::from(address));
            word(&mut w,&rig.meta.sum,lane,Wide::from(sum));
        }
        put(&mut w,rig.a,lane,a);put(&mut w,rig.work,lane,false);rs.push(r);
    }(w,rs)
}
fn full()->usize{
    let mut rows=0;let mut mutation_detections=0;let mut comparator_controls=0;
    let(mut raw_prefix_seen,mut window_prefix_seen)=(false,false);
    for (profile,p)in profiles().into_iter().enumerate(){
        let mut rig=Rig::new(p.optimized);let t=tapes(&mut rig,p);
        let mut mutants=Vec::new();
        for m in [K4Mutation::DropParity,K4Mutation::WrongParitySign,K4Mutation::DropAlternation,K4Mutation::DamageBoundary]{
            let(r,_)=rig.capture(p,true,m);let f=emit(&mut rig.b,&r,false);let i=emit(&mut rig.b,&r,true);
            assert!(f!=t.cf&&i!=t.ci,"effective tape mutation {m:?}");
            println!("K4_MUTANT_RECIPE profile={} mutation={:?} forward={:?}:{} inverse={:?}:{}",profile,m,counts(&f),fingerprint(&f),counts(&i),fingerprint(&i));
            mutants.push((m,f,i,[0u64;2]));
        }
        for id in 0..64{
            let(w,rs)=full_input(&rig,p,id);batch(&rig,p,&t,&w,&rs,id+profile*64);
            let expected=oracle(&rig,p,&w,&rs);let phase=mix(SEED^id as u64);
            for(_,f,i,bad)in &mut mutants{
                let(out,sign)=play(f,&w,phase);bad[0]|=diff(&out,&expected)|(sign^phase);
                let(out,sign)=play(i,&expected,phase);bad[1]|=diff(&out,&w)|(sign^phase);
            }
            if id==0{
                let mut phase_only=t.cf.clone();phase_only.push(Op{kind:K::CZ,
                    q_control1:rig.a,q_target:rig.sign,..Op::empty()});
                let(out,sign)=play(&phase_only,&w,phase);assert!(out==expected&&sign!=phase);
                let mut donor_only=t.cf.clone();donor_only.push(Op{kind:K::X,q_target:t.w,..Op::empty()});
                let(out,sign)=play(&donor_only,&w,phase);assert!(out!=expected&&sign==phase);
                for wire in 0..WIDTH{assert_eq!(out[wire]^expected[wire],if wire==t.w.0 as usize{u64::MAX}else{0});}
                comparator_controls+=2;
                // The physical fourth role is a spectator in the candidate,
                // even when it carries an arbitrary state rather than zero.
                let mut dirty=w.clone();dirty[rig.work.0 as usize]=mix(SEED^profile as u64);
                let want=oracle(&rig,p,&dirty,&rs);
                check(&t.cf,&dirty,&want,phase,"arbitrary fourth-role spectator");
                check(&t.ci,&want,&dirty,phase,"inverse fourth-role spectator");
            }
            rows+=64;
        }
        raw_prefix_seen|=rig.raw_prefix_seen;window_prefix_seen|=rig.window_prefix_seen;
        for(m,_,_,bad)in mutants{
            assert!(bad[0]!=0&&bad[1]!=0,"mutation {m:?} lacks both direction witnesses");
            println!("K4_MUTANT profile={} mutation={:?} forward_diff={:016x} inverse_diff={:016x}",profile,m,bad[0],bad[1]);mutation_detections+=1;
        }
    }
    assert!(raw_prefix_seen&&window_prefix_seen,"both real decoder prefix paths must run");
    assert_eq!((rows,mutation_detections,comparator_controls),(FULL_ROWS,144,72));rows
}
fn typed_controls()->usize{
    let mut rig=Rig::new(false);let p=Profile{n:128,lo:99,hi:127,kind:QueryKind::Window,reversed_target:false,optimized:false};
    let t=rig.target(p);let s=rig.ring[..p.n].to_vec();let bank=rig.bank();
    let window=SizeWindow::new(&rig.meta,Size::Z,p.lo,p.hi,31);
    let pre:Vec<_>=window.spares().into_iter().take(2).collect();
    let mut decoder=WindowDecoder::new(&window,&pre,rig.a);
    let protected=decoder.k4_contract();assert!(protected.parity.1);
    assert!(pre.iter().all(|q|protected.protected.contains(q)));
    let before=(rig.b.op_count(),rig.b.recording_len());
    let invoke=|b:&mut B,t:&[QubitId],a:QubitId,d:&[QubitId],query:&mut WindowDecoder<'_,'_>|{
        maj::physical_restoring_record3(b,t,&s,a,rig.e,rig.sign,rig.q[127],p.lo,p.hi,d,
            &[rig.ph,rig.work],query,K4Mutation::None)
    };
    assert!(matches!(invoke(&mut rig.b,&t,rig.e,&bank,&mut decoder),Err(K4Error::Alias(_))));
    let mut alias=t.clone();alias[0]=rig.meta.y[0];
    assert!(matches!(invoke(&mut rig.b,&alias,rig.a,&bank,&mut decoder),Err(K4Error::DecoderHeld(_))));
    assert!(matches!(invoke(&mut rig.b,&t,rig.a,&protected.protected,&mut decoder),Err(K4Error::NoDirtyLane)));
    let bad_pre=[rig.ph,pre[0]];
    let mut bad_decoder=WindowDecoder::new(&window,&bad_pre,rig.a);
    assert!(matches!(invoke(&mut rig.b,&t,rig.a,&bank,&mut bad_decoder),Err(K4Error::DecoderHeld(_))));
    assert!(matches!(invoke(&mut rig.b,&t,rig.ph,&bank,&mut decoder),Err(K4Error::HeldOwner(_))));
    assert!(matches!(invoke(&mut rig.b,&t,QubitId(600),&bank,&mut decoder),Err(K4Error::ActivityMismatch)));
    assert_eq!(before,(rig.b.op_count(),rig.b.recording_len()));6
}
#[test]
fn k4_u6_physical_restoring_native(){
    let small_rows=small();let full_rows=full();let controls=typed_controls();
    println!("K4_U6_COMPLETE small_rows={} full_rows={} small_profiles=18 full_profiles=36 directions=2 typed_controls={} dynamic_mutant_profiles=144 comparator_controls=72 spectator_profiles=36 width=660 whole_digit=false submit=CLOSED",small_rows,full_rows,controls);
}
