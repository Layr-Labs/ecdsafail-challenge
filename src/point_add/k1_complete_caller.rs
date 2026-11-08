//! Genuine parent traversal corpus producer. Never run during source preparation.
use super::{builder::B,direct_column::Column,frogdrop_col::{ColPar,Fd},outer_size::Roles,sum_size::SumSize};
use super::k1_complete_io::{self as io,Image,Receipt,WIDTH,BITS};
use crate::circuit::QubitId;
use ruint::aliases::U256;
use sha3::{digest::{ExtendableOutput,XofReader},Digest,Keccak256,Shake256};
use std::{fs::{File,OpenOptions},io::{Read,Write},path::Path};

pub(crate) const INPUTS:usize=128;
pub(crate) const COLUMNS:usize=203;
pub(crate) const CAPTURES:usize=(203+78+1)*2*2;
pub(crate) const CORPUS_BYTES:u64=128*1024*1024;
pub(crate) const DOMAIN:&[u8]=b"K1_COMPLETE_SOURCE_V1";
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Epoch {PreMap=0,PreTail=1,PreB0=2}
pub(crate) struct Layout {pub fd:Fd,pub p:Vec<QubitId>,pub pool:Vec<QubitId>,pub meta:SumSize}
impl Layout {
    /// Literal allocation order of point_add_pl through trav_forward_pl:
    /// x256, P258, ring-top1, Q128, E7, S5, PH1, four-role pool.
    pub fn allocate(b:&mut B)->Self {
        let x=b.alloc_n(256);let p=b.alloc_n(258);let mut ring=x;
        ring.extend(b.alloc_n(1));let q=b.alloc_n(128);let cnt=q[121..128].to_vec();
        let sy=b.alloc_n(7);let sx=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(4);
        let meta=SumSize{y:sy.as_slice().try_into().unwrap(),sum:sx.as_slice().try_into().unwrap()};
        assert_eq!(b.width(),WIDTH as u64);
        Self{fd:Fd{ring,q,sy,sx,ph,cnt},p,pool,meta}
    }
    pub fn column(&self,payload:bool)->Column<'_> {
        Column{meta:&self.meta,roles:Roles{tag:self.pool[0],cut:self.pool[1],toggle:self.pool[2],prefix:self.pool[3]},
            ring:&self.fd.ring,q:&self.fd.q,phase:self.fd.ph,compact:payload.then_some(self.p.as_slice()),
            dirty:&self.p,clean_external:if payload{&[]}else{&self.p[..2]}}
    }
}
pub(crate) fn builder()->B {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    let mut b=B::new();b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    b.global_cancel=false;b.force_unitary_and=false;b.no_rows=false;b
}
pub(crate) fn frozen_environment() {
    assert!(std::env::var_os("LS_NO_BAKE").is_none());
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    for(k,v)in super::BAKED_KNOBS{if !k.starts_with("C658_"){if let Some(actual)=std::env::var_os(k){assert_eq!(actual.to_str(),Some(*v),"override {k}");}}}
    for(k,_)in std::env::vars(){
        if ["FD_","C660_","C665_","C666_","L672_","QUOT_","LANE_","B7A_","B8A_","B8B_","B12A_","R9_","C45_","C55_","D1_","F1_"].iter().any(|p|k.starts_with(p)){
            assert!(super::BAKED_KNOBS.iter().any(|(name,_)|*name==k),"unfrozen knob {k}");
        }
    }
    super::bake_knobs();super::direct_traversal::require_admitted();
    assert!(super::payload::splice258::enabled());assert!(!super::frogdrop_col::c660_joint_size());
    assert_eq!(std::env::var("FD_NODEFERASE").unwrap(),"1");
}
fn xof(suffix:&[u8],id:usize,word:Option<usize>,out:&mut[u8]) {
    let mut s=Shake256::default();sha3::digest::Update::update(&mut s,DOMAIN);
    sha3::digest::Update::update(&mut s,suffix);sha3::digest::Update::update(&mut s,&(id as u64).to_le_bytes());
    if let Some(w)=word{sha3::digest::Update::update(&mut s,&(w as u64).to_le_bytes());}
    XofReader::read(&mut s.finalize_xof(),out);
}
pub(crate) fn scalar(id:usize)->[u8;32] {
    assert!(id<INPUTS);let mut a=[0u8;32];xof(b"",id,None,&mut a);
    let modulus:U256=(U256::ONE<<255usize)-U256::ONE;
    (U256::ONE+U256::from_le_bytes(a)%modulus).to_le_bytes::<32>()
}
fn payload_word(id:usize)->[u8;32] {
    let mut a=[0u8;32];for(w,chunk)in a.chunks_mut(8).enumerate(){xof(b"payload",id,Some(w),chunk);}
    // The original d/terminal-word ABI is a canonical secp256k1 field word.
    let p=U256::MAX-U256::from(0x1000003d0u64);
    (U256::from_le_bytes(a)%p).to_le_bytes()
}
fn phase_word(id:usize)->[u8;8]{let mut word=[0u8;8];xof(b"phase",id,Some(0),&mut word);word}
fn set(q:&mut[u64],ports:&[QubitId],bytes:&[u8;32],lane:usize) {
    assert_eq!(ports.len(),256);for(j,p)in ports.iter().enumerate(){if bytes[j/8]>>(j%8)&1!=0{q[p.0 as usize]|=1<<lane;}}
}
pub(crate) fn initial(l:&Layout,payload:bool,batch:usize)->Image {
    assert!(batch<2);let mut image=Image::zero();
    for lane in 0..64{let id=batch*64+lane;set(&mut image.q,&l.fd.ring[..256],&scalar(id),lane);
        let p=payload_word(id);set(&mut image.q,if payload{&l.p[..256]}else{&l.p[2..]},&p,lane);
        let phase=phase_word(id);image.phase|=((phase[0]&1)as u64)<<lane;
    }assert_ne!(image.phase,0);assert_ne!(image.phase,u64::MAX);image
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Key {pub payload:bool,pub batch:usize,pub column:usize,pub epoch:Epoch}
/// A consumer receives immutable actual state at a zero-operation boundary.
/// It cannot advance this simulator or supply replacement state. Later K4/K5
/// hooks need a separate source order; no extra boundary is called here.
pub(crate) trait BoundaryConsumer {
    fn observe(&mut self,key:&Key,cp:&ColPar,layout:&Layout,image:&Image,receipt:&Receipt);
}
thread_local!{static CONSUMER:std::cell::RefCell<Option<Box<dyn BoundaryConsumer>>>=const{std::cell::RefCell::new(None)};}
pub(crate) fn with_consumer<R>(consumer:Box<dyn BoundaryConsumer>,body:impl FnOnce()->R)->R {
    CONSUMER.with(|c|{assert!(c.borrow().is_none());*c.borrow_mut()=Some(consumer);});
    struct Reset;impl Drop for Reset{fn drop(&mut self){CONSUMER.with(|c|{c.borrow_mut().take();});}}
    let _reset=Reset;body()
}
fn hash_image(image:&Image)->String {let mut h=Keccak256::new();for v in image.q.iter().chain(&image.bits).chain([&image.phase]){h.update(v.to_le_bytes());}format!("{:x}",h.finalize())}
struct Writer {file:File,log:File,bytes:u64,count:usize,hash:Keccak256}
impl Writer {
    fn new(root:&Path)->Self{Self{file:OpenOptions::new().write(true).create_new(true).open(root.join("caller-images.bin")).unwrap(),
        log:OpenOptions::new().write(true).create_new(true).open(root.join("caller-images.tsv")).unwrap(),bytes:0,count:0,hash:Keccak256::new()}}
    fn write(&mut self,b:&[u8]){self.bytes+=b.len()as u64;assert!(self.bytes<=CORPUS_BYTES);self.file.write_all(b).unwrap();self.hash.update(b);}
    fn capture(&mut self,key:Key,cp:&ColPar,layout:&Layout){
        let(image,r)=io::snapshot();let offset=self.bytes;
        CONSUMER.with(|c|if let Some(consumer)=c.borrow_mut().as_mut(){consumer.observe(&key,cp,layout,&image,&r);});
        for v in [0x4b31494d41474531,u64::from(key.payload),key.batch as u64,key.column as u64,key.epoch as u64,WIDTH as u64,BITS as u64,image.phase]{self.write(&v.to_le_bytes());}
        for v in image.q.iter().chain(&image.bits){self.write(&v.to_le_bytes());}
        writeln!(self.log,"{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}\t{:?}",key.payload,key.batch,key.column,key.epoch as u8,offset,r.ops,r.rng_bytes,hash_image(&image),r,cp).unwrap();
        self.count+=1;
    }
}
/// Exact fixed caller producer. Original arithmetic and approximation sectors
/// advance every lane; a failed assertion retains its original scalar IDs.
/// No candidate call or candidate-dependent filtering appears in this path.
pub(crate) fn produce(root:&Path) {
    frozen_environment();let mut inputs=OpenOptions::new().write(true).create_new(true).open(root.join("inputs.tsv")).unwrap();
    for id in 0..INPUTS{writeln!(inputs,"{id}\t{:02x?}\t{:02x?}\t{:02x?}",scalar(id),payload_word(id),phase_word(id)).unwrap();}inputs.sync_all().unwrap();drop(inputs);
    let mut writer=Writer::new(root);let schedule=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let(columns,b0,_last)=super::pointadd_frogdrop::col_pars(&schedule);assert_eq!(columns.len(),COLUMNS);
    let mut producer_ops=0u64;let mut visits=0usize;
    for payload in [false,true]{for batch in 0..2{
        let mut b=builder();let mut l=Layout::allocate(&mut b);let input=initial(&l,payload,batch);
        let mut seed=DOMAIN.to_vec();seed.extend_from_slice(b"native-parent");seed.extend_from_slice(&[u8::from(payload),batch as u8]);
        let scope=io::begin(input,&seed,io::PRODUCER_OP_CAP);
        // Exact original initialization: Q=0, ring=x'||1, E=0, S=0, PH=0.
        b.x(l.fd.ring[256]);drop(b);drop(l);
        for cp in &columns{
            // Record IDs are builder-private and no deferred state may cross
            // this boundary. Physical IDs and native classical slots are fixed.
            let mut b=builder();let mut l=Layout::allocate(&mut b);
            super::frogdrop_col::set_counter_epoch(&mut l.fd,cp.col);
            println!("K1_CALLER_COLUMN_BEGIN payload={payload} batch={batch} column={} case_first={}",cp.col,batch*64);
            {let col=l.column(payload);let mut middle=super::direct_middle::DirectMiddle;
                super::direct_column::through_stage10(&mut b,&col,cp,&mut middle);
                b.flush_global();writer.capture(Key{payload,batch,column:cp.col,epoch:Epoch::PreMap},cp,&l);
                super::direct_map_tail_counter::finish_k1_observed(&mut b,&col,cp,|b|{
                    if cp.sw||cp.dl{b.flush_global();writer.capture(Key{payload,batch,column:cp.col,epoch:Epoch::PreTail},cp,&l);}
                });
            }
            assert!(b.ops.is_empty()&&b.pending_count()==0);assert_eq!(b.width(),WIDTH as u64);assert_eq!(b.bits_end(),BITS as u64);assert!(b.k1_retained_bytes()+8*1024*1024<=768*1024*1024);visits+=64;
        }
        {let mut host=builder();let layout=Layout::allocate(&mut host);writer.capture(Key{payload,batch,column:203,epoch:Epoch::PreB0},b0.as_ref().unwrap(),&layout);}
        let(_image,r)=io::finish(scope);producer_ops+=r.ops;
        println!("K1_CALLER_BATCH payload={payload} batch={batch} scalar_first={} scalar_last={} columns=203 receipt={r:?}",batch*64,batch*64+63);
    }}
    assert_eq!(writer.count,CAPTURES);assert_eq!(visits,51968);
    writer.file.sync_all().unwrap();writer.log.sync_all().unwrap();
    println!("K1_CALLER_COMPLETE scalar_cases=128 payload_modes=2 batches=4 column_visits={visits} captures={} bytes={} hash={:x} native_ops={} candidates=0",writer.count,writer.bytes,writer.hash.finalize(),producer_ops);
}
/// Exact readback keyed by immutable capture order; callers never search or
/// select inputs by a candidate outcome. Quantum/phase compare ignores only
/// independently sampled measurement scratch, as in qualified c119.
pub(crate) fn read(root:&Path,key:&Key)->Image {
    use std::io::{Seek,SeekFrom};
    let schedule=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let(columns,_,_)=super::pointadd_frogdrop::col_pars(&schedule);
    let mut ordinal=0usize;let mut found=None;
    for payload in [false,true]{for batch in 0..2{for cp in &columns{
        for epoch in [Epoch::PreMap,Epoch::PreTail]{if epoch==Epoch::PreTail&&!(cp.sw||cp.dl){continue;}
            if *key==(Key{payload,batch,column:cp.col,epoch}){found=Some(ordinal);}ordinal+=1;
        }}if *key==(Key{payload,batch,column:203,epoch:Epoch::PreB0}){found=Some(ordinal);}ordinal+=1;}}
    assert_eq!(ordinal,CAPTURES);let ordinal=found.expect("key outside fixed corpus");
    let length=8*(8+WIDTH+BITS);let mut f=File::open(root.join("caller-images.bin")).unwrap();f.seek(SeekFrom::Start((ordinal*length)as u64)).unwrap();
    let mut number=||{let mut a=[0u8;8];f.read_exact(&mut a).unwrap();u64::from_le_bytes(a)};
    assert_eq!(number(),0x4b31494d41474531);assert_eq!(number(),u64::from(key.payload));assert_eq!(number(),key.batch as u64);
    assert_eq!(number(),key.column as u64);assert_eq!(number(),key.epoch as u64);assert_eq!(number(),WIDTH as u64);assert_eq!(number(),BITS as u64);
    let phase=number();let q=(0..WIDTH).map(|_|number()).collect();let bits=(0..BITS).map(|_|number()).collect();Image{q,bits,phase}
}
