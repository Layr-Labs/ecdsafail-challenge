//! Complete three-owner crossing and fixed middle dispatch.
use super::builder::{B,G};
use super::cross_three::{Cross,Gate,Kernels,Roles,VTop};
use super::direct_three::{Column,Middle};
use super::payload_three::{self,Context,Ranges,Session};
use super::frogdrop_col::ColPar;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Concrete binding. Software state records which complete payload epoch
/// is open; it stores no simulated bit or additional quantum owner.
struct CrossKernels<'a,'p>{
    column:&'a Column<'p>,
    cp:&'a ColPar,
    ht:bool,
    payload_open:bool,
    payload:Option<Session>,
    v_record:Option<Vec<G>>,
    native_ring_v_record:Option<Vec<G>>,
}

impl CrossKernels<'_,'_>{
    fn ranges(&self)->Ranges{
        Ranges{z:self.cp.sz,y:(self.cp.sy.0.max(1),self.cp.sy.1.min(128))}
    }
    fn payload_roles(c:&Cross<'_>)->payload_three::Roles{
        payload_three::Roles{activity:c.roles.activity,flight:c.roles.flight,
            work:c.roles.work}
    }
    fn bank(&self,c:&Cross<'_>)->Vec<QubitId>{
        let r=c.roles;let mut seen:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum)
            .copied().chain([c.phase,r.activity,r.flight,r.work]).collect();
        // P remains arbitrary data and is optional. Using only ring/Q
        // here makes the complete V/frame contract also valid on T2/T3.
        c.dirty.iter().chain(c.ring).chain(c.q).copied()
            .filter(|q|seen.insert(*q)).collect()
    }
    fn arithmetic(&self)->super::cross_three_arithmetic::D{
        super::cross_three_arithmetic::D{ht:self.ht,payload_open:self.payload_open}
    }
    fn same_ports(&self,c:&Cross<'_>){
        let r=self.column.roles;
        assert_eq!(c.roles.activity,r.tag);
        assert_eq!(c.roles.flight,r.cut);
        assert_eq!(c.roles.work,r.work);
        assert_eq!(c.phase,self.column.phase);
        assert_eq!(c.ring,self.column.ring);assert_eq!(c.q,self.column.q);
    }
}

impl super::normalized_three_payload::PayloadPorts for CrossKernels<'_,'_>{
    fn hr_payload_word(&self)->&[QubitId]{
        assert!(!self.ht&&self.payload_open);
        &self.payload.as_ref().expect("native final HR requires an open payload session").raw
    }
}
impl super::normalized_three_controller::NativeRingV for CrossKernels<'_,'_>{
    fn native_ring_v(&mut self,b:&mut B,c:&Cross<'_>,ht:bool,inverse:bool){
        self.same_ports(c);assert_eq!(ht,self.ht);
        assert!(!self.payload_open&&self.payload.is_none());
        if self.native_ring_v_record.is_none(){
            let r=c.roles;
            self.native_ring_v_record=Some(super::midg::direct_native_ring_v::record_three(
                b,c.size,c.ring,c.q,r.activity,r.flight,c.phase,r.work,self.cp.sz,&self.bank(c)));
        }
        b.play(self.native_ring_v_record.as_ref().unwrap(),inverse);
    }
}

impl Kernels for CrossKernels<'_,'_>{
    fn top_frame(&mut self,b:&mut B,c:&Cross<'_>)->Vec<G>{
        self.same_ports(c);
        super::direct_frame::normalized_top_record(b,c.size,c.ring,c.roles.flight,&self.bank(c))
    }
    fn natural_frame(&mut self,_b:&mut B,c:&Cross<'_>)->Vec<G>{
        self.same_ports(c);
        // The direct natural frame already is the physical ring frame.
        // Bottom uses the exact two-band Gate and full Y boundary reads.
        vec![]
    }
    fn v(&mut self,b:&mut B,c:&Cross<'_>,ht:bool,park:Option<usize>,inverse:bool){
        self.same_ports(c);assert_eq!(ht,self.ht);
        assert!(!self.payload_open&&self.payload.is_none());
        assert!(park.is_none()||park==Some(0)||park==Some(2));
        if self.v_record.is_none(){
            let r=c.roles;
            self.v_record=Some(super::midg::direct_v::record_three(b,c.size,c.ring,c.q,
                r.activity,r.flight,c.phase,r.work,self.cp.sz,&self.bank(c)));
        }
        // Route-free P1 has ONE identical full tape for the plain/top/
        // bottom parked sessions. Parks begin atY; forY>=32 none touches
        // Q0..30. ForY<=31 the tape uses restored ALT Q64..94. The full
        // Q[Y..128] word and x128 remain passengers of every complete V.
        b.play(self.v_record.as_ref().unwrap(),inverse);
    }
    fn toggle_activity(&mut self,b:&mut B,c:&Cross<'_>,ht:bool){
        self.same_ports(c);assert_eq!(ht,self.ht);
        assert!(!self.payload_open&&self.payload.is_none(),
            "PH must be phase metadata before any activity query");
        if ht{self.column.xor_ht_activity(b,self.cp,c.roles.activity);}
        else{self.column.toggle_hr_activity(b);}
    }
    fn divide(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,inverse:bool){
        self.same_ports(c);
        // Inside the final HR payload loop every park is already erased.
        // Each payload tick returns x128, so it is the global-zero carry.
        // Otherwise PH is normalized only inside the complete kernel.
        self.arithmetic().divide(b,c,target,gate,inverse);
    }
    fn add(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate){
        self.same_ports(c);assert!(!self.payload_open);
        self.arithmetic().add(b,c,target,gate);
    }
    fn vbit(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,top:VTop){
        self.same_ports(c);assert!(!self.payload_open);
        self.arithmetic().vbit(b,c,target,gate,top);
    }
    fn hr_payload_open(&mut self,b:&mut B,c:&Cross<'_>){
        self.same_ports(c);assert!(!self.ht&&!self.payload_open&&self.payload.is_none());
        // The controller calls this only after both sets of Q parks,
        // including x128, returned. No PH/q0/top-save passenger survives.
        if let Some(compact)=self.column.compact{
            let ranges=self.ranges();
            self.payload=Some(payload_three::digit(b,&Context{meta:c.size,compact,
                ring:c.ring,q:c.q,phase:c.phase},Self::payload_roles(c),false,
                ranges,&self.bank(c)));
        }
        // Even T2/T3 can now use the returned x128 as inverse-divide carry;
        // this switch does not itself change PH or materialize a payload.
        self.payload_open=true;
    }
    fn hr_payload_tick(&mut self,b:&mut B,c:&Cross<'_>,bit:usize){
        self.same_ports(c);assert!(!self.ht&&self.payload_open);
        if let Some(session)=&self.payload{
            let compact=self.column.compact.expect("open session requires compact P");
            super::hr_three::tick(b,&Context{meta:c.size,compact,
                ring:c.ring,q:c.q,phase:c.phase},session,Self::payload_roles(c),
                self.cp,bit,&self.bank(c));
        }
        // Tick preserves e, returns work, and does not read phase. The
        // controller's following inverse divide consumes exactly this e.
    }
    fn hr_payload_close(&mut self,b:&mut B,c:&Cross<'_>){
        self.same_ports(c);assert!(!self.ht&&self.payload_open);
        if let Some(session)=self.payload.take(){
            payload_three::finish_phase(b,c.size,&session,self.cp.sz,c.roles.flight,&self.bank(c));
        }
        self.payload_open=false;
    }
    fn z_flip(&mut self,b:&mut B,c:&Cross<'_>){
        self.same_ports(c);assert!(!self.payload_open&&self.payload.is_none());
        let tape=super::direct_frame::z_lane_record(b,c.size,c.ring,c.roles.flight,
            self.cp.sz,256,None,&self.bank(c));
        b.play(&tape,false);
    }
}

/// Ordinary HR columns use the full QB30/head32/window33 controller.
/// The former fixed HR QB23/head25 truncates rare adjacent remainders:
/// one threshold can be low by one and the next quotient can need28 bits.
/// Apply this to the complete HR family, never selected by actual inputs.
/// The public TT column retains the original X-1 / X+1 bracket:
/// there T=t=1 is possible and plain restoring erasure requires T<t.
/// Fixed HT retains its distinct DONE/counter extension.
fn fixed(cp:&ColPar)->bool{
    (!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq)
}

/// Complete direct middle3..7. The three physical scalars correspond to
/// outer [tag,cut,work] and middle [A,e,Q128].
pub(crate) struct DirectMiddle;
impl Middle for DirectMiddle{
    fn run_complete(&mut self,b:&mut B,column:&Column<'_>,cp:&ColPar){
        assert!(!cp.nomap&&cp.n==257&&cp.nq==128&&cp.qb==30);
        assert!(cp.hr||cp.ht);
        if fixed(cp){
            // FixedRawLayout transports E high bits, reserves all suffix
            // loans and the c139 counter/D passengers, then invokes exactly
            // one inherited fixed middle with QB23/head24/TC32. It returns
            // raw sizes/SX/counter before its literal inverse transport.
            super::fixed_three::run(b,column,cp);return;
        }
        assert!(98<=cp.sz.0&&cp.sz.0<=cp.sz.1&&cp.sz.1<=256);
        let roles=Roles{activity:column.roles.tag,flight:column.roles.cut,
            work:column.roles.work};
        let cross=Cross{size:column.meta,ring:column.ring,q:column.q,
            phase:column.phase,roles,dirty:column.dirty,
            y_bounds:(cp.sy.0.max(1),cp.sy.1.min(128)),qb:30,
            clean_external:column.clean_external};
        let mut kernels=CrossKernels{column,cp,ht:false,payload_open:false,
            payload:None,v_record:None,native_ring_v_record:None};
        let mut controller=super::normalized_three_controller::Controller::new(&cross,column.compact.is_some());
        if cp.hr{
            // Input tag=W. Because W=>!PH, XOR !PH converts it to the
            // exact HR activity !PH&!W; HR close converts it back to W.
            controller.hr_begin(b,&mut kernels,true);
            controller.hr_finish(b,&mut kernels);
        }
        assert!(!kernels.payload_open&&kernels.payload.is_none());
        if cp.sw{column.xor_switch(b,roles.activity);} // W ->0, PH restored.
        if cp.ht{
            kernels.ht=true;
            // Retain complete HT activity for S5, including DQ/DONE.
            // The direct digit may then replace PH by the payload extra.
            column.xor_ht_activity(b,cp,roles.activity);
            super::normalized_three_ht::run(b,&cross,cp.sz,column.compact);
            // S5 has closed PH. Clear this A BEFORE the S6 controller's
            // separate activity lifetime; Q and E/S predicates unchanged.
            column.xor_ht_activity(b,cp,roles.activity);
            controller.ht_finish(b,&mut kernels,true);
        }
        assert!(!kernels.payload_open&&kernels.payload.is_none());
        assert!(controller.is_raw());
        // All three roles are returned by the complete contracts. No
        // cleanup is inferred from a truncated upto/stage mode.
    }
}
