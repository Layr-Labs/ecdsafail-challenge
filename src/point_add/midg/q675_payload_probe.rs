// Included inside the test-only five-band module, with its unchanged Cross helpers.
impl Cross<'_> {
    // HT consumes the same quotient during add-back. Its source is the ring
    // bottom; the source-bound prefix mask excludes the changing opposite X.
    // Ordinary X is returned, directly matching the inverse five-band entry.
    fn q675_rejected_multiply_ht_payload(&self,b:&mut B) {
        let pl=self.pl.expect("HT payload interface");let n=self.fd.ring.len();assert_eq!(n,258);assert!(!self.cp.tt);
        for kk in 0..self.kmax {let tl=self.natural_tl(kk);self.gate_nat(b,kk,true);self.inplace_at(b,&tl);
            let span=(super::super::super::payload::NP-kk).min(n);
            let t:Vec<_>=(kk..kk+span).map(|i|super::super::super::payload::wl(&pl.p,i)).collect();
            let sh=((usize::BITS-1-(kk+1).leading_zeros())as usize).min(4);
            super::super::trans_masked_q(b,&t,&self.fd.ring[..span],n,kk,self.c(),&self.fd.sy,sh,self.sylo(),self.syhi(),self.fd.sx[0],self.c0(),&self.fd.sx[1..3],&[],&pl.dirty);
            self.mul_back_at(b,&tl);self.gate_nat(b,kk,false);
        }
    }
}

#[test]
fn q675_natural_hr_payload_and_rejected_ht_shortcut(){
    use super::super::super::{frogdrop_sched::N,q675_vform_tests::{receipt_audit,run_tape}};
    fn putn(q:&mut[u64],p:&[QubitId],lane:usize,n:N){for(i,p)in p.iter().enumerate(){let m=1<<lane;if n.bit(i){q[p.0 as usize]|=m}else{q[p.0 as usize]&=!m}}}
    fn readn(q:&[u64],p:&[QubitId],lane:usize)->N{p.iter().enumerate().fold(N::ZERO,|a,(i,p)|a|(N::from((q[p.0 as usize]>>lane)&1)<<i))}
    super::super::super::bake_knobs();let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
    let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(&super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp=&mut cps[36];cp.n=258;cp.h=1;let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
    assert!(!cp.tt);
    let vg=rec(&mut b,|b|{let v=&sc.sz[..VB];super::super::super::frogdrop::reg_add_into(b,v,&fd.sy[..VB],&[],sc.f);
        for i in 0..VB{if VOFF>>i&1!=0{super::super::super::modp_frogdrop::inc_dirty_free(b,&v[i..],&dirty);}}
    });
    let pl=super::super::super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
    assert_eq!(pl.dirty.len(),28);
    let c=Cross{fd:&fd,cp,sc:&sc,pl:Some(&pl),vform:&[],parked:&[],parked_ht:&[],vg:&vg,zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
    c.toggle_hr_act(&mut b);c.q675_divide_natural(&mut b);c.toggle_hr_act(&mut b);let div=b.ops.clone();let divt=b.tof;
    b.ops.clear();b.tof=0;c.toggle_hr_act(&mut b);c.q675_multiply_natural(&mut b,false);c.toggle_hr_act(&mut b);let restore=b.ops.clone();let restoret=b.tof;
    b.ops.clear();b.tof=0;c.toggle_hr_act(&mut b);c.q675_divide_natural(&mut b);c.q675_multiply_natural(&mut b,true);c.toggle_hr_act(&mut b);let payload=b.ops.clone();let payloadt=b.tof;
    b.ops.clear();b.tof=0;c.toggle_ht_act(&mut b,false);c.q675_divide_natural(&mut b);c.q675_rejected_multiply_ht_payload(&mut b);c.toggle_ht_act(&mut b,false);let ht_payload=b.ops.clone();let htt=b.tof;
    let h=[receipt_audit(&div),receipt_audit(&restore),receipt_audit(&payload),receipt_audit(&ht_payload)];
    let mut cases=vec![];
    for sy in cp.sy.0..=cp.sy.1.min(128){for gap in[0,1,4,5,10,15,20,22]{let sz=257-sy-gap;
        if sz<cp.sz.0||sz>cp.sz.1||sy>sz{continue;}
        for seed in 0..8usize{cases.push((sy,sz,gap,seed));}
    }}
    let wtop=259-if cp.dl{cp.dlr.min(L0P+1)}else{L0P+1};
    let top:Vec<_>=fd.ring.iter().rev().copied().collect();let w:Vec<_>=pl.p.iter().rev().take(wtop).copied().collect();
    let fullw:Vec<_>=pl.p.iter().rev().copied().collect();let mut count=0;let mut missing_payload=0;let mut rejected_ht_lanes=0;
    for tape in 0..3 {for active in[0,u64::MAX,0x5555555555555555]{for batch in cases.chunks(64){
        let mut input=vec![0;675];input[fd.ph.0 as usize]=!active;
        for(i,&p)in pl.p.iter().enumerate(){input[p.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i*11+tape)as u32);}
        let mut expected_div=input.clone();let mut expected_payload=input.clone();
        for(lane,&(sy,sz,gap,seed))in batch.iter().enumerate(){
            let mask=(N::from(1)<<(sy-1))-N::from(1);
            let y=(N::from(1)<<(sy-1))|if seed==0{N::from(1)}else if seed==1{mask}else{N::from(0xd1b54a32d192ed03u64.rotate_left(seed as u32))&mask}|N::from(1);
            let cap=(1usize<<gap)-1;let quotient=match seed%4{0=>0,1=>1.min(cap),2=>cap/2,_=>cap};let rem=if seed%2==0{N::ZERO}else{y-N::from(1)};
            let x=y*N::from(quotient)+rem;assert!(x<(N::from(1)<<(257-sz)));
            putn(&mut input,&fd.q,lane,y);putn(&mut input,&fd.sy,lane,N::from(sy));putn(&mut input,&sc.sz,lane,N::from(sz));
            putn(&mut input,&fd.ring[..sz],lane,(N::from(1)<<(sz-1))|N::from(99991));putn(&mut input,&top[..258-sz],lane,x);
        }
        expected_div.clone_from(&input);expected_payload.clone_from(&input);
        for(lane,&(sy,sz,_,_))in batch.iter().enumerate(){if active>>lane&1!=0{
            let y=readn(&input,&fd.q,lane);let x=readn(&input,&top[..258-sz],lane);let quotient=x/y;let rem=x%y;
            putn(&mut expected_div,&top[..258-sz],lane,rem|(quotient<<sy));
            let oldw=readn(&input,&w,lane);putn(&mut expected_payload,&w,lane,(oldw+quotient*y)&((N::from(1)<<wtop)-N::from(1)));
        }}
        let out=run_tape(&div,675,&input,tape);assert_eq!(out.q,expected_div,"division tape{tape} active{active:x}");
        let back=run_tape(&restore,675,&expected_div,tape);assert_eq!(back.q,input,"restore tape{tape} active{active:x}");
        let carried=run_tape(&payload,675,&input,tape);assert_eq!(carried.q,expected_payload,"payload tape{tape} active{active:x}");count+=batch.len();
        let mut htin=input.clone();htin[fd.ph.0 as usize]=active;let mut htwant=htin.clone();
        for(lane,&(sy,sz,_,_))in batch.iter().enumerate(){if active>>lane&1!=0{
            let y=readn(&htin,&fd.q,lane);let x=readn(&htin,&top[..258-sz],lane);let quotient=x/y;let z=readn(&htin,&fd.ring[..sz],lane);let mut w=readn(&htin,&fullw,lane);
            for kk in 0..23{if quotient.bit(kk){assert!(sz+sy+kk<=257);let sh=((usize::BITS-1-(kk+1).leading_zeros())as usize).min(4);
                let high=258-(sy>>sh)*(1<<sh);let mask=(N::from(1)<<high)-N::from(1);w=(w&!mask)|((w+(z<<kk))&mask);
            }}putn(&mut htwant,&fullw,lane,w);
            if w!=readn(&htin,&fullw,lane){missing_payload+=1;}
        }}
        let htout=run_tape(&ht_payload,675,&htin,tape);
        for i in 0..675{if !pl.p.iter().any(|p|p.0 as usize==i){assert_eq!(htout.q[i],htwant[i],"rejected shortcut must retain all nonpayload state");}}
        for lane in 0..batch.len(){if pl.p.iter().any(|p|((htout.q[p.0 as usize]^htwant[p.0 as usize])>>lane)&1!=0){if rejected_ht_lanes==0{eprintln!("Q675_HT_SHORTCUT_FIRST_NEGATIVE case={:?} lane={lane} tape={tape} active={active:x}",batch[lane]);}rejected_ht_lanes+=1;}}
    }}}
    assert!(missing_payload>0);assert!(rejected_ht_lanes>0);eprintln!("Q675_QUOTIENT_PAYLOAD_PASS lanes_per_arm={count} div_ops={} div_T={divt} restore_ops={} restore_T={restoret} payload_ops={} payload_T={payloadt} ht_payload_ops={} ht_payload_T={htt} rejected_ht_payload_lanes={rejected_ht_lanes} HT_NOT_ADMITTED=true omitted_payload_detected={missing_payload} HMR={h:?} Q=675 actual_col=36 dl={} wtop={wtop} TT_unimplemented=true",div.len(),restore.len(),payload.len(),ht_payload.len(),cp.dl);
}
