//! SOURCE-ONLY optional high-E cache and virtual-boundary/lower-write fusion.
//! The enclosing complete-Y record, not individual bands, is inverted.
use super::{B,G,Cross,Gate,VTop,Op,QubitId,cover,product,price,sum_interval,literal,bank,witness};

fn tof(n:usize)->usize{match n{0|1=>0,2=>1,n=>4*(n-2)}}
fn guard_price(c:&Cross<'_>,gate:Gate)->usize{
    match gate{
        Gate::Bottom(k)=>{
            let byte:Vec<_>=c.size.y.iter().copied().chain([c.roles.mask]).collect();
            188+4*price(&product(cover(&byte,128-k,256),cover(&c.size.sum,17-k,32)))
        }
        Gate::Top(k)|Gate::Natural(k)=>4*price(&cover(&c.size.sum,0,32-k))
            .min(price(&cover(&c.size.sum,32-k,32))),
    }
}
fn low_gate_limit(gate:Gate)->usize{match gate{
    Gate::Bottom(k)=>17-k,Gate::Top(k)|Gate::Natural(k)=>32-k,
}}
fn high_guard_price(c:&Cross<'_>,gate:Gate,op:Op)->usize{
    if matches!(op,Op::Add){return 16;}
    2*(4+price(&product(cover(&c.size.y,0,96),cover(&c.size.sum,0,low_gate_limit(gate)))))
}
/// Scalar source-price walk: no builder or gate-record capture.
fn cost(c:&Cross<'_>,lo:usize,hi:usize,gate:Gate,op:Op,fused:bool,high:bool,external:bool)->usize{
    let mut cur:Option<(bool,usize,usize,usize)>=None;
    let mut root:Option<usize>=None;
    let mut total=0usize;
    let mut query=|y:usize,top:Option<bool>,extra:usize|{
        let (n,p,v,base,h)=if high&&y>=97{(5,if external{4}else{2},(y-1)&31,if external{2}else{4},true)}
            else if y>=97{(7,if external{2}else{0},y-1,if external{6}else{8},false)}
            else{let n=if y<=64{6}else{5};(n,n-1,(y-1)&((1<<n)-1),if external{2}else if n==6{3}else{4},false)};
        if cur.map(|(ch,cn,cp,_)|(ch,cn,cp))!=Some((h,n,p)){
            if let Some((_,_,cp,_))=cur{total+=cp;}cur=None;
        }
        if p>0{
            let mut keep=0;
            if let Some((_,_,_,old))=cur{
                while keep<p&&((old^v)>>(n-2-keep))==0{keep+=1;}total+=p-keep;
            }
            total+=p-keep;cur=Some((h,n,p,v));
        }
        if external&&y<=96&&root!=Some(n){
            if let Some(old)=root{total+=if old==6{1}else{3};}
            total+=if n==6{1}else{3};root=Some(n);
        }
        let(lo,hi)=if matches!(op,Op::Add){(0,32)}else{sum_interval(top,c.qb).unwrap()};
        total+=cover(&c.size.sum,lo,hi).iter().map(|t|tof(base+t.len()+extra)).sum::<usize>();
    };
    let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in(0..=hi).rev(){
        if matches!(op,Op::Add){if (lo..=hi).contains(&i){query(i,None,1);query(i,None,0);}continue;}
        for leading in[true,false]{
            if leading&&!split{continue;}let y=if leading{i+1}else{i};
            if !(lo..=hi).contains(&y){continue;}
            let top=if split{Some(leading)}else{None};query(y,top,0);query(y,top,0);
        }
    }
    drop(query);
    if let Some((_,_,p,_))=cur{total+=p;}
    if let Some(n)=root{total+=if n==6{1}else{3};}
    if !matches!(op,Op::Add){
        total+=guard_price(c,gate);
        total+=(hi-lo+1)*if fused{4}else{8};
        if fused{total+=2*((hi.min(127)+1).saturating_sub(lo));}
        if split{total+=(hi-lo+1)*if fused{4}else{5};}
    }
    let narrow=high&&lo<97;
    if narrow{total+=high_guard_price(c,gate,op);}
    total+=2*(hi+1).min(128);
    total+=if matches!(op,Op::Add){hi+if narrow{3*(hi-96)}else{0}}
        else{4*(hi+usize::from(fused))};
    total
}
pub(super) fn select(c:&Cross<'_>,lo:usize,hi:usize,gate:Gate,op:Op)->Option<(bool,bool)>{
    let mut best=cost(c,lo,hi,gate,op,false,false,false);let mut choice=None;
    for external in[false,true]{
        if external&&c.clean_external.len()<2{continue;}
        for high in[false,true]{
            if high&&hi<97{continue;}let next=cost(c,lo,hi,gate,op,true,high,external);
            if next<best{best=next;choice=Some((high,external));}
        }
    }choice
}

fn not_high(b:&mut B,c:&Cross<'_>,control:QubitId,target:QubitId,dirty:&[QubitId]){
    b.cx(control,target);
    literal(b,&[(c.size.y[5],false),(c.size.y[6],false),(control,false)],target,dirty);
}
/// This is NOT an unqualified nested e-witness. After F_G, e may contain
/// Aold & !G. The second transfer explicitly retains G on the low class.
fn high_guard(b:&mut B,c:&Cross<'_>,gate:Gate,op:Op,dirty:&[QubitId])->Vec<G>{
    let r=c.roles;b.begin();
    if matches!(op,Op::Add){
        not_high(b,c,r.flight,r.mask,dirty);not_high(b,c,r.mask,r.flight,dirty);
    }else{
        not_high(b,c,r.activity,r.flight,dirty);
        for mut t in product(cover(&c.size.y,0,96),cover(&c.size.sum,0,low_gate_limit(gate))){
            t.push((r.flight,false));literal(b,&t,r.activity,dirty);
        }
    }b.end()
}
struct Reader<'a>{e:&'a[QubitId],qpre:&'a[QubitId],external:&'a[QubitId],high:bool,
    cur:Option<(bool,usize,usize,usize)>,root:Option<(usize,QubitId)>}
impl Reader<'_>{
    fn pre(&self,h:bool,n:usize)->Vec<QubitId>{
        if h{self.e[5..7].iter().chain(self.external).copied().collect()}
        else if n==7{self.external.to_vec()}else{self.qpre.to_vec()}
    }
    fn root_xor(&self,b:&mut B,n:usize,control:QubitId){
        if n==6{b.x(self.e[6]);b.ccx(control,self.e[6],self.external[0]);b.x(self.e[6]);}
        else{b.ccx(control,self.e[6],self.external[1]);b.x(self.e[5]);
            b.ccx(self.external[1],self.e[5],self.external[0]);b.x(self.e[5]);
            b.ccx(control,self.e[6],self.external[1]);}
    }
    fn clear_root(&mut self,b:&mut B){if let Some((n,c))=self.root{self.root_xor(b,n,c);}self.root=None;}
    fn cell(&self,b:&mut B,h:bool,n:usize,level:usize,v:usize){
        let pre=self.pre(h,n);
        let(a,na)=if level==0{(self.e[n-1],v>>(n-1)&1==0)}else{(pre[level-1],false)};
        let(z,nz)=(self.e[n-2-level],v>>(n-2-level)&1==0);
        if na{b.x(a);}if nz{b.x(z);}b.ccx(a,z,pre[level]);if nz{b.x(z);}if na{b.x(a);}
    }
    fn clear(&mut self,b:&mut B){if let Some((h,n,p,v))=self.cur{
        for level in(0..p).rev(){self.cell(b,h,n,level,v);}
    }self.cur=None;self.clear_root(b);}
    fn finish_high(&mut self,b:&mut B,guard:&[G]){
        if self.high{self.clear(b);b.x(self.e[5]);b.x(self.e[6]);b.play(guard,true);self.high=false;}
    }
    fn query(&mut self,b:&mut B,c:&Cross<'_>,y:usize,top:Option<bool>,target:QubitId,
        control:QubitId,extra:&[(QubitId,bool)],add:bool,guard:&[G],dirty:&[QubitId]){
        if y<97{self.finish_high(b,guard);}
        let h=self.high&&y>=97;let n=if h{5}else if y<=64{6}else if y<=96{5}else{7};
        let external=self.external.len()==2;
        let p=if h{if external{4}else{2}}else if y<=96{n-1}else if external{2}else{0};
        let v=(y-1)&((1<<n)-1);
        if self.cur.map(|(ch,cn,cp,_)|(ch,cn,cp))!=Some((h,n,p)){self.clear(b);}
        let mut eq=vec![];
        if p>0{
            let mut keep=0;
            if let Some((_,_,_,old))=self.cur{
                while keep<p&&((old^v)>>(n-2-keep))==0{keep+=1;}
                for level in(keep..p).rev(){self.cell(b,h,n,level,old);}
            }
            for level in keep..p{self.cell(b,h,n,level,v);}
            self.cur=Some((h,n,p,v));
            let pre=self.pre(h,n);eq.push((pre[p-1],false));
            for i in 0..n-p-1{eq.push((self.e[i],v>>i&1==0));}
            if !h&&y<=96&&!external{eq.push((self.e[6],y<=64));if y>64{eq.push((self.e[5],true));}}
        }else{eq.extend(self.e.iter().enumerate().map(|(i,&q)|(q,(y-1)>>i&1==0)));}
        let control=if external&&y<=96{
            if self.root!=Some((n,control)){self.clear_root(b);self.root_xor(b,n,control);self.root=Some((n,control));}
            self.external[0]
        }else{control};
        let(lo,hi)=if add{(0,32)}else{sum_interval(top,c.qb).unwrap()};
        for mut t in cover(&c.size.sum,lo,hi){t.extend_from_slice(&eq);t.push((control,false));
            t.extend_from_slice(extra);literal(b,&t,target,dirty);}
    }
}

pub(super) fn record(b:&mut B,c:&Cross<'_>,t:&[QubitId],gate:Gate,op:Op,
    ht:bool,payload_open:bool,high:bool,use_external:bool)->Vec<G>{
    let r=c.roles;let hi=t.len()-1;let lo=c.y_bounds.0;
    let s=&c.q[..(hi+1).min(128)];let carry=if payload_open{r.x128}else{c.phase};
    let dirty=bank(c);let narrow=high&&lo<97;
    let external=if use_external{assert!(c.clean_external.len()>=2);&c.clean_external[..2]}else{&[]};
    let mut reader=Reader{e:&c.size.y,qpre:&c.q[120..125],external,high,cur:None,root:None};
    let add=matches!(op,Op::Add);let complement=matches!(op,Op::Divide);
    b.begin();let guard=if add{vec![]}else{witness(b,c,gate,&dirty)};b.play(&guard,false);
    if !payload_open&&ht{b.cx(r.activity,c.phase);}
    let hg=if narrow{high_guard(b,c,gate,op,&dirty)}else{vec![]};b.play(&hg,false);
    if high{b.x(c.size.y[5]);b.x(c.size.y[6]);}
    if complement{for &q in t{b.x(q);}}
    for i in 0..s.len(){let x=if i==0{carry}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);}
    for i in(0..t.len()).rev(){
        let x=if i==0{carry}else{s[i-1]};
        if i<s.len(){b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);}
        if add{
            if i<hi{b.cx(s[i],x);
                if narrow&&reader.high{literal(b,&[(r.flight,false),(r.mask,false),(x,false)],t[i],&dirty);}
                else{b.ccx(r.mask,x,t[i]);}b.cx(s[i],x);}
            if (lo..=hi).contains(&i){
                reader.query(b,c,i,None,t[i],r.flight,&[(x,false)],true,&hg,&dirty);
                reader.query(b,c,i,None,r.mask,r.flight,&[],true,&hg,&dirty);
            }continue;
        }
        let split=matches!(op,Op::VBit(VTop::Frame(0)));
        if split&&(lo..=hi).contains(&(i+1)){
            reader.query(b,c,i+1,Some(true),r.mask,r.activity,&[],false,&hg,&dirty);
            literal(b,&[(r.mask,false),(t[i],true),(x,true)],r.flight,&dirty);
            reader.query(b,c,i+1,Some(true),r.mask,r.activity,&[],false,&hg,&dirty);
        }
        let normal=(lo..=hi).contains(&i);let top=if split{Some(false)}else{None};
        if normal{
            reader.query(b,c,i,top,r.mask,r.activity,&[],false,&hg,&dirty);
            b.cx(r.mask,r.flight);literal(b,&[(r.mask,false),(t[i],false),(x,false)],r.flight,&dirty);
        }
        // M removes exactly the physical virtual-zero source cell.
        // Leading source is actual ONE and needs no correction.
        if i<s.len(){b.cx(s[i],x);if normal{b.ccx(r.mask,s[i],x);}}
        literal(b,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);
        if i<s.len(){if normal{b.ccx(r.mask,s[i],x);}b.cx(s[i],x);}
        if normal{reader.query(b,c,i,top,r.mask,r.activity,&[],false,&hg,&dirty);}
    }
    reader.clear(b);reader.finish_high(b,&hg);
    if add{b.cx(r.flight,r.mask);}
    if complement{for &q in t{b.x(q);}}
    if !payload_open&&ht{b.cx(r.activity,c.phase);}
    b.play(&guard,true);b.end()
}
