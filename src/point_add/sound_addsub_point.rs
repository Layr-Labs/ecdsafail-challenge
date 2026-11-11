//! Full secp256k1 point addition. Exact field products, full Solinas reduction,
//! M2 payload division/multiplication, and a reversible finite-exception wrapper.
//! Classical preprocessing depends ONLY on the supplied classical offset.
use super::super::{Build,Gate,Spec};
use super::PayloadProgram;
use std::{fs::File,io::{Read,Write,Seek,SeekFrom,BufWriter},path::Path};

pub const NONE:u16=u16::MAX;
pub const CLASS_X:u16=20;
pub const CLASS_CX:u16=21;
pub const CLASS_CCX:u16=22;
pub const CLASS_SWAP:u16=23;
/// Fixed-size local IR. Classical CCX is a reversible Boolean toggle expanded
/// into a balanced PUSH/conditional BIT_INVERT/POP block in the public format.
#[derive(Clone,Copy,Debug)]
pub struct Micro {pub kind:u16,pub a:u16,pub b:u16,pub t:u16,pub cond:u16}
impl Micro {
    pub fn bytes(self)->[u8;12] {let mut r=[0;12];for(i,x)in [self.kind,self.a,self.b,self.t,self.cond,0].into_iter().enumerate(){r[2*i..2*i+2].copy_from_slice(&x.to_le_bytes());}r}
    pub fn read(r:&[u8])->Self {let f=|i:usize|u16::from_le_bytes(r[2*i..2*i+2].try_into().unwrap());Self{kind:f(0),a:f(1),b:f(2),t:f(3),cond:f(4)}}
    pub fn real_len(self)->u64 {if self.kind==CLASS_CCX||self.kind==CLASS_SWAP{3}else{1}}
}
pub struct Writer {file:BufWriter<File>,pub count:u64,pub real_count:u64,pub toffolis:u64,pub max_q:u16,pub max_c:u16}
impl Writer {
    pub fn new(path:&Path)->Self {Self{file:BufWriter::with_capacity(4*1024*1024,File::create(path).unwrap()),count:0,real_count:0,toffolis:0,max_q:0,max_c:511}}
    pub fn emit(&mut self,m:Micro) {
        self.file.write_all(&m.bytes()).unwrap();self.count+=1;self.real_count+=m.real_len();
        if m.kind<20 {
            self.max_q=self.max_q.max(m.t);if m.kind!=6{self.max_q=self.max_q.max(m.a);}if m.kind==13{self.max_q=self.max_q.max(m.b);self.toffolis+=1;}
            if m.cond!=NONE{self.max_c=self.max_c.max(m.cond);}
        }else{self.max_c=self.max_c.max(m.t);if m.kind!=CLASS_X{self.max_c=self.max_c.max(m.a);}if m.kind==CLASS_CCX{self.max_c=self.max_c.max(m.b);}}
    }
    pub fn flush(&mut self){self.file.flush().unwrap();}
    pub fn append_reverse(&mut self,path:&Path,start:u64,end:u64) {
        self.flush();let mut rd=File::open(path).unwrap();let mut pos=end;
        while pos>start {let n=(pos-start).min(32768);let mut bytes=vec![0;n as usize*12];rd.seek(SeekFrom::Start((pos-n)*12)).unwrap();rd.read_exact(&mut bytes).unwrap();for r in bytes.chunks_exact(12).rev(){self.emit(Micro::read(r));}pos-=n;}
    }
}
#[derive(Clone,Copy)]
pub enum Coord {Add,Sub,Rsub,Neg}
pub struct FieldProgram {pub gates:Vec<Gate>,pub qubits:usize,pub ports:usize}
fn new_build()->Build {Build{sites:vec![],gates:vec![],next:0,mask:vec![],carry:0,prime:Spec::secp256k1().prime}}

pub fn coordinate(op:Coord)->FieldProgram {
    let mut b=new_build();let source=b.alloc(256);let dst=b.alloc(256);
    let mut a=source; a.extend(b.alloc(2));let mut x=dst;x.extend(b.alloc(2));
    b.mask=b.alloc(258);b.carry=b.bit();let flag=b.bit();let one=b.bit();b.x(one);
    match op {
        Coord::Add=>b.payload_add(one,&a,&x,flag),
        Coord::Sub=>{let start=b.gates.len();b.payload_add(one,&a,&x,flag);b.gates[start..].reverse();},
        Coord::Rsub=>{b.payload_neg(one,&x,flag);b.payload_add(one,&a,&x,flag);},
        Coord::Neg=>b.payload_neg(one,&x,flag),
    }
    b.x(one);for &g in &b.gates{g.op().validate();}
    FieldProgram{gates:b.gates,qubits:b.next,ports:512}
}
/// Compute the FULL 512-bit product, then three FULL Solinas folds, retaining
/// all intermediates until exact Bennett cleanup. No shifted short windows.

/// Exact Litinski controlled add/subtract schoolbook (arXiv:2410.00899).
/// Row i is NONNEGATIVE: (1-a_i)2^(n+i)+(2a_i-1)2^i*c.
/// Its partial sum is <2^(n+i+1); the newly introduced carry-out is0
/// beforehand. All n+1 row bits participate, with the carry-out retained.
fn school_prefix(b:&mut Build,a:&[u16],c:&[u16])->Vec<u16>{
 let n=a.len();assert_eq!(c.len(),n);let product=b.alloc(2*n+1);b.mask=b.alloc(2*n+1);b.carry=b.bit();
 for i in 0..n{
  for &q in &product[i..i+n]{b.x(q);b.cx(a[i],q);}
  let m=b.mask[..n+1].to_vec();for j in 0..n{b.cx(c[j],m[j]);}
  b.add(&m,&product[i..i+n+1],false);
  for j in 0..n{b.cx(c[j],m[j]);}
  for &q in &product[i..i+n+1]{b.x(q);b.cx(a[i],q);}
 }
 // Exact corrections in a FULL 2n+1-bit accumulator, including sign/overflow.
 // Add2^n(a+1), subtract(2^(2n)+c), add2^n*c, giving2*a*c.
 let m=b.mask[..n+1].to_vec();for j in 0..n{b.cx(a[j],m[j]);}b.x(b.carry);b.add(&m,&product[n..],false);b.x(b.carry);for j in 0..n{b.cx(a[j],m[j]);}
 let m=b.mask.clone();for j in 0..n{b.cx(c[j],m[j]);}b.x(m[2*n]);b.add(&m,&product,true);b.x(m[2*n]);for j in 0..n{b.cx(c[j],m[j]);}
 let m=b.mask[..n+1].to_vec();for j in 0..n{b.cx(c[j],m[j]);}b.add(&m,&product[n..],false);for j in 0..n{b.cx(c[j],m[j]);}
 // Low bit is EXACTLY0 by2*a*c. Rotate retains the entire2n-bit product;
 // the extra highest guard becomes0. No carry, borrow or window is dropped.
 b.rotate_right_zero(&product);product
}
/// Exact triangular square. The positive rows keep their full carry-out.
/// Summed bias: Q=cross-(diag-a)+2^(2n)-2^n*(a+1).
/// Full-word corrections give a^2, including every wrap/borrow.
fn triangle_prefix(b:&mut Build,a:&[u16])->Vec<u16>{
 let n=a.len();let product=b.alloc(2*n+1);b.mask=b.alloc(2*n+1);b.carry=b.bit();
 for i in 0..n{
  let len=n-i-1;let lo=2*i+1;
  for &q in &product[lo..lo+len]{b.x(q);b.cx(a[i],q);}
  let m=b.mask[..len+1].to_vec();for j in 0..len{b.cx(a[i+1+j],m[j]);}
  b.add(&m,&product[lo..lo+len+1],false);
  for j in 0..len{b.cx(a[i+1+j],m[j]);}
  for &q in &product[lo..lo+len+1]{b.x(q);b.cx(a[i],q);}
 }
 let m=b.mask[..n+1].to_vec();for j in 0..n{b.cx(a[j],m[j]);}b.x(b.carry);b.add(&m,&product[n..],false);b.x(b.carry);for j in 0..n{b.cx(a[j],m[j]);}
 // Subtract2^(2n), exactly modulo the FULL2n+1-bit word.
 b.x(product[2*n]);
 let m=b.mask.clone();for j in 0..n{b.cx(a[j],m[2*j+1]);}b.add(&m,&product,false);for j in 0..n{b.cx(a[j],m[2*j+1]);}
 for j in 0..n{b.cx(a[j],m[j]);}b.add(&m,&product,true);for j in 0..n{b.cx(a[j],m[j]);}
 product
}
fn product_prefix(b:&mut Build,a:&[u16],c:&[u16])->Vec<u16>{
 assert_eq!(a.len(),256);let product=if a==c{triangle_prefix(b,a)}else{school_prefix(b,a,c)};assert_eq!(product.len(),513);
 // These two extra wires are proved zero; the full512 product bits remain.
 b.mask.truncate(512);reduce_prefix(b,&product[..512])
}
fn reduce_prefix(b:&mut Build,product:&[u16])->Vec<u16> {
    // F=2^32+977 has these seven positive binary terms.
    const SHIFTS:[usize;7]=[0,4,6,7,8,9,32];
    // Exact zero-mask lifetime reuse, not arithmetic truncation. Upper223
    // product-mask wires are zero now and fold1 never uses them as scratch.
    let full_mask=b.mask.clone();assert_eq!(full_mask.len(),512);
    let mut fold1=full_mask[289..].to_vec();fold1.extend(b.alloc(289-fold1.len()));
    b.mask=full_mask[..289].to_vec();
    for i in 0..256{b.cx(product[i],fold1[i]);}
    for shift in SHIFTS {
        let m=b.mask[..289-shift].to_vec();
        for j in 0..256{b.cx(product[256+j],m[j]);}
        b.add(&m,&fold1[shift..],false);
        for j in 0..256{b.cx(product[256+j],m[j]);}
    }
    // Exact in-place second fold. ALL original33 high bits are retained.
    // Upper31 zero mask wires hold31 saved bits, with only2 fresh wires.
    let mut high1=b.mask[258..].to_vec();high1.extend(b.alloc(33-high1.len()));
    assert_eq!(high1.len(),33);b.mask.truncate(258);
    for j in 0..33{b.cx(fold1[256+j],high1[j]);b.cx(high1[j],fold1[256+j]);}
    let mut fold2=fold1[..257].to_vec(); // FULL proved257-bit second fold.
    for shift in SHIFTS{
        let m=b.mask[..257-shift].to_vec();
        for j in 0..33{b.cx(high1[j],m[j]);}
        b.add(&m,&fold2[shift..],false);
        for j in 0..33{b.cx(high1[j],m[j]);}
    }
    // Retain second-fold top bit. Original fold1 bit257 is already PROVED0,
    // so it supplies the full258th guard without allocating a new wire.
    let high2=b.bit();b.cx(fold2[256],high2);b.cx(high2,fold2[256]);
    fold2.push(fold1[257]);assert_eq!(fold2.len(),258);
    let fbits:Vec<_>=(0..33).map(|i|((1u64<<32)+977)>>i&1!=0).collect();
    b.constant(&fold2,&fbits,Some(high2),false);
    let ge=b.ge_prime(&fold2);b.prime_add(&fold2,Some(ge),true);
    fold2

}
pub fn product_oracle()->FieldProgram {
    let mut b=new_build();let a=b.alloc(256);let c=b.alloc(256);let out=b.alloc(256);
    let start=b.gates.len();let reduced=product_prefix(&mut b,&a,&c);let end=b.gates.len();
    for i in 0..256{b.cx(reduced[i],out[i]);}
    for i in (start..end).rev(){b.gates.push(b.gates[i]);}
    for &g in &b.gates{g.op().validate();}
    FieldProgram{gates:b.gates,qubits:b.next,ports:768}
}
pub fn reduction_oracle()->FieldProgram {
    let mut b=new_build();let input=b.alloc(512);let out=b.alloc(256);
    b.mask=b.alloc(512);b.carry=b.bit();let start=b.gates.len();
    let reduced=reduce_prefix(&mut b,&input);let end=b.gates.len();
    for i in 0..256{b.cx(reduced[i],out[i]);}
    for i in (start..end).rev(){b.gates.push(b.gates[i]);}
    for &g in &b.gates{g.op().validate();}
    FieldProgram{gates:b.gates,qubits:b.next,ports:768}
}
pub fn square_subtract()->FieldProgram {
    let mut b=new_build();let x=b.alloc(256);let y=b.alloc(256);let mut wide_x=x;wide_x.extend(b.alloc(2));
    let one=b.bit();let flag=b.bit();b.x(one);
    let start=b.gates.len();let reduced=product_prefix(&mut b,&y,&y);let end=b.gates.len();
    let subtract=b.gates.len();b.payload_add(one,&reduced,&wide_x,flag);b.gates[subtract..].reverse();
    for i in (start..end).rev(){b.gates.push(b.gates[i]);}
    b.x(one);for &g in &b.gates{g.op().validate();}
    FieldProgram{gates:b.gates,qubits:b.next,ports:512}
}
pub fn equality()->FieldProgram {
    // Input bits temporarily become complemented differences; target flag XORs
    // their FULL 512-bit equality. Ancillas are clean at return.
    let mut b=new_build();let data=b.alloc(512);let flag=b.bit();b.mask=b.alloc(510);
    for &q in &data{b.x(q);}b.payload_mcx(&data,flag);for &q in &data{b.x(q);}
    FieldProgram{gates:b.gates,qubits:b.next,ports:513}
}

struct Classical {next:usize,work:Vec<u16>,nonzero:u16,x2:Vec<u16>,y2:Vec<u16>,x3:Vec<u16>,y3:Vec<u16>,gated:std::collections::HashMap<u16,u16>}
impl Classical {
    fn alloc(&mut self,n:usize)->Vec<u16>{assert!(self.next+n<NONE as usize);let out=(self.next..self.next+n).map(|i|i as u16).collect();self.next+=n;out}
    fn word(&mut self)->Vec<u16>{self.alloc(256)}
    fn copy(&mut self,w:&mut Writer,source:&[u16])->Vec<u16>{let out=self.word();for (&a,&t)in source.iter().zip(&out){w.emit(Micro{kind:CLASS_CX,a,b:0,t,cond:NONE});}out}
    fn append(&self,w:&mut Writer,gates:&[Gate],ports:&[u16],port_count:usize,reverse:bool) {
        let map=|q:u16|if (q as usize)<port_count{ports[q as usize]}else{self.work[q as usize-port_count]};
        let mut one=|g:Gate|{
            let t=map(g.t);let a=if g.kind==6{0}else{map(g.a)};let b=if g.kind==13{map(g.b)}else{0};
            let kind=match g.kind{6=>CLASS_X,8=>CLASS_CX,10=>CLASS_SWAP,13=>if a==b{CLASS_CX}else{CLASS_CCX},_=>panic!()};
            if (kind==CLASS_CX||kind==CLASS_SWAP)&&a==t{return;}
            w.emit(Micro{kind,a,b,t,cond:NONE});
        };
        if reverse{for &g in gates.iter().rev(){one(g);}}else{for &g in gates{one(g);}}
    }
    fn coord(&self,w:&mut Writer,p:&FieldProgram,source:&[u16],target:&[u16]){let ports:Vec<_>=source.iter().chain(target).copied().collect();self.append(w,&p.gates,&ports,512,false);}
    fn mul(&mut self,w:&mut Writer,p:&FieldProgram,a:&[u16],b:&[u16])->Vec<u16>{let out=self.word();let ports:Vec<_>=a.iter().chain(b).chain(&out).copied().collect();self.append(w,&p.gates,&ports,768,false);out}
    fn divide(&self,w:&mut Writer,p:&PayloadProgram,a:&[u16],y:&[u16]){let ports:Vec<_>=a.iter().chain(y).copied().collect();self.append(w,&p.gates,&ports,512,false);}
    fn xor(&mut self,w:&mut Writer,a:u16,b:u16)->u16 {
        if a==b{return NONE;}if a==NONE{return b;}if b==NONE{return a;}
        let t=self.alloc(1)[0];w.emit(Micro{kind:CLASS_CX,a,b:0,t,cond:NONE});w.emit(Micro{kind:CLASS_CX,a:b,b:0,t,cond:NONE});t
    }
    fn gate(&mut self,w:&mut Writer,a:u16)->u16 {
        if a==NONE{return NONE;}
        if let Some(&g)=self.gated.get(&a){return g;}
        let t=self.alloc(1)[0];w.emit(Micro{kind:CLASS_CCX,a:self.nonzero,b:a,t,cond:NONE});self.gated.insert(a,t);t
    }
    fn gated_word(&mut self,w:&mut Writer,a:&[u16])->Vec<u16>{a.iter().map(|&bit|self.gate(w,bit)).collect()}
}
pub struct PointInfo {pub macros:u64,pub records:u64,pub toffolis:u64,pub qubits:usize,pub bits:usize,pub classical_end:u64,pub quantum_end:u64,pub c_nonzero:u16,pub c_x2:Vec<u16>,pub c_y2:Vec<u16>,pub c_x3:Vec<u16>,pub c_y3:Vec<u16>,pub class_work:Vec<u16>}
fn quantum_append(w:&mut Writer,gates:&[Gate],ports:&[u16],port_count:usize,base:u16,condition:u16,reverse:bool) {
    let map=|q:u16|if (q as usize)<port_count{ports[q as usize]}else{base+(q as usize-port_count)as u16};
    let mut one=|g:Gate|{w.emit(Micro{kind:g.kind,a:if g.kind==6{0}else{map(g.a)},b:if g.kind==13{map(g.b)}else{0},t:map(g.t),cond:condition});};
    if reverse{for &g in gates.iter().rev(){one(g);}}else{for &g in gates{one(g);}}
}
fn quantum_coord(w:&mut Writer,p:&FieldProgram,field:&[u16],target:&[u16],condition:u16) {
    const BASE:u16=516;
    for(i,&bit)in field.iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:6,a:0,b:0,t:BASE+i as u16,cond:bit});}}
    let ports:Vec<_>=(BASE..BASE+256).chain(target.iter().copied()).collect();
    // Existing divide payload-flag home; never alias a live coordinate wire.
    // Semantic-clean but Boolean-opaque flags must not poison carry banks.
    const FLAG_HOME:u16=1043;assert_eq!(p.qubits,777);assert!(FLAG_HOME>BASE+256+264);
    let map=|q:u16|if q<512{ports[q as usize]}else if q==775{FLAG_HOME}else{BASE+256+(q-512)};
    for &g in &p.gates{w.emit(Micro{kind:g.kind,a:if g.kind==6{0}else{map(g.a)},b:if g.kind==13{map(g.b)}else{0},t:map(g.t),cond:condition});}
    for(i,&bit)in field.iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:6,a:0,b:0,t:BASE+i as u16,cond:bit});}}
}
fn quantum_eq(w:&mut Writer,eq:&FieldProgram,point:&[u16],tag:u16,condition:u16) {
    for(i,&bit)in point.iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:6,a:0,b:0,t:i as u16,cond:bit});}}
    let ports:Vec<_>=(0..512).chain(std::iter::once(tag)).collect();
    quantum_append(w,&eq.gates,&ports,513,516,condition,false);
    for(i,&bit)in point.iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:6,a:0,b:0,t:i as u16,cond:bit});}}
}

pub fn generate(path:&Path)->PointInfo {
    let mut w=Writer::new(path);
    let spec=Spec::secp256k1();let divide=super::generate(&spec,false);let rate_divide=super::generate_rate(&spec,false);
    let add=coordinate(Coord::Add);let sub=coordinate(Coord::Sub);let rsub=coordinate(Coord::Rsub);let neg=coordinate(Coord::Neg);
    let mul=product_oracle();let sq=square_subtract();let eq=equality();
    for (name,p) in [("add",&add),("sub",&sub),("rsub",&rsub),("neg",&neg),("product",&mul),("square_sub",&sq),("equality512",&eq)]{
        println!("COMPONENT name={name} T={} Q={} gates={}",p.gates.iter().filter(|g|g.kind==13).count(),p.qubits,p.gates.len());
    }
    let mut c=Classical {next:512,work:vec![],nonzero:0,x2:vec![],y2:vec![],x3:vec![],y3:vec![],gated:std::collections::HashMap::new()};
    c.work=c.alloc((divide.qubits-512).max(mul.qubits-768));c.nonzero=c.alloc(1)[0];
    // q_nonzero = NOT(all 512 offset bits zero), exact reversible Boolean test.
    let eq_ports:Vec<_>=(0..512).chain(std::iter::once(c.nonzero)).collect();
    c.append(&mut w,&eq.gates,&eq_ports,513,false);w.emit(Micro{kind:CLASS_X,a:0,b:0,t:c.nonzero,cond:NONE});
    let ox:Vec<_>=(0..256).collect();let oy:Vec<_>=(256..512).collect();
    let negx=c.copy(&mut w,&ox);c.coord(&mut w,&neg,&ox,&negx);
    let negy=c.copy(&mut w,&oy);c.coord(&mut w,&neg,&ox,&negy);
    let twice_x=c.copy(&mut w,&ox);c.coord(&mut w,&add,&ox,&twice_x);
    let three_x=c.copy(&mut w,&twice_x);c.coord(&mut w,&add,&ox,&three_x);
    let twice_y=c.copy(&mut w,&oy);c.coord(&mut w,&add,&oy,&twice_y);
    let xsq=c.mul(&mut w,&mul,&ox,&ox);
    let numerator=c.copy(&mut w,&xsq);c.coord(&mut w,&add,&xsq,&numerator);c.coord(&mut w,&add,&xsq,&numerator);
    let slope=c.copy(&mut w,&numerator);c.divide(&mut w,&divide,&twice_y,&slope);
    let slope_sq=c.mul(&mut w,&mul,&slope,&slope);
    let x2=c.copy(&mut w,&slope_sq);c.coord(&mut w,&sub,&twice_x,&x2);
    let dx2=c.copy(&mut w,&ox);c.coord(&mut w,&sub,&x2,&dx2);
    let yp2=c.mul(&mut w,&mul,&slope,&dx2);let y2=c.copy(&mut w,&yp2);c.coord(&mut w,&sub,&oy,&y2);
    let negy2=c.copy(&mut w,&y2);c.coord(&mut w,&neg,&ox,&negy2);
    let den3=c.copy(&mut w,&x2);c.coord(&mut w,&sub,&ox,&den3);
    let slope3=c.copy(&mut w,&y2);c.coord(&mut w,&sub,&oy,&slope3);c.divide(&mut w,&divide,&den3,&slope3);
    let slope3sq=c.mul(&mut w,&mul,&slope3,&slope3);
    let x3=c.copy(&mut w,&slope3sq);c.coord(&mut w,&sub,&x2,&x3);c.coord(&mut w,&sub,&ox,&x3);
    let dx3=c.copy(&mut w,&ox);c.coord(&mut w,&sub,&x3,&dx3);
    let yp3=c.mul(&mut w,&mul,&slope3,&dx3);let y3=c.copy(&mut w,&yp3);c.coord(&mut w,&sub,&oy,&y3);
    c.x2=x2.clone();c.y2=y2.clone();c.x3=x3.clone();c.y3=y3.clone();
    let origin=vec![NONE;512];
    let join=|x:&Vec<u16>,y:&Vec<u16>|x.iter().chain(y).copied().collect::<Vec<_>>();
    let q=join(&ox,&oy);let minus_q=join(&ox,&negy);let two_q=join(&x2,&y2);let minus_two_q=join(&x2,&negy2);let three_q=join(&x3,&y3);
    let inputs=[origin.clone(),q.clone(),minus_q.clone(),minus_two_q];
    let outputs=[q.clone(),two_q.clone(),origin,minus_q];
    let mut in_delta=Vec::new();let mut out_delta=Vec::new();
    for j in 0..4 {
        let d:Vec<_>=inputs[j].iter().zip(&two_q).map(|(&a,&b)|c.xor(&mut w,a,b)).collect();in_delta.push(d);
        let d:Vec<_>=outputs[j].iter().zip(&three_q).map(|(&a,&b)|c.xor(&mut w,a,b)).collect();out_delta.push(d);
    }
    let in_gated:Vec<_>=inputs.iter().map(|a|c.gated_word(&mut w,a)).collect();
    let out_gated:Vec<_>=outputs.iter().map(|a|c.gated_word(&mut w,a)).collect();
    let in_d:Vec<_>=in_delta.iter().map(|a|c.gated_word(&mut w,a)).collect();
    let out_d:Vec<_>=out_delta.iter().map(|a|c.gated_word(&mut w,a)).collect();
    let gx=c.gated_word(&mut w,&ox);let gy=c.gated_word(&mut w,&oy);let gthree_x=c.gated_word(&mut w,&three_x);
    let classical_end=w.count;println!("CLASSICAL_PREP macros={classical_end} bits={}",c.next);
    let tx:Vec<_>=(0..256).collect();let ty:Vec<_>=(256..512).collect();
    for j in 0..4 {quantum_eq(&mut w,&eq,&in_gated[j],512+j as u16,c.nonzero);}
    for j in 0..4 {for(i,&bit)in in_d[j].iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:8,a:512+j as u16,b:0,t:i as u16,cond:bit});}}}
    // Actual generic mixed point addition, not a classical target lookup.
    quantum_coord(&mut w,&sub,&gx,&tx,c.nonzero);
    quantum_coord(&mut w,&sub,&gy,&ty,c.nonzero);
    let xy:Vec<_>=tx.iter().chain(&ty).copied().collect();
    quantum_append(&mut w,&rate_divide.gates,&xy,512,516,c.nonzero,false);
    quantum_coord(&mut w,&add,&gthree_x,&tx,c.nonzero);
    quantum_append(&mut w,&sq.gates,&xy,512,516,c.nonzero,false);
    quantum_append(&mut w,&rate_divide.gates,&xy,512,516,c.nonzero,true);
    quantum_coord(&mut w,&sub,&gy,&ty,c.nonzero);
    quantum_coord(&mut w,&rsub,&gx,&tx,c.nonzero);
    for j in 0..4 {for(i,&bit)in out_d[j].iter().enumerate(){if bit!=NONE{w.emit(Micro{kind:8,a:512+j as u16,b:0,t:i as u16,cond:bit});}}}
    for j in 0..4 {quantum_eq(&mut w,&eq,&out_gated[j],512+j as u16,c.nonzero);}
    let quantum_end=w.count;
    w.append_reverse(path,0,classical_end);w.flush();
    assert!((w.max_c as usize)<c.next);
    PointInfo{macros:w.count,records:w.real_count+1028,toffolis:w.toffolis,qubits:w.max_q as usize+1,bits:c.next,classical_end,quantum_end,c_nonzero:c.nonzero,c_x2:x2,c_y2:y2,c_x3:x3,c_y3:y3,class_work:c.work}
}

#[cfg(test)]mod school_tests{
 use super::*;
 fn apply(g:Gate,q:&mut[bool]){match g.kind{6=>q[g.t as usize]^=true,8=>q[g.t as usize]^=q[g.a as usize],13=>q[g.t as usize]^=q[g.a as usize]&q[g.b as usize],10=>q.swap(g.a as usize,g.t as usize),_=>panic!()}}
 fn put(q:&mut[bool],r:&[u16],x:usize){for(i,&j)in r.iter().enumerate(){q[j as usize]=x>>i&1!=0;}}
 fn get(q:&[bool],r:&[u16])->usize{r.iter().enumerate().fold(0,|x,(i,&j)|x|((q[j as usize]as usize)<<i))}
 #[test]fn exact_full_product_all_small_unsigned_pairs(){for n in 1..=5{let mut b=new_build();let a=b.alloc(n);let c=b.alloc(n);let p=school_prefix(&mut b,&a,&c);for x in 0..1<<n{for y in 0..1<<n{let mut q=vec![false;b.next];put(&mut q,&a,x);put(&mut q,&c,y);let initial=q.clone();for &g in &b.gates{apply(g,&mut q);}assert_eq!(get(&q,&p),x*y);assert_eq!(get(&q,&a),x);assert_eq!(get(&q,&c),y);assert!(!q[p[2*n]as usize]);assert!(b.mask.iter().all(|&j|!q[j as usize])&&!q[b.carry as usize]);for &g in b.gates.iter().rev(){apply(g,&mut q);}assert_eq!(q,initial);}}}}
 #[test]fn exact_square_with_aliased_control_source_all_small_bases(){for n in 1..=7{let mut b=new_build();let a=b.alloc(n);let p=school_prefix(&mut b,&a,&a);for x in 0..1<<n{let mut q=vec![false;b.next];put(&mut q,&a,x);let initial=q.clone();for &g in &b.gates{apply(g,&mut q);}assert_eq!(get(&q,&p),x*x);assert_eq!(get(&q,&a),x);assert!(b.mask.iter().all(|&j|!q[j as usize])&&!q[b.carry as usize]);for &g in b.gates.iter().rev(){apply(g,&mut q);}assert_eq!(q,initial);}}}
 #[test]fn exact_triangular_square_all_small_and_reverse(){for n in 1..=8{let mut b=new_build();let a=b.alloc(n);let p=triangle_prefix(&mut b,&a);for x in 0..1<<n{let mut q=vec![false;b.next];put(&mut q,&a,x);let initial=q.clone();for &g in &b.gates{apply(g,&mut q);}assert_eq!(get(&q,&p),x*x,"n={n} x={x}");assert_eq!(get(&q,&a),x);assert!(!q[p[2*n]as usize]);assert!(b.mask.iter().all(|&j|!q[j as usize])&&!q[b.carry as usize]);for &g in b.gates.iter().rev(){apply(g,&mut q);}assert_eq!(q,initial);}}}

}
