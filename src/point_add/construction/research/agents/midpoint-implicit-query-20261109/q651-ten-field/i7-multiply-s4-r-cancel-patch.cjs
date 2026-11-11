'use strict';
const path=require('path');
function zeroPair(c,small,large,z){
 if(!small.every(q=>large.includes(q)))throw Error('not nested');
 const cs=[...c,...small,...large.filter(q=>!small.includes(q))],k=c.length+small.length,n=cs.length;
 if(k<3||k>=n){this.zer(c,small,z);this.zer(c,large,z);return;}
 const loan=this.y.filter(q=>q!==z&&!cs.includes(q));if(loan.length<n-2)throw Error('pair loan');
 for(const q of large)this.raw(-1,-1,q);
 const pass=()=>{this.raw(cs[0],cs[1],loan[0]);if(k===3)this.raw(cs[2],loan[0],z);
  for(let j=2;j<=n-2;j++){this.raw(cs[j],loan[j-2],loan[j-1]);if(j===k-2)this.raw(cs[k-1],loan[k-3],z);}
  this.raw(cs[n-1],loan[n-3],z);for(let j=n-2;j>=2;j--)this.raw(cs[j],loan[j-2],loan[j-1]);};
 pass();pass();for(const q of large)this.raw(-1,-1,q);
}
let patches=require('./i7-multiply-s4-r-p-r648-final.js').map(p=>p.slice());
patches=patches.map(([a,s])=>{
 if(s.includes('function r43RelayPlan(w)')){
  const edit=(a,b)=>{if(s.split(a).length!==2)throw Error('R S3 anchor '+a);s=s.replace(a,b);};
  edit('const select=(z)=>','const select=(z,guard=[])=>');
  // The r-only denormalization commutes across the L-only rotation block.
  // It cancels the first rotation of inverse val; bias remains unchanged.
  edit('norm(a,w,controls,base);rot(a,w,controls,-1,base);one(a,()=>this.bias(controls,bias));','norm(a,w,controls,base);one(a,()=>this.bias(controls,bias));');
  edit('rot(all,r,c,-1,base);','/* cancelled across disjoint L rotations */');

  edit('this.lt([this.tst],A,r,z);','this.lt([this.tst,...guard],A,r,z);');
  edit('select(this.fire);match(c,r,tag[0]);select(this.fire);this.op([tag[0]],this.fire);this.op(c,tag[0]);','match([],r,tag[0]);select(this.fire,[tag[0]]);match([],r,tag[0]);');
  edit('this.zer(controls,word.slice(m-base),out);\n      if(base+stride<m)this.zer(controls,word.slice(m-base-stride),out);','if(base+stride<m)this.zeroPair(controls,word.slice(m-base),word.slice(m-base-stride),out);else this.zer(controls,word.slice(m-base),out);');
 }
 return [a,s];
});

module.exports=function(s){
 for(const [a,b]of patches){if(s.split(a).length!==2)throw Error('S3 history source anchor');s=s.replace(a,()=>b);}
 const anchor='function emitRegenerateSparse(sink,erase=false){';
 const init='Signed.prototype.zeroPair='+zeroPair.toString()+';\n'+
  'for(const C of [Signed,TopHost,R36Park,Terminal])require('+JSON.stringify(path.join(__dirname,'i7-multiply-s3-field-rotate.cjs'))+').adapt(Object.create(C.prototype));\n';
 if(s.split(anchor).length!==2)throw Error('S3 history install anchor');return s.replace(anchor,()=>init+anchor);
};

module.exports.patches=patches;module.exports.zeroPair=zeroPair;
