'use strict';
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('relay anchor '+a);return s.replace(a,()=>b);};
module.exports=function(pub,bits=5){
 const Base=pub.D2Canonical,flat=Object.getPrototypeOf(Base.prototype),unit=Object.getPrototypeOf(flat);
 let s=unit.plan.toString();
 s=edit(s,'let topPort=null;const n=this.n,L=this.L,R=this.R,tag=this.tag,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>ar.push({fn,rev,topPort}),cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({fn:other[i].fn,rev:!other[i].rev,topPort:other[i].topPort});};',
 `let topPort=null,tagPort=this.tst,extraPort=null,activeTag=this.tag,meta={};const fullTag=this.tag.slice(),extra=fullTag.at(-3),n=this.n,L=this.L,R=this.R,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>{const tg=activeTag;ar.push({fn:()=>{this.tag=tg;fn();},rev,topPort,tagPort,extraPort,meta:{...meta}});},cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({...other[i],rev:!other[i].rev});};`);
 s=edit(s,'const rot=(ar,w,controls,dir,base=0)=>{','const rot=(ar,w,controls,dir,base=0)=>{const tag=activeTag;');
 s=edit(s,'const norm=(ar,w,controls,base=0)=>{if(base)one(ar,()=>this.rot(controls,w,base));for(let j=tag.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(controls,w.slice(w.length-s),tag[j]);this.rot(controls.concat(tag[j]),w,s);});}};',
 `const norm=(ar,w,controls,base=0)=>{const tag=activeTag;if(base)one(ar,()=>this.rot(controls,w,base));const old=extraPort;if(base)extraPort=w[0];for(let j=tag.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(controls,w.slice(w.length-s),tag[j]);if(base)this.rotZero(controls.concat(tag[j]),w,s);else this.rot(controls.concat(tag[j]),w,s);});}if(!base)extraPort=old;};`);
 s=edit(s,'const val=(w,controls,bias,base=0)=>{const a=mk();norm(a,w,controls,base);rot(a,w,controls,-1,base);one(a,()=>this.bias(controls,bias));return a;};',
 `const val=(w,controls,bias,base=0)=>{if(bias)throw Error('relay bias');const a=mk();const old=extraPort;extraPort=null;norm(a,w,controls,base);extraPort=old;return a;};`);
 s=edit(s,'for(let k=0;k<n;k++){','for(let k=0;k<n-1;k++){');
 s=edit(s,'topPort=R[m];','topPort=R[m];activeTag=fullTag;extraPort=null;tagPort=this.tst;meta={k,t,m};');
 s=edit(s,'const stride=1<<tag.length;\n   for(let base=Math.floor((m-1)/stride)*stride;base>=0;base-=stride){\n    const hi=Math.min(m-1,base+stride-1);',
 `const low=1<<(fullTag.length-1),wide=1<<fullTag.length,sectors=[0];for(let b=low;b<m;b+=wide)sectors.push(b);
   for(const base of sectors.reverse()){
    const high=base!==0,stride=high?wide:low,hi=Math.min(m-1,base+stride-1);activeTag=high?fullTag:fullTag.filter(q=>q!==extra);const tag=activeTag;extraPort=null;tagPort=this.tst;meta={k,t,m,base,hi};`);
 s=edit(s,'one(all,()=>{this.op(c,r[m-1]);this.raw(-1,-1,this.tst);for(const z of dirtyDigit(r.slice(0,-1).concat(this.tst),A,r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.tst);});',
 `one(all,()=>{this.op(c,r[m-1]);this.constantDigit(r.slice(base,-1),A.slice(base),r[m-1],this.fire);});
   if(high){one(all,()=>this.swap(c,r[0],r[2]));extraPort=r[2];one(all,()=>this.swap(c,this.tst,r[1]));tagPort=r[1];}`);
 s=edit(s,'one(all,()=>this.op(c,this.tst));','if(high)one(all,()=>this.op(c,this.tst));');
 s=edit(s,'for(let i=0;i<hi;i++)one(all,()=>{eq(i);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);for(const z of dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});',
 `for(let i=0;i<hi;i++){
    if(high&&i===1){one(all,()=>this.swap(c,r[1],r[0]));tagPort=r[0];}
    if(high&&i===2){one(all,()=>this.swap(c,r[2],r[1]));extraPort=r[1];}
    one(all,()=>{if(i||high)eq(i);const en=i||high?[this.tst]:c,rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i],crop=Math.max(0,base-i-1);for(const z of A.slice(i))this.swap(en,carry,z);if(i===0&&!high)this.constantDigit(rh.slice(crop,-1),ah.slice(crop),carry,en[0]);else for(const z of dirtyDigit(rh.slice(crop,-1).concat(this.fire),ah.slice(crop),carry,en[0],this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
    if(!high&&i===0){one(all,()=>this.swap(c,this.tst,r[0]));tagPort=r[0];one(all,()=>this.op(c,this.tst));}
   }`);
 s=edit(s,'this.raw(-1,-1,r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));this.raw(-1,-1,r[0]);',
 `if(!high&&i===0)this.reverse(()=>this.constantDigit(v.slice(0,-1),u,A[i],en[0]));else{const h=high?r[2]:r[i];this.raw(-1,-1,h);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(h),u,0,A[i]));this.raw(-1,-1,h);}`);
 s=edit(s,'rot(all,r,c,-1,base);',
 `one(all,()=>this.swap(c,this.tst,r[0]));tagPort=this.tst;
   if(high){one(all,()=>this.swap(c,r[1],r[0]));extraPort=r[0];}
   // Rail denormalization commutes with the following L-only rotations and
   // cancels the inverse valuation's renormalizing rotations exactly.`);
 s=edit(s,'return all;','this.tag=fullTag;return all;');
 const plan=Function('dirtyDigit','return function '+s)(pub.dirtyDigit);
 return class Relay extends Base{
  constructor(n){super(n,Math.min(bits,Math.ceil(Math.log2(n))));}
  constantDigit(...args){return require('./i7-multiply-s4-m-constant-fast.cjs').apply(this,args);}
  rotZero(c,w,s){
   // Delete zero vertex 0 from the permutation. Its predecessor and successor
   // are linked. On enabled normalization, both displaced data values are zero.
   const n=w.length,next=Array.from({length:n},(_,i)=>(i+s)%n),seen=new Set([0]);
   const pred=(n-s)%n;next[pred]=next[0];
   for(let k=1;k<n;k++){if(seen.has(k))continue;seen.add(k);for(let j=next[k];j!==k;j=next[j]){if(j===0||seen.has(j))throw Error('rotZero cycle');seen.add(j);this.swap(c,w[k],w[j]);}}
  }
  plan(){const a=plan.call(this);a.push({...flat.plan.call(this).at(-1),extraPort:null,tagPort:this.tst});return a;}
 };
};
