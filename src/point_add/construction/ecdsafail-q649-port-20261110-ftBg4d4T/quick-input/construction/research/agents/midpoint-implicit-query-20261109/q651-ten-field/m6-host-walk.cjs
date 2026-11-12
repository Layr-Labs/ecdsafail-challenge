'use strict';
const edit=(s,a,b)=>{if(s.split(a).length!==2)throw Error('host walk anchor '+a);return s.replace(a,()=>b);};
// Eliminate a reversible primitive's virtual known-one bit, retaining its exact
// evolving Boolean polynomial. The final polynomial must again be one.
function eliminateRaw(rows,h,emit){
 const key=a=>[...new Set(a)].sort((a,b)=>a-b).join(',');
 const xor=(a,b)=>{const o=new Set(a);for(const x of b)o.has(x)?o.delete(x):o.add(x);return o;};
 const mul=(a,b)=>{let o=new Set;for(const x of a)for(const y of b)o=xor(o,new Set([key([...x.split(',').filter(Boolean).map(Number),...y.split(',').filter(Boolean).map(Number)])]));return o;};
 const variable=w=>new Set([String(w)]);let E=new Set(['']);
 for(const r of rows){const z=r.at(-1);let C=new Set(['']);for(const w of r.slice(0,-1))C=mul(C,w===h?E:variable(w));
  if(z===h){E=xor(E,C);continue;}
  for(const term of C){const cs=term===''?[]:term.split(',').map(Number);if(cs.includes(z))throw Error('nonreversible virtual target');emit(cs,z);}
  let next=new Set;for(const term of E){const vs=term===''?[]:term.split(',').map(Number);next=xor(next,vs.includes(z)?mul(new Set([key(vs.filter(w=>w!==z))]),xor(variable(z),C)):new Set([term]));}E=next;
  if(E.size>10000)throw Error('polynomial cap');
 }
 if(E.size!==1||!E.has(''))throw Error('virtual one not restored '+JSON.stringify([...E]));
}
const constantCache=new Map();
function eliminate(rows,h,emit){
 const ids=[h],map=new Map([[h,0]]),id=w=>{if(!map.has(w)){map.set(w,ids.length);ids.push(w);}return map.get(w);};
 const canon=rows.map(r=>r.map(id)),key=JSON.stringify(canon);let out=constantCache.get(key);
 if(!out){out=[];eliminateRaw(canon,0,(cs,z)=>out.push([...cs,z]));constantCache.set(key,out);}
 for(const r of out)emit(r.slice(0,-1).map(w=>ids[w]),ids[r.at(-1)]);
}
module.exports=function hostWalk(pub,bits=6){
 const Base=pub.D2Canonical,flat=Object.getPrototypeOf(Base.prototype),unit=Object.getPrototypeOf(flat);
 let s=unit.plan.toString();
 s=edit(s,'let topPort=null;','let topPort=null,tagPort=this.tst;');
 s=edit(s,'ar.push({fn,rev,topPort})','ar.push({fn,rev,topPort,tagPort})');
 s=edit(s,'topPort:other[i].topPort','topPort:other[i].topPort,tagPort:other[i].tagPort');
 s=edit(s,'for(let k=0;k<n;k++){','for(let k=0;k<n-1;k++){');
 s=edit(s,'one(all,()=>{this.op(c,r[m-1]);this.raw(-1,-1,this.tst);for(const z of dirtyDigit(r.slice(0,-1).concat(this.tst),A,r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.tst);});',
 'one(all,()=>{this.op(c,r[m-1]);this.constantDigit(r.slice(0,-1),A,r[m-1],this.fire);});');
 s=edit(s,'one(all,()=>this.op(c,this.tst));','// tst currently holds the extra tag; z>=1 makes digit zero unconditional under fire.');
 s=edit(s,'for(let i=0;i<hi;i++)one(all,()=>{eq(i);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);for(const z of dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});',
 `for(let i=0;i<hi;i++){
    one(all,()=>{if(i)eq(i);const en=i?[this.tst]:c,rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);if(i===0)this.constantDigit(rh.slice(0,-1),ah,carry,en[0]);else for(const z of dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,en[0],this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
    if(i===0){one(all,()=>this.swap(c,this.tst,r[0]));tagPort=r[0];one(all,()=>this.op(c,this.tst));}
   }`);
 s=edit(s,'this.raw(-1,-1,r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));this.raw(-1,-1,r[0]);',
 'if(i===0)this.reverse(()=>this.constantDigit(v.slice(0,-1),u,A[i],en[0]));else{this.raw(-1,-1,r[i]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[i]),u,0,A[i]));this.raw(-1,-1,r[i]);}');
 s=edit(s,'rot(all,r,c,-1,base);',
 'one(all,()=>this.swap(c,this.tst,r[0]));tagPort=this.tst;rot(all,r,c,-1,base);');
 // Emission-only metadata. Does not select or alter gates.
 s=edit(s,'let topPort=null,tagPort=this.tst;','let topPort=null,tagPort=this.tst,meta={phase:"prologue"};');
 s=edit(s,'ar.push({fn,rev,topPort,tagPort})','ar.push({fn,rev,topPort,tagPort,meta:{...meta}})');
 s=edit(s,'tagPort:other[i].tagPort','tagPort:other[i].tagPort,meta:other[i].meta');
 s=edit(s,'topPort=R[m];','topPort=R[m];meta={k,t,m,phase:"balance"};');
 s=edit(s,'const hi=Math.min(m-1,base+stride-1);','const hi=Math.min(m-1,base+stride-1);meta={k,t,m,base,hi,phase:"sector"};');
 const plan=Function('dirtyDigit','return function '+s)(pub.dirtyDigit);
 return class HostedWalk extends Base{
  constructor(n){super(n,Math.min(bits,Math.ceil(Math.log2(n))));if(this.tag.length<3)throw Error('host walk needs >=3 tags');}
  constantDigit(a,b,h,e){eliminate(pub.dirtyDigit([...a,1001],b,h,e,this.y[0]),1001,(cs,z)=>this.op(cs,z));}
  plan(){const a=plan.call(this);a.push(flat.plan.call(this).at(-1));return a;}
 };
};
