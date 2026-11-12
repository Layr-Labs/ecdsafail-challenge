'use strict';
// Generator-level edits; no emitted stream table. rot2 and tap2 ideas adapted
// from Akashneelesh 5909718a q650/mul/{mulopt.cjs,p-mul650.js}.
function rot2(c,A,s){
 const n=A.length;s=(s%n+n)%n;if(!s)return;
 const gcd=(a,b)=>b?gcd(b,a%b):a;
 const refl=a=>{const q=[];for(let i=0;i<n;i++){const j=((a-i)%n+n)%n;if(i<j)q.push([A[i],A[j]]);}return q;};
 // Original cycle schedule sends old position i to i+s.
 const V1=refl(0),V2=refl(s),pairs=V1.length+V2.length;
 if(c.length!==2||4*pairs+2>=6*(n-gcd(n,s)))return this.d9oldRot(c,A,s);
 const d=this.y.find(q=>!c.includes(q)&&!A.includes(q));if(d===undefined)throw Error('rotation loan');
 const cx=V=>{for(const[a,b]of V)this.raw(a,-1,b);},ts=V=>{for(const[a,b]of V)this.raw(d,b,a);},g=()=>this.raw(c[0],c[1],d);
 cx(V1);ts(V1);g();ts(V1);cx(V1);cx(V2);ts(V2);g();ts(V2);cx(V2);
}
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
function install(w,dirtyDigit,options={rot:true,pair:true}){
 if(options.rot){w.d9oldRot=w.rot;w.rot=rot2;}
 if(options.pair){
  let p=Object.getPrototypeOf(w),base;
  while(p){if(Object.hasOwn(p,'plan')&&p.plan.toString().includes('const stride=1<<tag.length')){base=p.plan;break;}p=Object.getPrototypeOf(p);}
  if(!base)throw Error('sector plan not found');
  const a='this.zer(controls,word.slice(m-base),out);\n      if(base+stride<m)this.zer(controls,word.slice(m-base-stride),out);';
  const b='if(base+stride<m)this.zeroPair(controls,word.slice(m-base),word.slice(m-base-stride),out);else this.zer(controls,word.slice(m-base),out);';
  let source=base.toString();if(!source.includes('dirtyDigit'))return w; // original aux-based forward outer
  if(source.split(a).length!==2)throw Error('match source anchor');
  if(options.select){
   const edits=[['const select=(z)=>','const select=(z,guard=[])=>'],['this.lt([this.tst],A,r,z);','this.lt([this.tst,...guard],A,r,z);'],['select(this.fire);match(c,r,tag[0]);select(this.fire);this.op([tag[0]],this.fire);this.op(c,tag[0]);','match([],r,tag[0]);select(this.fire,[tag[0]]);match([],r,tag[0]);']];
   for(const [old,next]of edits){if(source.split(old).length!==2)throw Error('select anchor');source=source.replace(old,next);}
  }
  const next=Function('dirtyDigit','return ({'+source.replace(a,b)+'}).plan;')(dirtyDigit),old=w.plan;
  w.zeroPair=zeroPair;w.plan=function(){const full=old.call(this),core=base.call(this);return next.call(this).concat(full.slice(core.length));};
 }
 return w;
}
module.exports={install,rot2,zeroPair};
