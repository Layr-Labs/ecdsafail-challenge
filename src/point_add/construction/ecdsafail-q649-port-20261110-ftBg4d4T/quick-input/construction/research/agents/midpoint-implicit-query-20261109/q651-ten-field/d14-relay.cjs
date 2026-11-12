'use strict';
// R43/R6 relay-source.cjs port, applied to the donor's own canonical/reduced plan.
function edit(s,a,b){if(s.split(a).length!==2)throw Error('D10 relay anchor '+a);return s.replace(a,()=>b);}
function transform(base,dirtyDigit,small){let p=base.toString();
p=edit(p,'plan(){','function(){');
p=edit(p,'let topPort=null;const n=this.n,L=this.L,R=this.R,tag=this.tag,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>ar.push({fn,rev,topPort}),cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({fn:other[i].fn,rev:!other[i].rev,topPort:other[i].topPort});};',
`let topPort=null,relayPort=null,activeTag=this.tag,row=null,sector=null;const fullTag=this.tag.slice(),missing=fullTag.at(-2),n=this.n,L=this.L,R=this.R,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>{const tg=activeTag;ar.push({fn:()=>{this.tag=tg;fn();},rev,topPort,relayPort,row,sector});},cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({...other[i],rev:!other[i].rev});};`);
p=edit(p,'const rot=(ar,w,controls,dir,base=0)=>{','const rot=(ar,w,controls,dir,base=0)=>{const tag=activeTag;');
p=edit(p,'const norm=(ar,w,controls,base=0)=>{','const norm=(ar,w,controls,base=0)=>{const tag=activeTag;');
p=edit(p,'topPort=R[m];','topPort=R[m];row={k,t,m};sector=null;activeTag=fullTag;relayPort=null;');
p=edit(p,`const stride=1<<tag.length;
   for(let base=Math.floor((m-1)/stride)*stride;base>=0;base-=stride){
    const hi=Math.min(m-1,base+stride-1);`,
`const low=1<<(fullTag.length-1),wide=1<<fullTag.length,sectors=[0];for(let b=low;b<m;b+=wide)sectors.push(b);
   for(const base of sectors.reverse()){
    const useRelay=base!==0,stride=useRelay?wide:low,hi=Math.min(m-1,base+stride-1);
    activeTag=useRelay?fullTag:fullTag.filter(q=>q!==missing);const tag=activeTag;relayPort=useRelay?this.tst:null;sector={base,hi};`);
p=edit(p,'one(all,()=>{this.op(c,r[m-1]);this.raw(-1,-1,this.tst);for(const z of dirtyDigit(r.slice(0,-1).concat(this.tst),A,r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.tst);});',
`one(all,()=>{const h=useRelay?r[0]:this.tst;this.op(c,r[m-1]);this.raw(-1,-1,h);for(const z of dirtyDigit(r.slice(useRelay?base:0,-1).concat(h),A.slice(useRelay?base:0),r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,h);});
   if(useRelay){one(all,()=>this.swap(c,this.tst,r[1]));all.at(-1).lease={from:this.tst,to:r[1],fire:this.fire,name:'norm-to-digit0'};relayPort=r[1];}`);
p=edit(p,'for(let i=0;i<hi;i++)one(all,()=>{eq(i);',
`for(let i=0;i<hi;i++){if(useRelay&&i===1){one(all,()=>this.swap(c,r[1],r[0]));all.at(-1).lease={from:r[1],to:r[0],fire:this.fire,name:'digit0-to-rest'};relayPort=r[0];}one(all,()=>{eq(i);`);
p=edit(p,'dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,this.tst,this.y[0])','dirtyDigit(rh.slice(useRelay?Math.max(0,base-i-1):0,-1).concat(this.fire),ah.slice(useRelay?Math.max(0,base-i-1):0),carry,this.tst,this.y[0])');
p=edit(p,'this.op(en.concat(A[i]),carry);});','this.op(en.concat(A[i]),carry);});}');
p=edit(p,'for(let i=hi-1;i>=0;i--)one(all,()=>{',
`for(let i=hi-1;i>=0;i--)one(all,()=>{`);
p=edit(p,'const en=[this.tst];this.raw(-1,-1,r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));this.raw(-1,-1,r[0]);',
 'const en=[this.tst],h=useRelay?r[1]:r[0];this.raw(-1,-1,h);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(h),u,0,A[i]));this.raw(-1,-1,h);');
p=edit(p,'rot(all,r,c,-1,base);',
`if(useRelay){one(all,()=>this.swap(c,r[0],this.tst));all.at(-1).lease={from:r[0],to:this.tst,fire:this.fire,name:'coeff-to-denorm'};relayPort=this.tst;}
   rot(all,r,c,-1,base);`);
// Return the original permanent tag list after plan construction. Every closure installs its own captured list.
p=edit(p,'return all;','this.tag=fullTag;return all;');
if(small){
 p=edit(p,'this.zer(controls,word.slice(m-base),out);\n      if(base+stride<m)this.zer(controls,word.slice(m-base-stride),out);','if(base+stride<m)this.zeroPair(controls,word.slice(m-base),word.slice(m-base-stride),out);else this.zer(controls,word.slice(m-base),out);');
 p=edit(p,'const select=(z)=>','const select=(z,guard=[])=>');
 p=edit(p,'this.lt([this.tst],A,r,z);','this.lt([this.tst,...guard],A,r,z);');
 p=edit(p,'select(this.fire);match(c,r,tag[0]);select(this.fire);this.op([tag[0]],this.fire);this.op(c,tag[0]);','match([],r,tag[0]);select(this.fire,[tag[0]]);match([],r,tag[0]);');
}
return Function('dirtyDigit','return ('+p+');')(dirtyDigit);}
function install(w,dirtyDigit){
 if(w.tag.length<3)throw Error('D10 relay requires at least three tags (tag0 remains selector)');
 let p=Object.getPrototypeOf(w),base;
 while(p){if(Object.hasOwn(p,'plan')&&p.plan.toString().includes('const stride=1<<tag.length')){base=p.plan;break;}p=Object.getPrototypeOf(p);}
 if(!base||!base.toString().includes('dirtyDigit'))throw Error('D10 requires aux-free plan');
 const old=w.plan,next=transform(base,dirtyDigit,!!w.zeroPair),fullTag=w.tag.slice(),missing=fullTag.at(-2);
 w.plan=function(){
  const full=old.call(this),core=base.call(this),blocks=next.call(this).concat(full.slice(core.length));
  for(const block of blocks){const fn=block.fn;block.fn=()=>{fn();for(let i=0;i<this.g.length;i++){
   const x=this.g[i],map=q=>{if(q!==missing)return q;if(block.relayPort==null)throw Error('unhosted missing tag');return block.relayPort;};
   const a=map(x>>>20&1023),b=map(x>>>10&1023),t=map(x&1023);
   if(a===t||b===t||(a!==1023&&a===b))throw Error('relay logical alias');this.g[i]=(a<<20)|(b<<10)|t;
  }};}
  this.tag=fullTag;return blocks;
 };return w;
}
module.exports={install,transform};
