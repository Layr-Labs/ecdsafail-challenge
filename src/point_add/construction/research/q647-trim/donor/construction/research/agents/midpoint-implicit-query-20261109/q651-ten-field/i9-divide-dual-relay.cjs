'use strict';
// Source-level dual relay. No fixture-dependent gate selection.
function plan(){
 const full=this.tag.slice(),first=full.at(-2),second=full.at(-3),n=this.n,L=this.L,R=this.R,c=[this.fire],all=[];
 let topPort=null,relayPort=null,secondPort=null,tag=full,row=null,sector=null;
 const one=(ar,fn,rev=false)=>{const tg=tag;ar.push({fn:()=>{this.tag=tg;fn();},rev,topPort,relayPort,secondPort,row,sector});};
 const cat=(ar,a,inv=false)=>{if(inv)for(let j=a.length;j--;)ar.push({...a[j],rev:!a[j].rev});else ar.push(...a);};
 const rot=(ar,w,ct,dir,base=0)=>{const tg=tag;if(base)one(ar,()=>this.rot(ct,w,dir*base));for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=w.length)break;one(ar,()=>this.rot(ct.concat(tg[j]),w,dir*s));}};
 const norm=(ar,w,ct,base,dual)=>{const tg=tag;if(base)one(ar,()=>this.rot(ct,w,base));if(dual)secondPort=w[2];for(let j=tg.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(ct,w.slice(w.length-s),tg[j]);this.rot(ct.concat(tg[j]),dual?w.slice(base):w,s);});}};
 const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]),W=L.slice(0,n),S=R.slice(0,n);
 one(all,()=>{const h=S[n-1];this.op([h],this.sign);this.raw(-1,-1,h);this.lt([h],S.slice(0,-1),W.slice(1),this.sign);this.raw(-1,-1,h);});
 one(all,()=>{const cc=[this.sign];for(const z of W)this.raw(-1,-1,z);this.add(cc,W,S,0,null);for(const z of W)this.raw(-1,-1,z);for(const z of S)this.op(cc,z);});
 one(all,()=>this.raw(-1,-1,R[n]));
 for(let k=0;k<n;k++){
  const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);topPort=R[m];row={k,t,m};sector=null;relayPort=null;secondPort=null;tag=full;
  const select=(z,guard=[])=>{const large=()=>{this.zer([],this.d18reduced?r:A.slice(1),this.tst);this.raw(-1,-1,this.tst);};large();this.lt([this.tst,...guard],A,r,z);this.reverse(large);};
  if(k>0&&k<n-1){const cp=[this.tst];one(all,()=>select(this.fire));
   one(all,()=>{const qa=this.tag[0],qcond=()=>{this.op([r[m-1]],qa);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);this.raw(-1,-1,r[m-1]);};const consumer=()=>{this.op([this.fire,qa],this.tst);for(const z of u)this.raw(-1,-1,z);this.lt([this.fire,qa],v,u,this.tst);for(const z of u)this.raw(-1,-1,z);};qcond();consumer();this.reverse(qcond);if(full.length===3)consumer();});
   one(all,()=>{this.reverse(()=>this.add(cp,r,A,this.cin,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,this.cin,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
   one(all,()=>this.op(this.d18reduced?[this.fire,L[n-k]]:[L[n-k]],this.tst));one(all,()=>select(this.fire));
  }
  const low=1<<(full.length-2),mid=2*low,wide=1<<full.length,sectors=[{base:0,width:low,kind:0}];
  if(low<m)sectors.push({base:low,width:low,kind:1});for(let b=mid;b<m;b+=wide)sectors.push({base:b,width:wide,kind:2});
  for(const {base,width,kind} of sectors.reverse()){
   const hi=Math.min(m-1,base+width-1),dual=kind===2,relay=kind>0;
   tag=dual?full:kind===1?full.filter(q=>q!==second):full.filter(q=>q!==second&&q!==first);const tg=tag;
   relayPort=relay?this.tst:null;secondPort=null;sector={base,hi,kind};
   const match=(ct,w,z)=>{if(base+width<m)this.zeroPair(ct,w.slice(m-base),w.slice(m-base-width),z);else this.zer(ct,w.slice(m-base),z);};
   const eq=i=>{if(i>=base&&i<=hi)this.multag(c,i-base,[],this.tst);};
   const dirtySelector=[first,second,full.at(-1)].includes(tag[0]);
   if(tag[0]===first)relayPort=topPort;if(tag[0]===second)secondPort=topPort;
   if(base===0&&hi===m-1)one(all,()=>select(this.fire));
   else one(all,()=>{match([],r,tg[0]);select(this.fire,[tg[0]]);match([],r,tg[0]);if(dirtySelector)select(this.fire,[tg[0]]);});
   relayPort=relay?this.tst:null;secondPort=null;
   one(all,()=>this.op(c,R[m]));norm(all,r,c,base,dual);
   one(all,()=>{const h=relay?r[0]:this.tst;this.op(c,r[m-1]);this.raw(-1,-1,h);for(const z of this.d18digit(r.slice(relay?base:0,-1).concat(h),A.slice(relay?base:0),r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,h);});
   if(relay){one(all,()=>this.swap(c,this.tst,r[1]));relayPort=r[1];}
   one(all,()=>this.op(c,this.tst));
   for(let i=0;i<hi;i++){
    if(relay&&i===1){one(all,()=>this.swap(c,r[1],r[0]));relayPort=r[0];}
    if(dual&&i===2){one(all,()=>this.swap(c,r[2],r[1]));secondPort=r[1];}
    one(all,()=>{eq(i);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);for(const z of this.d18digit(rh.slice(relay?Math.max(0,base-i-1):0,-1).concat(this.fire),ah.slice(relay?Math.max(0,base-i-1):0),carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
   }
   one(all,()=>eq(hi));
   for(let i=hi-1;i>=0;i--)one(all,()=>{eq(i+1);const en=[this.tst],h=dual?r[2]:relay?r[1]:r[0];this.raw(-1,-1,h);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(h),u,0,A[i]));this.raw(-1,-1,h);for(let j=t;j--;)this.swap(en,A[i],u[j]);});
   one(all,()=>{this.op(c,this.tst);eq(0);});
   one(all,()=>{const carry=r[m-1];this.raw(-1,-1,this.tst);this.reverse(()=>this.restore(c,v.slice(0,-1).concat(this.tst),u,0,carry));this.raw(-1,-1,this.tst);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
   if(relay){one(all,()=>this.swap(c,r[0],this.tst));relayPort=this.tst;}
   if(dual){one(all,()=>this.swap(c,r[1],r[2]));secondPort=r[2];}
   // rot(r,-1) and rot(r,+1) commute through coefficient-only L rotations; cancel.
   one(all,()=>this.rot(c,L.slice(m,n+1),-1));rot(all,L.slice(0,n+1),c,-1,base);
   const un=[];norm(un,r,c,base,dual);cat(all,un,true);
   relayPort=null;secondPort=null;
   one(all,()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);const non=()=>{this.zer([],R.slice(0,m+1),this.tst);this.raw(-1,-1,this.tst);};if(this.d18reduced)non();const guard=this.d18reduced?[this.tst,L[n-k]]:[L[n-k]];if(base===0&&hi===m-1)this.op(guard,this.fire);else match(guard,L.slice(0,m),this.fire);if(this.d18reduced)this.reverse(non);});
  }
 }
 one(all,()=>this.raw(-1,-1,this.sign));this.tag=full;return all;
}
function install(w,digit){
 if(w.tag.length<3)throw Error('dual relay needs 3 tags');
 let p=Object.getPrototypeOf(w),base;while(p){if(Object.hasOwn(p,'plan')&&p.plan.toString().includes('const stride=1<<tag.length')){base=p.plan;break;}p=Object.getPrototypeOf(p);}
 if(!base)throw Error('aux-free plan');w.d18reduced=base.toString().includes('this.zer([],r,this.tst)');const old=w.plan,full=w.tag.slice(),first=full.at(-2),second=full.at(-3);w.d18digit=digit;
 w.plan=function(){const original=old.call(this),core=base.call(this),blocks=plan.call(this).concat(original.slice(core.length));for(const block of blocks){const fn=block.fn;block.fn=()=>{const oldY=this.y,pre=full.length===3&&block.sector===null&&block.topPort!=null,host=oldY.at(-1);if(pre)this.y=oldY.slice(0,-1);try{fn();}finally{this.y=oldY;}for(let j=0;j<this.g.length;j++){const x=this.g[j],map=q=>{if(q===first){if(block.relayPort==null)throw Error('unhosted first');return block.relayPort;}if(q===second){if(pre)return host;if(block.secondPort==null)throw Error('unhosted second');return block.secondPort;}return q;};const a=map(x>>>20&1023),b=map(x>>>10&1023),z=map(x&1023);if(a===z||b===z||(a===b&&a!==1023))throw Error('dual alias '+JSON.stringify({row:block.row,sector:block.sector,a,b,z}));this.g[j]=(a<<20)|(b<<10)|z;}};}this.tag=full;return blocks;};return w;
}
module.exports={install,plan};
