'use strict';
// D22 arbitrary-depth constructive-zero relay. Fixed, input-independent sectors.
function plan(){
 const full=this.tag.slice(),roles=full.slice(0,-2).reverse(),n=this.n,L=this.L,R=this.R,c=[this.fire],all=[];
 let topPort=null,ports=[],tag=full,row=null,sector=null;
 const one=(ar,fn,rev=false)=>{const tg=tag;ar.push({fn:()=>{this.tag=tg;fn();},rev,topPort,ports:ports.slice(),row,sector,rawSource:fn.toString()});};
 const cat=(ar,a,inv=false)=>{if(inv)for(let j=a.length;j--;)ar.push({...a[j],rev:!a[j].rev});else ar.push(...a);};
 const rot=(ar,w,ct,dir,base=0)=>{const tg=tag;if(base)one(ar,()=>this.rot(ct,w,dir*base));for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=w.length)break;one(ar,()=>this.rot(ct.concat(tg[j]),w,dir*s));}};
 const norm=(ar,w,ct,base,dual)=>{const tg=tag;if(base)one(ar,()=>this.rot(ct,w,base));for(let j=2;j<=sector.kind;j++)ports[j-1]=w[j];for(let j=tg.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(ct,w.slice(w.length-s),tg[j]);this.rot(ct.concat(tg[j]),dual?w.slice(base):w,s);});}};
 const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]),W=L.slice(0,n),S=R.slice(0,n);
 one(all,()=>{const h=S[n-1];this.op([h],this.sign);this.raw(-1,-1,h);this.lt([h],S.slice(0,-1),W.slice(1),this.sign);this.raw(-1,-1,h);});
 one(all,()=>{const cc=[this.sign];for(const z of W)this.raw(-1,-1,z);this.add(cc,W,S,0,null);for(const z of W)this.raw(-1,-1,z);for(const z of S)this.op(cc,z);});
 one(all,()=>this.raw(-1,-1,R[n]));
 for(let k=0;k<n;k++){
  const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);topPort=R[m];row={k,t,m};sector=null;ports=[];tag=full;
  const select=(z,guard=[])=>{const large=()=>{this.zer([],this.d18reduced?r:A.slice(1),this.tst);this.raw(-1,-1,this.tst);};large();this.lt([this.tst,...guard],A,r,z);this.reverse(large);};
  if(k>0&&k<n-1){const cp=[this.tst];one(all,()=>select(this.fire));
   one(all,()=>{const qa=full.at(-2),qcond=()=>{this.op([r[m-1]],qa);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);this.raw(-1,-1,r[m-1]);};const consumer=()=>{this.op([this.fire,qa],this.tst);for(const z of u)this.raw(-1,-1,z);this.lt([this.fire,qa],v,u,this.tst);for(const z of u)this.raw(-1,-1,z);};qcond();consumer();this.reverse(qcond);});
   one(all,()=>{this.reverse(()=>this.add(cp,r,A,this.cin,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,this.cin,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
   one(all,()=>this.op(this.d18reduced?[this.fire,L[n-k]]:[L[n-k]],this.tst));one(all,()=>select(this.fire));
  }
  const depth=Math.min(roles.length,m>48?4:m>24?3:2),low=4,wide=1<<(depth+2),sectors=[{base:0,width:low,kind:0}];
  for(let j=1;j<depth;j++){const base=1<<(j+1);if(base<m)sectors.push({base,width:base,kind:j});}for(let base=1<<(depth+1);base<m;base+=wide)sectors.push({base,width:wide,kind:depth});
  for(const {base,width,kind} of sectors.reverse()){
   const hi=Math.min(m-1,base+width-1),dual=kind>=2,relay=kind>0;
   tag=full.slice(full.length-2-kind);const tg=tag;
   ports=relay?[this.tst]:[];sector={base,hi,kind};
   const match=(ct,w,z)=>{if(base+width<m)this.zeroPair(ct,w.slice(m-base),w.slice(m-base-width),z);else this.zer(ct,w.slice(m-base),z);};
   const eq=i=>{if(i>=base&&i<=hi)this.multag(c,i-base,[],this.tst);};
   const dirtySelector=true;
   if(roles.includes(tag[0]))ports[roles.indexOf(tag[0])]=topPort;
   if(base===0&&hi===m-1)one(all,()=>select(this.fire));
   else one(all,()=>{match([],r,full.at(-2));select(this.fire,[full.at(-2)]);match([],r,full.at(-2));});
   ports=relay?[this.tst]:[];
   one(all,()=>this.op(c,R[m]));norm(all,r,c,base,dual);
   one(all,()=>{const h=relay?r[0]:this.tst;this.op(c,r[m-1]);this.raw(-1,-1,h);for(const z of this.d18digit(r.slice(relay?base:0,-1).concat(h),A.slice(relay?base:0),r[m-1],this.fire,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,h);});
   if(relay){one(all,()=>this.swap(c,this.tst,r[1]));ports[0]=r[1];}
   one(all,()=>this.op(c,this.tst));
   for(let i=0;i<hi;i++){
    if(i>=1&&i<=kind){one(all,()=>this.swap(c,r[i],r[i-1]));ports[i-1]=r[i-1];}
    one(all,()=>{eq(i);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1),carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);for(const z of this.d18digit(rh.slice(relay?Math.max(0,base-i-1):0,-1).concat(this.fire),ah.slice(relay?Math.max(0,base-i-1):0),carry,this.tst,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
   }
   one(all,()=>eq(hi));
   for(let i=hi-1;i>=0;i--)one(all,()=>{eq(i+1);const en=[this.tst],h=r[kind];this.raw(-1,-1,h);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(h),u,0,A[i]));this.raw(-1,-1,h);for(let j=t;j--;)this.swap(en,A[i],u[j]);});
   one(all,()=>{this.op(c,this.tst);eq(0);});
   one(all,()=>{const carry=r[m-1];this.raw(-1,-1,this.tst);this.reverse(()=>this.restore(c,v.slice(0,-1).concat(this.tst),u,0,carry));this.raw(-1,-1,this.tst);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
   if(relay){one(all,()=>this.swap(c,r[0],this.tst));ports[0]=this.tst;}
   for(let j=kind;j>=2;j--){one(all,()=>this.swap(c,r[j-1],r[j]));ports[j-1]=r[j];}
   // rot(r,-1) and rot(r,+1) commute through coefficient-only L rotations; cancel.
   one(all,()=>this.rot(c,L.slice(m,n+1),-1));rot(all,L.slice(0,n+1),c,-1,base);
   const un=[];norm(un,r,c,base,dual);cat(all,un,true);
   ports=[];
   one(all,()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);const non=()=>{this.zer([],R.slice(0,m+1),this.tst);this.raw(-1,-1,this.tst);};if(this.d18reduced)non();const guard=this.d18reduced?[this.tst,L[n-k]]:[L[n-k]];if(base===0&&hi===m-1)this.op(guard,this.fire);else match(guard,L.slice(0,m),this.fire);if(this.d18reduced)this.reverse(non);});
  }
 }
 one(all,()=>this.raw(-1,-1,this.sign));this.tag=full;return all;
}
function install(w,digit){
 if(w.tag.length<3||w.tag.length>7)throw Error('D22 relay requires 3..7 tags');
 let p=Object.getPrototypeOf(w),base;while(p){if(Object.hasOwn(p,'plan')&&p.plan.toString().includes('const stride=1<<tag.length')){base=p.plan;break;}p=Object.getPrototypeOf(p);}
 if(!base)throw Error('aux-free plan');w.d18reduced=base.toString().includes('this.zer([],r,this.tst)');const old=w.plan,full=w.tag.slice(),roles=full.slice(0,-2).reverse();w.d18digit=digit;
 w.plan=function(){const original=old.call(this),core=base.call(this),blocks=plan.call(this).concat(original.slice(core.length));for(const block of blocks){const fn=block.fn;block.fn=()=>{const oldY=this.y,pre=block.sector===null&&block.topPort!=null,host=oldY.at(-1);if(pre)this.y=oldY.slice(0,-1);try{fn();}finally{this.y=oldY;}for(let j=0;j<this.g.length;j++){const x=this.g[j],map=q=>{const j=roles.indexOf(q);if(j>=0){if(pre&&q===full[0])return host;if(block.ports[j]==null)throw Error('unhosted D22 relay '+j);return block.ports[j];}return q;};const a=map(x>>>20&1023),b=map(x>>>10&1023),z=map(x&1023);if(a===z||b===z||(a===b&&a!==1023))throw Error('dual alias '+JSON.stringify({row:block.row,sector:block.sector,a,b,z}));this.g[j]=(a<<20)|(b<<10)|z;}};}this.tag=full;return blocks;};return w;
}
module.exports={install,plan};
