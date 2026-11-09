function digit(n,A,B,h,e=null,t=null){const g=[];const X=(a)=>g.push([a]);const CX=(a,b)=>g.push([a,b]);const T=(a,b,c)=>g.push([a,b,c]);const end=n-1;if(n===1){X(B[0]);if(e===null){T(B[0],A[0],h);X(B[0]);X(h);T(h,A[0],B[0]);}else{T(e,A[0],t);T(t,B[0],h);X(B[0]);CX(e,h);T(t,h,B[0]);T(e,A[0],t);}return g;}for(const x of B)X(x);for(let i=1;i<n;i++)CX(A[i],B[i]);if(e===null)CX(A[end],h);else T(e,A[end],h);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);if(e===null){T(B[end],A[end],h);X(h);}else{T(e,A[end],t);T(t,B[end],h);T(e,A[end],t);CX(e,h);T(e,h,t);}const p=e===null?h:t;T(p,A[end],B[end]);for(let i=n-2;i>=0;i--){T(B[i],A[i],A[i+1]);T(p,A[i],B[i]);}if(e!==null)T(e,h,t);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const x of B)X(x);return g;}


class Gate{constructor(){this.g=[];this.nct=[0,0,0];this.mx=-1;}
 raw(a,b,z){this.g.push(((a<0?1023:a)<<20)|((b<0?1023:b)<<10)|z);this.nct[a<0?0:b<0?1:2]++;this.mx=Math.max(this.mx,a,b,z);}
 swap(c,a,b){if(a===b)return;this.raw(a,-1,b);this.op(c.concat(b),a);this.raw(a,-1,b);}
 rot(c,A,s){const n=A.length;s=(s%n+n)%n;if(!s)return;const seen=new Uint8Array(n);for(let k=0;k<n;k++){if(seen[k])continue;seen[k]=1;for(let j=(k+s)%n;j!==k;j=(j+s)%n){this.swap(c,A[k],A[j]);seen[j]=1;}}}
 zer(c,arr,z){for(const a of arr)this.raw(-1,-1,a);this.op(c.concat(arr),z);for(const a of arr)this.raw(-1,-1,a);}
 less(c,arr,constant,z){for(let j=0;j<arr.length;j++){if(constant&(1<<j))continue;const ctrl=[arr[j]],neg=[];for(let q=j+1;q<arr.length;q++){ctrl.push(arr[q]);if(!(constant&(1<<q)))neg.push(arr[q]);}for(const a of neg)this.raw(-1,-1,a);this.op(c.concat(ctrl),z);for(const a of neg)this.raw(-1,-1,a);}}
 reverse(f){const p=this.g.length;f();for(let i=p,j=this.g.length-1;i<j;i++,j--)[this.g[i],this.g[j]]=[this.g[j],this.g[i]];}
 add(c,A,B,cin,cout){let n=A.length,op=(cs,z)=>this.op(c.concat(cs),z);
  for(let i=0;i<n;i++){const a=A[i],b=B[i],v=i?A[i-1]:cin;op([a],b);op([a],v);op([v,b],a);}
  if(cout!==null)op([A[n-1]],cout);
  for(let i=n-1;i>=0;i--){const a=A[i],b=B[i],v=i?A[i-1]:cin;op([v,b],a);op([a],v);op([v],b);}
 }
 restore(c,A,B,cin,out){this.reverse(()=>this.add(c,A,B,cin,out));this.add(c.concat(out),A,B,cin,null);this.op(c,out);}
}


class UnitWalk extends Gate{
 constructor(n){super(n,false,[]);this.n=n;this.L=Array.from({length:n+2},(_,i)=>i);this.R=this.L.map(i=>i+n+2);
 const data=2*(n+2)+(n+1)+2*n;this.y=Array.from({length:2*n},(_,i)=>3*n+5+i);this.clean=[];
 this.e=data;this.sign=data+1;this.tag=Array.from({length:Math.ceil(Math.log2(n))},(_,i)=>data+2+i);this.fire=this.tag.at(-1)+1;this.tst=this.fire+1;this.aux=this.fire+2;this.nq=this.aux+1;this.cin=this.R[n+1];this.hi=this.L[n+1];this.both=this.hi;}
 op(c,z){if(c.length<=2){this.raw(c.length?c[0]:-1,c.length===2?c[1]:-1,z);return;}const b=this.y,n=c.length;
 if(n-2>b.length)throw Error("borrow");
 for(let s=0;s<2;s++){if(s===0)this.raw(c[0],c[1],b[0]);for(let i=1;i<n-2;i++)this.raw(c[i+1],b[i-1],b[i]);this.raw(c[n-1],b[n-3],z);for(let i=n-3;i>=1;i--)this.raw(c[i+1],b[i-1],b[i]);if(s===0)this.raw(c[0],c[1],b[0]);}}
 add(c,a,b,unused,h){const n=a.length,k=n-1;if(n===1){if(h!==null)this.op(c.concat(a[0],b[0]),h);this.op(c.concat(a[0]),b[0]);return;}
  for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);if(h!==null)this.op(c.concat(a[k]),h);for(let i=n-2;i>=1;i--)this.raw(a[i],-1,a[i+1]);for(let i=0;i<n-1;i++)this.raw(b[i],a[i],a[i+1]);if(h!==null)this.op(c.concat(b[k],a[k]),h);this.op(c.concat(a[k]),b[k]);for(let i=n-2;i>=0;i--){this.raw(b[i],a[i],a[i+1]);this.op(c.concat(a[i]),b[i]);}for(let i=1;i<n-1;i++)this.raw(a[i],-1,a[i+1]);for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);}
 lt(c,a,b,h){const n=a.length,k=n-1;for(const z of b)this.raw(-1,-1,z);if(n===1){this.op(c.concat(a[0],b[0]),h);this.raw(-1,-1,b[0]);return;}for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);this.op(c.concat(a[k]),h);for(let i=n-2;i>=1;i--)this.raw(a[i],-1,a[i+1]);for(let i=0;i<n-1;i++)this.raw(b[i],a[i],a[i+1]);this.op(c.concat(b[k],a[k]),h);for(let i=n-2;i>=0;i--)this.raw(b[i],a[i],a[i+1]);for(let i=1;i<n-1;i++)this.raw(a[i],-1,a[i+1]);for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);for(const z of b)this.raw(-1,-1,z);}
 restore(c,a,b,unused,h){if(c.length!==1)throw Error('single control');const e=c[0],n=a.length,k=n-1;
  if(h!==this.aux&&e!==this.aux){for(const z of digit(n,a,b,h,e,this.aux))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));return;}
  for(const z of b)this.raw(-1,-1,z);if(n===1){this.op([e,a[0],b[0]],h);this.raw(-1,-1,b[0]);this.raw(e,-1,h);this.raw(h,a[0],b[0]);return;}
  for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);this.raw(e,a[k],h);for(let i=n-2;i>=1;i--)this.raw(a[i],-1,a[i+1]);for(let i=0;i<n-1;i++)this.raw(b[i],a[i],a[i+1]);this.op([e,a[k],b[k]],h);this.raw(e,-1,h);this.raw(h,a[k],b[k]);for(let i=n-2;i>=0;i--){this.raw(b[i],a[i],a[i+1]);this.raw(h,a[i],b[i]);}for(let i=1;i<n-1;i++)this.raw(a[i],-1,a[i+1]);for(let i=1;i<n;i++)this.raw(a[i],-1,b[i]);for(const z of b)this.raw(-1,-1,z);}
 multag(c,q,hi,z){const neg=[];for(let j=0;j<this.tag.length;j++)if(!(q&(1<<j)))neg.push(this.tag[j]);neg.push(...hi);for(const w of neg)this.raw(-1,-1,w);this.op(c.concat(this.tag,hi),z);for(const w of neg)this.raw(-1,-1,w);}
 bias(c,v){for(let j=0;j<this.tag.length;j++){if(!(v&(1<<j)))continue;for(let i=this.tag.length-1;i>=j;i--)this.op(c.concat(this.tag.slice(j,i)),this.tag[i]);}}
 perm(c,arr,src){const used=new Set();for(let s=0;s<arr.length;s++){if(used.has(s))continue;let j=s;while(!used.has(j)){used.add(j);const nx=src[j];if(nx!==s)this.swap(c,arr[j],arr[nx]);j=nx;}}}
 plan(){
  let topPort=null;const n=this.n,L=this.L,R=this.R,tag=this.tag,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>ar.push({fn,rev,topPort}),cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({fn:other[i].fn,rev:!other[i].rev,topPort:other[i].topPort});};
  const rot=(ar,w,controls,dir)=>{for(let j=0;j<tag.length;j++){const s=1<<j;if(s>=w.length)break;one(ar,()=>this.rot(controls.concat(tag[j]),w,dir*s));}};
  const norm=(ar,w,controls)=>{for(let j=tag.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(controls,w.slice(w.length-s),tag[j]);this.rot(controls.concat(tag[j]),w,s);});}};
  const val=(w,controls,bias)=>{const a=mk();norm(a,w,controls);rot(a,w,controls,-1);one(a,()=>this.bias(controls,bias));return a;};
  const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]);
  const W=L.slice(0,n),S=R.slice(0,n);
  one(all,()=>{const high=S[n-1];this.op([high],this.sign);this.raw(-1,-1,high);this.lt([high],S.slice(0,-1),W.slice(1),this.sign);this.raw(-1,-1,high);});
  one(all,()=>{const cc=[this.sign];for(const z of W)this.raw(-1,-1,z);this.add(cc,W,S,0,null);for(const z of W)this.raw(-1,-1,z);for(const z of S)this.op(cc,z);});
  one(all,()=>this.raw(-1,-1,R[n]));
  for(let k=0;k<n;k++){
   const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);topPort=R[m];
   const select=(z)=>{const large=()=>{this.zer([],A.slice(1),this.tst);this.raw(-1,-1,this.tst);};large();this.lt([this.tst],A,r,z);this.reverse(large);};
   one(all,()=>select(this.fire));
   if(k>0&&k<n-1){const cp=[this.tst];
    one(all,()=>{const qcond=()=>{this.op([r[m-1]],this.aux);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),this.aux);this.raw(-1,-1,r[m-1]);};qcond();this.op([this.fire,this.aux],this.tst);for(const z of u)this.raw(-1,-1,z);this.lt([this.fire,this.aux],v,u,this.tst);for(const z of u)this.raw(-1,-1,z);this.reverse(qcond);});
    one(all,()=>{this.reverse(()=>this.add(cp,r,A,this.cin,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,this.cin,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
    one(all,()=>this.op([L[n-k]],this.tst));
   }
   one(all,()=>this.op(c,R[m]));norm(all,r,c);
   one(all,()=>{this.op(c,r[m-1]);this.raw(-1,-1,this.aux);for(const z of digit(m,r.slice(0,-1).concat(this.aux),A,r[m-1],this.fire,this.tst))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));this.raw(-1,-1,this.aux);});
   one(all,()=>this.op(c,this.tst));
   for(let i=0;i<m-1;i++)one(all,()=>{this.multag(c,i,[],this.tst);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1);for(const z of A.slice(i))this.swap(en,this.aux,z);this.raw(-1,-1,r[0]);this.restore(en,rh.slice(0,-1).concat(r[0]),ah,0,this.aux);this.raw(-1,-1,r[0]);this.op(en.concat(this.aux),A[i]);this.op(en.concat(A[i]),this.aux);});
   one(all,()=>this.multag(c,m-1,[],this.tst));
   for(let i=m-2;i>=0;i--)one(all,()=>{this.multag(c,i+1,[],this.tst);const en=[this.tst];this.raw(-1,-1,r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));this.raw(-1,-1,r[0]);for(let j=t;j--;)this.swap(en,A[i],u[j]);});
   one(all,()=>{this.op(c,this.tst);this.multag(c,0,[],this.tst);});
   one(all,()=>{const carry=r[m-1];this.raw(-1,-1,this.tst);this.reverse(()=>this.restore(c,v.slice(0,-1).concat(this.tst),u,0,carry));this.raw(-1,-1,this.tst);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
   rot(all,r,c,-1);
   one(all,()=>this.rot(c,L.slice(m,n+1),-1));rot(all,L.slice(0,n+1),c,-1);
   cat(all,val(r,c,0),true);one(all,()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);this.op([L[n-k]],this.fire);});
  }
  one(all,()=>{this.raw(-1,-1,this.sign);
    });
  return all;
 }
}
class FlatUnit extends UnitWalk{plan(){const a=super.plan(),n=this.n,u=Array.from({length:n},(_,i)=>this.L[n-i]),v=Array.from({length:n},(_,i)=>this.R[n-i]);a.push({rev:false,fn:()=>{const save=this.cin;this.cin=this.aux;this.zer([],v.slice(1),this.sign);const ctl=[this.sign];for(const z of v)this.raw(-1,-1,z);this.add(ctl,v,u,0,null);for(const z of v)this.raw(-1,-1,z);for(const z of u)this.op(ctl,z);const high=u[n-1];this.op([high],this.sign);this.raw(-1,-1,high);this.lt([high],u.slice(0,-1),v.slice(1),this.sign);this.raw(-1,-1,high);this.raw(-1,-1,this.L[0]);for(let j=0;j<n+1;j++)this.swap([],this.L[j],this.R[n-j]);this.cin=save;}});return a;}}
function emit109(inverse,sink){const n=109,W=new FlatUnit(n),ops=W.plan(),map=new Map(),q=(k,z)=>map.set(k,z);
 for(let i=0;i<n;i++){q(W.L[i],148+i);q(W.R[i],i);}q(W.L[n],624);q(W.R[n],625);
 q(W.sign,626);for(let i=0;i<6;i++)q(W.tag[i],627+i);q(W.fire,633);q(W.tst,634);q(W.aux,635);
 for(let i=0;i<148;i++)q(W.y[i],475+i);if(inverse)ops.reverse();let max=0,maxDirty=0,topPort=null;const wire=j=>{if(j===W.tag[6])j=topPort;if(j===1023)return j;if(!map.has(j))throw Error('unbound '+j);const val=map.get(j);max=Math.max(val,max);if(val>=475&&val<623)maxDirty=Math.max(maxDirty,val);return val;};
 for(const o of ops){topPort=o.topPort;W.g=[];o.fn();for(let i=0;i<W.g.length;i++){const g=W.g[i];const a=wire(g>>>20&1023),b=wire(g>>>10&1023),t=wire(g&1023);if(a===t||b===t||a!==1023&&a===b)throw Error('alias '+[a,b,t]);W.g[i]=(a<<20)|(b<<10)|t;}if(o.rev!==inverse)W.g.reverse();sink(W.g);}return {nct:W.nct,nq:max+1,maxDirty};}
module.exports = { emit109 };
