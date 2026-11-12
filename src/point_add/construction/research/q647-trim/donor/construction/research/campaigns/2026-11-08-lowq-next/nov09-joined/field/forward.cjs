function digit(n,A,B,h,e=null,t=null){const g=[];const X=(a)=>g.push([a]);const CX=(a,b)=>g.push([a,b]);const T=(a,b,c)=>g.push([a,b,c]);const end=n-1;if(n===1){X(B[0]);if(e===null){T(B[0],A[0],h);X(B[0]);X(h);T(h,A[0],B[0]);}else{T(e,A[0],t);T(t,B[0],h);X(B[0]);CX(e,h);T(t,h,B[0]);T(e,A[0],t);}return g;}for(const x of B)X(x);for(let i=1;i<n;i++)CX(A[i],B[i]);if(e===null)CX(A[end],h);else T(e,A[end],h);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);if(e===null){T(B[end],A[end],h);X(h);}else{T(e,A[end],t);T(t,B[end],h);T(e,A[end],t);CX(e,h);T(e,h,t);}const p=e===null?h:t;T(p,A[end],B[end]);for(let i=n-2;i>=0;i--){T(B[i],A[i],A[i+1]);T(p,A[i],B[i]);}if(e!==null)T(e,h,t);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const x of B)X(x);return g;}
function vec(n,off){return Array.from({length:n},(_,i)=>i+off);}
function plus(A,B,H,e=null,t=null){const n=A.length,iTop=n-1,g=[];const CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);if(n===1){if(H!==null){if(e===null)T(A[0],B[0],H);else {T(e,A[0],t);T(t,B[0],H);T(e,A[0],t);}}if(e===null)CX(A[0],B[0]);else T(e,A[0],B[0]);return g;}for(let i=1;i<n;i++)CX(A[i],B[i]);if(H!==null){if(e===null)CX(A[iTop],H);else T(e,A[iTop],H);}for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);if(H!==null){if(e===null)T(B[iTop],A[iTop],H);else{T(e,A[iTop],t);T(t,B[iTop],H);T(e,A[iTop],t);}}if(e===null)CX(A[iTop],B[iTop]);else T(e,A[iTop],B[iTop]);for(let i=n-2;i>=0;i--){T(B[i],A[i],A[i+1]);if(e===null)CX(A[i],B[i]);else T(e,A[i],B[i]);}for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);return g;}
function NR(n,k,ctl=false){const A=vec(n,0),D=vec(n+k,n),e=ctl?2*n+k:null,t=e===null?null:e+1,g=[];for(let j=k-1;j>=0;j--){const B=D.slice(j,j+n),h=D[j+n],old=j==k-1?null:D[j+n+1];const before=()=>{if(old!==null)g.push([old]);for(const u of [...B,h])g.push(old===null?[u]:[old,u]);if(old!==null)g.push([old]);};before();g.push(...plus(A,B,h,e,t));before();}const sign=D[n];if(ctl)g.push([e,sign,t]);g.push(...plus(A,D.slice(0,n),null,ctl?t:sign));if(ctl)g.push([e,sign,t]);for(const h of D.slice(n))g.push(ctl?[e,h]:[h]);return g;}
function lt(A,B,H){const n=A.length,last=n-1,g=[];const X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);for(const w of B)X(w);if(n===1){T(A[0],B[0],H);X(B[0]);return g;}for(let i=1;i<n;i++)CX(A[i],B[i]);CX(A[last],H);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);T(B[last],A[last],H);for(let i=n-2;i>=0;i--)T(B[i],A[i],A[i+1]);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const w of B)X(w);return g;}
function MCX(c,t,dirty){if(c.length<3)return [[...c,t]];const z=[],u=c.length,v=dirty.slice(0,u-2);if(v.length!==u-2)throw 'dirty';const A=[c[0],c[1],v[0]],M=[];for(let j=2;j<u-1;j++)M.push([c[j],v[j-2],v[j-1]]);const Z=[c[u-1],v[u-3],t],R=[...M].reverse();return [A,...M,Z,...R,A,...M,Z,...R];}
function negate(c,p,bools){let g=[];let w=c.filter((v,i)=>!bools[i]);for(const x of w)g.push([x]);g=g.concat(p);for(const x of w)g.push([x]);return g;}
function eq_bits(c,v){return c.map((_,j)=>!!(v>>j&1));}
function gt(s,i,e,outer,dirty){let g=[];for(let j=0;j<s.length;j++)if(!(i>>j&1)){let C=[s[j],...s.slice(j+1)],B=[true,...s.slice(j+1).map((_,b)=>!!(i>>(b+j+1)&1))];if(outer!==null){C.push(outer);B.push(true);}g=g.concat(negate(C,MCX(C,e,dirty),B));}return g;}
function fr(c,a,b){return [[a,b],[c,b,a],[a,b]];}
function rotleft(n,k){const order=Array.from({length:n},(_,i)=>i);const target=Array.from({length:n},(_,i)=>(i+n-k)%n),out=[];for(let i=0;i<n;i++)if(order[i]!==target[i]){const j=order.indexOf(target[i]);out.push([i,j]);const g=order[i];order[i]=order[j];order[j]=g;}return out;}
function normal(T,Q,s,dirty,qmove=true){const n=T.length,g=[];for(let j=s.length-1;j>=0;j--){const d=2**j,C=T.slice(n-d),V=negate(C,MCX(C,s[j],dirty),C.map(()=>false));g.push(...V);const tr=rotleft(n,d);for(const [a,b] of tr){g.push(...fr(s[j],T[a],T[b]));if(qmove)g.push(...fr(s[j],Q[a],Q[b]));}}return g;}
function incReg(H,G,control=null){if(!H.length)return [];if(H.length===1)return[control===null?[H[0]]:[control,H[0]]];G=G.slice(0,H.length);if(G.length!==H.length)throw'missing dirty';const A=plus(G,H,null,control).reverse(),g=[...A];for(const w of G)g.push([w]);g.push(...A);for(const w of G)g.push([w]);return g;}
function where(g,map){return g.map(z=>z.map(i=>map[i]));}
function madd(M,A,B,h){return [...plus(A,B,h),...digit(M.length,M,B,h),...lt(A,B,h)];}
function remprep(n,k,M,S,C,Q,scratch,holes,pos,neg,enabledDirection=false){let g=[],raw=NR(n,k),lut=[...M,...S,...C],ops=raw.map(row=>row.map(i=>lut[i])),res=S.slice(0,n);const md=madd(M,res,Q,scratch);for(const [mask,reverse] of [[neg,true],[pos,false]]){for(const x of mask)g.push([holes[x]]);g=g.concat(ops,reverse?[...md].reverse():md,[...ops].reverse());for(const x of mask)g.push([holes[x]]);}return g;}
function val_low(M,J,t,dirty){let g=[];for(let l=2;l<M.length;l++){const mask=(l-1)%2**J.length;if(!mask)continue;const ct=M.slice(0,l+1),B=ct.map((_,i)=>i===l);const A=negate(ct,MCX(ct,t,dirty),B);g=g.concat(A);for(let j=0;j<J.length;j++)if(mask>>j&1)g.push([t,J[j]]);g=g.concat([...A].reverse());}return g;}
function one_stage(n,outer,M,X,s,J,e,t,dirty,i,kappa){const flag=gt(s,i,e,outer,dirty);let g=[...flag,...digit(n-1,M.slice(1),X.slice(0,-1),X[n-1],e,t)];const split=2**J.length;const C=M.slice(0,split+1),high=negate(C,MCX(C,t,dirty),C.map(()=>false));g=g.concat(high);const ids=[...J,t];for(let j=0;j<n-1;j++){const v=eq_bits(ids,j),cs=[e,...ids,X[j]],vs=[true,...v,true];g=g.concat(negate(cs,MCX(cs,X[n-1],dirty),vs));if(i<=j&&((kappa>>BigInt(j-i))&1n)){const ct=[e,...ids],vt=[true,...v];g=g.concat(negate(ct,MCX(ct,X[n-1],dirty),vt));}}g=g.concat([...high].reverse());for(let j=n-1;j>0;j--)g=g.concat(fr(e,X[j],X[j-1]));return g.concat([...flag].reverse());}
function wideadd(A,Z,carry){const bits=Z.slice(0,A.length),top=Z.slice(A.length);if(bits.length<A.length)throw'truncated';if(!top.length)return plus(A,bits,null);return [...plus(A,bits,carry),...incReg(top,[...A,...bits],carry),...lt(A,bits,carry)];}
function fieldprod(n,d,pterms){const T=vec(d,0),Q=vec(d,d),Y=vec(n,2*d),C=vec(d,2*d+n),w0=3*d+n,w1=w0+1,f=w1+1,j=[...Q,...Y],upper=j.slice(n),lower=j.slice(0,n),mapping=[...T,...j];let g=NR(d,n,false).map(r=>r.map(i=>mapping[i])).reverse();function mac(high){let p=[];const zz=[...lower,high];for(const [i,sign] of pterms){const adds=wideadd(upper,zz.slice(i),f);p=p.concat(sign===1?adds:adds.reverse());}return p;}
function ac(Z,conditional=null){let p=[];const G=[...T,...Q,...Y,...C].filter(v=>!Z.includes(v)&&v!==conditional);for(const [i,sgn] of pterms){const AD=incReg(Z.slice(i),G,conditional);p=p.concat(sgn===1?AD:AD.reverse());}return p;}
g=g.concat(mac(w0),ac([...lower,w0]),incReg(upper,T,w0),[[w0]],ac(lower,w0).reverse(),[[w0]]);const checking=mac(w1),inv=[...checking].reverse();g=g.concat(inv,[[w1,w0]],checking);return{g,T,C,Q,Y,L:lower,H:upper,W:f+1};}
function shprod(n,M,X,C,R,P){if(R.length!==2*n)throw'word size';const [xh,th,t2,tmp]=P;const mm=plus(M,X,xh),D0=[...X,xh];let all=[...mm];for(let idx=0;idx<2;idx++){const si=R.slice(idx*n,idx*n+n),other=R.slice((1-idx)*n,(1-idx)*n+n),br=[...other.slice(0,n-1),th],raw=[...br,t2,...si],A=where(NR(n+1,n),[...D0,...raw]).reverse(),B=where(NR(n,n+1),[...M,...raw]),result=raw.slice(0,n);function depo(Q,sub){const G=X,kk=idx*n,view=[...G.slice(0,kk),...Q];let run=kk?where(NR(n,kk),[...M,...view]):[];const rr=view.slice(0,n),mac=madd(M,rr,C,tmp),ar=sub?[...mac].reverse():mac;return [].concat(run,ar,[...run].reverse());}all=all.concat(A,B,depo(result,false),[...B].reverse(),[...A].reverse(),depo(br,true));}return all.concat([...mm].reverse());}
function shortinv(a,N){if(N===1n)return 0n;let u=1n,v=0n,A=a,B=N;while(B){let q=A/B;[A,B]=[B,A%B];[u,v]=[v,u-q*v];}return (u%N+N)%N;}
function nativeForward128(emitPUnit,sink){const n=128,P=(1n<<256n)-(1n<<32n)-977n,D=1n<<128n,kappa=shortinv(P,D),ff=fieldprod(256,128,[[32,1],[10,1],[5,-1],[4,-1],[0,1]]);const{T,H,L,C}=ff,S=vec(7,640),color=647,outer=648,idx=vec(6,649),en=655,tmp=656;const norm=normal(T,H,S,L),unn=normal(T,H,S,L,false),can=digit(n,T,C,color),mad=madd(T,C,H,tmp),vp=val_low(T,idx,tmp,L);function run(g,rev=false){sink('nct',rev?[...g].reverse():g);}function prod(back){run(shprod(128,T,H,C,L,vec(4,649)),back);}function prep(back){const loc=[0,4,5,10,32,256],R=[];let k=0;for(let j=0;j<257;j++){const a=loc.indexOf(j);R.push(a<0?L[k++]:idx[a]);}run(remprep(128,257,T,R,C,H,en,idx,[5,2,1],[4,3,0]),back);}function unit(back){run(can,true);emitPUnit(back,buf=>sink('packed',buf));run(can);}function power(back){run(vp);for(let k=0;k<127;k++)run(one_stage(128,outer,T,H,S,idx,en,tmp,L,back?126-k:k,kappa),back);run(vp,true);}run(ff.g);run(norm);run(can);run(mad);for(let i=0;i<n;i++){run([[C[i],H[i]]]);sink('hmr',[H[i],i]);sink('phase',[C[i],i]);}prep(false);unit(false);power(false);prod(true);for(let i=0;i<n;i++)sink('phase',[C[i],i]);prod(false);power(true);unit(true);prep(true);run(can,true);run(unn,true);}
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
 this.e=data;this.sign=data+1;this.tag=Array.from({length:Math.log2(n)},(_,i)=>data+2+i);this.fire=this.tag.at(-1)+1;this.tst=this.fire+1;this.aux=this.fire+2;this.nq=this.aux+1;this.cin=this.R[n+1];this.hi=this.L[n+1];this.both=this.hi;}
 op(c,z){if(c.length<=2){this.raw(c.length?c[0]:-1,c.length===2?c[1]:-1,z);return;}const b=this.y,n=c.length;
 if(n-2>b.length)throw Error("borrow");
 for(let s=0;s<2;s++){if(s===0)this.raw(c[0],c[1],b[0]);for(let i=1;i<n-2;i++)this.raw(c[i+1],b[i-1],b[i]);this.raw(c[n-1],b[n-3],z);for(let i=n-3;i>=1;i--)this.raw(c[i+1],b[i-1],b[i]);if(s===0)this.raw(c[0],c[1],b[0]);}}
 add(controls,a,b,cin,cout){
  if(!controls.length){super.add(controls,a,b,cin,cout);return;}
  const tmp=controls.length>1&&!controls.includes(this.aux)&&cout!==this.aux?this.aux:null;const en=controls.length===1?[controls[0]]:tmp===null?controls:[tmp];if(tmp!==null)this.op(controls,tmp);
  for(let i=0;i<a.length;i++){const x=a[i],y=b[i],z=i?a[i-1]:cin;this.raw(x,-1,y);this.raw(x,-1,z);this.raw(z,y,x);}
  if(cout!==null)this.op(en.concat(a.at(-1)),cout);
  for(let i=a.length-1;i>=0;i--){const x=a[i],y=b[i],z=i?a[i-1]:cin;this.raw(z,y,x);this.raw(x,-1,z);this.raw(x,-1,y);this.op(en.concat(x),y);this.op(en.concat(z),y);}
  if(tmp!==null)this.op(controls,tmp);
 }
 lt(c,a,b,z){for(const i of b)this.raw(-1,-1,i);const maj=()=>{for(let i=0;i<a.length;i++){const v=i?a[i-1]:this.cin;this.raw(a[i],-1,b[i]);this.raw(a[i],-1,v);this.raw(v,b[i],a[i]);}};maj();this.op(c.concat(a.at(-1)),z);this.reverse(maj);for(const i of b)this.raw(-1,-1,i);}
 restore(c,A,B,cin,h){if(c.length!==1)throw Error("fused single control");const e=c[0];for(const z of digit(A.length,A,B,h,e,cin))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z.at(-1));}
 multag(c,q,hi,z){const neg=[];for(let j=0;j<this.tag.length;j++)if(!(q&(1<<j)))neg.push(this.tag[j]);neg.push(...hi);for(const w of neg)this.raw(-1,-1,w);this.op(c.concat(this.tag,hi),z);for(const w of neg)this.raw(-1,-1,w);}
 bias(c,v){for(let j=0;j<this.tag.length;j++){if(!(v&(1<<j)))continue;for(let i=this.tag.length-1;i>=j;i--)this.op(c.concat(this.tag.slice(j,i)),this.tag[i]);}}
 perm(c,arr,src){const used=new Set();for(let s=0;s<arr.length;s++){if(used.has(s))continue;let j=s;while(!used.has(j)){used.add(j);const nx=src[j];if(nx!==s)this.swap(c,arr[j],arr[nx]);j=nx;}}}
 plan(){
  const n=this.n,L=this.L,R=this.R,tag=this.tag,c=[this.fire],all=[],mk=()=>[],one=(ar,fn,rev=false)=>ar.push({fn,rev}),cat=(ar,other,inv=false)=>{if(!inv)ar.push(...other);else for(let i=other.length;i--;)ar.push({fn:other[i].fn,rev:!other[i].rev});};
  const rot=(ar,w,controls,dir)=>{for(let j=0;j<tag.length;j++){const s=1<<j;if(s>=w.length)break;one(ar,()=>this.rot(controls.concat(tag[j]),w,dir*s));}};
  const norm=(ar,w,controls)=>{for(let j=tag.length;j--;){const s=1<<j;if(s>=w.length)continue;one(ar,()=>{this.zer(controls,w.slice(w.length-s),tag[j]);this.rot(controls.concat(tag[j]),w,s);});}};
  const val=(w,controls,bias)=>{const a=mk();norm(a,w,controls);rot(a,w,controls,-1);one(a,()=>this.bias(controls,bias));return a;};
  const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]);
  const W=L.slice(0,n),S=R.slice(0,n);
  one(all,()=>this.lt([],S,W.slice(1).concat(this.hi),this.sign));
  one(all,()=>{const cc=[this.sign];for(const z of S)this.op(cc,z);this.op(cc,this.cin);this.add(cc,W,S,this.cin,null);this.op(cc,this.cin);});
  one(all,()=>this.raw(-1,-1,R[n]));cat(all,val(W,[],0));
  for(let k=0;k<n;k++){
   const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);
   const select=(z)=>{for(let a=k;a<n-1;a++){const bits=[];for(let j=k+1;j<=a;j++)bits.push(R[n-j]);this.multag([],a,bits,z);}};
   one(all,()=>select(this.fire));
   if(k>0&&k<n-1){const cp=[this.tst];
    one(all,()=>{const cond=()=>{this.op([r[m-1]],this.both);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),this.both);this.raw(-1,-1,r[m-1]);const add=()=>this.add([],v,u,this.cin,this.aux);add();this.reverse(()=>this.add([],v,u,this.cin,null));this.raw(-1,-1,this.aux);};cond();this.op([this.fire,this.aux,this.both],this.tst);this.reverse(cond);});
    cat(all,val(A,cp,k),true);
    one(all,()=>{this.reverse(()=>this.add(cp,r,A,this.cin,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,this.cin,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
    cat(all,val(A,cp,k));one(all,()=>this.op([L[n-k]],this.tst));
   }
   cat(all,val(A,c,k),true);
   norm(all,r,c);
   one(all,()=>this.restore(c,r,A,this.cin,this.hi));
   one(all,()=>this.op(c,this.tst));
   for(let i=0;i<m-1;i++)one(all,()=>{this.multag(c,i,[],this.tst);const en=[this.tst],rh=r.slice(i+1),ah=A.slice(i+1);for(const z of A)this.swap(en,this.aux,z);this.restore(en,rh,ah,this.cin,this.aux);this.op(en.concat(this.aux),A[0]);this.op(en.concat(A[0]),this.aux);});
   one(all,()=>this.multag(c,m-1,[],this.tst));
   rot(all,r,c,-1);
   one(all,()=>this.op(c,this.tst));
   for(let i=0;i<m-1;i++)one(all,()=>{this.multag(c,i,[],this.tst);const en=[this.tst];this.reverse(()=>this.restore(en,v,u,this.cin,A[i]));for(let j=t;j--;)this.swap(en,A[i],u[j]);});
   one(all,()=>this.multag(c,m-1,[],this.tst));
   one(all,()=>{this.reverse(()=>this.restore(c,v,u,this.cin,this.hi));for(let j=t;j--;)this.swap(c,this.hi,u[j]);});
   for(let h=0;h<m;h++)one(all,()=>{this.multag(c,h,[],this.tst);const a=m-h,src=Array(n+2).fill(-1);for(let i=0;i<a;i++)src[i]=h+i;
    for(let j=0;j<h+t;j++)src[n-j]=j<h?j:(j===h?n+1:n-(j-h-1));src[n+1]=m;
    if(new Set(src).size!==n+2||src.includes(-1))throw Error("perm");this.perm([this.tst],L,src);this.multag(c,h,[],this.tst);});
   one(all,()=>{for(let j=0;j<n+2;j++)this.swap(c,L[j],R[j]);this.bias(c,k);this.op(c,this.sign);this.op([L[n-k]],this.fire);});
  }
  one(all,()=>{for(const w of tag)this.raw(-1,-1,w);this.raw(-1,-1,this.sign);
    for(const B of [L,R])for(let j=n;j>=1;j--)this.swap([],B[j],B[j+1]);});
  return all;
 }
}
class FlatUnit extends UnitWalk{plan(){const a=super.plan(),n=this.n,u=Array.from({length:n},(_,i)=>this.L[n+1-i]),v=Array.from({length:n},(_,i)=>this.R[n+1-i]);a.push({rev:false,fn:()=>{const save=this.cin;this.cin=this.aux;this.zer([],v.slice(1),this.sign);const ctl=[this.sign];for(const z of u)this.op(ctl,z);this.op(ctl,this.cin);this.add(ctl,v,u,this.cin,null);this.op(ctl,this.cin);this.lt([],u,v.slice(1).concat(this.L[1]),this.sign);this.raw(-1,-1,this.L[0]);for(let j=0;j<n+2;j++)this.swap([],this.L[j],this.R[n+1-j]);this.cin=save;}});return a;}}
class LiftKit extends UnitWalk{
 constructor(n){super(n);const vec=(a,m)=>Array.from({length:m},(_,i)=>a+i);this.modw=vec(0,n);this.dat=vec(3*n,n);this.outerTag=vec(5*n,Math.log2(n));const ix=5*n+Math.log2(n);this.on=ix;this.ext=ix+1;this.choice=ix+2;this.cin=ix+3;this.helper=ix+4;this.aux=ix+5;this.y=vec(n,2*n);this.incWord=vec(n,n);this.maxPhys=ix+9;}
 tick(ctl,xs,ys,b){const h=this.helper;for(let j=0;j<xs.length;j++){this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);this.raw(ctl,xs[j],h);}}
 incmod(){this.raw(-1,-1,this.cin);this.add([],this.incWord,this.modw,this.cin,null);this.raw(-1,-1,this.cin);this.reverse(()=>this.add([],this.incWord,this.modw,this.cin,null));}
 lifts(K){const a=[],n=this.n,U=this.dat,M=this.modw,H=this.outerTag,active=this.on,b=this.choice;
  const flip=U.filter((_,j)=>Boolean((K>>BigInt(j))&1n));
  for(let i=0;i<n-1;i++)a.push({rev:false,fn:()=>{this.less([],H,i,active);for(const z of flip)this.raw(-1,-1,z);this.tick(active,U,M,b);this.reverse(()=>this.incmod());this.tick(active,U,M,b);this.incmod();for(const z of flip)this.raw(-1,-1,z);
   this.add([b],M,U,this.cin,null);this.op([active],b);this.lt([active],M,U,b);this.rot([active],M,1);this.less([],H,i,active);
  }});return a;
 }
 lengths(){const ops=[],M=this.modw,h=this.outerTag,k=h.length;for(let j=k;j--;)ops.push({rev:false,fn:()=>{const d=1<<j;this.zer([],M.slice(M.length-d),h[j]);this.rot([h[j]],M,d);}});for(let j=0;j<k;j++)ops.push({rev:false,fn:()=>this.rot([h[j]],M,-(1<<j))});return ops;}
}
function unitMap(n,W,K){const m=new Array(W.nq).fill(-1),ix=5*n+Math.log2(n),q=[ix,ix+2,ix+3,ix+4];
 for(let j=0;j<n;j++){m[W.L[j]]=j;m[W.R[j]]=3*n+j;}
 m[W.L[n]]=q[0];m[W.L[n+1]]=q[1];m[W.R[n]]=q[2];m[W.R[n+1]]=q[3];
 for(let j=0;j<n;j++)m[2*(n+2)+j]=4*n+j;m[2*(n+2)+n]=ix+9;for(let j=0;j<2*n;j++)m[3*n+5+j]=n+j;
 m[W.e]=ix+1;m[W.sign]=ix+5;for(let j=0;j<W.tag.length;j++)m[W.tag[j]]=5*n+j;m[W.fire]=ix+6;m[W.tst]=ix+7;m[W.aux]=ix+8;
 if(m.some(i=>i<0)||new Set(m).size!==W.nq||Math.max(...m)!==W.nq-1)throw Error("wire map");return m;}
function emitPUnit(reverse,sink){const n=128,p=(1n<<256n)-(1n<<32n)-977n,mask=(1n<<128n)-1n;let z=1n;for(let k=1;k<n;k*=2)z=(z*(2n-p*z))&mask;const l=new LiftKit(n),w=new FlatUnit(n),wm=unitMap(n,w,l),nrm=l.lengths(),all=[[l,l.lifts(p&mask),true,null],[l,nrm,true,null],[w,w.plan(),false,wm],[l,nrm,false,null],[l,l.lifts(z),false,null]];
 if(reverse)all.reverse();for(const [G,ops,rv,map] of all){const inv=rv!==!!reverse;if(inv)ops.reverse();for(const block of ops){G.g=[];block.fn();if(map){for(let i=0;i<G.g.length;i++){const t=G.g[i],a=t>>>20&1023,b=t>>>10&1023;G.g[i]=((a===1023?1023:map[a])<<20)|((b===1023?1023:map[b])<<10)|map[t&1023];}}if(block.rev!==inv)G.g.reverse();sink(G.g);}if(inv)ops.reverse();}return l.nct.map((x,i)=>x+w.nct[i]);}
class Terminal extends Gate{
 op(c,z){return UnitWalk.prototype.op.call(this,c,z);}
 constructor(m,pol,digits){const k=Math.log2(m),stride=m+2;const flags=3*m+5+2*m,e=flags;super(0,e,m,true);
  this.m=m;this.digits=digits;this.E=e;this.sg=e+1;this.tag=Array.from({length:k},(_,i)=>e+2+i);this.cin=e+2+k;this.f=this.cin+1;this.yq=this.cin+2;this.pol=pol;
  this.S=Array.from({length:m},(_,i)=>stride-1-i);this.M=Array.from({length:m},(_,i)=>2*stride-1-i);
  this.T=Array.from({length:m},(_,i)=>2*stride+i);this.Jtop=2*stride+m;const yw=2*stride+m+1;
  this.D=Array.from({length:m},(_,i)=>yw+i);this.y=Array.from({length:m},(_,i)=>yw+m+i);this.clean=[];
 }
 add(ctrl,a,b,cin,cout){
  if(!ctrl.length){super.add(ctrl,a,b,cin,cout);return;}for(let i=0;i<a.length;i++){const x=a[i],y=b[i],v=i?a[i-1]:cin;this.raw(x,-1,y);this.raw(x,-1,v);this.raw(v,y,x);}
  if(cout!==null)this.op(ctrl.concat(a.at(-1)),cout);for(let i=a.length;i--;){const x=a[i],y=b[i],v=i?a[i-1]:cin;this.raw(v,y,x);this.raw(x,-1,v);this.raw(x,-1,y);this.op(ctrl.concat(x),y);this.op(ctrl.concat(v),y);}
 }
 lt(c,a,b,z){for(const i of b)this.raw(-1,-1,i);const maj=()=>{for(let i=0;i<a.length;i++){const v=i?a[i-1]:this.cin;this.raw(a[i],-1,b[i]);this.raw(a[i],-1,v);this.raw(v,b[i],a[i]);}};maj();this.op(c.concat(a.at(-1)),z);this.reverse(maj);for(const i of b)this.raw(-1,-1,i);}
 mod(c,a,b,minus){
  const body=()=>{this.add(c,a,b,this.cin,this.f);this.reverse(()=>this.add(c,this.M,b,this.cin,this.f));this.add(c.concat(this.f),this.M,b,this.cin,null);this.op(c,this.f);this.lt(c,a,b,this.f);};
  if(minus)this.reverse(body);else body();
 }
 orient(sign=this.sg){const c=sign===null?[this.f]:[sign,this.f];this.zer([],this.S,this.f);this.raw(-1,-1,this.f);
  for(const i of this.S)this.op(c,i);this.op(c,this.cin);this.add(c,this.M,this.S,this.cin,null);this.op(c,this.cin);
  this.raw(-1,-1,this.f);this.zer([],this.S,this.f);
 }
 plan(){
  const k=this.tag.length,blocks=[],append=(fn,rev=false)=>blocks.push({fn,rev});
  const norm=(i)=>{const s=1<<i;this.zer([],this.M.slice(this.m-s),this.tag[i]);this.rot([this.tag[i]],this.M,s);this.rot([this.tag[i]],this.S,s);this.rot([this.tag[i]],this.T,s);};
  for(let i=k;i--;)append(()=>norm(i));append(()=>this.orient());
  const reduce=()=>this.restore([],this.M,this.D,this.cin,this.yq);append(reduce);
  const max=this.digits.length-1,act=this.pol?[this.E]:[];
  const acc=(a,minus)=>append(()=>this.mod(act,a,this.T,minus));
  acc(this.S,true);
  const word=[],rows=[];
  for(let i=0;i<=max;i++){
   const cur=(i&1)?this.D:this.S,old=(i&1)?this.S:this.D;
   if(this.digits[i])word.push({fn:()=>this.mod([],cur,this.T,true),rev:false});
   if(i<max){const f=()=>this.mod([],cur,old,false);word.push({fn:f,rev:false});rows.push(f);}
  }
  for(let i=rows.length;i--;)word.push({fn:rows[i],rev:true});
  for(const step of word)append(step.fn,step.rev);
  const reflect=()=>this.orient(this.pol?this.E:null);
  append(reflect);
  for(let i=word.length;i--;)append(word[i].fn,!word[i].rev);
  append(reflect,true);
  append(reduce,true);append(()=>this.orient(),true);for(let i=0;i<k;i++)append(()=>norm(i),true);
  return blocks;
 }
}
class UnitPark extends Terminal{
 parking(){
  const k=this.tag.length,blocks=[],append=(fn,rev=false)=>blocks.push({fn,rev}),e=this.pol?[this.E]:[];
  const norm=j=>{const s=1<<j;this.zer(e,this.M.slice(this.m-s),this.tag[j]);this.rot(e.concat(this.tag[j]),this.M,s);};
  for(let i=k;i--;)append(()=>norm(i));
  append(()=>this.restore(e,this.M,this.S,this.cin,this.Jtop));
  for(let i=0;i<this.m-1;i++)append(()=>{this.less(e,this.tag,i,this.f);const c=e.concat(this.f);
   for(const b of this.S)this.swap(c,this.yq,b);this.restore(c,this.M,this.S,this.cin,this.yq);
   this.op(c.concat(this.yq),this.S[0]);this.op(c.concat(this.S[0]),this.yq);this.less(e,this.tag,i,this.f);
  });
  for(let j=0;j<k;j++)append(()=>this.rot(e.concat(this.tag[j]),this.S,-(1<<j)));
  for(let i=1;i<this.m;i++)append(()=>{const l=this.m-1-i;this.less(e,this.tag,l,this.f);this.swap(e.concat(this.f),this.S[i],this.T[i]);this.less(e,this.tag,l,this.f);});
  for(let i=0;i<k;i++)append(()=>norm(i),true);return blocks;
 }
}
function terms(p){const k=(p-1n)/2n,a=[1n,1n];while(a.at(-1)<=k)a.push(a.at(-1)+a.at(-2));a.pop();let rem=k;const out=Array(a.length).fill(false);for(let i=a.length;i--;){if(a[i]<=rem){out[i]=true;rem-=a[i];}}if(rem)throw Error("fib");return out;}

function emitRegenerate(sink,erase=false){const n=128,p=(1n<<256n)-(1n<<32n)-977n,pk=new UnitPark(n,false,[]),w=new UnitWalk(n),s=new Terminal(n,true,terms(p));const ex={rev:false,fn:()=>{for(let i=0;i<n+2;i++)w.swap([],w.L[i],w.R[n+1-i]);}},seq=[[pk,pk.parking(),false],[w,[ex],false],[w,w.plan(),false],[s,s.plan(),false],[w,w.plan(),true],[w,[ex],true],[pk,pk.parking(),true]];
 if(!erase)seq.reverse();for(const [G,ops,rv] of seq){const inv=rv!==(!erase);if(inv)ops.reverse();for(const o of ops){G.g=[];o.fn();if(inv!==o.rev)G.g.reverse();sink(G.g);}if(inv)ops.reverse();}return w.nct.map((x,i)=>x+s.nct[i]+pk.nct[i]);}
function preparedForwardBody(emitF,sink){const W=new UnitWalk(128),P=new UnitPark(128,false,[]),X=P.S,V=P.M,J=P.T,Y=P.D.concat(P.y),E=W.e,ct=[0,0,0],mp=X.concat(J,Y,V),extra=[W.L[0],W.L[1],W.R[0],W.R[1],P.Jtop,...Array.from({length:11},(_,i)=>646+i)];for(let i=640,j=0;i<657;i++)mp[i]=i===648?E:extra[j++];W.y=Y;
 function use(buf){for(const g of buf){const a=g>>>20&1023,b=g>>>10&1023;ct[a===1023?0:b===1023?1:2]++;}sink('packed',buf);}
 function chunk(f){W.g=[];f();use(W.g);}const recode=()=>{W.raw(X[0],-1,V[0]);W.zer([V[0]],X.slice(1).concat(V.slice(1)),X[0]);W.raw(X[0],-1,V[0]);};
 for(let i=0;i<128;i++)sink('hmr',[J[i],128+i]);chunk(recode);chunk(()=>W.raw(-1,-1,E));emitF(emitPUnit,(kind,d)=>{if(kind==='packed'){for(let i=0;i<d.length;i++){const z=d[i],a=z>>>20&1023,b=z>>>10&1023;d[i]=((a===1023?1023:mp[a])<<20)|((b===1023?1023:mp[b])<<10)|mp[z&1023];}use(d);return;}if(kind==='nct'){for(let off=0;off<d.length;off+=4096){const out=[];for(let j=off;j<d.length&&j<off+4096;j++){const row=d[j];out.push(((row.length>1?mp[row[0]]:1023)<<20)|((row.length>2?mp[row[1]]:1023)<<10)|mp[row.at(-1)]);}use(out);}return;}sink(kind,[mp[d[0]],d[1]]);});
 chunk(()=>{for(let i=0;i<128;i++){W.swap([],J[i],Y[i]);W.swap([],J[i],Y[128+i]);}});chunk(recode);emitRegenerate(use);chunk(()=>W.raw(-1,-1,E));for(let i=0;i<128;i++)sink('phase',[J[i],128+i]);return ct;}
function emitForward128(sink){return nativeForward128(emitPUnit,sink);}function emitPreparedForward(sink){return preparedForwardBody(nativeForward128,sink);}
module.exports = { UnitWalk, UnitPark, emitRegenerate, emitForward128, emitPreparedForward };
