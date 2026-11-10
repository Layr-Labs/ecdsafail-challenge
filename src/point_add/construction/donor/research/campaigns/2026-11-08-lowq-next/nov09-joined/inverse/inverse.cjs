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
function emitForward128(emitPUnit,sink){const n=128,P=(1n<<256n)-(1n<<32n)-977n,D=1n<<128n,kappa=shortinv(P,D),ff=fieldprod(256,128,[[32,1],[10,1],[5,-1],[4,-1],[0,1]]);const{T,H,L,C}=ff,S=vec(7,640),color=647,outer=648,idx=vec(6,649),en=655,tmp=656;const norm=normal(T,H,S,L),unn=normal(T,H,S,L,false),can=digit(n,T,C,color),mad=madd(T,C,H,tmp),vp=val_low(T,idx,tmp,L);function run(g,rev=false){sink('nct',rev?[...g].reverse():g);}function prod(back){run(shprod(128,T,H,C,L,vec(4,649)),back);}function prep(back){const loc=[0,4,5,10,32,256],R=[];let k=0;for(let j=0;j<257;j++){const a=loc.indexOf(j);R.push(a<0?L[k++]:idx[a]);}run(remprep(128,257,T,R,C,H,en,idx,[5,2,1],[4,3,0]),back);}function unit(back){run(can,true);emitPUnit(back,buf=>sink('packed',buf));run(can);}function power(back){run(vp);for(let k=0;k<127;k++)run(one_stage(128,outer,T,H,S,idx,en,tmp,L,back?126-k:k,kappa),back);run(vp,true);}run(ff.g);run(norm);run(can);run(mad);for(let i=0;i<n;i++){run([[C[i],H[i]]]);sink('hmr',[H[i],i]);sink('phase',[C[i],i]);}prep(false);unit(false);power(false);prod(true);for(let i=0;i<n;i++)sink('phase',[C[i],i]);prod(false);power(true);unit(true);prep(true);run(can,true);run(unn,true);}
function ltg(A,B,H,e,t){const n=A.length,last=n-1,g=[];const X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);for(const w of B)X(w);if(n===1){T(e,A[0],t);T(t,B[0],H);T(e,A[0],t);X(B[0]);return g;}for(let i=1;i<n;i++)CX(A[i],B[i]);T(e,A[last],H);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);T(e,A[last],t);T(t,B[last],H);T(e,A[last],t);for(let i=n-2;i>=0;i--)T(B[i],A[i],A[i+1]);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const w of B)X(w);return g;}
function mdg(M,A,B,h,e,t){return [...plus(A,B,h,e,t),...digit(M.length,M,B,h,e,t),...ltg(A,B,h,e,t)];}
function fusedblock(n,k,M,J,e,t){let g=[];for(let i=k-1;i>=0;i--)g=g.concat(digit(n,M,J.slice(i,i+n),J[i+n],e,t));return g;}
function gcdN(a,b){while(b){const t=a%b;a=b;b=t;}return a;}function shseq(w,value,e=null){let g=[];for(let j=0;j<w.length;j++)if(value>>j&1)for(let k=w.length-1;k>=j;k--){const c=[...(e===null?[]:[e]),...w.slice(j,k)];g=g.concat(MCX(c,w[k],shseq.borrow));}return g;}function flagHeight(w,t,z,d){const c=w.slice(t-1),v=c.map((_,j)=>j===0);return negate(c,MCX(c,z,d),v);}function mcN(c,values,dest,loan){return negate(c,MCX(c,dest,loan),values);}function Wstream(Cls,n,rev,L,R,ws,dirty,sink){const w=new Cls(n),m=new Array(w.nq).fill(-1),set=(old,nn)=>old.forEach((j,i)=>m[j]=nn[i]);set(w.L,L);set(w.R,R);set(w.y,dirty);m[w.sign]=ws.sign;set(w.tag,ws.tag);m[w.fire]=ws.fire;m[w.tst]=ws.tst;m[w.aux]=ws.aux;const plan=w.plan();if(rev)plan.reverse();for(const B of plan){w.g=[];B.fn();if(B.rev!==rev)w.g.reverse();for(let i=0;i<w.g.length;i++){const z=w.g[i],a=z>>>20&1023,b=z>>>10&1023,t=z&1023,aa=a===1023?1023:m[a],bb=b===1023?1023:m[b],tt=m[t];if(aa<0||bb<0||tt<0||aa===tt||bb===tt||aa===bb&&aa!==1023)throw 'W ports '+[a,b,t,aa,bb,tt];w.g[i]=(aa<<20)|(bb<<10)|tt;}sink('packed',w.g);}}
function pModShear(terms,rr,v,u,out,n,borrow,pad,tmp,sp,en,sink,undo=false){const run=(g,rev=false)=>sink('nct',rev?[...g].reverse():g),W0=where;const T=terms.slice();if(undo)T.reverse();for(const [k,sign] of T){const neg=(sign<0)!==undo;if(k===0){run(mdg(v,u,out,tmp,en,sp),neg);continue;}const input=borrow.slice(0,k),A=[...input,...u,pad],B=[...input,pad,...u];const pass=(w,sub)=>{const map=W0(NR(n,k+1),[...v,...w]);run(map);run(mdg(v,w.slice(0,n),out,tmp,en,sp),sub);run(map,true);};if(neg){pass(A,false);pass(B,true);}else{pass(B,false);pass(A,true);}}}
function outerloadJ(n,term,L,R,J,sign,data,ws,sink){const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]),[e,tmp,sp,pad]=ws;for(let t=1;t<=n;t++){const cls=flagHeight(v,t,e,data);sink('nct',cls);pModShear(term,null,v.slice(0,t),u.slice(0,t),J.slice(0,t),t,data,pad,tmp,sp,e,sink);if(t>1){sink('nct',[[sign],[e,sign,sp],[sign]]);const a=J.slice(0,t);for(let w of a)sink('nct',[[sp,w]]);sink('nct',incReg(a,data,sp));sink('nct',plus(v.slice(0,t),a,null,sp));sink('nct',[[sign],[e,sign,sp],[sign]]);}sink('nct',[...cls].reverse());}}
function mulG(n,L,R,J,x,ws,borrow,sink){const vo=Array.from({length:n},(_,j)=>R[n+1-j]),w=[...J,x];const [sel,tmp]=ws;for(let t=1;t<=n;t++){const d=n+1-t,cls=flagHeight(vo,t,sel,borrow),rot=[];for(const[i,j]of rotleft(n+1,d))rot.push(...fr(sel,w[i],w[j]));sink('nct',cls);sink('nct',rot);const g=fusedblock(d,t,L.slice(0,d),w,sel,tmp);sink('nct',[...g].reverse());sink('nct',[...cls].reverse());}}

function Gtop(n,L,VR,J,ws,loan,put){const [ctl,non]=ws,vs=Array.from({length:n},(_,i)=>VR[n+1-i]);for(let t=1;t<=n;t++){const d=n-t,B=L.slice(0,d),choose=flagHeight(vs,t,ctl,loan);put(choose);put([[ctl,L[d]]]);if(d){const nn=mcN([ctl,...B],[true,...B.map(()=>false)],non,loan);put([[ctl,non]]);put(nn);const z=[...J.slice(t),...vs.slice(0,t)],g=where(NR(d,t),[...B,...z]);put([...g].reverse());put([[non,z.at(-1),L[d]]]);put(g);put([...nn].reverse());put([[ctl,non]]);}put([...choose].reverse());}}
function routeZeros(n,L,R,ws,loan,put,inv=false){const V=Array.from({length:n},(_,j)=>R[n+1-j]);for(let i=0;i<n;i++){const t=inv?n-i:i+1,j=n+1-t,sel=flagHeight(V,t,ws,loan);const a=fr(ws,L[0],L[j]),b=fr(ws,L[1],L[j+1]);put(sel);put(inv?b:a);put(inv?a:b);put([...sel].reverse());}}
function parkOuter(n,M,rem,Q,S,p,off,tmp,loan,sink,rev=false){const put=z=>sink('nct',z);if(!rev){for(let j=0;j<S.length;j++)put([[S[j],Q[j]]]);for(let j=0;j<S.length;j++)sink('hmr',[S[j],off+j]);return;}const k=-shortinv(p,1n<<BigInt(S.length));for(let j=0;j<S.length;j++){const low=M.slice(0,j+1),pp=mcN(low,low.map(()=>false),tmp,loan);put(pp);put([[tmp,Q[j],S[j]]]);for(let x=0;x<1<<(j+1);x++)if((BigInt(x)*k>>BigInt(j))&1n){const a=[tmp,...rem.slice(0,j+1)],b=[true,...eq_bits(rem,x).slice(0,j+1)];put(mcN(a,b,S[j],loan));}put([...pp].reverse());sink('phase',[S[j],off+j]);put([[S[j],Q[j]]]);}}
function parkInner(n,L,R,Q,S,sg,p,off,ws,loan,sink,rev=false){const [e,t,h,D]=ws,put=g=>sink('nct',g),V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),bits=S.length,kp=shortinv(p,1n<<BigInt(bits));shseq.borrow=loan;function delta(){for(let l=0;l<n-1;l++){const A=gt(S,l,e,null,loan),C=[e,...V.slice(0,l+1)],B=[true,...V.slice(0,l).map(()=>false),true];put(A);put(mcN(C,B,D,loan));put([...A].reverse());}}
function bias(back){for(let ii=0;ii<n;ii++){const l=back?n-1-ii:ii,cs=[D,...V.slice(0,l+1)],v=[true,...V.slice(0,l).map(()=>false),true],g=mcN(cs,v,e,loan),a=shseq(S,(l+1)%n,e);put(g);put(back?a:[...a].reverse());put([...g].reverse());}}
function mark(){for(let i=0;i<n-1;i++){const cs=[D,...S],v=[true,...eq_bits(S,i)];put(mcN(cs,v,L[i],loan));}}
function mask(){put([[D]]);for(let j=0;j<bits;j++)put([[D,S[j],U[j]]]);put([[D]]);}
function move(){for(let i=1;i<=n;i++){const a=flagHeight(V,i,e,loan);put(a);put(fr(e,D,L[n-i]));put([...a].reverse());}}
function extract(){for(let j=0;j<n-1;j++){const cs=[D,...L.slice(0,j+1)],v=[true,...L.slice(0,j).map(()=>false),true],a=mcN(cs,v,e,loan);put(a);for(let b=0;b<bits;b++)if((j>>b)&1)put([[e,S[b]]]);put([...a].reverse());}for(let j=0;j<bits;j++){const cs=[D,...V.slice(0,j+1)],v=cs.map(()=>false),a=mcN(cs,v,e,loan);put(a);put([[e,U[j],S[j]]]);const m=1<<(j+1);for(let raw=1;raw<m;raw+=2){const sol=shortinv(BigInt(raw),BigInt(m));for(let si=0;si<2;si++){const guess=(BigInt(si?1:-1)*kp*sol+BigInt(m*m)*kp)%BigInt(m);if((guess>>BigInt(j))&1n){const qa=[e,sg,...Q.slice(0,j+1)],pol=[true,!!si,...eq_bits(Q,raw).slice(0,j+1)];put(mcN(qa,pol,S[j],loan));}}}put([...a].reverse());}}
if(!rev){Gtop(n,L,R,Q,[e,t],loan,put);delta();bias(false);mark();mask();move();for(let j=0;j<bits;j++)sink('hmr',[S[j],off+j]);routeZeros(n,L,R,e,loan,put);}else{routeZeros(n,L,R,e,loan,put,true);move();extract();for(let j=0;j<bits;j++)sink('phase',[S[j],off+j]);mask();mark();bias(true);delta();Gtop(n,L,R,Q,[e,t],loan,put);}}
function inverseField(n,G,Wc,sink,tap=()=>{}){const terms=n===4?[[8,1],[2,-1],[0,-1]]:n===8?[[16,1],[4,-1],[0,1]]:[[256,1],[32,-1],[10,-1],[5,1],[4,1],[0,-1]],p=terms.reduce((a,[j,v])=>a+BigInt(v)*(1n<<BigInt(j)),0n),K=terms.slice(1).map(([j,v])=>[j,-v]);const bits=Math.log2(n),base=5*n,M=vec(n,0),rm=vec(n,n),H=vec(n,2*n),Q=vec(n,3*n),C=vec(n,4*n),RR=[...rm,...H],loan=[...H,...C],Htop=base,S=vec(bits,base+1),act=base+bits+1,lp=[act+1,act+2],rp=[act+3,act+4],sig=act+5,e=act+6,t=act+7,x=act+8,temps=[act,e,t,x],L=[...M,...lp],R=[...rm,...rp],ws={sign:sig,tag:S,fire:e,tst:t,aux:x},vt=Array.from({length:n},(_,j)=>R[n+1-j]);const put=(v)=>sink('nct',v),rev=v=>[...v].reverse(),rot=(word,dir)=>{let a=[];for(let j=0;j<bits;j++){const z=1<<j;for(const [i,k]of rotleft(word.length,(word.length+dir*z)%word.length))a=a.concat(fr(S[j],word[i],word[k]));}return a;};const norm=normal(M,[],S,C,false),high=digit(n,M,H,Htop),split=where(NR(n,n),[...M,...RR]);
put([[act]]);put(norm);put(high);put(split);tap('split');const ss=[];for(let j=0;j<bits;j++)ss.push(...[[S[j],Q[j]],[Q[j],S[j]],[S[j],Q[j]]]);put(ss);
Wstream(G,n,false,L,R,ws,loan,sink);put(rev(ss));tap('outer');outerloadJ(n,terms,L,R,Q,sig,loan,temps,sink);tap('alpha');parkInner(n,L,R,Q,S,sig,p,0,temps,loan,sink,false);tap('ipark');
const wi={sign:act,tag:S,fire:e,tst:t,aux:x};Wstream(Wc,n,false,[...vt,R[0],R[1]],[...Q,L[0],L[1]],wi,loan,sink);tap('inner');parkInner(n,L,R,Q,S,sig,p,0,temps,loan,sink,true);tap('unpark');
mulG(n,L,R,Q,act,[e,t],loan,sink);tap('winding');parkOuter(n,M,rm,Q,S,p,bits,act,loan,sink);Wstream(G,n,true,L,R,ws,loan,sink);parkOuter(n,M,rm,Q,S,p,bits,act,loan,sink,true);tap('restore');
put(rev(split));put(rev(high));for(let j=0;j<n-1;j++){const q=gt(S,j,e,null,C);put(q);put(digit(n-1-j,M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,t));put(rev(q));}tap('qsplit');
for(let i=0;i<n;i++){const q=gt(S,n-i-1,e,null,C);put(q);put(fr(e,Q[i],t));sink('hmr',[t,2*bits+i]);put(rev(q));}put(rot(M,-1));tap('preF');
const ff=fieldprod(2*n,n,K),perm=w=>w===base+1?act:w===base+2?e:w;put(rev(ff.g.map(a=>a.map(perm))));tap('F');
const y=[...H,...Q],neg=(1n<<BigInt(n))-shortinv(p,1n<<BigInt(n));let cm=[];for(let j=0;j<n;j++)if((neg>>BigInt(j))&1n)cm=cm.concat(plus(y.slice(0,n-j),rm.slice(j),null));put(cm);const rt=rot(rm,-1);put(rt);
for(let i=0;i<n;i++){const q=gt(S,n-i-1,e,null,C);put(q);sink('cphase',[e,rm[i],2*bits+i]);put(rev(q));}put(rev(rt));put(rev(cm));put(rot(M,1));put(rev(norm));put([[act]]);tap('complete');return{M,Roriginal:RR,Y:y,C,Zero:rm,active:act,qubits:x+1};}
const InverseGeneric=(function(){
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
   const select=(z)=>{for(let a=k;a<n-1;a++){const bits=[];for(let j=k+1;j<=a;j++)bits.push(R[n-j]);this.multag([],a,bits,z);this.multag([],a,bits.concat(R.slice(0,n-a)),z);}};
   one(all,()=>select(this.fire));
   if(k>0&&k<n-1){const cp=[this.tst];
    one(all,()=>{const cond=()=>{this.op([r[m-1]],this.both);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),this.both);this.raw(-1,-1,r[m-1]);const add=()=>this.add([],v,u,this.cin,this.aux);add();this.reverse(()=>this.add([],v,u,this.cin,null));this.raw(-1,-1,this.aux);};cond();this.op([this.fire,this.aux,this.both],this.tst);this.reverse(cond);});
    cat(all,val(A,cp,k),true);
    one(all,()=>{this.reverse(()=>this.add(cp,r,A,this.cin,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,this.cin,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
    cat(all,val(A,cp,k));one(all,()=>this.op([this.fire,L[n-k]],this.tst));
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
   one(all,()=>{for(let j=0;j<n+2;j++)this.swap(c,L[j],R[j]);this.bias(c,k);this.op(c,this.sign);if(k===0){this.op([L[n]],this.fire);}else{this.less([],tag,k-1,this.tst);this.op([this.tst,L[n-k]],this.fire);this.less([],tag,k-1,this.tst);}});
  }
  for(let len=1;len<=n;len++){const ml=n+1-len,split=R[n-len+1],larger=R.slice(1,n-len+1);
    const denTest=()=>this.zer([split],larger,this.fire);
    one(all,denTest);cat(all,val(L.slice(0,ml),c,len-1),true);
    one(all,()=>{for(let j=n;j>=ml;j--)this.swap(c,L[j],L[j+1]);});one(all,denTest);}
  one(all,()=>{this.raw(-1,-1,this.sign);for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});
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
function fq(c,A,B,cin,h){if(c.length!==1||!A.length||A.length!==B.length||[...A,...B,h,...c].includes(cin))throw'fold port';for(const op of digit(A.length,A,B,h,c[0],cin)){const z=op.at(-1);this.raw(op.length===1?-1:op[0],op.length===3?op[1]:-1,z);}}
UnitWalk.prototype.restore=fq;
return UnitWalk;})();
const InverseUnit=(function(){
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
function fq(c,A,B,cin,h){if(c.length!==1||!A.length||A.length!==B.length||[...A,...B,h,...c].includes(cin))throw'fold port';for(const op of digit(A.length,A,B,h,c[0],cin)){const z=op.at(-1);this.raw(op.length===1?-1:op[0],op.length===3?op[1]:-1,z);}}
UnitWalk.prototype.restore=fq;
return FlatUnit;})();
function emitInverse128(sink){return inverseField(128,InverseGeneric,InverseUnit,sink);}
module.exports = { emitInverse128 };
