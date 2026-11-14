'use strict';
// Q648_DIV source patches on the D14 divide body (evict): count carrier c2 (logical 643) eviction, applied after d14-p-d14-all.
// Parts (comma list in Q648_DIV, see d648-walks.cjs):
//   c2a : segment A start. After the outer walk c2 goes Q2 -> Q120 (all lanes; Q6..Q125 are zero there), then heights
//         121..124 -> their gap L[n+1-t]. Alpha: heights 125 (outerloadJ single group) and 126..127 (explicit path) relay Q120 -> selector shadow V[t] -> gap inside their own
//         iteration; height 128 is a 2-pass of its iteration (selector v127&Q120 clears Q120 and exits to gap=L[1]; then
//         v127&!gap). After alpha, c2 is on Q120 (h<=120) or gap(h) (h>=121).
//   c2g : ipark Gtop. At Gtop start 121 -> Q121, 122 -> Q122; 127/128 with 8|V: clear U2 by the identity U2=Q1^U1^Q2, then
//         gap -> U2. heights <=125: inside their own Gtop iteration c2 relays rest host -> V[t+2] (not in Gtop's
//         NR dividend Q[t..]++V[0..t-1]; hooks use V[t],V[t+1]) and back. 126: 2-pass (cls&gap clears gap, restores it
//         after the body; then cls&!gap). (Q120 alone was NOT structural: it is a dividend bit of Gtop's NR for t<=120.) After Gtop: Q120 (<=120), Q121, Q122, gap (123..126), U2 (127/128, 8|V; else c2=0).
//   c2ca: ipark count arithmetic. logic() wrapper lowers virtual c2 (S[2]) per height bucket: <=120 Q120, 121 Q121, 122 Q122,
//         123..126 gap, 127/128 U2 under 8|V (c2=0 there off-guard, measured). mask2 skips 127/128. Gather moves c2 into
//         port 641 after c3's hmr and rebuilds the masked U2 (identity + D/S1 correction), then hmr(641, off+2).
//   c2up: unpark. Extract c1, then c2 into port 641 and scatter2 (exact reverse of gather2) into the bucket hosts; c3 is
//         extracted through 641 (not 643), then c4. The reverse count arithmetic uses the same lowering (D648UP).
//   c2n : start. normal() computes c2 straight into Q2 (Q is zero at entry; high/split never touch Q) and the j=2 ss swap is
//         dropped, so the outer walk sees c2 on Q2 exactly as before and 643 is never written.
//   c2t : tail. parkOuter rev skips j=2 (Q2 stays folded = Q2_po^c2; rm2 == Q2_po on guard lanes N0..3=0, ledger); record 9's
//         phase from t = guard&(Q2^rm2). Before qsplit: e = c2, M <- rot(M,-4) under e (the 4-step of the un-normalization),
//         Q2 unfolded, e ^= !M127 (normalized N has M127=1, so after the step c2 = !M127 on every lane). qsplit: 2 passes per
//         iteration gated by M127; the c2=1 pass reads N through the wire view [M124..127, M0..123] with c2 fixed in gt.
//         rot(M,-1) without its j=2 step gives M_orig; then [s>j] = [top j+1 bits of M_orig zero] (cubes) in preF/complete,
//         and the c2 oracle (XOR over m>=1 of [top 4m bits zero]) feeds rot(rm,-1) and rot(M,1)/rev(normal) through e.
//   c2u2: unpark Gtop^-1 (2-pass for 123..126 with gap, as c2g), the unpark loop moves 123..126 from gap to Q126; then at
//         D14BeforeWinding start, buckets -> ledger's c2w entry hosts: tz(g)>=2 -> Q127, tz(g)<=1 & 8|V -> cleared U2.
//   c2upT: test scaffold. Route c2 from the bucket hosts back into 643 right after unpark's count arithmetic.
//   c2gT: test scaffold. Route back into 643 after ipark Gtop (instead of c2aT).
//   c2aT: test scaffold only. Route c2 from the alpha hosts back into 643 at the start of ipark (before Gtop).
// (hmr2 retracted: po.hmr folds c2 INTO Q2 (CNOT 643->Q2) before measuring, and the restore reads it back from Q2.)
const {parts}=require('./d648-walks.cjs');
const HELP=`
function D648RouteIn(n,L,R,Q,loan,put){
 put([[Q[2],Q[n-8]],[Q[n-8],Q[2]]]);
 const vt=Array.from({length:n},(_,j)=>R[n+1-j]);
 for(let t=n-7;t<=n-4;t++){const sel=flagHeight(vt,t,R[1],loan);put(sel);put(fr(R[1],Q[n-8],L[n+1-t]));put([...sel].reverse());}
}
function D648RouteOutA(n,L,R,Q,S2,loan,put){
 const vt=Array.from({length:n},(_,j)=>R[n+1-j]);
 for(let t=n-7;t<=n;t++){const sel=flagHeight(vt,t,R[1],loan);put(sel);put(fr(R[1],L[n+1-t],S2));put([...sel].reverse());}
 const lo=vt.slice(n-8),pr=mcN(lo,lo.map(()=>false),R[1],loan);put(pr);put(fr(R[1],Q[n-8],S2));put([...pr].reverse());
}
function D648Pred(vt,t,extra,pol,z,loan){const hc=vt.slice(t-1),cs=[...hc,...extra],ps=[...hc.map((_,i)=>i===0),...pol];return mcN(cs,ps,z,loan);}
function D648GtopIn(n,L,R,Q,loan,put){
 const vt=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),e=R[1];
 for(const [t,h] of [[n-7,Q[n-7]],[n-6,Q[n-6]]]){const p=D648Pred(vt,t,[],[],e,loan);put(p);put(fr(e,L[n+1-t],h));put([...p].reverse());}
 for(const t of [n-1,n]){const p=D648Pred(vt,t,vt.slice(0,3),[false,false,false],e,loan);put(p);put([[e,Q[1],U[2]],[e,U[1],U[2]],[e,Q[2],U[2]]]);put(fr(e,L[n+1-t],U[2]));put([...p].reverse());}
}
function D648GtopOutT(n,L,R,Q,S2,loan,put){
 const vt=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),e=R[1];
 for(const t of [n-1,n]){const p=D648Pred(vt,t,vt.slice(0,3),[false,false,false],e,loan);put(p);put(fr(e,U[2],S2));put([[e,Q[1],U[2]],[e,U[1],U[2]],[e,Q[2],U[2]]]);put([...p].reverse());}
 for(const [t,h] of [[n-7,Q[n-7]],[n-6,Q[n-6]]]){const p=D648Pred(vt,t,[],[],e,loan);put(p);put(fr(e,h,S2));put([...p].reverse());}
 for(let t=n-5;t<=n-2;t++){const p=D648Pred(vt,t,[],[],e,loan);put(p);put(fr(e,L[n+1-t],S2));put([...p].reverse());}
 const lo=vt.slice(n-8),pr=mcN(lo,lo.map(()=>false),e,loan);put(pr);put(fr(e,Q[n-8],S2));put([...pr].reverse());
}
function D648Buckets(n,L,Q,V,U){const B=[],lo=V.slice(n-8);
 B.push({t:n-8,hc:lo,hp:lo.map(()=>false),g:[],host:Q[n-8]});
 for(let t=n-7;t<=n;t++){const hc=V.slice(t-1),hp=hc.map((_,i)=>i===0),host=t===n-7?Q[n-7]:t===n-6?Q[n-6]:t<=n-2?L[n+1-t]:U[2];B.push({t,hc,hp,g:t>=n-1?V.slice(0,3):[],host});}
 return B;}
function D648WindIn(n,L,R,Q,loan,put){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),mc=(cs,ps,z)=>{const m=new Map();for(let i=0;i<cs.length;i++){if(m.has(cs[i])&&m.get(cs[i])!==ps[i])return [];m.set(cs[i],ps[i]);}const k=[...m.keys()];return mcN(k,k.map(w=>m.get(w)),z,loan.filter(w=>w!==z&&!m.has(w)));};
 const lo=V.slice(n-8),B=[[lo,lo.map(()=>false),Q[n-8]]];
 for(let t=n-7;t<=n-2;t++){const hc=V.slice(t-1);B.push([hc,hc.map((_,i)=>i===0),t===n-7?Q[n-7]:t===n-6?Q[n-6]:Q[n-2]]);}
 const v8=[V[0],V[1],V[2]],f=[false,false,false],cubes=[[[...v8,V[n-1],L[0]],[...f,false,true]],[[...v8,V[n-1],L[0],L[1]],[...f,false,false,true]]];
 const T=[V[n-1],L[0],L[1]],tp=[false,false,false];
 for(const [hb,hp,h] of B){
  for(const [cs,ps] of cubes){for(const w of [Q[2],Q[1],U[1]])put(mc([...hb,...cs,w],[...hp,...ps,true],U[2]));
   put(mc([...hb,...cs,h],[...hp,...ps,true],U[2]));put(mc([...hb,...cs,U[2]],[...hp,...ps,true],h));}
  put(mc([...hb,...T,h],[...hp,...tp,true],Q[n-1]));put(mc([...hb,...T,Q[n-1]],[...hp,...tp,true],h));
 }
}
function D648Tp(n,L,Q){return {lo:n-2,hi:n-2,rhi:n-3,rest:t=>t<=n-8?Q[n-8]:t===n-7?Q[n-7]:t===n-6?Q[n-6]:L[n+1-t]};}
function D648RotStep(word,sh,c){const n=word.length,a=[];for(const [i,k] of rotleft(n,(n+sh)%n))a.push(...fr(c,word[i],word[k]));return a;}
function D648Rot(word,dir,S,skip,sub){let a=[];for(let j=0;j<S.length;j++){const c=j===skip?sub:S[j];if(c===null)continue;a=a.concat(D648RotStep(word,dir*(1<<j),c));}return a;}
function D648C2Or(M,dst,C){const n=M.length,o=[];for(let sh=4;sh<n;sh+=4){const w=M.slice(n-sh);o.push(...mcN(w,w.map(()=>false),dst,C));}return o;}
function D648Gt(s,i,e,dirty,fj,fv,xw,xv){let g=[];for(let j=0;j<s.length;j++)if(!(i>>j&1)){
 let C=[s[j],...s.slice(j+1)],B=[true,...s.slice(j+1).map((_,b)=>!!(i>>(b+j+1)&1))];const k=C.indexOf(s[fj]);
 if(k>=0){if(B[k]!==!!fv)continue;C=C.filter((_,x)=>x!==k);B=B.filter((_,x)=>x!==k);}
 C.push(xw);B.push(xv);g=g.concat(negate(C,MCX(C,e,dirty),B));}return g;}
function D648AlphaIter(t,n,v,J,L,e,gap,cls,put,body){
 if(t>=n-2&&t<n){put(cls);put([[e,J[n-8],v[t]],[e,v[t],J[n-8]]]);body();put([[e,v[t],gap],[e,gap,v[t]]]);put([...cls].reverse());return;}
 if(t===n){const X=J[n-8],h=v[n-1];
  put([[h,X,e],[e,X]]);body();put([[e,gap],[h,gap,e]]);
  put([[gap],[h,gap,e],[gap]]);body();put([[gap],[h,gap,e],[gap]]);return;}
 put(cls);body();put([...cls].reverse());
}
`;
module.exports=function(s){
 const on=parts();
 const one=(a,b)=>{const k=s.split(a).length-1;if(k!==1)throw Error('d648 anchor x'+k+': '+a.slice(0,70));s=s.replace(a,()=>b);};
 if(on('c2a')){
  one('loan,false,sink);put(rev(ss));','loan,false,sink);put(rev(ss).filter(r=>!r.includes(S[2])));D648RouteIn(n,L,R,Q,loan,put);');
  one(' put(cls);\n if(t===n-1)put(',' const __body=()=>{\n if(t===n-1)put(');
  one('put(D2F.plus(m,a,null,gap));};const cond=()=>put([[sign],[e,sign,gap],[sign]]);neg();cond();neg();cond();put([...cls].reverse());',
      'put(D2F.plus(m,a,null,gap));};const cond=()=>put([[sign],[e,sign,gap],[sign]]);neg();cond();neg();cond();};D648AlphaIter(t,n,v,J,L,e,gap,cls,put,__body);');
  one('put(cls);put(park);if(t===2)put([[e,J[0]]]);','put(cls);if(t===n-3)put([[e,J[n-8],v[t]],[e,v[t],J[n-8]]]);put(park);if(t===2)put([[e,J[0]]]);');
  one('neg();cond();neg();cond();put(park.slice().reverse());put([...cls].reverse());','neg();cond();neg();cond();put(park.slice().reverse());if(t===n-3)put([[e,v[t],gap],[e,gap,v[t]]]);put([...cls].reverse());');
  if(on('c2g')){
   one('function Gtop(n,L,VR,J,ws,loan,put,before=null,after=null){','function Gtop(n,L,VR,J,ws,loan,put,before=null,after=null,tp=null){');
   one('put(cls);if(before)put(before(t));put([[ctl,L[size]]]);','const __b=()=>{if(before)put(before(t));put([[ctl,L[size]]]);');
   one('}if(after)put(after(t));put([...cls].reverse());','}if(after)put(after(t));};if(tp&&tp.rest&&t<=tp.rhi){const h=tp.rest(t),w=v[t+2];put(cls);put([[ctl,h,w],[ctl,w,h]]);__b();put([[ctl,w,h],[ctl,h,w]]);put([...cls].reverse());}else if(tp&&t>=tp.lo&&t<=tp.hi){const gp=L[n+1-t],hc=v.slice(t-1),ps=hc.map((_,i)=>i===0),c1=mcN([...hc,gp],[...ps,true],ctl,loan),c0=mcN([...hc,gp],[...ps,false],ctl,loan);put(c1);put([[ctl,gp]]);__b();put([[ctl,gp]]);put([...c1].reverse());put(c0);__b();put([...c0].reverse());}else{put(cls);__b();put([...cls].reverse());}');
   one('Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);','D648GtopIn(n,L,R,Q,loan,put);Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter,D648Tp(n,L,Q));'+(on('c2gT')&&!on('c2ca')?'D648GtopOutT(n,L,R,Q,S[2],loan,put);':''));
  }
  if(on('c2ca')){
   one('const logic=(cs,pol,z,markIndex=-1)=>{\n if(!cs.includes(c4)','const logic0=(cs,pol,z,markIndex=-1)=>{\n if(!cs.includes(c4)');
   one('// Before mask, U3 hosts count3 on high classes.',`const S2v=S[2],B2=D648Buckets(n,L,Q,V,U),D648UP=${on('c2up')?'true':'false'};
const logic=(cs,pol,z,markIndex=-1)=>{
 if((rev&&!D648UP)||(!cs.includes(S2v)&&z!==S2v))return logic0(cs,pol,z,markIndex);
 const rows=[];
 for(const B of B2){
  if(markIndex>=0&&B.t>n-8&&markIndex>=n-B.t)continue;
  const gp=B.g.map(()=>false);
  if(z===S2v){rows.push(...logic0([...B.hc,...B.g,...cs],[...B.hp,...gp,...pol],B.host,markIndex));continue;}
  const ix=cs.indexOf(S2v),rest=cs.filter((_,i)=>i!==ix),rp=pol.filter((_,i)=>i!==ix);
  if(!pol[ix])rows.push(...logic0([...B.hc,...rest],[...B.hp,...rp],z,markIndex));
  rows.push(...logic0([...B.hc,...B.g,...rest,B.host],[...B.hp,...gp,...rp,true],z,markIndex));
 }
 return rows;
};
function mask2(){for(const B of B2)if(!B.g.length)put(raw([...B.hc,D,B.host],[...B.hp,false,true],U[2]));}
function gather2G(){const g=[];for(const B of B2){const pr=raw([...B.hc,...B.g],[...B.hp,...B.g.map(()=>false)],e);g.push(...pr);
  if(!B.g.length)g.push(...fr(e,B.host,S[0]));
  else{g.push([e,U[2],S[0]],[e,S[0],U[2]],[e,Q[1],U[2]],[e,U[1],U[2]],[e,Q[2],U[2]]);g.push(...raw([e,D,S[1]],[true,false,true],U[2]));g.push(...raw([e,D,S[0]],[true,false,true],U[2]));}
  g.push(...[...pr].reverse());}return g;}
function gather2(){put(gather2G());}
function scatter2(){put(gather2G().reverse());}
// Before mask, U3 hosts count3 on high classes.`);
   one('function mask(){for(let j=0;j<bits;j++)if(j===3)mask3();else put(logic([D,S[j]],[false,true],U[j]));}','function mask(){for(let j=0;j<bits;j++)if(j===3)mask3();else if(j===2&&(!rev||D648UP))mask2();else put(logic([D,S[j]],[false,true],U[j]));}');
   one("sink('hmr',[S[0],off+4]);gather3(S[0],false);sink('hmr',[S[0],off+3]);","sink('hmr',[S[0],off+4]);gather3(S[0],false);sink('hmr',[S[0],off+3]);gather2();sink('hmr',[S[0],off+2]);");
   one("for(let j=1;j<bits;j++)if(j!==3&&j!==4)sink('hmr',[S[j],off+j]);","for(let j=1;j<bits;j++)if(j!==3&&j!==4&&j!==2)sink('hmr',[S[j],off+j]);");
  }
  if(on('c2up')){
   one("extractBit(4,S[0]);sink('phase',[S[0],off+4]);\n extractBit(1,S[1]);sink('phase',[S[1],off+1]);extractBit(3,S[2]);sink('phase',[S[2],off+3]);gather3(S[2],true);\n for(let j=2;j<bits;j++)if(j!==3&&j!==4){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}",
       "extractBit(1,S[1]);sink('phase',[S[1],off+1]);extractBit(2,S[0]);sink('phase',[S[0],off+2]);scatter2();\n extractBit(3,S[0]);sink('phase',[S[0],off+3]);gather3(S[0],true);extractBit(4,S[0]);sink('phase',[S[0],off+4]);\n for(let j=5;j<bits;j++){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}");
   if(on('c2upT'))one('mask();mark();bias(true);delta();','mask();mark();bias(true);delta();D648GtopOutT(n,L,R,Q,S[2],loan,put);');
  }
  if(on('c2n')){
   one('const norm=normal(M,[],S,C,false)','const norm=normal(M,[],S.map((w,i)=>i===2?Q[2]:w),C,false)');
   one('for(let j=0;j<bits-1;j++)ss.push(...[[S[j],Q[j]],[Q[j],S[j]],[S[j],Q[j]]]);','for(let j=0;j<bits-1;j++)if(j!==2)ss.push(...[[S[j],Q[j]],[Q[j],S[j]],[S[j],Q[j]]]);');
  }
  if(on('c2t')){
   one('for(let j=0;j<S.length;j++){if(n===128&&off===7&&S.length===7&&j===3)continue;','for(let j=0;j<S.length;j++){if(n===128&&off===7&&S.length===7&&(j===3||j===2))continue;');
   one('S[bits-2]=sig;S[bits-3]=e;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);','S[bits-2]=sig;S[bits-3]=e;parkOuter(n,M,rm,Q,S,p,bits,L[n],loan,sink,true);{const g=mcN([...M.slice(0,4),Q[2]],[false,false,false,false,true],t,C);put([[rm[2],Q[2]]]);put(g);sink(\'phase\',[t,bits+2]);put([...g].reverse());put([[rm[2],Q[2]]]);}');
   one("put([[t,Q[3]]]);}","put([[t,Q[3]]]);}{const g=mcN([...M.slice(0,4),Q[2]],[false,false,false,false,true],e,C);put([[rm[2],Q[2]]]);put(g);put([[rm[2],Q[2]]]);put(D648RotStep(M,-4,e));put([[e,Q[2]],[M[n-1]],[M[n-1],e],[M[n-1]]]);}");
   one("for(let j=0;j<n-1;j++){const q=gt(S,j,e,null,C);put(q);put(D2F.dirtyDigit(M.slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]));put(rev(q));}",
       "{const Nv=[M[n-4],M[n-3],M[n-2],M[n-1],...M.slice(0,n-4)];for(let j=0;j<n-1;j++)for(const b of [0,1]){const q=D648Gt(S,j,e,C,2,b,M[n-1],b===0);put(q);put(D2F.dirtyDigit((b?Nv:M).slice(j+1),Q.slice(0,n-1-j),Q[n-1-j],e,C[0]));put(rev(q));}}");
   one("put(rot(M,-1));","put(D648Rot(M,-1,S,2,null));");
   s=s.split("const q=gt(S,n-i-1,e,null,C);").join("const q=mcN(M.slice(i),M.slice(i).map(()=>false),e,C);");
   one("const rt=rot(rm,-1);put(rt);","const rt=[...D648C2Or(M,e,C),...D648Rot(rm,-1,S,2,e),...D648C2Or(M,e,C)];put(rt);");
   one("put(rot(M,1));put(rev(normal(M,[],S,C,false)));","put(D648C2Or(M,e,C));put(D648Rot(M,1,S,2,e));put(rev(normal(M,[],S.map((w,i)=>i===2?e:w),C,false)));");
  }
  if(on('c2u2')){
   one('Gtop(n,L,R,Q,[e,t],loan,put,reverseBefore,reverseAfter);','Gtop(n,L,R,Q,[e,t],loan,put,reverseBefore,reverseAfter,D648Tp(n,L,Q));');
   one("D14BeforeWinding(n,L,R,Q,loan,sink);D2Winding(n,L,R,Q,loan,sink);tap('winding');","D648WindIn(n,L,R,Q,loan,put);D14BeforeWinding(n,L,R,Q,loan,sink);D2Winding(n,L,R,Q,loan,sink);tap('winding');");
  }
  if(on('c2aT'))one('if(!rev){Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);','if(!rev){D648RouteOutA(n,L,R,Q,S[2],loan,put);Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);');
  s+=HELP;
 }
 return s;
};
