'use strict';
// r35 divide rewrite (ours): re-host count bit 6 ("c6") so the divide stage never needs logical helper 647.
//   norm/qsplit/preF/complete : c6 on rp[0] (651), free outside the walks
//   forward outer walk        : c6 in Q[n-1] (the outer walk never touches Q)
//   alpha                     : class<n keeps it in Q[n-1] (untouched there); class n folds it into L[0] (g=1 => L[0]=1)
//   ipark/unpark              : count register = [S0..S5, Q[n-2]]; sweeps P1/P2/P3/Pw move c6 and the displaced J bits
//   winding                   : class<n c6 on utop (L[n+2-t]); class n as not(L[0])
//   restore                   : unhost to S0, Q[6]^=c6, hmr record 13; parkOuter(rev) recomputes c6 onto rp[0]
// Walk tags shrink to S0..S5 (outer Reduced(n,5), inner SectorCanonical(n,4)).
module.exports=function(d){
  const rep=(a,b,k=1)=>{if(d.split(a).length!==k+1)throw Error('div10 anchor x'+(d.split(a).length-1)+': '+a.slice(0,80));d=d.split(a).join(b);};
  rep("Htop=base,S=vec(bits,base+1),act=base+bits+1,lp=[act+1,act+2],rp=[act+3,act+4],sig=act+5,",
      "Htop=base,act=base+bits+1,lp=[act+1,act+2],rp=[act+3,act+4],S=[...vec(bits-1,base+1),rp[0]],T6=S.slice(0,bits-1),sig=act+5,");
  rep("ws={sign:sig,tag:S,fire:S[5],tst:S[6],aux:L[n+1]}","ws={sign:sig,tag:[...T6,-1],fire:S[4],tst:S[5],aux:L[n+1]}");
  rep("const ss=[];for(let j=0;j<bits;j++)ss.push(...[[S[j],Q[j]],[Q[j],S[j]],[S[j],Q[j]]]);put(ss);",
      "const ss=[];for(let j=0;j<bits-1;j++)ss.push(...[[S[j],Q[j]],[Q[j],S[j]],[S[j],Q[j]]]);put(ss);put([[S[bits-1],Q[n-1]],[Q[n-1],S[bits-1]]]);");
  rep("new Reduced(n)","new Reduced(n,5)",2);
  rep("put(cls);if(t===2)put([[e,J[0]]]);","put(cls);if(t===n)put([[e,J[n-1],L[0]],[L[0]],[e,L[0],J[n-1]],[L[0]]]);if(t===2)put([[e,J[0]]]);");
  // parkInner: replace the whole function
  const a=d.indexOf('function parkInner('),b=d.indexOf('function inverseField(');if(a<0||b<a)throw Error('div10 parkInner span');
  const old=d.slice(a,b);
  const grab=(name)=>{const i=old.indexOf('function '+name+'(');if(i<0)throw Error('div10 grab '+name);const nxt=old.indexOf('\nfunction ',i+1),j=nxt<0?old.indexOf('\nif(!rev)',i):nxt;if(j<0)throw Error('div10 grab end '+name);return old.slice(i,j);};
  const parts=['delta','bias','mark','mask','extract'].map(grab).join('\n');
  const head="function parkInner(n,L,R,Q,S0,sg,p,off,ws,loan,sink,rev=false){const S=[...S0,Q[n-2]],X=Q[n-2],e=ws[0],D=Q[n-1],t=D,put=g=>sink('nct',g),V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),bits=S.length,kp=shortinv(p,1n<<BigInt(bits));shseq.borrow=loan;";
  const tail=[
   "const cl=(c,g)=>{const a=flagHeight(V,c,e,loan);put(a);put(g);put([...a].reverse());},gapw=c=>L[n+1-c],utop=c=>L[n+2-c],slot=c=>L[n-c];",
   "function P1(){for(let c=1;c<n;c++)cl(c,fr(e,D,gapw(c)));}",
   "function P2(inv){for(let c=1;c<=n;c++){const g=c<n?[fr(e,X,utop(c)),fr(e,X,gapw(c))]:[fr(e,D,L[1]),fr(e,X,L[2]),fr(e,X,L[0])];if(inv)g.reverse();cl(c,g.flat());}}",
   "function P3(inv){for(let c=1;c<=n;c++){const g=[fr(e,X,utop(c)),fr(e,D,c<n?slot(c):L[1])];if(inv)g.reverse();cl(c,g.flat());}}",
   "function Pw(){for(let c=1;c<n;c++)cl(c,fr(e,gapw(c),utop(c)));}",
   "if(!rev){P1();Gtop(n,L,R,Q,[e,t],loan,put);P2(false);delta();bias(false);mark();mask();for(let j=0;j<bits;j++)sink('hmr',[S[j],off+j]);P3(false);routeZeros(n,L,R,e,loan,put);}",
   "else{routeZeros(n,L,R,e,loan,put,true);P3(true);extract();for(let j=0;j<bits;j++)sink('phase',[S[j],off+j]);mask();mark();bias(true);delta();P2(true);Gtop(n,L,R,Q,[e,t],loan,put);Pw();}}"].join('\n');
  if(!/^function parkInner\(n,L,R,Q,S,sg,p,off,ws,loan,sink,rev=false\)\{const e=ws\[0\],D=Q\[n-1\],t=D,/.test(old))throw Error('div10 parkInner head changed');
  d=d.slice(0,a)+head+parts+'\n'+tail+'\n'+d.slice(b);
  rep("parkInner(n,L,R,Q,S,sig,","parkInner(n,L,R,Q,T6,sig,",2);
  rep("const wi={sign:L[1],tag:S,fire:S[4],tst:S[5],aux:S[6]};emitWalk(new SectorCanonical(n,5),",
      "const wi={sign:L[1],tag:[...T6,-1],fire:S[3],tst:S[4],aux:S[5]};emitWalk(new SectorCanonical(n,4),");
  rep("parkOuter(n,M,rm,Q,S,p,bits,R[1],loan,sink);",
      "parkOuter(n,M,rm,Q,T6,p,bits,R[1],loan,sink);{const cl=(c,g)=>{const a=flagHeight(vt,c,R[1],loan);put(a);put(g);put(rev(a));};for(let c=1;c<n;c++)cl(c,fr(R[1],T6[0],L[n+2-c]));cl(n,[[R[1],L[0]],...fr(R[1],T6[0],L[0]),[R[1],L[0]]]);put([[T6[0],Q[bits-1]]]);sink('hmr',[T6[0],2*bits-1]);}");
  return d;
};
