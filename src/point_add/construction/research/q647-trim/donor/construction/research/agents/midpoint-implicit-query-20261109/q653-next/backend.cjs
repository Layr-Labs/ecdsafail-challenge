'use strict';
const {f:oldF,d:oldD,replace,dirtyDigit,dirtyMdg,dirtyBlock,lowValuationSweep,plusOneMod,VirtualCanonical,SectorReduced,SectorCanonical,emitWalk}=require('./parts.cjs');
let f=replace(oldF,'idx=vec(4,649)','idx=vec(3,649)');
f=replace(f,'if(back)for(let i=0;i<15;i++)run(inc,true);const loc=[5,10,32,256]','if(back)for(let i=0;i<47;i++)run(inc,true);const loc=[10,32,256]');
f=replace(f,'idx,[3,0],[2,1]),back);if(!back)for(let i=0;i<15;i++)run(inc);','idx,[2],[1,0]),back);if(!back)for(let i=0;i<47;i++)run(inc);');
f=replace(f,'shprod(128,T,H,C,L,vec(4,649))','shprod(128,T,H,C,L,[649,650,651,655])');
f=replace(f,'m[W.fire]=m[W.R[n+1]];return m;','m[W.fire]=m[W.R[n+1]];m[W.sign]=m[W.tag[6]];return m;');
f=replace(f,'if(map){for(let i=0;i<G.g.length;i++){const t=G.g[i],a=t>>>20&1023,b=t>>>10&1023;G.g[i]=((a===1023?1023:map[a])<<20)|((b===1023?1023:map[b])<<10)|map[t&1023];}}',
  'if(map){const tr=q=>q===1023?1023:map[q===G.tag[6]?block.topPort:q];for(let i=0;i<G.g.length;i++){const x=G.g[i],a=tr(x>>>20&1023),b=tr(x>>>10&1023),t=tr(x&1023);if(a===t||b===t||a===b&&a!==1023||t===undefined||a===undefined||b===undefined)throw Error("aliased public unit");G.g[i]=(a<<20)|(b<<10)|t;}}');
const multiply=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')({exports:{}},VirtualCanonical,dirtyDigit,lowValuationSweep,plusOneMod);

let d=replace(oldD,'sig=act+5,e=act+6,t=lp[0]','sig=act+5,e=lp[1],t=lp[0]');
d=replace(d,'ws={sign:sig,tag:S,fire:e,tst:S[6],aux:L[n+1]}','ws={sign:sig,tag:S,fire:S[5],tst:S[6],aux:L[n+1]}');
d=replace(d,'const wi={sign:L[1],tag:S,fire:e,tst:S[5],aux:S[6]};emitWalk(new SectorCanonical(n),','const wi={sign:L[1],tag:S,fire:S[4],tst:S[5],aux:S[6]};emitWalk(new SectorCanonical(n,5),');
// U<V/2 unless V=2. Both positive-modulus shift windows have a zero top
// quotient after NR, including the second window 2^(k+1)U+dirty.
d=replace(d,'run(mdg(v,u,out,tmp,en,sp),neg);continue;','run(mdg(v,u,out,pad,en,sp),neg);continue;');
d=replace(d,'run(mdg(v,w.slice(0,n),out,tmp,en,sp),sub);','run(mdg(v,w.slice(0,n),out,w.at(-1),en,sp),sub);');
const start=d.indexOf('function outerloadJ('),end=d.indexOf('\n',start);
d=d.slice(0,start)+`function outerloadJ(n,terms,L,R,J,sign,loan,ws,sink){
 const e=ws[0],v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]);
 for(let t=2;t<=n;t++){
  const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=flagHeight(v,t,e,loan),put=g=>sink('nct',g);
  put(cls);if(t===2)put([[e,J[0]]]);else pModShear(terms,null,m,u.slice(0,t),a,t,loan,gap,null,null,e,sink);
  const neg=()=>{for(const q of a)put([[gap,q]]);put(incReg(a,loan,gap));put(plus(m,a,null,gap));};
  const cond=()=>put([[sign],[e,sign,gap],[sign]]);neg();cond();neg();cond();put([...cls].reverse());
 }
}`+d.slice(end);
const gs=d.indexOf('function Gtop('),ge=d.indexOf('\n',gs);
d=d.slice(0,gs)+`function Gtop(n,L,VR,J,ws,loan,put){const ctl=ws[0],v=Array.from({length:n},(_,i)=>VR[n+1-i]);
 for(let t=1;t<=n;t++){const size=n-t,B=L.slice(0,size),cls=flagHeight(v,t,ctl,loan);put(cls);put([[ctl,L[size]]]);
  if(size){const z=[...J.slice(t),...v.slice(0,t)],g=where(NR(size,t),[...B,...z]),hi=z.at(-1);
   put([...g].reverse());put([[ctl,hi,L[size]]]);put(mcN([ctl,hi,...B],[true,true,...B.map(()=>false)],L[size],loan));put(g);
  }put([...cls].reverse());
 }
}`+d.slice(ge);
d=replace(d,'const [e,t]=ws,D=t,put=g=>','const e=ws[0],D=Q[n-1],t=D,put=g=>');
d=replace(d,'if(!rev){Gtop(n,L,R,Q,[e,t],loan,put);delta();','if(!rev){Gtop(n,L,R,Q,[e,t],loan,put);move();delta();');
d=replace(d,'mask();mark();bias(true);delta();Gtop(n,L,R,Q,[e,t],loan,put);','mask();mark();bias(true);delta();move();Gtop(n,L,R,Q,[e,t],loan,put);');
const ms=d.indexOf('function mulG('),me=d.indexOf('\n',ms);
d=d.slice(0,ms)+`function mulG(n,L,R,J,x,ws,loan,sink){const sel=R[1],v=Array.from({length:n},(_,i)=>R[n+1-i]);
 for(let t=1;t<n;t++){const size=n+1-t,w=[...J,L[size]],cls=flagHeight(v,t,sel,loan),rot=[];
  for(const [i,j]of rotleft(n+1,size))rot.push(...fr(sel,w[i],w[j]));sink('nct',cls);sink('nct',rot);
  sink('nct',dirtyBlock(size,t,L.slice(0,size),w,sel).reverse());sink('nct',[...cls].reverse());
 }
}`+d.slice(me);
const divide=Function('module','dirtyMdg','dirtyBlock','emitWalk','Reduced','SectorCanonical',d+'\nreturn inverseField;')({exports:{}},dirtyMdg,dirtyBlock,emitWalk,SectorReduced,SectorCanonical);
function mapped(sink,back){
  const free=back?[648,652,654,655,656]:[648,652,653,654,656],move=back?653:655;
  const ids=new Int16Array(1024);ids.fill(-1);ids[1023]=1023;
  for(let i=0;i<657;i++)if(!free.includes(i))ids[i]=i===move?652:i;
  const port=q=>{if(ids[q]<0||ids[q]===undefined)throw Error('extra field site '+[back,q]);return ids[q];};
  return(kind,data)=>{if(kind==='packed'){const g=new Uint32Array(data.length);for(let i=0;i<data.length;i++){const x=data[i];g[i]=(port(x>>>20&1023)<<20)|(port(x>>>10&1023)<<10)|port(x&1023);}sink(kind,g);}
    else if(kind==='nct')sink(kind,data.map(r=>r.map(port)));else sink(kind,data.map((q,i)=>i===data.length-1?q:port(q)));};
}
function emitMultiplySparse(sink){multiply(mapped(sink,false));}
function emitDivideSparse(sink){divide(128,null,null,mapped(sink,true));}
module.exports={emitMultiplySparse,emitDivideSparse};
