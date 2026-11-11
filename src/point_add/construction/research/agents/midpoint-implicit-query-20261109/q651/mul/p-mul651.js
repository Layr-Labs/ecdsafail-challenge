'use strict';
// Incremental [from,to] list AFTER q652/mul/p-mul652.js. Evict logical 651.
const A='const multiply=Function(';
const inner=(a,b)=>[A,'f=replace(f,'+JSON.stringify(a)+','+JSON.stringify(b)+');\n'+A];
const helpers=String.raw`
// Constant-one top addend, no physical wire for that bit. Borrow is value-independent.
function r36lt(A,B,h,e=null){const n=A.length,k=n-1,g=[],X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);
 const op=cs=>{if(e!==null)cs=[e,...cs];const used=new Set([...A,...B,h,...cs,127,651]);const loan=Array.from({length:640},(_,i)=>i).filter(q=>!used.has(q));g.push(...MCX(cs,h,loan));};
 for(const b of B)X(b);if(n===1){op([A[0],B[0]]);X(B[0]);return g;}
 for(let i=1;i<n;i++)CX(A[i],B[i]);op([A[k]]);for(let i=n-2;i>=1;i--)CX(A[i],A[i+1]);for(let i=0;i<n-1;i++)T(B[i],A[i],A[i+1]);op([B[k],A[k]]);
 for(let i=n-2;i>=0;i--)T(B[i],A[i],A[i+1]);for(let i=1;i<n-1;i++)CX(A[i],A[i+1]);for(let i=1;i<n;i++)CX(A[i],B[i]);for(const b of B)X(b);return g;}
function r36plus(A,B,H,e=null,t=null){if(A.at(-1)!==1001)return plus(A,B,H,e,t);
 const a=A.slice(0,-1),b=B.slice(0,-1),z=B.at(-1);if(!a.length)throw Error('r36 top width');
 if(H===null){const g=plus(a,b,null,e);g.push(...r36lt(a,b,z,e));g.push(e===null?[z]:[e,z]);return g;}
 if(e!==null)throw Error('r36 controlled top carry');
 return [[z,H],...plus(a,b,z),...r36lt(a,b,H,z),[z]];}
function r36digit(A,B,h){if(A.at(-1)!==1001)return digit(A.length,A,B,h);
 // Compare B >= (2^(n-1)+a): gate the lower comparison on B's top.
 const z=B.at(-1),a=A.slice(0,-1),b=B.slice(0,-1);
 return [[z,h],...r36lt(a,b,h,z),...r36plus(A,B,null,h).reverse()];}
function r36nr(n,k,map){const A=map.slice(0,n),D=map.slice(n),g=[];
 for(let j=k-1;j>=0;j--){const B=D.slice(j,j+n),h=D[j+n],old=j===k-1?null:D[j+n+1];const before=()=>{if(old!==null)g.push([old]);for(const u of [...B,h])g.push(old===null?[u]:[old,u]);if(old!==null)g.push([old]);};before();g.push(...r36plus(A,B,h));before();}
 const sign=D[n];g.push(...r36plus(A,D.slice(0,n),null,sign));for(const h of D.slice(n))g.push([h]);return g;}
function r36madd(M,A,B,h){return [...plus(A,B,h),...r36digit(M,B,h),...lt(A,B,h)];}
function r36prod(n,M0,X,C,R,P){const M=[...M0.slice(0,-1),1001],host=M0.at(-1),[xh,th]=P,t2=host,tmp=xh;
 const mm=r36plus(M,X,xh),um=[...mm].reverse(),D0=[...X,xh];let all=[[host]];
 for(let idx=0;idx<2;idx++){const si=R.slice(idx*n,idx*n+n),other=R.slice((1-idx)*n,(1-idx)*n+n),br=[...other.slice(0,n-1),th],raw=[...br,t2,...si],A=[...mm,...r36nr(n+1,n,[...D0,...raw]).reverse(),...um],B=r36nr(n,n+1,[...M,...raw]),result=raw.slice(0,n);
 function depo(Q,sub){const kk=idx*n,view=[...X.slice(0,kk),...Q],run=kk?r36nr(n,kk,[...M,...view]):[],rr=view.slice(0,n),mac=r36madd(M,rr,C,tmp);return [...run,...(sub?[...mac].reverse():mac),...[...run].reverse()];}
 all=all.concat(A,B,depo(result,false),[...B].reverse(),[...A].reverse(),depo(br,true));}
 return all.concat([[host]]);}
`;
module.exports=[
 ['class R35UnitWalk extends SectorCanonical{constructor(n){super(n,6);}}','class R35UnitWalk extends SectorCanonical{constructor(n){super(n,5);}}'],
 inner('m[W.fire]=651;','m[W.fire]=646;'),
 inner('tick(ctl,xs,ys,b){const h=this.helper;for(let j=0;j<xs.length;j++){this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);this.raw(ctl,xs[j],h);}}',
       'tick(ctl,xs,ys,b){for(let j=0;j<xs.length;j++){const h=this.y.find(q=>q!==ctl&&q!==xs[j]&&q!==ys[j]&&q!==b);if(h===undefined)throw Error("r36 tick loan");this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);}}'),
 inner('idx=vec(3,649),en=647,tmp=647;','idx=vec(2,649),en=647,tmp=647;'),
 inner('function shprod(n,M,X,C,R,P){',helpers+'\nfunction shprod(n,M,X,C,R,P){'),
 inner('shprod(128,T,H,C,L,[649,650,651])','r36prod(128,T,H,C,L,[649,650])'),
 // Match only multiply's forward arm: also works after the package's p-field652.js merge.
 [':[648,652,653,654,655,656],move=back?653:-1;',
  ':[648,651,652,653,654,655,656],move=back?653:-1;'],
];
