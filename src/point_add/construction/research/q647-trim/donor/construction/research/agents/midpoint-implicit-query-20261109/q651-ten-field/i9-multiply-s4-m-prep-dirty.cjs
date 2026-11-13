'use strict';
const base=require('./i9-multiply-s4-m-lift-candidate.cjs');
const definition=`
// Dirty-controlled interval reflections. A,B canonical, M normalized virtual-top-one.
function m6sub(M,A,B,h){
 const n=B.length,loM=M.slice(0,-1),loB=B.slice(0,-1),top=B.at(-1);
 const lessA=lt(A,B,h);
 const lessM=[[h],[top,h],...r36lt(loM,loB,h,top)];
 const refl=(withM)=>[...B.map(z=>[h,z]),...plus(A,B,null,h),...(withM?r36plus(M,B,null,h):[])];
 const prefix=refl(false),upper=refl(true),pa=lessA,pu=[...lessA,...lessM];
 // U; toggle(predicate); U; toggle(predicate) = reflection restricted to invariant interval.
 const first=[...prefix,...pa,...prefix,...pa];
 const second=[...upper,...pu,...upper,...pu];
 const last=[...B.map(z=>[z]),...r36plus(M,B,null)];
 return [...first,...second,...last];
}
`;
function f(s){s=base.f(s);const a='md=[...relay,...r36madd([...T.slice(0,-1),1001],R.slice(0,128),H,sc),...relay]';
 if(s.split(a).length!==2)throw Error('dirty MD anchor');
 s=s.replace(a,'md=m6sub([...T.slice(0,-1),1001],R.slice(0,128),H,sc).reverse()');
 return definition+s;
}
module.exports={source:base.source,f,definition};
