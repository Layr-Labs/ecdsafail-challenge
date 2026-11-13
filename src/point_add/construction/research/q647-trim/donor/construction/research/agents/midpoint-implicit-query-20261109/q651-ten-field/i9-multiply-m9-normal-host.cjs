'use strict';
// Six count sites plus encoded last shift on modulus top. Unintegrated component.
function hostedNormal(T,Q,S,dirty,{normal,fr},qmove=true){
 const n=T.length,k=Math.log2(n);if(S.length!==k-1||n<2||k%1)throw Error('power-of-two width');
 const virtual=[-999,...S];
 // normal's j>=1 blocks do not read virtual[0]. Build the same high steps directly.
 const g=[];const mcx=(c,t)=>{if(c.length<=2)return [[...c,t]];const v=dirty.slice(0,c.length-2);if(v.length!==c.length-2)throw Error('loans');const A=[c[0],c[1],v[0]],M=[];for(let j=2;j<c.length-1;j++)M.push([c[j],v[j-2],v[j-1]]);const Z=[c.at(-1),v.at(-1),t],R=M.slice().reverse();return [A,...M,Z,...R,A,...M,Z,...R];};
 const rot=(w,d,ctl)=>{const seen=new Set();for(let i=0;i<w.length;i++){if(seen.has(i))continue;seen.add(i);for(let j=(i+d)%w.length;j!==i;j=(j+d)%w.length){g.push(...fr(ctl,w[i],w[j]));seen.add(j);}}};
 for(let j=k-1;j>=1;j--){const d=1<<j,c=T.slice(n-d),h=S[j-1];g.push(...c.map(q=>[q]),...mcx(c,h),...c.map(q=>[q]));rot(T,d,h);if(qmove)rot(Q,d,h);}
 const top=T.at(-1);g.push([top]);if(qmove)rot(Q,1,top);rot(T.slice(0,-1),1,top);g.push([top,T[0]]);
 return g;
}
module.exports={hostedNormal};

