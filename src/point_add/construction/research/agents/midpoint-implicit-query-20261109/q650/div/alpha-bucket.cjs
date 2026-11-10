'use strict';
// q650 divide: bucketed alpha (op saving, width unchanged).
//
// The 651 alpha runs one literal class body per V-height class t (outerloadJ(t,t), ~11.7K*t ops each).
// Its result alpha = lambda*U mod V (then the sign-conditioned m-alpha) is linear in (U,V), so for d=T-t
// the class-T body applied to (U*2^d, V*2^d) yields alpha*2^d. For a bucket of classes [lo,T]:
//   sweep: per class c in [lo,T-1], under its height selector (e=R[1]):
//          park g's bits u[c+1..T] in Q[T..T+d-1] (zero: alpha's slice for these lanes ends below T),
//          and write d=T-c into the shift register D=Q[T+W..] (W=T-lo).
//   barrel: rotate the first T wires of u and v left by D (cyclic; the vacated low wires receive
//          u[c..T-1]=gap+parked zeros and V's zero high bits), so U'=U*2^d, V'=V*2^d, height T, gap u[T]=0.
//   body:  the unchanged literal class-T body (its own selector flagHeight(v,T) now selects every bucket lane).
//   unwind: rotate Q[0..T-1] right by D (alpha'=alpha*2^d has d low zeros), un-rotate u,v, undo the sweep.
// Buckets run in ascending class order (as the literal loop does): when bucket [lo,T] runs, lower lanes'
// alpha lies below lo<=T and higher lanes still have Q=0, so G and D are zero for every lane outside the bucket.
// V is unchanged while the selectors are computed and uncomputed (sweep runs before/after the barrels).
// Inactive lanes: sweep moves and D writes are selector-controlled, barrels are D-controlled (D=0),
// the body is inactive (height != T) and its uncontrolled parts are inverse pairs.
// Classes 1,2 and t>=125 keep their original bodies.
module.exports=function(d){
  const rep=(a,b)=>{if(d.split(a).length!==2)throw Error('alpha-bucket anchor x'+(d.split(a).length-1)+': '+a.slice(0,80));d=d.replace(a,()=>b);};
  const head="function D2Alpha(n,terms,L,R,J,sign,loan,ws,sink){const e=ws[0],v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g);let added=0;";
  const loop=" for(let t=2;t<=n;t++){const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=D2F.flagHeight(v,t,e,loan),utop=u[t-1];";
  const bucket=[
   "const QTOP=+(process.env.Q650_ABTOP||124),BK=[];if(process.env.Q650_ABUCKET!=='0'){let T=QTOP;while(T>=3){let w=1;for(let k=1;k<=T-2;k++){const W=k-1,nb=Math.ceil(Math.log2(W+1));if(T+W+nb-1<=QTOP)w=k;}if(w>1)BK.push([T-w+1,T]);T=T-w;}}if(process.env.Q650_ABONLY){const [a,b]=process.env.Q650_ABONLY.split(",").map(Number);BK.splice(0,BK.length,...BK.filter(x=>x[0]===a&&x[1]===b));}",
   "const covered=new Set();for(const [lo,T] of BK)for(let c=lo;c<=T;c++)covered.add(c);",
   "const rotL=(list,k,ctl)=>{const g=[];if(!(k%list.length))return g;for(const [i,j] of D2F.rotleft(list.length,k%list.length))g.push(...D2F.fr(ctl,list[i],list[j]));return g;};",
   "BK.sort((x,y)=>x[0]-y[0]);for(const [lo,T] of BK){const W=T-lo,nb=Math.ceil(Math.log2(W+1)),G=J.slice(T,T+W),Dw=J.slice(T+W,T+W+nb);if(T+W+nb-1>=n-2||G.length!==W||Dw.length!==nb)throw Error('alpha bucket room '+[lo,T]);",
   " const sweep=inv=>{for(let c=lo;c<T;c++){const s=D2F.flagHeight(v,c,e,loan),b=[];for(let i=0;i<T-c;i++)b.push(...D2F.fr(e,u[c+1+i],G[i]));for(let k=0;k<nb;k++)if(((T-c)>>k)&1)b.push([e,Dw[k]]);put(s);put(inv?[...b].reverse():b);put([...s].reverse());}};",
   " const barrel=list=>{const g=[];for(let k=0;k<nb;k++)g.push(...rotL(list,1<<k,Dw[k]));return g;};",
   " const bu=barrel(u.slice(0,T)),bv=barrel(v.slice(0,T)),bq=barrel(J.slice(0,T));",
   " sweep(false);put(bu);put(bv);outerloadJ(n,terms,L,R,J,sign,loan,ws,sink,T,T);put([...bq].reverse());put([...bv].reverse());put([...bu].reverse());sweep(true);}"
  ].join('\n');
  if(d.split(head).length!==2)throw Error('alpha-bucket head');
  rep(loop, bucket+"\n"+loop+"if(covered.has(t))continue;");
  return d;
};
