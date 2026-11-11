'use strict';
function sourceDouble(n,M,H,en,q,tmp,p){const rows=[];for(let j=0;j<n;j++)rows.push(...p.fr(en,q,H[j]));rows.push(...p.digit(n,M,H,q,en,tmp));return rows;}
function powerFactory(p,raw,lower,check){
 const T=Array.from({length:128},(_,i)=>i),H=T.map(i=>384+i),S=[640,641],D=Array.from({length:256},(_,i)=>128+i),en=642,q=643;
 const emit=(cs,z,neg=[])=>{for(const w of neg)raw([w]);for(const r of p.MCX(cs,z,D.filter(w=>w!==z&&!cs.includes(w))))raw(r);for(const w of neg.slice().reverse())raw([w]);};
 const cls=(c,cs,z,neg=[])=>emit([...S,...cs],z,[...S.filter((w,j)=>!(c>>j&1)),...neg]);
 const greater=(bits,value,c,z)=>{for(let j=0;j<bits.length;j++)if(!(value>>j&1))cls(c,[bits[j],...bits.slice(j+1)],z,bits.slice(j+1).filter((w,k)=>!(value>>(j+1+k)&1)));};
 const guard=i=>{if(i===0)cls(1,[],en);else if(i===1)cls(1,[T[0]],en);if(i<3)cls(2,[],en);else if(i<6)greater(T.slice(0,2),i-3,2,en);if(i<7)cls(3,[],en);else greater(T.slice(0,7),i,3,en);};
 const erase=()=>{for(let j=3;j<7;j++)emit([640,641,T[j]],639+j);};
 const P=(1n<<256n)-(1n<<32n)-977n,mask=(1n<<128n)-1n;let kappa=1n;for(let k=1;k<128;k*=2)kappa=kappa*(2n-P*kappa)&mask;
 const iteration=i=>{
  guard(i);
  for(const r of sourceDouble(128,T,H,643,644,645,p))lower(r);
  check();
  const classes=i>=6?[[3,7,false]]:[[1,1,true],[2,2,true],[3,7,true]].filter(([c])=>c===1?i<2:c===2?i<6:true);
  for(const [c,d,explicit]of classes)for(let v=Math.max(i+1,d);v<128;v++){
   const low=T.slice(d,v),controls=[en,...low,T[v],H[v]],neg=[...low];if(kappa>>BigInt(v-i-1)&1n)neg.push(H[v]);
   if(explicit)cls(c,controls,q,neg);else emit(controls,q,neg);
  }
  guard(i);
 };
 return{erase,iteration};
}
module.exports={sourceDouble,powerFactory};
