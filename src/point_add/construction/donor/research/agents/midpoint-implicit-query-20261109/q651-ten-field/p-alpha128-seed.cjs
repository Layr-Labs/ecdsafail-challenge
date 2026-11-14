'use strict';
// After D1 prefix. Exact alpha128 seed encoding prototype; reconnects to645.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('seed anchor '+a);s=s.replace(a,()=>b);};
 one('if(t===n)put(D2F.fr(e,J[n-3],5*n+5));','if(t===n)put(D2F.fr(e,J[n-3],J[2]));');
 const a=s.indexOf('function D2Alpha('),b=s.indexOf('\nfunction D2Winding(',a);let f=s.slice(a,b);
 const end='neg();cond();neg();cond();put([...cls].reverse());';
 if(f.split(end).length!==2)throw Error('alpha end');
 f=f.replace(end,`neg();cond();neg();cond();put([...cls].reverse());
 if(t===n){
  // Q = orientation(pU + 4*c4) mod V. On c4=1, V is divisible by 16.
  // For V divisible8 and U odd, sign=Q1 xor U1 and c4=Q2 xor U2 xor sign.
  const guard=[v[n-1],...v.slice(0,3)],pol=[true,false,false,false];
  for(const w of [J[2],u[2]])put(mcN([...guard,w],[...pol,true],sign,loan));
  const h=v[n-1],implicit=[...v.slice(0,-1),1001];
  const add4=[];
  add4.push(...mcN([e,...J.slice(2)],[true,...J.slice(2).map(()=>true)],h,loan));
  add4.push(...incReg(J.slice(2),loan,e));
  const dg=D2F.dirtyDigit(implicit,J,h,e,loan[0]);
  eliminate(dg,1001,1,(cs,z)=>add4.push(...MCX(cs,z,loan.filter(w=>w!==z&&!cs.includes(w)))));
  add4.push(...mcN([e,...J.slice(2)],[true,...J.slice(2).map(()=>false)],h,loan));
  for(const orientation of [0,1]){
   const pred=[];
   if(!orientation)pred.push(...mcN([...guard,sign],[...pol,true],e,loan));
   for(const w of [J[1],u[1]])pred.push(...mcN([...guard,sign,w],[...pol,true,true],e,loan));
   put(pred);put([[h]]);put(orientation?[...add4].reverse():add4);put([[h]]);put([...pred].reverse());
  }
  // Interim integration boundary: transfer c4 to original middle, restore sign.
  const g=mcN(guard,pol,e,loan);put(g);put(fr(e,sign,5*n+5));
  for(const w of [J[1],u[1]])put([[e,w,sign]]);put([...g].reverse());
 }`);
 return s.slice(0,a)+f+s.slice(b);
};
