'use strict';
// D3 partial: prefix + both complete Gtop traversals omit645. Middle still645.
// Apply after p-alpha128-seed(p-candidate(source)).
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('connected anchor '+a);s=s.replace(a,()=>b);};
 one(`for(let c=1;c<n;c++){
  const pred=flagHeight(vt,c,R[1],loan),host=c<n-2?Q[n-3]:c===n-2?L[4]:L[1];
  put(pred);put(fr(R[1],host,base+5));if(c===n-1)put([[R[1],L[1]]]);put(rev(pred));
 }
 S[4]=base+5;T6[4]=base+5;tap('alpha');`, `S[4]=base+5;T6[4]=base+5;tap('alpha');`);
 one(`const g=mcN(guard,pol,e,loan);put(g);put(fr(e,sign,5*n+5));
  for(const w of [J[1],u[1]])put([[e,w,sign]]);put([...g].reverse());`,
 `// Keep c4 on sign when height128 and V divisible8; else c4 is known0.`);
 one('if(!rev){Gtop(n,L,R,Q,[e,t],loan,put,p1,p2);delta();', `
const leaseGuard=[V[n-1],...V.slice(0,3)],leasePol=[true,false,false,false];
const signToggle=()=>{for(const w of [Q[1],U[1]])put(mcN([...leaseGuard,w],[...leasePol,true],sg,loan));};
const transferMiddle=(back)=>{
 for(let c=1;c<n;c++)cl(c,fr(e,L[n-c],S[4]));
 if(back)signToggle();
 const pr=mcN(leaseGuard,leasePol,e,loan);put(pr);put(fr(e,sg,S[4]));put([...pr].reverse());
 if(!back)signToggle();
};
const forwardBefore=c=>{
 if(c===n)return p1(c);
 const src=c<n-2?Q[n-3]:c===n-2?L[4]:L[1];
 return [...fr(e,src,V[c]),...(c===n-1?[[e,L[1]]]:[]),...p1(c)];
};
const forwardAfter=c=>[...p2(c),...(c<n?fr(e,V[c],L[n-c]):[])];
const reverseBefore=c=>[...(c<n?fr(e,L[n-c],V[c]):[]),...p2(c).reverse()];
const reverseAfter=c=>{
 const rows=pw(c);if(c<n-2)return [...rows,...fr(e,V[c],Q[n-3])];
 if(c===n)return rows;
 // At high126/127, c4=1 implies V divisible8 (v2(g)<=2).
 const guard=[e,...V.slice(0,3)],pol=[true,false,false,false];
 for(const w of [Q[1],U[1]])rows.push(...mcN([...guard,w],[...pol,true],sg,loan));
 // Move into the now-zero orientation, preserving an arbitrary inactive sign.
 for(const r of fr(e,V[c],sg)){
  // Whole swap must have both height and low-zero controls, including its CXs.
  const cs=r.slice(0,-1).filter(w=>w!==e);
  rows.push(...mcN([...guard,...cs],[...pol,...cs.map(()=>true)],r.at(-1),loan));
 }
 return rows;
};
const reconnectAfter=()=>{
 for(let c=1;c<n-2;c++)cl(c,fr(e,Q[n-3],S[4]));
 for(let c=n-2;c<=n;c++){
  const pr=flagHeight(V,c,e,loan);put(pr);
  const cs=[e,...V.slice(0,3)],vs=[true,false,false,false];
  // Use a multi-controlled swap under the stable class and V-low guard.
  for(const r of fr(e,sg,S[4])){const controls=r.slice(0,-1).filter(w=>w!==e);put(mcN([...cs,...controls],[...vs,...controls.map(()=>true)],r.at(-1),loan));}
  for(const w of [Q[1],U[1]])put(mcN([...cs,w],[...vs,true],sg,loan));
  put([...pr].reverse());
 }
};
if(!rev){Gtop(n,L,R,Q,[e,t],loan,put,forwardBefore,forwardAfter);transferMiddle(false);delta();`);
 one('bias(true);delta();Gtop(n,L,R,Q,[e,t],loan,put,c=>p2(c).reverse(),pw);',
 'bias(true);delta();transferMiddle(true);Gtop(n,L,R,Q,[e,t],loan,put,reverseBefore,reverseAfter);reconnectAfter();');
 return s;
};
