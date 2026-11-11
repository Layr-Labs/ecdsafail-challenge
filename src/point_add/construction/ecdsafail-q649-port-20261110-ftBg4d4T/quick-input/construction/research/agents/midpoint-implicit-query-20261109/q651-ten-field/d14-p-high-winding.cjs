'use strict';
module.exports=s=>{
 const a=s.indexOf(' for(let c=n-2;c<=n;c++){',s.indexOf('const reconnectAfter=')),b=s.indexOf('\n};',a);
 if(a<0||b<0)throw Error('high reconnect span');
 s=s.slice(0,a)+s.slice(b);
 const old="D2Winding(n,L,R,Q,loan,sink);tap('winding');parkOuter(n,M,rm,Q,T6.slice(0,-1),p,bits,R[1],loan,sink);";
 const next=`D2Winding(n,L,R,Q,loan,sink);tap('winding');
 // Count0 is copied/erased first. Q1..3 must remain intact for orientation.
 parkOuter(n,M,rm,Q,T6.slice(0,1),p,bits,R[1],loan,sink);
 for(let c=1;c<=n;c++){
  const sel=flagHeight(vt,c,R[1],loan);put(sel);
  if(c<n-2)put(fr(R[1],S[4],T6[0]));
  else{
   const guard=[R[1],...vt.slice(0,3)],pol=[true,false,false,false];
   for(const row of fr(R[1],sig,T6[0])){const cs=row.slice(0,-1).filter(w=>w!==R[1]);put(mcN([...guard,...cs],[...pol,...cs.map(()=>true)],row.at(-1),loan));}
   // Q now equals g*Qpre. For V divisible8, Qpre is odd and
   // sign = bit1(Qpre) xor U1 = Q[k+1] xor odd(g)[1] xor U1.
   const size=n-c;
   for(let g=1;g<1<<(size+1);g++){
    const gc=c===n?[]:L.slice(0,size+1),gp=gc.map((_,j)=>!!(g>>j&1));
    let k=0;while(!(g>>k&1))k++;
    const cs=[...guard,...gc],ps=[...pol,...gp];
    for(const w of [Q[k+1],L[n]])put(mcN([...cs,w],[...ps,true],sig,loan));
    if(g>>(k+1)&1)put(mcN(cs,ps,sig,loan));
   }
  }
  put(rev(sel));
 }
 put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);
 for(let j=1;j<4;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}`;
 if(s.split(old).length!==2)throw Error('high winding anchor');return s.replace(old,()=>next);
};
