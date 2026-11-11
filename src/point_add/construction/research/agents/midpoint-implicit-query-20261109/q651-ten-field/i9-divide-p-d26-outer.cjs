 'use strict';
// Count1 remains live; transport it to the just-measured count0 host.
// Its original copy/HMR stays after the orientation work. Native642 becomes port.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D26 outer anchor '+a);s=s.replace(a,()=>b);};
 one('parkOuter(n,M,rm,Q,T6.slice(0,1),p,bits,R[1],loan,sink);D14ParkCount',
     "parkOuter(n,M,rm,Q,T6.slice(0,1),p,bits,R[1],loan,sink);const D26count1Host=T6[0];put([[T6[1],D26count1Host],[D26count1Host,T6[1]]]);T6[0]=T6[1];tap('d26.outer.port642');D14ParkCount");
 one("for(let j=1;j<2;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}T6[0]=T6[1];tap('d24.port642');",
     "put([[D26count1Host,Q[1]]]);sink('hmr',[D26count1Host,bits+1]);T6[0]=T6[1];tap('d24.port642');");
 return s;
};
