'use strict';
// From ledger (q650-divx d4aa804), env gates removed for integration.
// ipark Htop routing (logical 640 evicted). Contract (evict): Htop enters ipark (alpha exit) on
//   class<=125: Q125 | 126: L4 (U top) | 127: L1 (XOR on known 1) | 128,V odd: 641 | 128,V even: 650 (XOR on U0=1)
// and must be on 643 after the count hmr. Requires efree.cjs (e untouched from Gtop end to hmr).
// Gtop: in its own class iteration (selector e set) Htop shadows on V[127] (not read by that body, vacated before
// the selector uncompute), then lands on a class zero: <=124 Q124 | 125 L4 | 126 L2 | 127 L1. Class 128 stays put.
// After Gtop one V-literal-controlled move per class puts Htop on e; after hmr a uniform move puts it on 643.
function one(d,a,b){if(d.split(a).length!==2)throw Error('ipark anchor '+a.slice(0,70));return d.replace(a,()=>b);}
const HT=`let HT=null;HT=(()=>{const V127=V[127],Q125=Q[n-3],Q124=Q[n-4];
 const P=t=>{const w=V.slice(t-1);return [w,w.map((_,j)=>j===0)];};
 const mvP=([w,v],a,b,aval=0)=>{const g=[];if(aval)g.push([a]);g.push(...mcN([...w,a],[...v,true],b,loan));g.push(...mcN([...w,b],[...v,true],a,loan));if(aval)g.push([a]);return g;};
 return {
  mi(c){if(c>127)return [];const src=c<=125?Q125:c===126?L[4]:L[1],av=c===127;const g=[];if(av)g.push([src]);g.push([e,src,V127],[e,V127,src]);if(av)g.push([src]);return g;},
  mo(c){if(c>127)return [];const dst=c<=124?Q124:c===125?L[4]:c===126?L[2]:L[1];return [[e,V127,dst],[e,dst,V127]];},
  hopG(){return [...mvP([V.slice(124),[false,false,false,false]],Q124,e),...mvP(P(125),L[4],e),...mvP(P(126),L[2],e),...mvP(P(127),L[1],e),
   ...mvP([[V127,V[0]],[true,true]],641,e),...mvP([[V127,V[0]],[true,false]],650,e,1)];},
  hop(){put(this.hopG());},
  toS(){put([[e,643],[643,e]]);},
  fromS(){put([[643,e],[e,643]]);},
  unhop(){put([...this.hopG()].reverse());},
  Z(c){return c<=124?Q124:c===125?L[4]:c===126?L[2]:L[1];},
  X(c){const x=process.env.HTX?JSON.parse(process.env.HTX):{};const k=c<=124?'le124':c;return x[k]!==undefined?x[k]:Q[n-1];},
  mi2(c){if(c>127)return [];const z=this.Z(c);return [[e,z,V127],[e,V127,z]];},
  mo2(c){if(c>127)return [];const x=this.X(c);return [[e,V127,x],[e,x,V127]];}
 };})();`;
function iparkHtop(d){
 d=one(d,"shseq.borrow=loan;","shseq.borrow=loan;"+HT);
 d=one(d,"if(!rev){Gtop(n,L,R,Q,[e,t],loan,put,p1,p2);","if(!rev){Gtop(n,L,R,Q,[e,t],loan,put,c=>[...HT.mi(c),...p1(c)],c=>[...p2(c),...HT.mo(c)]);HT.hop();");
 d=one(d,"for(let j=0;j<bits;j++)sink('hmr',[S[j],off+j]);","for(let j=0;j<bits;j++)sink('hmr',[S[j],off+j]);HT.toS();");
 {
  d=one(d,"else{routeZeros(n,L,R,e,loan,put,true,null,c=>p3(c).reverse());extract();","else{routeZeros(n,L,R,e,loan,put,true,null,c=>p3(c).reverse());HT.fromS();extract();");
  d=one(d,"delta();Gtop(n,L,R,Q,[e,t],loan,put,c=>p2(c).reverse(),pw);}}","delta();HT.unhop();Gtop(n,L,R,Q,[e,t],loan,put,c=>[...HT.mi2(c),...p2(c).reverse()],c=>[...pw(c),...HT.mo2(c)]);}}");}
 return d;}
module.exports={iparkHtop};
