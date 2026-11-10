'use strict';
// From ledger (q650-divx d4aa804), env gates removed for integration.
// e-free parkInner helpers: delta, bias and extract no longer use the selector ancilla e (R1). Each e-controlled
// operation instead carries e's defining conjunction (literals on D, V or L) as its own controls. Same map exactly:
// e was computed from wires the controlled ops do not write, and uncomputed right after.
function one(d,a,b){if(d.split(a).length!==2)throw Error('efree anchor '+a.slice(0,70));return d.replace(a,()=>b);}
function efree(d){
 d=one(d,"function delta(){for(let l=0;l<n-1;l++){const A=gt(S,l,e,null,loan),C=[e,...V.slice(0,l+1)],B=[true,...V.slice(0,l).map(()=>false),true];put(A);put(mcN(C,B,D,loan));put([...A].reverse());}}",
  "function delta(){for(let l=0;l<n-1;l++){const vp=V.slice(0,l+1),vb=[...V.slice(0,l).map(()=>false),true];for(let j=0;j<S.length;j++)if(!(l>>j&1)){const C=[S[j],...S.slice(j+1),...vp],B=[true,...S.slice(j+1).map((_,b)=>!!(l>>(b+j+1)&1)),...vb];put(mcN(C,B,D,loan));}}}");
 d=one(d,"function bias(back){for(let ii=0;ii<n;ii++){const l=back?n-1-ii:ii,cs=[D,...V.slice(0,l+1)],v=[true,...V.slice(0,l).map(()=>false),true],g=mcN(cs,v,e,loan),a=shseq(S,(l+1)%n,e);put(g);put(back?a:[...a].reverse());put([...g].reverse());}}",
  "function bias(back){for(let ii=0;ii<n;ii++){const l=back?n-1-ii:ii,cs=[D,...V.slice(0,l+1)],v=[true,...V.slice(0,l).map(()=>false),true],val=(l+1)%n;let a=[];for(let j=0;j<S.length;j++)if(val>>j&1)for(let k=S.length-1;k>=j;k--){const w=S.slice(j,k);a=a.concat(mcN([...cs,...w],[...v,...w.map(()=>true)],S[k],loan));}put(back?a:[...a].reverse());}}");
 d=one(d,"function extract(){for(let j=0;j<n-1;j++){const cs=[D,...L.slice(0,j+1)],v=[true,...L.slice(0,j).map(()=>false),true],a=mcN(cs,v,e,loan);put(a);for(let b=0;b<bits;b++)if((j>>b)&1)put([[e,S[b]]]);put([...a].reverse());}",
  "function extract(){for(let j=0;j<n-1;j++){const cs=[D,...L.slice(0,j+1)],v=[true,...L.slice(0,j).map(()=>false),true];for(let b=0;b<bits;b++)if((j>>b)&1)put(mcN(cs,v,S[b],loan));}");
 d=one(d,"for(let j=0;j<bits;j++){const cs=[D,...V.slice(0,j+1)],v=cs.map(()=>false),a=mcN(cs,v,e,loan);put(a);put([[e,U[j],S[j]]]);",
  "for(let j=0;j<bits;j++){const cs=[D,...V.slice(0,j+1)],v=cs.map(()=>false);put(mcN([...cs,U[j]],[...v,true],S[j],loan));");
 d=one(d,"const qa=[e,sg,...Q.slice(0,j+1)],pol=[true,!!si,...eq_bits(Q,raw).slice(0,j+1)];put(mcN(qa,pol,S[j],loan));}}}put([...a].reverse());}}",
  "const qa=[...cs,sg,...Q.slice(0,j+1)],pol=[...v,!!si,...eq_bits(Q,raw).slice(0,j+1)];put(mcN(qa,pol,S[j],loan));}}}}}");
 return d;}
module.exports={efree};
