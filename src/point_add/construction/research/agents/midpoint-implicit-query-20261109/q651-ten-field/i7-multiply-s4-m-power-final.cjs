'use strict';
const base=require('./i7-multiply-s4-m-power-host.cjs');
const parts=`function m6powerParts(n,T,H,S,en,L,kappa,extra){
 const maxDigits=Math.min(M6_POWER_DIGITS,Math.log2(n)),parts=[],encodings=[];
 for(let r=1;r<=maxDigits;r++){
  const encode=[];for(let l=r;l<n;l++)if((l-1)&(1<<(r-1))){const word=T.slice(r,l+1);encode.push(...negate(word,MCX(word,T[r-1],L),word.map((_,j)=>j===word.length-1)));}
  encodings.push(encode);parts.push(()=>encode);
  for(let i=r-1;i<(r===maxDigits?n-1:r);i++)parts.push(()=>m6powerSweep(n,T,H,S,T.slice(0,r),en,L,i,kappa));
 }
 for(const g of encodings.reverse())parts.push(()=>g.slice().reverse());return parts;
}
`;
module.exports={source:base.source,f:s=>{s=base.f(s);s=s.replace('dirtyDigit(M.slice(2),X.slice(1,-1)', 'dirtyDigit(M.slice(J.length),X.slice(J.length-1,-1)').replace('const cs=M.slice(2,k)','const cs=M.slice(J.length,k)');
 const a=s.indexOf('function m6powerParts('),b=s.indexOf('\nfunction m6sub',a);if(a<0||b<0)throw Error('power parts bounds');
 return 'const M6_POWER_DIGITS='+5+';\n'+s.slice(0,a)+parts+s.slice(b);
}};
