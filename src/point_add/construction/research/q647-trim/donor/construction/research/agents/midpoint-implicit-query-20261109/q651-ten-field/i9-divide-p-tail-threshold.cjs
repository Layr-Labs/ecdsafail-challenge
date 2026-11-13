'use strict';
// Exploratory: when M is denormalized, s=clz(M) and [s>j]=zero(top j+1 M bits).
// Leave register lifetimes and measurement functions unchanged.
module.exports=s=>{
 const a=s.indexOf('function D17GTOracle(S,value,e,loan,M){'),b=s.indexOf('function D17RotOracle(',a);
 if(a<0||b<0)throw Error('D20 threshold span');
 return s.slice(0,a)+`function D17GTOracle(S,value,e,loan,M){
 const w=M.slice(M.length-value-1);return D17Raw(w,w.map(()=>false),e,loan);
}\n`+s.slice(b);
};
