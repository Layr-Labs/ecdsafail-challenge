'use strict';
// During the remainder rotation e is clean and otherwise unused. Sequentially
// materialize count0/count2 there, rotate, and erase before the next consumer.
module.exports=s=>{
 s=require('./i9-divide-p-tail-room.cjs')(s);
 const call='D17RotOracle(rm,-1,S,M,C)';if(s.split(call).length!==2)throw Error('D20 rt call');s=s.replace(call,'D17RotOracle(rm,-1,S,M,C,e)');
 const a=s.indexOf('function D17RotOracle('),b=s.indexOf('function D20Count(',a);if(a<0||b<0)throw Error('D20 rt span');
 return s.slice(0,a)+`function D17RotOracle(word,dir,S,M,loan,e){const rows=[];
 for(let j=0;j<S.length;j++){
  const held=j===0||j===2,pre=held?D20Count(M,e,loan,j):[],control=held?e:S[j];rows.push(...pre);
  for(const [a,b]of rotleft(word.length,(word.length+dir*(1<<j))%word.length))rows.push(...fr(control,word[a],word[b]));
  rows.push(...pre.slice().reverse());
 }return rows;
}\n`+s.slice(b);
};
