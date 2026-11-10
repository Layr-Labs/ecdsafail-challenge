'use strict';
const fs=require('node:fs');
const {upper:leased}=require('../q652-lease/upper.cjs');
const file=require.resolve('../q651-ten-field/alternating-digit.cjs');
const alt=fs.readFileSync(file,'utf8');
function upper(source){
    const out=leased(source),begin=out.indexOf('function dirtyDigit(A,B,h,e,loan) {'),end=out.indexOf('class UnguardedGeneral extends OddEstimateGeneral {',begin);
    const start=alt.indexOf('function alternatingDigit('),stop=alt.indexOf('module.exports={alternatingDigit};',start);
    if(begin<0||end<=begin||start<0||stop<=start)throw Error('Changed Q652 restoring digit source');
    const body=alt.slice(start,stop).replace('function alternatingDigit(', 'function dirtyDigit(');
    return out.slice(0,begin)+body+'\n'+out.slice(end);
}
module.exports={upper};
