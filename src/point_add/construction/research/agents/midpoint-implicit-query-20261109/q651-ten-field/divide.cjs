'use strict';
const published=require('./public-backend.cjs');
const {replace}=require('../q653-next/parts.cjs');
function build(pub){
// Jackylee0424's Q651 count transport touches Q126 only in the two largest
// heights. Below 127 the reduced coefficient and its pad can be parked in
// the known-zero modulus suffix. This lets one residual divide cover a band.
const select='const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=flagHeight(v,t,e,loan),put=g=>sink(\'nct\',g);';
let d=replace(pub.d,select,`
  const groups={2:2,64:3,96:65,112:97,120:113,124:121,125:125,126:126},lo=groups[t];
  if(lo===undefined)continue;
  const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],put=g=>sink('nct',g);
  const zero=(word,dest)=>mcN(word,word.map(()=>false),dest,loan);
  const cls=lo===t?flagHeight(v,t,e,loan):zero(v.slice(t),e).concat(zero(v.slice(lo-1),e)),park=[];
  if(lo<t)for(let j=lo;j<=t;j++){
    const z=v[t+j-lo],tail=v.slice(j,t),test=[e,...tail,z],match=[true,...tail.map(()=>false),true];
    const target=j===t?gap:u[j];
    if(z===undefined)throw Error('missing zero modulus port for grouped Q651 residue');
    park.push([target,z],...mcN(test,match,target,loan),[target,z]);
  }`);
d=replace(d,'put(cls);if(t===n)put([[e,J[n-1],L[0]],[L[0]],[e,L[0],J[n-1]],[L[0]]]);if(t===2)',
    'put(cls);put(park);if(t===2)');
const end='neg();cond();neg();cond();put([...cls].reverse());\n }\n}\nfunction mulG';
d=replace(d,end,'neg();cond();neg();cond();put(park.slice().reverse());put([...cls].reverse());\n }\n}\nfunction mulG');
const divide=Function('module','dirtyDigit','dirtyMdg','dirtyBlock','emitWalk','Reduced','SectorCanonical',d+'\nreturn inverseField;')(
    {exports:{}},pub.dirtyDigit,pub.dirtyMdg,pub.dirtyBlock,pub.emitWalk,pub.D2Reduced,pub.D2Canonical);
function mapPort(q){
    if(q===1023)return q;
    if(!Number.isInteger(q)||q<0||q>653||q===646||q===647||q===648||q===652)
        throw Error('Q651 divider touched removed logical site '+q);
    return q===651?646:q===653?647:q;
}
function emitDivideSparse(sink,tap){
    divide(128,null,null,(kind,data)=>{
        if(kind==='packed'){
            const next=new Uint32Array(data.length);
            for(let j=0;j<data.length;j++){const x=data[j];next[j]=(mapPort(x>>>20)<<20)|(mapPort(x>>>10&1023)<<10)|mapPort(x&1023);}
            sink(kind,next);
        }else if(kind==='nct')sink(kind,data.map(row=>row.map(mapPort)));
        else sink(kind,data.map((q,i)=>i===data.length-1?q:mapPort(q)));
    },tap);
}
return {emitDivideSparse,emitMultiplySparse:pub.emitMultiplySparse};
}
module.exports={...build(published),build};
