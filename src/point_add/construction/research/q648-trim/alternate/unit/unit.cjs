'use strict';

const path=require('node:path');

function source(width=648){
  if(width===647){
    const base=require('../q647.cjs').source(),{compiler}=require('../../upper/build.cjs');
    return require('../../../q647-trim/upper/integrated.cjs').patch(base,compiler);
  }
  if(width!==648)throw Error('Supported unit widths 647 and 648');
  const {circuit}=require('../../circuit.cjs'),{family}=require('../../upper/build.cjs');
  const api=circuit(),stages=require(path.resolve(__dirname,'../../donor',family,'stage-map.cjs'));
  const old=stages.upper;let result;
  stages.upper=(...args)=>result=old(...args);
  try{api.arithmetic(null);}finally{stages.upper=old;}
  if(!result||api.config.width!==648)throw Error('Q648 selected source');
  return result;
}

function mergedUnitMixed(tape,q,v,rem,back){
  const J=q.concat(rem),n=v.length,r=q.length,ops=[];
  const x=w=>tape.out(1023,1023,w),cx=(c,w)=>tape.out(1023,c,w);
  const flip=j=>{
    const old=j===r-1?null:J[j+n+1];
    if(old!==null)x(old);
    for(const w of J.slice(j,j+n+1))if(old===null)x(w);else cx(old,w);
    if(old!==null)x(old);
  };
  const join=(j,rev)=>{
    const h=J[j+n],lo=J[j-1],old=j===r-1?null:J[j+n+1];
    const shared=()=>{x(h);for(const w of J.slice(j,j+n))cx(h,w);x(h);};
    const high=()=>{x(h);if(old!==null)cx(old,h);};
    const low=()=>{x(lo);cx(h,lo);};
    if(rev){low();high();shared();}else{shared();high();low();}
  };
  ops.push(()=>flip(r-1));
  for(let j=r-1;j>=0;j--){
    ops.push(rv=>this.nrAdder(tape,v,J.slice(j,j+n),J[j+n],null,rv));
    ops.push(j===0?()=>flip(0):rv=>join(j,rv));
  }
  ops.push(rv=>this.nrAdder(tape,v,J.slice(0,n),null,J[n],rv),()=>{for(const b of J.slice(n))x(b);},
    rv=>this.permute(tape,J,J.slice(n).concat(J.slice(0,n)),[],rv));
  stepList(ops,!back,fn=>fn(!back));
}

function patch(s){
  const begin=s.indexOf('    unit(tape,ctrl,back) {'),end=s.indexOf('\n    }',begin);
  if(begin<0||end<begin||s.indexOf('    unit(tape,ctrl,back) {',end)>=0)throw Error('EarlyUnit source');
  let cut=s.slice(begin,end);
  function one(a,b){if(cut.split(a).length!==2)throw Error('EarlyUnit dependency '+a);cut=cut.replace(a,()=>b);}
  one('        const seq=[',`        const lowA=a.slice(0,v.length);
        const exchange=rv=>this.permute(tape,[...v,...lowA],[...lowA,...v],ctrl,rv);
        const productA=rv=>{
            exchange(false);this.mixed(tape,this.r,v,d,[],rv);exchange(true);
        };
        const seq=[`);
  one('rv=>this.mixed(tape,this.r,a,wideCarry,ctrl,rv)','productA');
  one('rv=>this.mixed(tape,this.r,v,d,ctrl,!rv)','rv=>this.mixed(tape,this.r,v,d,[],!rv)');
  const cls='class EarlyUnit extends UnitPreparation {';
  if(s.split(cls).length!==2)throw Error('EarlyUnit mixed source');
  return s.replace(cls,()=>mergedUnitMixed.toString()+'\n'+cls+'\n'+cut+'\n    }\n    unguardedMixed(t,q,v,d,back){return mergedUnitMixed.call(this,t,q,v,d,back); }');
}
module.exports={source,patch};
