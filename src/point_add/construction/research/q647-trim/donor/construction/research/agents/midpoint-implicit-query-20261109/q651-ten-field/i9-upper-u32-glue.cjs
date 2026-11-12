'use strict';
// Incremental source overlay after U28's unit extension, before S3 and the one sink.
// Bodies omit logical pick. Outer-family ABI adapters are deliberately not supplied.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U32 anchor '+a);s=s.replace(a,()=>b);};
 one('    mixed(tape,q,v,rem,controls,back) {',`    mixed(tape,q,v,rem,controls,back) {
        if(this.u32Glue&&controls.length){
            const live=controls.filter(q=>q!==tape.one);
            if(live.length!==1)throw Error('U32 mixed control contract');
            const H=Object.create(this);H.u32Glue=false;H.pick=this.carry;
            H.digit=MixedArithmetic.prototype.digit;
            return MixedArithmetic.prototype.mixed.call(H,tape,q,v,rem,live,back);
        }`);
 one('const correct=(flag,rv)=>H.u23LiteralV(tape,this.pick,L=>tape.add(v,this.A,[...ctrl,flag===host?this.pick:flag],this.carry,!rv));',
     `const correct=(flag,rv)=>this.u32Glue?this.u32Correct(tape,flag,!rv):H.u23LiteralV(tape,this.pick,L=>tape.add(v,this.A,[...ctrl,flag===host?this.pick:flag],this.carry,!rv));`);
 one('rv=>virtualCoef(!rv),rv=>H.removeDebt(tape,rv)',
     'rv=>this.u32Glue?this.u32VirtualCoef(tape,!rv):virtualCoef(!rv),rv=>H.removeDebt(tape,rv)');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u32Correct(tape,flag,back){
      // Under take, the literal V top is one; its physical site retains flag2.
      const g=[...this.ctrl,flag],v=this.v,A=this.A;
      const seq=[rv=>tape.add(v.slice(0,-1),A,g,this.carry,rv),
                 rv=>this.inc(tape,A.slice(this.k),g,rv)];
      stepList(seq,back,fn=>fn(back));
    }
    u32VirtualCoef(tape,back){
      const H=Object.create(this);H.u32Glue=false;
      H.digit=function(t,z,v,controls,rv){this.digitTopOne(t,z,v,controls,rv);};
      MixedArithmetic.prototype.mixed.call(H,tape,this.q,this.v,this.u,[this.take],back);
    }
`);
 // Preserve the existing method graph; outer windows explicitly drop glue context.
 one('class FoldTape extends Tape {',`// U32 family scope. No gate-list inspection or input-dependent emission.
const u32Emit=UnguardedGeneral.prototype.emit;
UnguardedGeneral.prototype.u32Run=function(inputTape,back,method='emit'){
 const H=Object.create(this),tape=Object.create(inputTape);H.u32Glue=true;
 tape.ids=inputTape.ids.filter(q=>q!==this.pick);
 tape.loan=(used,n)=>inputTape.loan([...used,this.pick],n);
 for(const name of ['trial','signProbe','estimate','removeDebt','affine']){
   const original=this[name];
   H[name]=function(tp,...args){
     const L=Object.create(this);L.u32Glue=false;
     // Restore the original outer method (nested virtual dispatch remains valid).
     L[name]=original;
     return original.call(L,tp,...args);
   };
 }
 return method==='emit'?u32Emit.call(H,tape,back):this[method].call(H,tape,back);
};
UnguardedGeneral.prototype.emit=function(tape,back){return this.u32Run(tape,back);};
class FoldTape extends Tape {`);
 return s;
};
