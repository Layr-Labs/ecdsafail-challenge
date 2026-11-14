'use strict';
// Apply after U5. Public row guards only; retains the nine-helper ABI.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U7 anchor '+a);s=s.replace(a,()=>b);};
 one('const flag=this.tags[0],on=[this.g,flag];',
     'const flag=this.k===127?this.pick:this.tags[0],on=[this.g,flag];');
 one('    removeDebt(tape,back){\n        const g=this.ctrl,Q=this.q,H=',
 `    removeDebt(tape,back){
        if(this.k>=113&&this.k<=119){this.u7Debt(tape,back);return;}
        const g=this.ctrl,Q=this.q,H=`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    // Enumerate only the small threshold body. Pack/unpack and Q changes stay shared.
    u7Threshold(tape,target){
      for(let count=0;count<=this.maxShift;count++){
        const H=Object.create(this),sel=this.pick,n=this.n;
        H.tag=[];H.uDebt=false;H.digit=H.digitDirty;H.ctrl=[this.g,sel];
        H.indicator=(tp,j,kind,controls,dest)=>{
          if(kind==='eq'?count===j:kind==='gt'?count>j:count<=j)H.toggle(tp,controls,[],dest);
        };
        const mark=()=>this.toggle(tape,[...this.ctrl,n[this.m-1-count]],n.slice(this.m-count),sel);
        const origins=count?n.slice(-count).concat(n.slice(0,-count)):n;
        mark();this.permute(tape,n,origins,[],false);
        H.threshold(tape,target);
        this.permute(tape,n,origins,[],true);mark();
      }
    }
    u7Debt(tape,back){
      const g=this.ctrl,Q=this.q,seq=[rv=>this.packNumber(tape,rv),
        rv=>this.inc(tape,Q,g,rv),()=>this.u7Threshold(tape,this.dv[0]),
        rv=>this.inc(tape,Q,g,rv),()=>this.u7Threshold(tape,this.dv[1]),
        rv=>this.inc(tape,Q,g,!rv),rv=>this.inc(tape,Q,g,!rv),
        rv=>this.packNumber(tape,!rv)];
      stepList(seq,back,fn=>fn(back));
    }
`);
 one('        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=',
 `        if(this.k>=113&&this.k<=126){H.tag[0]=this.pick;H.digit=H.digitDirty;}
        const D=this.topDivisor(),Q=this.q,g=this.ctrl,js=`);
 one('        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),\n            rv=>this.inc(tape,Q,g,rv),()=>H.threshold',
 `        if(this.k>=120&&this.k<=123){H.tag=H.tag.slice();H.tag[0]=this.carry;H.uDebt=true;}
        if(this.k>=124&&this.k<=126){H.tag=H.tag.slice();H.tag[0]=this.v[this.k];H.u38NormLease=true;}
        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
            rv=>this.inc(tape,Q,g,rv),()=>H.threshold`);
 return s;
};
