'use strict';
// ringhole (q648): u7Threshold without the carry wire; removeDebt rows 113..U7_HI (default 126) all use the u7Debt form. The count loop is compile-time, so the threshold's per-count
// selector (installZeros / mixedHead: indicator -> carry, then ops controlled by carry) is a constant: the ops become uncontrolled when the
// predicate holds and are skipped otherwise. carry is then untouched inside u7Threshold (it can host a flag there).
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('u7 anchor '+a.slice(0,60));s=s.replace(a,()=>b);};
 one("        H.tag=[];H.uDebt=false;H.digit=H.digitDirty;H.ctrl=[this.g,sel];",
 String.raw`        H.tag=[];H.uDebt=false;H.digit=H.digitDirty;H.ctrl=[this.g,sel];
        if(process.env.U7_OFF!=='1'){
          const pred=(kind,j)=>kind==='eq'?count===j:kind==='gt'?count>j:count<=j;
          H.installZeros=function(tape,back){const Q=this.q;
            stepList(split(0,this.maxShift),back,j=>{if(pred('le',j))this.permute(tape,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[],back);});
            tape.out(NONE,NONE,this.n.at(-1));};
          H.mixedHead=function(tape,D,C,back){const Q=this.q,stages=[rv=>this.mixed(tape,Q.slice(0,2),D,C,[],rv)];
            for(let i=2;i<Q.length;i++){if(!pred('gt',i-2))continue;const z=[...C,Q[i]],origins=[...z.slice(1),z[0]];
              stages.push(rv=>{const seq=[rr=>this.digit(tape,z,D,[this.g],!rr),rr=>this.permute(tape,z,origins,[],rr)];stepList(seq,rv,fn=>fn(rv));});}
            stepList(stages,back,fn=>fn(back));};
        }`);
 const U7HI=+(process.env.U7_HI||126);
 one("        if(this.k>=113&&this.k<=119){this.u7Debt(tape,back);return;}","        if(this.k>=113&&this.k<="+U7HI+"){this.u7Debt(tape,back);return;}");
 return s;
};
