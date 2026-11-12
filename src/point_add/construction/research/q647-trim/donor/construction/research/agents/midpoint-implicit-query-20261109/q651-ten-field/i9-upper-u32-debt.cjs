'use strict';
// Source-only extension after u32-glue. Candidate until its replay receipts pass.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U32 debt anchor '+a);s=s.replace(a,()=>b);};
 one('const L=Object.create(this);L.u32Glue=false;',"const L=Object.create(this);L.u32Glue=false;if(name==='removeDebt')L.u32Debt=true;");
 one('if(this.u23Late){this.u23LiteralV(tape,this.pick,H=>H.mixed(tape,H.r,H.v,H.u,[],back));return;}',
     'if(this.u23Late){this.u23LiteralV(tape,this.u32Debt?this.carry:this.pick,H=>H.mixed(tape,H.r,H.v,H.u,[],back));return;}');
 one('    u7Threshold(tape,target){',`    u7Threshold(tape,target){
      if(this.u32Debt){this.u32Threshold(tape,target);return;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u32Threshold(tape,target){
      for(let count=0;count<=this.maxShift;count++){
        const H=Object.create(this),sel=this.carry,n=this.n;
        H.tag=[];H.uDebt=false;H.ctrl=[this.g,sel];
        H.installZeros=function(tp,back){
          stepList(split(0,this.maxShift),back,j=>{if(count<=j)this.permute(tp,[this.n[j],this.q[j+2]],[this.q[j+2],this.n[j]],[],back);});
          tp.out(NONE,NONE,this.n.at(-1));
        };
        H.mixedHead=function(tp,D,C,back){
          const Q=this.q,stages=[rv=>this.mixed(tp,Q.slice(0,2),D,C,[],rv)];
          for(let i=2;i<Q.length;i++)if(count>i-2){
            const z=[...C,Q[i]],origins=[...z.slice(1),z[0]];
            stages.push(rv=>{const seq=[rr=>MixedArithmetic.prototype.digit.call(this,tp,z,D,[],!rr),rr=>this.permute(tp,z,origins,[],rr)];stepList(seq,rv,fn=>fn(rv));});
          }
          stepList(stages,back,fn=>fn(back));
        };
        const mark=()=>this.toggle(tape,[...this.ctrl,n[this.m-1-count]],n.slice(this.m-count),sel);
        const origins=count?n.slice(-count).concat(n.slice(0,-count)):n;
        mark();this.permute(tape,n,origins,[],false);H.threshold(tape,target);
        this.permute(tape,n,origins,[],true);mark();
      }
    }
`);
 return s;
};
