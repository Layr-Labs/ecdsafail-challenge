'use strict';
// Exact direction comparator with constant-zero high divisor bit, no pick642.
// No witness window is claimed freed: normalization still needs pick642.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U35 direction anchor '+a);s=s.replace(a,()=>b);};
 one('        // upper approximation for V/2 < U: toggle floor(V/2) < U.',`        if(this.u35DirectionOnly){this.u35Direction(tape);return;}
        // upper approximation for V/2 < U: toggle floor(V/2) < U.`);
 one('    trial(tape,witness,back){\n      if(!witness&&this.k<=112&&!this.u30Trial){',`    trial(tape,witness,back){
      if(witness&&this.k<=112&&!this.u35DirectionOnly){const H=Object.create(this);H.u35DirectionOnly=true;H.trial(tape,witness,back);return;}
      if(!witness&&this.k<=112&&!this.u30Trial){`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u35Direction(tape){
      const x=this.v.slice(1),y=this.u,n=y.length,high=y.at(-1),bit=this.dv[1],ctrl=this.ctrl;
      this.toggle(tape,[...ctrl,high],[],bit);if(n===1)return;
      this.cnotList(tape,[],x);const ops=[];
      for(let i=1;i<n-1;i++)ops.push([NONE,y[i],x[i]]);
      for(let i=n-2;i>=1;i--)ops.push([NONE,y[i],y[i+1]]);
      for(let i=0;i<n-1;i++)ops.push([x[i],y[i],y[i+1]]);
      stepList(ops,false,([a,b,t])=>{if(t===high)this.toggle(tape,[...ctrl,...[a,b].filter(q=>q!==NONE)],[high],bit);else tape.out(a,b,t);});
      stepList(ops,true,([a,b,t])=>{if(t!==high)tape.out(a,b,t);});this.cnotList(tape,[],x);
    }
`);
 return s;
};
