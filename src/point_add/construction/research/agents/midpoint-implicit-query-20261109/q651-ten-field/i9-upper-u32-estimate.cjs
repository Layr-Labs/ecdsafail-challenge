'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U32 estimate anchor '+a);s=s.replace(a,()=>b);};
 one("if(name==='removeDebt')L.u32Debt=true;","if(name==='removeDebt')L.u32Debt=true;if(name==='estimate')L.u32Estimate=true;");
 one('    estimate(tape,back){',`    estimate(tape,back){
        if(this.u32Estimate){this.u32EstimateBody(tape,back);return;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u32EstimateBody(tape,back){
      if(this.k<113||this.k>123)throw Error('U32 estimate row scope');
      const H=Object.create(this.hostRank(this.dv[1]));H.tag=H.tag.slice();
      if(H.tag.length>=3)H.tag[2]=this.dv[0];
      if(this.k>=120)H.tag[1]=this.dv[1];
      const lease=this.k<=119;
      if(lease)H.tag[1]=this.v[this.k];
      H.tag=H.tag.map(q=>q===647?this.borrow:q);H.tag[0]=this.n.at(-1);
      const top=this.n.at(-1),low=this.n.slice(0,-1),Q=this.q,D=this.topDivisor(),g=this.ctrl;
      H.normalize=function(tp,rv){
        const prefix=rr=>stepList(split(1,this.tag.length).reverse(),rr,j=>{
          const d=1<<j,t=this.tag[j],orig=this.n.slice(-d).concat(this.n.slice(0,-d));
          const seq=[()=>this.toggle(tp,[this.take],this.n.slice(-d),t),bb=>this.permute(tp,this.n,orig,[this.take,t],bb)];stepList(seq,rr,fn=>fn(rr));
        });
        const seq=[prefix,()=>tp.out(NONE,this.take,top),
          rr=>this.permute(tp,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,top],rr),
          ()=>this.toggle(tp,[this.take,top],[],low[0])];
        if(lease&&!rv)tp.out(NONE,this.take,this.v[this.k]);
        stepList(seq,rv,fn=>fn(rv));
        if(lease&&rv)tp.out(NONE,this.take,this.v[this.k]);
      };
      H.digit=function(tp,z,v,controls,rv){this.digitTopOne(tp,z,v,controls,rv);};
      H.reducedTerm=function(tp,D,j,rv){
        const sel=this.carry,ctrl=this.ctrl,mark=()=>{this.indicator(tp,j,'eq',ctrl,sel);if(j<this.maxShift)this.indicator(tp,j,'gt',[...ctrl,this.n[j]],sel);};
        mark();
        if(j===0){const seq=[rr=>this.addTop(tp,D.slice(0,-1),this.q,[sel],rr),()=>tp.out(NONE,sel,this.q.at(-1))];stepList(seq,rv,fn=>fn(rv));}
        else tp.add(D.slice(0,this.q.length-j),this.q.slice(j),[sel],this.pick,rv);
        mark();
      };
      const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),
        ()=>this.cnotList(tape,g,Q.slice(0,-1)),
        ()=>{for(let i=0;i<Q.length-1;i++)this.toggle(tape,[...g,D[i]],[],Q[i]);}];
      for(let j=this.maxShift-1;j>=0;j--)seq.push(rv=>H.middleDigit(tape,j,D,rv));
      seq.push(rv=>this.inc(tape,Q,g,rv));
      for(let j=0;j<=this.maxShift;j++)seq.push(rv=>H.reducedTerm(tape,D,j,rv));
      for(let j=0;j<=this.maxShift;j++)seq.push(rv=>H.moveQuotient(tape,j,rv));
      seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv));
      stepList(seq,back,fn=>fn(back));
    }
`);
 return s;
};
