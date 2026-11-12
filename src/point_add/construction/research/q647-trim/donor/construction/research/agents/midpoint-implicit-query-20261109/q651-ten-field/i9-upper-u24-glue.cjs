'use strict';
// Incremental source overlay AFTER U19 source, BEFORE the sole W4096 sink.
exports.upper=s=>{
 const anchor='      if(this.k!==127){super.core(tape,back);return;}';
 if(s.split(anchor).length!==2)throw Error('U24 requires U19 core');
 if(s.split('    u16Sign(inputTape,target){').length!==2)throw Error('U24 requires U16 probe source');
 return s.replace(anchor,`      if(this.k>=113&&this.k<=126){this.u24Core(tape,back);return;}
${anchor}`).replace('    u16Sign(inputTape,target){',`    u24Core(tape,back){
      const q=this.q,v=this.v,g=this.ctrl,flag=this.dv[0];
      const coef=rv=>this.mixed(tape,q,v,this.u,g,rv),seq=[];
      // p=HV+rU, V>=2^k, r>=2^half imply q<2^(half-k).
      for(let j=this.half-this.k-1;j>=0;j--){
        const high=this.r.slice(this.m-this.k-j); // Exact zero-bit bound for tall r.
        seq.push(()=>this.toggle(tape,g,high,q[j]),rv=>this.inc(tape,q,g,rv),coef,
          rv=>this.flagProbe(tape,flag,0,rv),rv=>coef(!rv),rv=>this.inc(tape,q,g,!rv),
          ()=>this.toggle(tape,[...g,flag],[],q[j]),
          ()=>this.toggle(tape,g,[q[j],...high],flag));
      }
      seq.push(rv=>this.inc(tape,q,g,rv),coef,rv=>this.affine(tape,rv),
        rv=>this.permute(tape,[...this.bank,...this.u,...q.slice(-2)],
          [...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],g,rv));
      stepList(seq,back,fn=>fn(back));
    }
    u16Sign(inputTape,target){`);
};
