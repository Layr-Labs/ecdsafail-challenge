'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U23 late anchor '+a);s=s.replace(a,()=>b);};
 one('    packNumber(tape,back){this.mixed(tape,this.r,this.v,this.u,[],back);}',`    packNumber(tape,back){
      if(this.u23Late){this.u23LiteralV(tape,this.pick,H=>H.mixed(tape,H.r,H.v,H.u,[],back));return;}
      this.mixed(tape,this.r,this.v,this.u,[],back);
    }`);
 // Carry flag 2 on V's known leading bit; relay it to clean arithmetic gaps.
 one('        const q=this.q,v=this.v,u=this.u,ctrl=this.ctrl,coef=rv=>this.mixed(tape,q,v,u,ctrl,rv);',`        if(this.k>=113){this.u23Core(tape,back);return;}
        const q=this.q,v=this.v,u=this.u,ctrl=this.ctrl,coef=rv=>this.mixed(tape,q,v,u,ctrl,rv);`);
 one('    signProbe(tape,target,back){\n      if(this.k>=120',`    signProbe(tape,target,back){
      if(this.u23Late){this.u23LateProbe(tape,target,back);return;}
      if(this.k>=120`);
 one('    removeDebt(tape,back){',`    removeDebt(tape,back){
        if(this.u23Late){this.u7Debt(tape,back);return;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u23LiteralV(tape,spare,body){
      const host=this.v[this.k],H=Object.create(this);H.u23Late=false;
      const swap=()=>{tape.out(NONE,host,spare);tape.out(NONE,spare,host);tape.out(NONE,host,spare);};
      swap();tape.out(NONE,this.take,host);body(H);tape.out(NONE,this.take,host);swap();
    }
    u23Core(inputTape,back){
      const H=Object.create(this),host=this.v[this.k],tape=Object.create(inputTape);
      tape.ids=inputTape.ids.filter(q=>q!==host);H.u23Late=true;H.dv=[this.dv[0],host];
      const q=this.q,v=this.v,u=this.u,ctrl=this.ctrl,coef=rv=>this.mixed(tape,q,v,u,ctrl,rv),virtualCoef=rv=>H.u23LiteralV(tape,this.carry,L=>L.mixed(tape,q,v,u,[this.take],rv));
      const lease=()=>tape.out(NONE,this.take,host);
      const correct=(flag,rv)=>H.u23LiteralV(tape,this.pick,L=>tape.add(v,this.A,[...ctrl,flag===host?this.pick:flag],this.carry,!rv));
      const twoPad=q.slice(-2),seq=[rv=>this.estimate(tape,rv),coef,lease,
        rv=>H.flagProbe(tape,H.dv[0],0,rv),rv=>correct(H.dv[0],rv),
        rv=>H.flagProbe(tape,H.dv[1],1,rv),rv=>correct(H.dv[1],rv),
        rv=>virtualCoef(!rv),rv=>H.removeDebt(tape,rv),lease,coef,rv=>this.affine(tape,rv),
        rv=>this.permute(tape,[...this.bank,...u,...twoPad],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],ctrl,rv)];
      stepList(seq,back,fn=>fn(back));
    }
    u23LateProbe(inputTape,target,back){
      const H=Object.create(this),tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==647&&q!==this.v[this.k]);
      tape.out=(a,b,z)=>{if([a,b,z].includes(647))throw Error('U23 late probe ban647 '+[this.k,a,b,z]);inputTape.out(a,b,z);};
      H.probeBack=back;H.u38ProbeLease=true;
      if(target===this.dv[1]||this.k===127)Object.defineProperty(H,'ab',{value:this.half+1});
      if(H.r.length<=H.ab){H.u40FixedRank=0;H.u40FixedSign(tape,target);return;}
      // Always retain four rank positions. The extra high position is zero when F<8.
      H.tags=this.tags.slice();H.tags[3]=target===this.dv[0]?this.dv[1]:this.A.at(-1);
      H.u23LateCode=true;if(H.r.length-H.ab<=11)H.u6DoubleSign(tape,target);else H.u9ThreeSign(tape,target);
    }
`);
 one('const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q),tag=rankTag.concat(S[2]);',
 `const rankTag=this.probeTag(base,this.tags.slice(0,this.u23LateCode?Math.max(4,bits):bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q),tag=rankTag.concat(S[2]);`);
 one("if(bits<4||free+12>=2**(bits+1))throw Error('U9 capacity '+this.k);", "if(!this.u23LateCode&&(bits<4||free+12>=2**(bits+1)))throw Error('U9 capacity '+this.k);");
 one('const high=this.r.slice(base),top=2**bits;', 'const high=this.r.slice(base),top=2**rankTag.length;');
 one('for(let rank=0;rank<3;rank++){', 'for(let rank=0;rank<3&&rank<=free;rank++){');
 one('const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);\n      if(this.u18Lead)',
     'const tag=this.probeTag(base,this.tags.slice(0,this.u23LateCode?Math.max(4,bits):bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);\n      if(this.u18Lead)');
 one('const max=2**bits-1,codes=[max-2,max-1,max,max-3];','const max=2**tag.length-1,codes=[max-2,max-1,max,max-3];');
 return s;
};
