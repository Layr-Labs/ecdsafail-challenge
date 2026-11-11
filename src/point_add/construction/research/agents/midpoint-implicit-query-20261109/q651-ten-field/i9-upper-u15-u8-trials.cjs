'use strict';
// Apply after U6; source transformation, no emitted-circuit edits.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U8 anchor '+a);s=s.replace(a,()=>b);};
 one('layer.u39Temp=witness?this.qtop:this.carry;layer.tag[1]=this.n.at(-1);',
     'layer.u39Temp=witness?this.qtop:this.carry;layer.tag[1]=this.n.at(-1);if(!witness){layer.tag[0]=this.qtop;layer.u8Relay=true;}');
 one('    u39Divisor(tape,B,run,back){',`    u39Divisor(tape,B,run,back){
      if(this.u8Relay){
        const host=B.T.at(-1);
        if(host===this.tag[0]||B.D.includes(host))throw Error('U8 band relay alias');
        const H=Object.create(this);H.u8Relay=false;H.u8Ones=true;H.tag=this.tag.slice();H.tag[0]=host;
        const swap=rv=>this.permute(tape,[this.tag[0],host],[host,this.tag[0]],[],rv);
        if(globalThis.__u8Host)globalThis.__u8Host(tape,this,B,host,back);
        const body=(J,rv)=>{const clear=()=>{if(B.lo)J.toggle(tape,[J.g,J.take,-19],J.q.slice(0,-1),J.qtop);};
          if(rv)clear();run(J,rv);if(!rv)clear();};
        swap(false);H.u39Divisor(tape,B,body,back);swap(true);return;
      }
`);
 one('      if(!this.useCoefficientDirection){super.trial(tape,witness,back);return;}',`
      if(this.k<=95&&!witness&&!this.u8Entered){
        const H=Object.create(this);H.u8Entered=true;
        const high=()=>this.toggle(tape,this.ctrl,this.q.slice(0,-1).concat(this.r.slice(this.half+1)),this.qtop);
        if(back)high();H.trial(tape,witness,back);if(!back)high();return;
      }
      if(!this.useCoefficientDirection){super.trial(tape,witness,back);return;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    onesBlock(tape,R,D,n,extra,ctrl,back){
      if(!this.u8Ones){super.onesBlock(tape,R,D,n,extra,ctrl,back);return;}
      const t=this.carry,origin=[...R,this.dv[0]],active=[...ctrl,...extra];
      if(this.tag[0]!==this.dv[0])throw Error('U8 recurrence host');
      this.toggle(tape,active,[],t);
      let remain=R.slice(),spare=this.dv[0];const seq=[];
      for(let j=0;j<n;j++){
        const input=spare,z=[input,...remain],high=z.at(-1);
        seq.push(rv=>{
          const v=D.slice(1),zz=z.slice(1),loan=tape.loan([...zz,...v,t,input],1)[0];
          stepList(dirtyDigit(v,zz.slice(0,-1),high,t,loan),rv,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op.at(-2):NONE,op.at(-1)));
        },()=>tape.out(NONE,t,high),rv=>this.permute(tape,[input,high],[high,input],[],rv));
        remain=z.slice(0,-1);spare=high;
      }
      seq.push(rv=>this.permute(tape,origin,[...remain,spare],[],rv));
      const shift=n%R.length,unrotate=R.slice(shift).concat(R.slice(0,shift));
      seq.push(rv=>{tape.out(NONE,NONE,t);this.permute(tape,R,unrotate,[t],rv);tape.out(NONE,NONE,t);});
      stepList(seq,back,fn=>fn(back));this.toggle(tape,active,[],t);
    }
`);
 return s;
};
