'use strict';
// Incremental source overlay after U16 sourceUpper, BEFORE the one W4096 sink.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U17 anchor '+a);s=s.replace(a,()=>b);};
 one(' return layer;\n    }\n    // r36 U2:',` if(!witness&&this.k<=95){layer.u17Carry=true;layer.uLift=true;layer.tag[layer.tag.indexOf(647)]=this.carry;}
 if(this.k>=96&&this.k<=111){layer.u17LateNorm=true;layer.tag[layer.tag.indexOf(647)]=witness?this.qtop:this.carry;
   if(witness){layer.u11Witness=true;layer.u17BandSlot=layer.tag.length-1;}else{layer.u17Carry=true;layer.uLift=true;}}
 if(this.k===112&&this.u17DirectionRelay){layer.u17LateNorm=true;layer.dv=[this.dv[0],this.borrow];}
 return layer;
    }
    // r36 U2:`);
 one('    u39Normalize(tape,back){',`    u39Normalize(tape,back){
      if(this.u17LateNorm){this.u17Normalize(tape,back);return;}
      if(this.u17Carry){this.u11Normalize(tape,back);return;}`);
 one('const host=B.T.at(-1),H=Object.create(this);H.tag=this.tag.slice();H.tag[0]=host;H.u11Witness=false;',
     'const slot=this.u17BandSlot??0,host=B.T.at(-1),H=Object.create(this);H.tag=this.tag.slice();H.tag[slot]=host;H.u11Witness=false;');
 one('const swap=rv=>this.permute(tape,[this.tag[0],host],[host,this.tag[0]],[],rv);\n      swap(false);',
     'const swap=rv=>this.permute(tape,[this.tag[slot],host],[host,this.tag[slot]],[],rv);\n      swap(false);');
 one('    onesBlock(tape,R,D,n,extra,ctrl,back){\n      if(!this.u8Ones)',`    onesBlock(tape,R,D,n,extra,ctrl,back){
      if(this.u17Carry&&this.u8Ones){this.u17Ones(tape,R,D,n,extra,ctrl,back);return;}
      if(!this.u8Ones)`);
 one('      if(this.k<=95&&!witness&&!this.u8Entered){',`      if(this.k===112&&!this.u17DirectionRelay){
        const H=Object.create(this);H.u17DirectionRelay=true;H.dv=[this.dv[0],this.qtop];
        const high=()=>this.toggle(tape,this.ctrl,this.q.slice(0,-1).concat(this.r.slice(this.half+1)),this.qtop);
        const pack=this.packNumber;H.packNumber=function(tp,rv){
          const swap=rr=>this.permute(tp,[this.borrow,this.qtop],[this.qtop,this.borrow],[],rr);
          if(rv)swap(true);pack.call(this,tp,rv);if(!rv)swap(false);
        };
        if(back&&!witness)high();H.trial(tape,witness,back);if(!back&&!witness)high();return;
      }
      if(this.k<=95&&!witness&&!this.u8Entered){`);
 one('OddEstimateGeneral.prototype.oddQuotient.call(H,tape,B,rv);},back);',
     `const clear=()=>{if(H.u17DirectionRelay&&B.lo)H.toggle(tape,[H.g,H.take,-19],H.q.slice(0,-1),H.qtop);};
      if(rv)clear();OddEstimateGeneral.prototype.oddQuotient.call(H,tape,B,rv);if(!rv)clear();},back);`);
 one('    oddProduct(tape,T,D,ctrl,back){\n        if(this.uLift){',`    oddProduct(tape,T,D,ctrl,back){
        if(this.u17Carry){this.u17Product(tape,T,D,ctrl,back);return;}
        if(this.uLift){`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u17Product(tape,T,D,ctrl,back){
      stepList(split(0,T.length-1).reverse(),back,i=>{
        const src=D.slice(1,T.length-i),dst=T.slice(i+1),on=[...ctrl,T[i]];
        const loan=tape.loan([...T,...D,...this.tag,...this.tags,this.g,this.take,this.carry,this.pick,...ctrl],1)[0];
        const flip=()=>this.cnotList(tape,[loan],dst),mark=()=>this.toggle(tape,on,[],loan);
        const add=rv=>{if(dst.length>src.length)this.addTop(tape,src,dst,[loan],rv);else tape.add(src,dst,[loan],this.pick,rv);};
        const seq=[flip,mark,add,mark,rv=>add(!rv),flip];stepList(seq,back,fn=>fn(back));
      });
    }
    u17Normalize(tape,back){
      if(this.u38NormLease){const H=Object.create(this);H.u38NormLease=false;
        if(!back)tape.out(NONE,this.take,this.v[this.k]);H.u17Normalize(tape,back);if(back)tape.out(NONE,this.take,this.v[this.k]);return;}
      const n=this.n,top=n.at(-1),low=n.slice(0,-1);
      if(this.tag[0]!==top)throw Error('U17 late rank0 host');
      const large=rv=>stepList(split(1,this.tag.length).reverse(),rv,j=>{
        const d=1<<j,t=this.tag[j],orig=n.slice(-d).concat(n.slice(0,-d));
        const seq=[()=>this.toggle(tape,[this.take],n.slice(-d),t),rr=>this.permute(tape,n,orig,[this.take,t],rr)];
        stepList(seq,rv,fn=>fn(rv));
      });
      const seq=[large,()=>tape.out(NONE,this.take,top),
        rv=>this.permute(tape,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,top],rv),
        ()=>this.toggle(tape,[this.take,top],[],low[0])];
      stepList(seq,back,fn=>fn(back));
    }
    u17Ones(tape,R,D,n,extra,ctrl,back){
      {
        const origin=[...R,this.dv[0]];let remain=R.slice(),spare=this.dv[0];const seq=[];
        if(this.tag[0]!==this.dv[0])throw Error('U17 recurrence host');
        const enabled=(host,run)=>{
          if(this.inUpperHalf&&extra.length===1&&this.tag.indexOf(extra[0])>=(this.packedShort?4:3)){
            const q=extra[0];if(q===this.carry||q===this.pick){run(tape,q);return;}
            this.uControl(tape,[this.take,q],[],run);return;
          }
          const H=Object.create(this);H.tag=this.tag.map(q=>q===this.tag[0]?host:q);
          const yes=[...ctrl,...extra].map(q=>q===this.tag[0]?host:q);H.uControl(tape,yes,[],run);};
        for(let j=0;j<n;j++){
          const input=spare,z=[input,...remain],high=z.at(-1);
          seq.push(rv=>enabled(input,(tp,t)=>{
            const v=D.slice(1),zz=z.slice(1),loan=tp.loan([...zz,...v,t,input],1)[0];
            stepList(dirtyDigit(v,zz.slice(0,-1),high,t,loan),rv,op=>tp.out(op.length===3?op[0]:NONE,op.length>=2?op.at(-2):NONE,op.at(-1)));
          }),()=>enabled(input,(tp,t)=>tp.out(NONE,t,high)),rv=>this.permute(tape,[input,high],[high,input],[],rv));
          remain=z.slice(0,-1);spare=high;
        }
        seq.push(rv=>this.permute(tape,origin,[...remain,spare],[],rv));
        const shift=n%R.length,unrotate=R.slice(shift).concat(R.slice(0,shift));
        // R^-1 controlled by NOT e = unconditional R^-1 then R controlled by e.
        seq.push(rv=>this.permute(tape,R,unrotate,[],rv),rv=>enabled(this.tag[0],(tp,t)=>this.permute(tp,R,unrotate,[t],!rv)));
        stepList(seq,back,fn=>fn(back));
      }
    }
`);
 return s;
};
