'use strict';
// Incremental overlay after the R38 partial upper. Only quotient/witness trials.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U1 anchor '+a);s=s.replace(a,()=>b);};
 one('layer.uLift=witness;layer.uSpare=!witness;', 'layer.uLift=witness;layer.uSpare=!witness;if(this.k<=95){layer.u39Trial=true;layer.u39Temp=witness?this.qtop:this.carry;layer.tag[1]=this.n.at(-1);}');
 one('work.n=packed.slice(0,-1);','work.n=packed.slice(0,-1);if(H.u39Trial){rank[1]=work.n.at(-1);}');
 one('    normalize(tape,back){\n',`    normalize(tape,back){
        if(this.u39Trial){this.u39Normalize(tape,back);return;}
`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u39Normalize(tape,back){
      const H=Object.create(this),tmp=this.u39Temp,top=this.n.at(-1),n=this.n;
      if(globalThis.__u39Host)globalThis.__u39Host(tape,this,back?'normalizer-inverse-entry':'normalizer-forward-entry',{tmp,top});
      H.tag=this.tag.slice();H.tag[1]=tmp;
      const norm=rv=>stepList(split(0,H.tag.length).reverse(),rv,j=>{
        const s=1<<j,t=H.tag[j],origins=n.slice(-s).concat(n.slice(0,-s));
        const seq=[()=>H.toggle(tape,[this.take],n.slice(-s),t),rr=>H.permute(tape,n,origins,[this.take,t],rr)];
        stepList(seq,rv,fn=>fn(rv));
      });
      const lease=rv=>{
        if(globalThis.__u39Host)globalThis.__u39Host(tape,this,rv?'norm-out':'norm-in',{tmp,top});
        const seq=[()=>tape.out(NONE,this.take,top),rr=>this.permute(tape,[top,tmp],[tmp,top],[this.take],rr)];
        stepList(seq,rv,fn=>fn(rv));
      };
      stepList([norm,lease],back,fn=>fn(back));
    }
    u39Divisor(tape,B,run,back){
      const H=Object.create(this),top=this.tag[1];H.tag=this.tag.slice();H.tag[1]=B.d0;
      if(globalThis.__u39Host)globalThis.__u39Host(tape,this,'band-entry',{B,top});
      H.u39Trial=false;H.u39LowOne=B.d0;
      const swap=rv=>{
        const seq=[rr=>this.permute(tape,[top,B.d0],[B.d0,top],[],rr),()=>tape.out(NONE,NONE,top)];
        stepList(seq,rv,fn=>fn(rv));
      };
      swap(false);
      H.roundedDivisor(tape,B,false);H.inUpperHalf=B.lo!==0;
      // run is a lexical closure over the original row: use an inner body supplied by caller.
      run(H,back);
      H.inUpperHalf=null;H.roundedDivisor(tape,B,true);swap(true);
    }
    roundedDivisor(tape,B,back){
      if(this.u39LowOne===undefined){super.roundedDivisor(tape,B,back);return;}
      const seq=[rv=>this.inc(tape,B.H,[],!rv),rv=>this.inc(tape,B.H.slice(1),[this.dv[1]],rv)];
      stepList(seq,back,fn=>fn(back));
    }
    digit(tape,z,v,controls,back){
      if(this.u39LowOne===undefined){super.digit(tape,z,v,controls,back);return;}
      this.u39Digit(tape,z,v,controls,back);
    }
    u39Digit(tape,z,v,controls,back){
      if(v[0]!==this.u39LowOne||controls.length!==1)throw Error('U1 implicit low-one ports');
      const loan=tape.loan([...z,...v,...controls],1)[0],ops=dirtyDigit(v,z.slice(0,-1),z.at(-1),controls[0],loan);
      stepList(ops,back,op=>{
        if(op.at(-1)===v[0])throw Error('U1 low divisor written');
        const cs=op.slice(0,-1).filter(q=>q!==v[0]);
        tape.out(cs.length===2?cs[0]:NONE,cs.length?cs.at(-1):NONE,op.at(-1));
      });
    }
    oddQuotient(tape,B,back){
      if(!this.u39Trial){super.oddQuotient(tape,B,back);return;}
      this.u39Divisor(tape,B,(H,rv)=>{H.digit=H.u39Digit;H.withDivisor=(tp,band,fn,rr)=>fn([H.g,H.take,-19],rr);OddEstimateGeneral.prototype.oddQuotient.call(H,tape,B,rv);},back);
    }
    oddWitness(tape,B,back){
      if(!this.u39Trial){super.oddWitness(tape,B,back);return;}
      this.u39Divisor(tape,B,(H,rv)=>{H.withDivisor=(tp,band,fn,rr)=>fn([H.g,H.take,-19],rr);OddEstimateGeneral.prototype.oddWitness.call(H,tape,B,rv);},back);
    }
`);
 return s;
};
