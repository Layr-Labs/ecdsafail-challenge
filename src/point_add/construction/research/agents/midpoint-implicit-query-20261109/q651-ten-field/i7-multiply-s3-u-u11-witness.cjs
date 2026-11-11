'use strict';
// Incremental SOURCE overlay after U8. No emitted-stream rewrites.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U11 anchor '+a);s=s.replace(a,()=>b);};
 one('if(!witness){layer.tag[0]=this.qtop;layer.u8Relay=true;}',
     'if(!witness){layer.tag[0]=this.qtop;layer.u8Relay=true;}else{layer.tag[0]=this.qtop;layer.u11Witness=true;}');
 one('    u39Normalize(tape,back){',`    u39Normalize(tape,back){
      if(this.u11Witness){this.u11Normalize(tape,back);return;}
`);
 one('    oddWitness(tape,B,back){\n      if(!this.u39Trial)',`    oddWitness(tape,B,back){
      if(this.u11Witness){this.u11Band(tape,B,back);return;}
      if(!this.u39Trial)`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u11Normalize(tape,back){
      const H=Object.create(this),n=this.n,top=n.at(-1),low=n.slice(0,-1),q=this.tag[0];
      H.tag=this.tag.slice();H.tag[1]=q;
      const large=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const d=1<<j,t=H.tag[j],orig=n.slice(-d).concat(n.slice(0,-d));
        const seq=[()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>H.permute(tape,n,orig,[this.take,t],rr)];
        stepList(seq,rv,fn=>fn(rv));
      });
      const seq=[large,()=>tape.out(NONE,this.take,top),
        rv=>this.permute(tape,[top,q],[q,top],[this.take],rv),
        rv=>this.permute(tape,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,q],rv),
        ()=>this.toggle(tape,[this.take,q],[],low[0])];
      stepList(seq,back,fn=>fn(back));
    }
    u11Band(tape,B,back){
      const host=B.T.at(-1),H=Object.create(this);H.tag=this.tag.slice();H.tag[0]=host;H.u11Witness=false;
      const swap=rv=>this.permute(tape,[this.tag[0],host],[host,this.tag[0]],[],rv);
      swap(false);
      H.u39Divisor(tape,B,(J,rv)=>J.u11Predicate(tape,B),back);
      swap(true);
    }
    u11Predicate(tape,B){
      const top=-1101,T=B.T.slice(0,-1).concat(top),flag=this.dv[0],ctrl=[this.g,this.take,-19],owner=this;
      const phase=this.measureTarget===flag,target=phase?this.zword.at(-1):flag;
      const hidden=[...this.tag,...this.tags,flag,target,this.take,this.g];
      const tp=Object.create(tape);tp.loan=(used,n)=>tape.loan([...used,...hidden],n);
      const flips=new Set(),tags=new Set(this.tag),guards=[];
      if(this.inUpperHalf)guards.push({yes:[this.g,this.take],no:[]});
      guards.push({yes:[this.g,this.take],no:this.tag.slice(3)});
      if(this.packedShort)guards.push({yes:[this.g,this.take,this.tag[3]],no:this.tag.filter((q,i)=>i!==3)});
      const accumulate=(a,b)=>{
        for(const guard of guards){
          const yes=[a,b].filter(q=>q!==NONE),no=[];
          for(const q of guard.yes)(flips.has(q)?no:yes).push(q);
          for(const q of guard.no)(flips.has(q)?yes:no).push(q);
          if(yes.some(q=>no.includes(q)))continue;
          owner.toggle(tape,[...new Set(yes)],[...new Set(no)],target);
        }
      };
      let deposit=true;
      tp.out=(a,b,t)=>{
        if(a===top||b===top)throw Error('U11 virtual high read');
        if(t!==top){
          if(tags.has(t)){
            if(a!==NONE||b!==NONE)throw Error('U11 non-X rank mutation');
            if(flips.has(t))flips.delete(t);else flips.add(t);
          }
          tape.out(a,b,t);return;
        }
        if(deposit)accumulate(a,b);
      };
      const pre=[rv=>this.inc(tp,T,[],rv),rv=>this.oddProduct(tp,T,B.D,[],rv),rv=>this.lowReflect(tp,T,B.w,[],rv)];
      this.toggle(tape,ctrl,[],target);
      stepList(pre,false,fn=>fn(false));
      if(phase)tape.z(target);
      deposit=phase;
      stepList(pre,true,fn=>fn(true));
      if(flips.size)throw Error('U11 rank frame not restored');
      if(phase){this.toggle(tape,ctrl,[],target);tape.z(target);tape.z(flag);}
    }
`);
 return s;
};

