'use strict';
// Apply after U4. Partial U5: does not claim complete 649.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U5 anchor '+a);s=s.replace(a,()=>b);};
 one('o.measureTarget=wire;emit();o.measureTarget=null;', 'o.measureTarget=wire;o.u5CleanPhase=wire;emit();o.u5CleanPhase=null;o.measureTarget=null;');
 one('function phaseDeposit(o,tape,wire,write){write();if(o.measureTarget===wire){tape.z(wire);write();}}',`function phaseDeposit(o,tape,wire,write){
 if(o.u5PhaseHost===wire){
   const dirty=o.zword.at(-1);write(dirty);tape.z(dirty);write(dirty);tape.z(dirty);
   return;
 }
 write(wire);if(o.measureTarget===wire){tape.z(wire);write(wire);}
}`);
 one('u40Deposit(tape,target,S,word){','u40Deposit(tape,target,S,word){\n      const phaseTarget=target;if(this.u5PhaseHost===target)target=this.zword.at(-1);');
 one('phaseDeposit(this,tape,target,()=>{\n        write(c);','phaseDeposit(this,tape,phaseTarget,()=>{\n        write(c);');
 one('phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);','phaseDeposit(this,tape,target,(target)=>{this.toggle(tape,this.ctrl,[],target);');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    signProbe(tape,target,back){
      if(this.u5CleanPhase===target&&this.k<=112){
        const H=Object.create(this);H.tags=this.tags.slice();H.tags[0]=target;H.u5PhaseHost=target;
        const tp=Object.create(tape);tp.ids=tape.ids.filter(q=>q!==target&&q!==this.zword.at(-1));
        H.alignedSign(tp,target);return;
      }
      super.signProbe(tape,target,back);
    }
`);
 const guard='this.tag[this.u37Slot||2]';
 if(s.split(guard).length!==2)throw Error('U5 affine guard');
 s=s.replace(guard,'this.tag[this.u37Slot??2]');
 const a='if(!this.deep){super.affine.call(H,tape,back);return;}';
 if(s.split(a).length!==2)throw Error('U5 affine anchor');
 return s.replace(a,`if(this.k>=96&&this.k<=119){H.tag=H.tag.slice();H.tag[0]=this.v[this.k];H.u37Slot=0;H.u3Affine=true;
        if(this.k>=112){const R=this.hostRank(this.pick);H.tag[3]=R.tag[3];H.rankHost=R.rankHost;H.digit=R.digit;}
      }
      if(this.k>=120&&this.k<=126){H.tag=H.tag.slice();H.tag[0]=this.A[this.half];}
      ${a}`);
};
