'use strict';
// SOURCE-ONLY incremental overlay. Ordinary trials use compressed count and evict flag644.
exports.wholeStageFreed=false;
exports.interface={kind:'trial',rows:[0,112],witness:false,evicted:644,helpers:[256,642,643,645,646,648],physical:[512,641,642,644,643,645],sign:{logical:649,physical:646},boundaryTransportImplemented:false};
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U30 anchor '+a);s=s.replace(a,()=>b);};
 one('if(witness&&this.k<=95)layer.u26=true;', 'if(this.k<=95){layer.u26=true;layer.tag[2]=this.carry;}if(!witness&&this.k>=96&&this.k<=111){layer.u17LateNorm=false;layer.tag=[this.qtop,this.n.at(-1),this.carry,this.pick,this.borrow];layer.u6TrialSlot=1;layer.u8Relay=true;}if(!witness&&this.k===112){layer.tag[2]=this.carry;layer.u17Carry=true;layer.uLift=true;}');
 one('    oddQuotient(tape,B,back){\n      if(!this.u39Trial)',`    oddQuotient(tape,B,back){
      if(this.u26&&!this.u30Band){const H=Object.create(this);H.u30Band=true;const tp=H.u26Tape(tape);H.oddQuotient(tp,B,back);tp.u26Check();return;}
      if(!this.u39Trial)`);
 one('    trial(tape,witness,back){\n\n',`    trial(tape,witness,back){
      if(!witness&&this.k<=112&&!this.u30Trial){
        const H=Object.create(this);H.u30Trial=true;
        const tp=Object.create(tape);tp.ids=tape.ids.filter(q=>q!==644);
        tp.out=(a,b,t)=>{if([a,b,t].includes(644))throw Error('U30 evicted644 use '+[this.k,a,b,t]);tape.out(a,b,t);};
        H.trial(tp,witness,back);return;
      }

`);
 one('if(this.k<=95&&!witness&&!this.u8Entered){','if(this.k<=111&&!witness&&!this.u8Entered){');
 return s;
};

