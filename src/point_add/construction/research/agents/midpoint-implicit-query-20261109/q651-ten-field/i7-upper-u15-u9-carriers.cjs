'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U9 anchor '+a);s=s.replace(a,()=>b);};
 one('if(this.k>=84&&this.k<=95){H.tag=H.tag.slice();H.tag[0]=this.A[this.half-1];', 'if(this.k>=64&&this.k<=95){H.tag=H.tag.slice();H.tag[0]=this.A[this.half-1];');
 // U7's independent one-band k127 width-selector change.
 if(!s.includes('const flag=this.k===127?this.pick:this.tags[0],on=[this.g,flag];'))
  one('const flag=this.tags[0],on=[this.g,flag];','const flag=this.k===127?this.pick:this.tags[0],on=[this.g,flag];');
 // V is not an arithmetic operand in a sign probe. Its leading bit is one
 // on active rows; all leases are returned even on inactive inputs.
 one('    signProbe(tape,target,back){\n      if(this.u5CleanPhase',`    signProbe(tape,target,back){
      if(this.k>=120&&this.k<=126 || this.k===119&&target===this.dv[0]){
        const H=Object.create(this);H.tags=this.tags.slice();H.tags[0]=this.v[this.k];H.u9Lead=true;H.u38ProbeLease=true;
        const tp=Object.create(tape);tp.ids=tape.ids.filter(q=>q!==this.v[this.k]);
        tape.out(NONE,this.take,this.v[this.k]);super.signProbe.call(H,tp,target,back);tape.out(NONE,this.take,this.v[this.k]);return;
      }
      if(this.u5CleanPhase`);
 one('if(this.k>=96&&this.k<=119){\n            const H=Object.create(this);H.tags=', 'if(!this.u9Lead&&this.k>=96&&this.k<=119){\n            const H=Object.create(this);H.tags=');
 one('if(this.k<=112&&this.u5PhaseHost===undefined){H.u40Probe=true;H.u6ProbeSlot=0;}', 'if(this.k<=119&&this.u5PhaseHost===undefined){H.u40Probe=true;H.u6ProbeSlot=0;}');
 one('(this.k===96||this.k===111||this.k===112)', '(this.k===96||this.k===111||this.k===112||this.k===119)');
 one('F.take=this.u6ProbeSlot===0?this.aux[3]:this.tags[0];', 'F.take=this.k===119?this.v[this.k]:this.u6ProbeSlot===0?this.aux[3]:this.tags[0];');
 one('F.ctrl=[this.g,F.take];','F.ctrl=this.k===119?[this.g,this.take,F.take]:[this.g,F.take];');
 return s;
};
