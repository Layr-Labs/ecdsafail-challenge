'use strict';
exports.upper=s=>{
 const a='    u40Sign(tape,target){',b=`    u40Sign(tape,target){
      if(this.k>=96&&this.k<=111){
        if(!this.u38ProbeLease)throw Error('U18 missing V lead lease');
        const H=Object.create(this);H.u18Lead=true;if(this.k===111)Object.defineProperty(H,'ab',{value:this.half+1});if(this.k<=99)H.u9ThreeSign(tape,target);else H.u6DoubleSign(tape,target);return;
      }`;
 if(s.split(a).length!==2)throw Error('U18 probe lead anchor');s=s.replace(a,()=>b);
 const a2='      const max=2**bits-1,codes=[max-2,max-1,max,max-3];';
 if(s.split(a2).length!==2)throw Error('U18 double anchor');
 s=s.replace(a2,()=>`      if(this.u18Lead){if(tag.at(-1)!==647)throw Error('U18 double expected647');tag[tag.length-1]=this.v[this.k];if(new Set(tag).size!==tag.length)throw Error('U18 double alias');}
${a2}`);
 const a3='      if(new Set(tag).size!==tag.length)throw Error(\'U9 tag collision\');';
 if(s.split(a3).length!==2)throw Error('U18 three anchor');
 s=s.replace(a3,()=>`      if(this.u18Lead){const j=rankTag.indexOf(647);if(j<0)throw Error('U18 three expected647');rankTag[j]=this.v[this.k];tag[j]=this.v[this.k];}
${a3}`);
 const a4='if(this.k<=119&&this.u5PhaseHost===undefined){H.u40Probe=true;H.u6ProbeSlot=0;}';
 if(s.split(a4).length!==2)throw Error('U18 reset probe dispatch');
 s=s.replace(a4,'if(this.k<=119&&(this.u5PhaseHost===undefined||this.k>=96&&this.k<=111)){H.u40Probe=true;H.u6ProbeSlot=0;}');
 return s;
};



