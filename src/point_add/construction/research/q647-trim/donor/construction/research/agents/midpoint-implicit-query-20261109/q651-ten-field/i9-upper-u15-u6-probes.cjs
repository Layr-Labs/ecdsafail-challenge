'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U6 probe anchor '+a);s=s.replace(a,()=>b);};
 one('H.tags[1]=this.v[this.k];H.u38ProbeLease=true;',
 `H.tags[1]=this.v[this.k];H.u38ProbeLease=true;
 if(this.k<=112&&this.u5PhaseHost===undefined){H.u40Probe=true;H.u6ProbeSlot=0;}`);
 one('if(this.k===64&&!this.u40Split){this.u40SplitSign(tape,target);return;}',
 'if((this.k===64||(this.u6ProbeSlot===0&&(this.k===96||this.k===111||this.k===112)))&&!this.u40Split){this.u40SplitSign(tape,target);return;}');
 one('target).map((q,i)=>i===2?this.carry:i===1?this.pick:q);',
 'target).map((q,i)=>i===2?this.carry:i===(this.u6ProbeSlot??1)?this.pick:q);');
 one('H.u40Tag=tag.slice();H.u40Tag[1]=S[0];','H.u40Tag=tag.slice();H.u40Tag[this.u6ProbeSlot??1]=S[0];');
 one('F.u40FixedRank=0;F.take=this.tags[0];', 'F.u40FixedRank=0;F.take=this.u6ProbeSlot===0?this.aux[3]:this.tags[0];');
 return s;
};
