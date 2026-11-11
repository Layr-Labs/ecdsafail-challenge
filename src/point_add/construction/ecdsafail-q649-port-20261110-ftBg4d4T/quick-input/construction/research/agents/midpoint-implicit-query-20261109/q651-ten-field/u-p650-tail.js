'use strict';
// q650 upper saving: the probe's tail digits use the clean fused digit with f1 (=dv[0]) as its ancilla wherever f1 is
// provably zero: the whole retire probe (f1 was just reset by hmr; the phase deposit writes and unwrites it), and the
// compute half of a probe whose target is f1 (f1 is first written by the deposit). The other half keeps dirtyDigit,
// which is the same map as the clean digit with a zero ancilla, so the two halves remain exact inverses.
module.exports=[
 ['        stepList(seq,false,fn=>fn(false));\n        phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);',
  '        const f1z=target===this.dv[0]&&(this.measureTarget===target||!this.probeBack);this.f1Clean=f1z;\n        stepList(seq,false,fn=>fn(false));this.f1Clean=false;\n        phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);'],
 ['        stepList(seq,true,fn=>fn(true));\n    }\n    signProbe(tape,target,back){this.alignedSign(tape,target);}',
  '        this.f1Clean=f1z&&this.measureTarget===target;stepList(seq,true,fn=>fn(true));this.f1Clean=false;\n    }\n    signProbe(tape,target,back){this.probeBack=back;this.alignedSign(tape,target);}'],
 ['      const loan=tape.loan([...z,...S,this.take],1)[0];\n      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);',
  '      if(this.f1Clean){const L2=Object.create(layer);L2.pick=this.dv[0];MixedArithmetic.prototype.digit.call(L2,tape,z,S,[this.take],back);return;}\n      const loan=tape.loan([...z,...S,this.take],1)[0];\n      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);'],
];
