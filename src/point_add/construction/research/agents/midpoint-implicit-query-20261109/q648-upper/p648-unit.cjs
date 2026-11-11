'use strict';
// q648 (papers): EarlyUnit's qual predicate off f2 (647). qual = g & shape & ~a_top lives only between its two qual()
// toggles; LIVE=647 shows pick idle and zero across every such interval (forward and under retirePredicate), so qual
// is renamed onto pick for the unit row. Env Q648_UNIT=0 disables; Q648_UNITQ=<wire> overrides the host.
module.exports.upper=s=>{
  if(process.env.Q648_UNIT==='0')return s;
  const a=s.indexOf('class EarlyUnit extends UnitPreparation {'),e=s.indexOf('class EarlyGeneral extends',a);
  if(a<0||e<0)throw Error('q648 unit anchor');
  let body=s.slice(a,e);const n=body.split('this.qual').length-1;if(n!==2)throw Error('q648 unit qual count '+n);
  body=body.replace('    emit(tape,back){\n','    emit(tape,back){\n        const QH=process.env.Q648_UNITQ?+process.env.Q648_UNITQ:this.pick;if(QH===undefined||QH===this["qu"+"al"])throw Error("q648 unit host");\n');
  body=body.split('this.qual').join('QH');
  return s.slice(0,a)+body+s.slice(e);
};
