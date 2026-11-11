'use strict';
// Incremental extension AFTER selected U41. No sink, allocator, or frame swaps.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U44 selected-U41 anchor '+a);s=s.replace(a,()=>b);};
 one('H.r.length-H.ab<=12){H.u34UnarySign(tape,target);return;}', 'H.r.length-H.ab<=15){H.u34UnarySign(tape,target);return;}');
 one('    u40Sign(tape,target){', '    u40Sign(tape,target){\n      if(this.k===112&&this.u5PhaseHost!==target){this.u34UnarySign(tape,target);return;}\n');
 return s;
};
// Canonical U37 metadata, exact target/direction/phase guards; all else delegates.
exports.select=w=>w.kind==='signProbe'&&w.phaseHost!==w.args[0]&&(
 (w.k===112&&!w.back&&w.args[0]===644)||
 (w.k===113&&(w.args[0]===644||w.args[0]===370))||
 (w.k===114&&w.args[0]===371)
)?{evict:643,reason:'U44 late prefix F<=15; carry643 clean and absent'}:null;
exports.wholeStageFreed=false;
exports.probeBodiesFreed=288;
