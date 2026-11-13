'use strict';
// U24 k124 emits only predicate dv[0]. Preserve the inherited wider standalone
// flagProbe API for its unused carry-target call; it is not a 647-covered window.
exports.upper=s=>{
 const a='        if(this.k===124){\n          const H=Object.create(this),tp=Object.create(tape);H.u40Probe=true;';
 if(s.split(a).length!==2)throw Error('U40 k124 API anchor');
 return s.replace(a,'        if(this.k===124&&target===this.dv[0]){\n          const H=Object.create(this),tp=Object.create(tape);H.u40Probe=true;');
};
