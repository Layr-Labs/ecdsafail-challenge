'use strict';
// q650 divide field list: the 651 field list, then the q650 divide rewrites applied to the final divide source d.
// Width/geometry unchanged (651); the integrator adds the 650 maps.
const path=require('path');
const rw=require('./divide650.cjs');
global.__q650div=rw;
module.exports=[...require(path.join(__dirname,'../../q651/p-field651.js')),
 ["function D2Reduced(n,j){return j===4?new D2ReducedImpl(n,5):","function D2Reduced(n,j){return j===4?new D2ReducedImpl(n,5):j===-4?new D2ReducedImpl(n,4):"],
 // 9-helper divide (Q650_HTOP_STAGE=full): divide logical 640 (Htop) is never touched, so the divide's sparse map
 // sends its logical 650 (L[129]) onto field logical 640 and removes 640 (a removed port throws). Field logical 650,
 // also freed by the multiply, is then unused by both field stages.
 ...(process.env.Q650_HTOP_STAGE==='full'?[["ids[i]=back&&i===651?646:i===move?647:i;","ids[i]=back&&i===651?646:back&&i===650?640:back&&i===640?-1:i===move?647:i;"]]:[]),
 ["const divide=Function('module','dirtyDigit','dirtyMdg'","d=global.__q650div(d);const divide=Function('module','dirtyDigit','dirtyMdg'"]];
