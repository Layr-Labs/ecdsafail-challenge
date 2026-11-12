"use strict";
// Apply once after n651a q651-ten-field upper(raw). All changes precede one sink.
exports.wholeStageFreed=true;
exports.sourceUpper=s=>require('./u-upper-helper-map.cjs').upper(require('./u-upper-u14.cjs').sourceUpper(s,{overlays:[require('./u-u11-witness.cjs').upper,require('./u-u12-carrier.cjs').upper]}));
// q648 (papers): Q648_PROBE=1 applies the f2-free sign probes (../q648-upper/p648-probe4.cjs; its own Q648_P4* switches default on) before the sink.
// q648 (hole): ringhole's order sourceUpper -> p648-affine -> p648-trial96 -> p648-probe4 -> p648-unit -> sink. Q648_AFFINE=1 = affine + trial96
// (ringhole: tested together); Q648_AFFINE=affine = affine only; Q648_PROBE=1 papers' probes; Q648_UNIT=1 papers' EarlyUnit qual off 647.
// Extra Q648_AFFINE tokens (ringhole's tested order): ltrial = ledger q648w/p648-trial.cjs (rows 0..63 trial+witness, after trial96, before probes);
// flag = papers p648-flag (rows 113..127 flag probes; needs Q648_F113=1), after unit; u7, r113 = ringhole p648-u7 / p648-r113 (rows 113..127).
// r112p = ringhole p648-r112p (row 112 original trial as a 2-pass on its direction bit), after trial96, before ltrial.
// Full 647-free stack: Q648_AFFINE=1,r112p,ltrial,flag,u7,r113 + Q648_PROBE=1 + Q648_UNIT=1 + Q648_F113=1.
const q648Overlays=s=>{const a=(process.env.Q648_AFFINE||'').split(',');if(a.includes('1')||a.includes('affine'))s=require('../q648-upper/p648-affine.cjs').upper(s);
 if(a.includes('1')||a.includes('trial'))s=require('../q648-upper/p648-trial96.cjs').upper(s);if(a.includes('r112p'))s=require('../q648-upper/p648-r112p.cjs').upper(s);if(a.includes('ltrial'))s=require('../q648w/p648-trial.cjs').upper(s);if(process.env.Q648_PROBE==='1')s=require('../q648-upper/p648-probe4.cjs').upper(s);
 if(process.env.Q648_UNIT==='1')s=require('../q648-upper/p648-unit.cjs').upper(s);if(a.includes('flag'))s=require('../q648-upper/p648-flag.cjs').upper(s);
 if(a.includes('u7'))s=require('../q648-upper/p648-u7.cjs').upper(s);if(a.includes('r113'))s=require('../q648-upper/p648-r113.cjs').upper(s);return s;};
exports.upper=s=>require('./u-p-upper-peep.cjs').upper(q648Overlays(exports.sourceUpper(s)));
