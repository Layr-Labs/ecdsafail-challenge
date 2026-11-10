'use strict';
// q650 upper (hole, integrator): ringhole q650-upper @ 11d0334 (hand-off 12ef380 + save2/trial savings), list WIDTH of upper/upper.cjs
// (coef, probe3, v112, trial, affv, aff4 [papers], aff0). Applied to the final q651 upper source before the 650 geometry.
// Upper logical 651 (tags[1]) is then never touched.
const u=require('./upper/upper.cjs');
const EXPECT=['p650-coef.js','width/p650-probe3.js','width/p650-v112.js','width/p650-trial.js','width/p650-affv.js','width/p650-aff4.js','width/p650-aff0.js','width/p650-save2.js'];
if(JSON.stringify(u.WIDTH)!==JSON.stringify(EXPECT))throw Error('q650 upper650: unexpected WIDTH list '+JSON.stringify(u.WIDTH));
module.exports={apply:s=>u.apply(s,u.WIDTH),LISTS:u.WIDTH};
