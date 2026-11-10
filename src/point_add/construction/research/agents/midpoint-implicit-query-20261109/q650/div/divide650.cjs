'use strict';
// q650 divide source rewrites, applied in order to the final 651 divide source text.
const st=process.env.Q650_HTOP_STAGE;
const steps=[require('./alpha-bucket.cjs'),...(st?[require('./htop.cjs')]:[]),...(st==='full'?[d=>require('./efree.cjs').efree(d),d=>require('./ipark-htop.cjs').iparkHtop(d),d=>require('./wind-htop.cjs').windHtop(d)]:[])];
module.exports=function(d){for(const f of steps)d=f(d);return d;};
