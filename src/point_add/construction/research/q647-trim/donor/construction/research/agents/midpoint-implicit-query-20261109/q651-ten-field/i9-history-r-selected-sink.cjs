'use strict';
exports.create=out=>{
 const index=require('./i9-history-s3-u-peep-index.cjs').createPeep(out,{window:65536});
 const frame=require('./i9-history-s3-u-peep-frame2.cjs').createPeep(index.gate,{window:4096});
 const swap=require('./i9-history-s3-u-peep-swap.cjs').createPeep(frame.gate,{window:4096,mode:'commute'});
 return {gate(a,b,t){if(t===645)throw Error('constant sentinel targeted');swap.gate(a===645?1023:a,b===645?1023:b,t);},flush(){swap.flush();frame.flush();index.flush();}};
};
