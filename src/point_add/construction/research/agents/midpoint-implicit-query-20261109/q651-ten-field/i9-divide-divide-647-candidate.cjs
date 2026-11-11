 'use strict';
const partial=require('./i9-divide-divide-647-partial.cjs');
function build(pub){const b=partial.build(pub,{d25:require('./i9-divide-complete-source.cjs')});return {...b,emitDivideSparse(sink,tap){b.emitDivideSparse((k,d)=>{const check=q=>{if([641,643,644,645,648].includes(q))throw Error('D26 forbidden ABI wire '+q);};if(k==='packed')for(const x of d){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else if(k==='nct')for(const r of d)r.forEach(check);else d.slice(0,-1).forEach(check);sink(k,d);},tap);}};}
module.exports={build,wholeStageFreed:true,helpers:[640,642,646,647,649,650],physicalHelpers:[512,641,642,643,644,645],signPassenger:646,status:'Candidate: qualification receipts required'};
