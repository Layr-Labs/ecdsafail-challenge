'use strict';
const {optimizeStream}=require('./commute.cjs');
const field=require('../q651-ten-field/multiply.cjs'), history=require('../q651-ten-field/regen.cjs');
function emitMultiplySparse(sink){optimizeStream(field.emitMultiplySparse,sink);}
function emitDivideSparse(sink){optimizeStream(field.emitDivideSparse,sink);}
function emitRegenerateSparse(sink,erase=false){
    optimizeStream(visitor=>history.emitRegenerateSparse(gs=>visitor('packed',gs),erase),
        (kind,gates)=>{if(kind!=='packed')throw Error('unexpected history event');sink(gates);});
}
module.exports={emitMultiplySparse,emitDivideSparse,emitRegenerateSparse};
