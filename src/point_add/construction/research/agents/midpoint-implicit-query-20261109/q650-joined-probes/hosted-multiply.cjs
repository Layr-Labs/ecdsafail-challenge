'use strict';
const path=require('node:path');
const {implicitTopDigit}=require('./implicit-top.cjs');
function install(q){
    const patch=require(path.join(q,'multiply-nine.cjs')),old=patch.walk;
    patch.walk=(pub,bits=6)=>{
        const Base=old(pub,bits);
        return class extends Base{
            constantDigit(a,b,h,e){
                const self=this,tape={loan(used,n){const block=new Set(used);return self.y.filter(w=>!block.has(w)).slice(0,n);},
                    out(x,y,t){if(x===1023)self.raw(y===1023?-1:y,-1,t);else self.raw(x,y===1023?-1:y,t);}};
                implicitTopDigit(tape,[...b,h],[...a,-1001],[e],false);
            }
        };
    };
}
module.exports={install};
