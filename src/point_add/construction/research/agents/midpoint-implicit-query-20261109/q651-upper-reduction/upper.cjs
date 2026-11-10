'use strict';
const base=require('../q651-ten-field/upper.cjs');
const {replace}=require('../q653-next/parts.cjs');
function upper(source){
    let code=base.upper(source);
    code=replace(code,'this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};',
        "const filter=require('../../../../agents/midpoint-implicit-query-20261109/q651-upper-reduction/pass.cjs').upperFilter(output);"+
        "this.endUpper=filter.flush;output=filter;this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};");
    code=replace(code,'const b=l.bank.length,R=D.slice(0,m-b),U=D.slice(m-b),',
        't.endUpper();const b=l.bank.length,R=D.slice(0,m-b),U=D.slice(m-b),');
    code=replace(code,'if(t.hist.size)throw Error("unfinished deferred phases");',
        'if(t.hist.size)throw Error("unfinished deferred phases");t.endUpper();');
    return code;
}
module.exports={upper};
