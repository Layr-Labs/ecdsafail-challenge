'use strict';

// Decompose [x<L] into the disjoint first differing bits, comparing in either
// direction and choosing the cheaper native gate sequence. Only the frozen
// ordinary comparator is replaced; the rank grammar still owns its correction.
function shortBelow(owner,tape,word,limit,controls,targets){
    const n=word.length;
    if(n>13||!n||limit<=0n||limit>=(1n<<BigInt(n))||!targets.length)return false;
    if(word.includes(tape.one)||new Set(word.concat(controls,targets)).size!==word.length+controls.length+targets.length)return false;
    const active=controls.filter(q=>q!==tape.one);
    function mcCost(k){return k<=1?0:k===2?1:4*k-8;}
    function build(c,invert){
        const terms=invert?[[active.slice(),[]]]:[],positive=active.slice(),negative=[];
        for(let i=n-1;i>=0;i--){
            const bit=(c>>i)&1;
            if(bit!==Number(invert)){
                terms.push(bit?[positive.slice(),negative.concat(word[i])]:[positive.concat(word[i]),negative.slice()]);
            }
            (bit?positive:negative).push(word[i]);
        }
        const price=terms.reduce((sum,term)=>sum+mcCost(term[0].length+term[1].length),0)*targets.length;
        return {terms,price};
    }
    const L=Number(limit),below=build(L,false),above=build(L-1,true);
    const which=below.price<=above.price?below:above;
    if(which.price>=4*n+2*mcCost(active.length))return false;
    for(const [yes,no] of which.terms)for(const t of targets){
        WordArithmetic.prototype.toggle.call(owner,tape,yes,no,t);
    }
    return true;
}

function patch(s){
    const c='class Tape {',p='if(tape.frontierThreshold){tape.frontierThreshold(word,limit,controls,targets);return;}';
    if(s.split(c).length!==2||s.split(p).length!==2)throw Error('ordinary comparator source');
    return s.replace(c,()=>shortBelow.toString()+'\n'+c).replace(p,()=>p+'\n        if(shortBelow(this,tape,word,limit,controls,targets))return;');
}
module.exports={patch,shortBelow};
