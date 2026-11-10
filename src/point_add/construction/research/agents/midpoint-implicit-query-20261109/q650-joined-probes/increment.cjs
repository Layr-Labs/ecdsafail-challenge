'use strict';
// Conjugating subtraction by bitwise NOT on both n-bit words changes
// x -= d into x += ~d. Preceding it by x += d therefore gives x -= 1.
function sharedConditionalIncrement(tape,b,controls,dirtyWord,loans,inverse){
    const cs=controls.filter(q=>q!==tape.one),n=b.length;
    if(!n||!cs.length||cs.some(q=>q<0)||new Set(cs).size!==cs.length)return false;
    if(n===1){
        tape.mc(cs,b[0],loans);return true;
    }
    if(dirtyWord.length!==n||loans.length<Math.max(0,cs.length-2))return false;
    const all=[...b,...dirtyWord],occupied=new Set([...all,...cs]);
    if(occupied.size!==2*n+cs.length)return false;
    const rest=loans.filter(w=>!occupied.has(w));
    if(rest.length<Math.max(0,cs.length-2))return false;
    const flip=()=>{
        if(cs.length===1){for(const q of all)tape.out(1023,cs[0],q);return;}
        const first=all[0];
        for(let i=1;i<all.length;i++)tape.out(1023,first,all[i]);
        tape.mc(cs,first,rest);
        for(let i=1;i<all.length;i++)tape.out(1023,first,all[i]);
    };
    if(inverse){
        tape.equal(dirtyWord,b,[],null,false,rest);
        flip();tape.equal(dirtyWord,b,[],null,true,rest);flip();
    }else{
        flip();tape.equal(dirtyWord,b,[],null,false,rest);flip();
        tape.equal(dirtyWord,b,[],null,true,rest);
    }
    return true;
}
function patchIncrement(source){
    const def='class Tape {',anchor='    increment(b,controls,dirtyWord,loans,inverse=false) {';
    for(const s of [def,anchor])if(source.split(s).length!==2)throw Error('increment anchor '+s);
    return source.replace(def,()=>sharedConditionalIncrement.toString()+'\n'+def).replace(anchor,()=>anchor+'\n        if(sharedConditionalIncrement(this,b,controls,dirtyWord,loans,inverse))return;');
}
module.exports={sharedConditionalIncrement,patchIncrement};
