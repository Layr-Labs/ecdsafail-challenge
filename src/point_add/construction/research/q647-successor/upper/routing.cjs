'use strict';

// A family of left/right rotations that differs only by a few excluded cells.
// First use the full-word permutation. Each successive branch changes it by
// exactly the relative permutation, which fixes almost every destination.
function sparseRotations(owner,tape,word,d,common,selectors,subwords,back){
    if(new Set(word).size!==word.length||common.some(q=>word.includes(q))||word.includes(selectors[0]))return false;
    const sequence=[];let previous=word;
    for(let j=0;j<subwords.length;j++){
        const sub=subwords[j],rot=d%sub.length;
        const origins=rot?sub.slice(-rot).concat(sub.slice(0,-rot)):sub;
        const from=new Map(sub.map((w,i)=>[w,origins[i]]));
        const desired=word.map(w=>from.get(w)??w),at=new Map(previous.map((w,i)=>[w,word[i]]));
        const active=[],mapped=[],controls=common.concat(selectors.slice(0,j));
        for(let i=0;i<word.length;i++){
            const w=at.get(desired[i]);
            if(w!==word[i]){active.push(word[i]);mapped.push(w);}
        }
        if(controls.some(q=>active.includes(q)||(word.includes(q)&&previous[word.indexOf(q)]!==q)))return false;
        sequence.push(rv=>owner.permute(tape,active,mapped,controls,rv));
        previous=desired;
    }
    stepList(sequence,back,f=>f(back));return true;
}

function patch(source){
    let s=source;
    const c='class Tape {';
    if(s.split(c).length!==2)throw Error('Q647 sparse permutation install');
    s=s.replace(c,()=>sparseRotations.toString()+'\n'+c);
    function method(name,next,anchor,body){
        const start=s.indexOf('    '+name+'(tape,back){'),end=s.indexOf('\n    '+next+'(',start);
        if(start<0||end<=start)throw Error('Q647 routing method '+name);
        const text=s.slice(start,end);if(text.split(anchor).length!==2)throw Error('Q647 routing body '+name);
        s=s.slice(0,start)+text.replace(anchor,()=>anchor+'\n        '+body)+s.slice(end);
    }
    method('u38Normalize','u38Bias','const short=word.filter(w=>!C.xyz.includes(w));',
        'if(sparseRotations(this,tape,word,d,[this.take,t],[C.c],[word,short],rv))return;');
    method('u42Normalize','u42Tape','const partial=word.filter(w=>w!==x),short=word.filter(w=>!C.xyz.includes(w));',
        'if(sparseRotations(this,tape,word,d,[this.take,t],[C.c,x],[word,partial,short],rv))return;');
    method('u43Normalize','u43Witness','const short=word.filter(q=>q!==C.x&&q!==C.y);',
        'if(sparseRotations(this,tape,word,d,[this.take,t],[C.c],[word,short],rv))return;');
    method('u26Normalize','u26Bias','const short=word.filter(w=>w!==C.x&&w!==C.y);',
        'if(sparseRotations(this,tape,word,d,[this.take,bit],[C.c],[word,short],rv))return;');
    return s;
}
function install(research){
    const path=require('node:path');
    require('./index.cjs').install(research);
    const host=require(path.join(research,'q648-frontier/upper/six.cjs'));
    const before=host.patch;host.patch=(...args)=>patch(before(...args));
}
module.exports={patch,sparseRotations,install};
