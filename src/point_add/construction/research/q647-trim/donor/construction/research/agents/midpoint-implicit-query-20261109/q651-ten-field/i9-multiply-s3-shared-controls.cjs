'use strict';
// Build a controlled permutation from two involutions. The borrowed selector
// enters in an arbitrary state. For each involution L, applying L^d before
// and L^(d xor f) after a toggle of d applies L^f for either original d.
function sharedControlledPermutation(tape,word,origins,controls,back){
    const enabled=controls.filter(q=>q!==tape.one);
    const n=enabled.length;
    if(n<2||word.length<3||enabled.some(q=>q<0)||new Set(enabled).size!==n)return false;
    const where=new Map(word.map((w,i)=>[w,i]));
    if(where.size!==word.length||enabled.some(q=>where.has(q)))return false;
    const forward=origins.map(w=>where.get(w));
    if(forward.length!==word.length||forward.some(i=>i===undefined)||new Set(forward).size!==word.length)throw Error('invalid permutation');
    const marked=new Uint8Array(word.length),first=[],second=[];
    for(let i=0;i<word.length;i++)if(!marked[i]){
        const cycle=[];for(let j=i;!marked[j];j=forward[j]){cycle.push(word[j]);marked[j]=1;}
        const len=cycle.length;
        for(let j=1;j<len-j;j++)first.push([cycle[j],cycle[len-j]]);
        for(let j=0;j<len-1-j;j++)second.push([cycle[j],cycle[len-1-j]]);
    }
    const swaps=first.length+second.length;
    const conjunction=n===2?1:4*n-8;
    if(2*swaps+2*conjunction>=(4*n-4)*swaps)return false;
    const loans=tape.loan([...word,...controls],n-1),bit=loans[0],rest=loans.slice(1);
    const on=()=>tape.mc(enabled,bit,rest);
    function layer(pairs){
        for(const [x,y] of pairs){
            tape.out(1023,x,y);tape.out(bit,y,x);tape.out(1023,x,y);
        }
    }
    const a=back?second:first,b=back?first:second;
    // S3: cancel the commuting CNOT frames around each disjoint reflection.
    function echo(pairs){
        for(const [x,y] of pairs)tape.out(1023,x,y);
        for(const [x,y] of pairs)tape.out(bit,y,x);
        on();
        for(const [x,y] of pairs)tape.out(bit,y,x);
        for(const [x,y] of pairs)tape.out(1023,x,y);
    }
    echo(a);echo(b);
    return true;
}
function patchPermutation(source){
    const anchor='class MixedArithmetic extends WordArithmetic {',entry='    permute(tape,word,origins,controls,back) {';
    for(const s of [anchor,entry])if(source.split(s).length!==2)throw Error('shared permutation anchor '+s);
    return source.replace(anchor,()=>sharedControlledPermutation.toString()+'\n'+anchor)
        .replace(entry,()=>entry+'\n        if(sharedControlledPermutation(tape,word,origins,controls,back))return;');
}
module.exports={sharedControlledPermutation,patchPermutation};
