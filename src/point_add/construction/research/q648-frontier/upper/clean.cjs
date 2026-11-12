'use strict';

// The Q648 affine row reserves its carry as a clean selector. It already
// uses this exact wire for guardedBarrel and the borrow of reflectMinusOne.
// Before and after each mark, this carry is zero for active and idle lanes.
function cleanAffineRotation(owner,tape,word,controls,plan,b,flag,back){
    const shift=(1<<b)%word.length;
    if(!plan.masks[b].length||!shift)return;
    function mark(){
        for(const [pos,neg] of plan.masks[b]){
            const yes=controls.slice(),no=[];
            plan.wires.forEach((q,i)=>{if(pos>>i&1)yes.push(q);if(neg>>i&1)no.push(q);});
            if(yes.some(q=>no.includes(q)))continue;
            owner.toggle(tape,[...new Set(yes)],[...new Set(no)],flag);
        }
    }
    mark();
    owner.permute(tape,word,word.slice(shift).concat(word.slice(0,shift)),[flag],back);
    mark();
}

function patch(source) {
    let s=source;
    function once(a,b){if(s.split(a).length!==2)throw Error('clean affine source anchor '+a);s=s.replace(a,()=>b);}
    once('class Tape {',cleanAffineRotation.toString()+'\nclass Tape {');
    once('if(n<35||n>m||!m)return fallback();', "if(n<(kind==='affine'?16:35)||n>m||!m)return fallback();");
    const anchor='const sequence=[rv=>rotate(true,!rv),sweep,rv=>rotate(false,rv),fixed];';
    once(anchor,`if(kind==='affine'){
        if(owner.fieldBits!==256||flag!==owner.carry||plan.wires.includes(flag))throw Error('affine carry domain');
        const checked=f=>{tape.q648RollingCarry?.(flag,owner);f();tape.q648RollingCarry?.(flag,owner);};
        const rotateClean=rv=>checked(()=>stepList(split(0,plan.masks.length),rv,b=>cleanAffineRotation(owner,tape,word,active,plan,b,flag,rv)));
        stepList([rv=>checked(()=>sweep(rv)),rotateClean],back,f=>f(back));return;
    }
    `+anchor);
    return s;
}

module.exports={patch};
