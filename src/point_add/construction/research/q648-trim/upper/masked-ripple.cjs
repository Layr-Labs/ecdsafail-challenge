'use strict';
// Lower h coefficient bits are f ? payload : 0. When f=0 the low carry
// computation can still run on arbitrary payload. Suppress its crossing
// into A[h] and its permanent writes to B[0:h]. Its two halves then unwind
// each other for every payload and B. The high gates are exactly the ripple
// with zero low coefficient. When f=1 the entire ripple is unchanged.
function maskedRipple(tape, a, b, encoded, flag, reserved, plain, run) {
    const h = encoded.length, first = -1170, none = 1023;
    if (h >= a.length || h >= b.length || new Set([...encoded,flag]).size !== h+1) throw Error('Q648 masked ripple shape');
    const symbols = Array.from({length:h}, (_,i)=>first-i);
    const low = q => q <= first && q > first-h;
    const real = q => low(q) ? encoded[first-q] : q;
    const source = [...symbols,...a.slice(h)], prefix = b.slice(0,h), occurrences = new Uint8Array(h);
    const proxy = Object.create(tape);
    proxy.ids = tape.ids.filter(q=>!reserved.includes(q));
    const loan = proxy.loan([...a,...b,...encoded,flag,...reserved],1)[0];
    proxy.out = (x,y,t) => {
        const vx=low(x), vy=low(y), vt=low(t);
        if (!vx && !vy && !vt) { tape.out(x,y,t); return; }
        if (vt) {
            if (!vx && !vy) throw Error('Q648 masked prefix gate unconditionally writes payload');
            tape.out(real(x),real(y),real(t)); return;
        }
        let guard = t === a[h];
        if (!guard) {
            const i = prefix.indexOf(t);
            if (i < 0 || (x !== symbols[i] && y !== symbols[i])) throw Error('Q648 unexpected prefix output '+[x,y,t]);
            // The plain adder has matching pre/post CNOTs at i>=1 and
            // its permanent i-th CNOT between them in either direction.
            // The controlled ripple instead makes its permanent write a CCX.
            if (x === none) {
                occurrences[i]++;
                guard = plain && (i === 0 || occurrences[i] === 2);
            } else guard = true;
        }
        const u=real(x),v=real(y);
        if (!guard) { tape.out(u,v,t); return; }
        if (u===none) { tape.out(flag,v,t); return; }
        if (u===loan||v===loan||t===loan||flag===loan) throw Error('Q648 mask dirty collision');
        tape.out(flag,u,loan);tape.out(loan,v,t);tape.out(flag,u,loan);tape.out(loan,v,t);
    };
    run(proxy,source);
    for(let i=0;i<h;i++){
        const expected=(i===0?0:2)+(plain?1:0);
        if(occurrences[i]!==expected)throw Error('Q648 masked low write count '+[i,occurrences[i],expected]);
    }
}

function maskedAffine(owner,tape,layer,r,a,d,back) {
    const tag=owner.tag,flag=a[1],payload=owner.u648?[tag[0],tag[1],tag[4]]:[tag[0],tag[1]];
    const reserved=[...tag,flag,owner.carry,owner.take],local=Object.create(layer);
    // Only exceptional rank one has its numerical bit 1 in tag[0]; bit 0
    // is zero on this rank. On ordinary ranks the swapped payload is masked.
    const swap=()=>owner.permute(tape,[tag[0],tag[1]],[tag[1],tag[0]],[tag[2]],false);
    local.digit=(tp,z,v,on,rv)=>maskedRipple(tp,v,z,payload,flag,reserved,false,(p,m)=>cleanTop(p,z,m,on,owner.carry,rv));
    swap();local.mixed(tape,r,a,d,[owner.take],back);swap();
}

function maskedProbeAdd(owner,tape,a,b) {
    const tag=owner.u40Tag,flag=tag.at(-1);
    const p=owner.u648C.Pc.slice(0,owner.u9H).map(i=>tag[i]);
    return (high,predicate,back)=>maskedRipple(tape,a,b,p,flag,[...tag,high,predicate],predicate===null,
        (tp,m)=>MixedArithmetic.prototype.nrAdder.call(owner,tp,m,b,high,predicate,back));
}

function maskedProbeProduct(owner,tape,q,v,rem,back) {
    const local=Object.create(owner);
    local.nrAdder=(tp,a,b,high,predicate,rv)=>maskedProbeAdd(owner,tp,a,b)(high,predicate,rv);
    local.unguardedMixed(tape,q,v,rem,back);
}
module.exports = {maskedRipple,maskedAffine,maskedProbeAdd,maskedProbeProduct};
