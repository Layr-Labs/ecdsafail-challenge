'use strict';

// This rank encoding conditionally inverts rank bits around a lower-width
// comparison. Capture those changes symbolically so inspecting the predicate
// never emits gates or changes the caller's actual data.
function sixCutoff(source) {
    let s = source;
    function once(before, after) {
        if (s.split(before).length !== 2) throw Error('Q647 cutoff grammar '+before);
        s = s.replace(before, () => after);
    }
    once('    const term=(pos,neg)=>{', `    const flipped=new Set(),unsupported=Symbol('six-cutoff');
    function known(q){return q===tape.one;}
    grab.out=(a,b,w)=>{
        if(w===flag){term([a,b].filter(q=>q!==NONE),[]);return;}
        if(a!==NONE||b!==NONE||known(w))throw unsupported;
        if(flipped.has(w))flipped.delete(w);else flipped.add(w);
    };
    const term=(p,n)=>{
        if(n.some(known))return;
        const pos=p.filter(q=>!known(q)&&!flipped.has(q)).concat(n.filter(q=>flipped.has(q)));
        const neg=n.filter(q=>!flipped.has(q)).concat(p.filter(q=>flipped.has(q)));`);
    once("if(cs.length||dest.length!==1||dest[0]!==flag)throw Error('tail cutoff predicate');", `if(dest.length!==1||dest[0]!==flag)throw unsupported;
        const yes=cs.filter(q=>!known(q)&&!flipped.has(q)).map(slot),no=cs.filter(q=>flipped.has(q)).map(slot);
        const invert=word.map(q=>flipped.has(q)?1:0);`);
    once('((x>>positions[b])&1)<<b;', '(((x>>positions[b])&1)^invert[b])<<b;');
    once('return rank<Number(limit);', 'return rank<Number(limit)&&yes.every(i=>x>>i&1)&&no.every(i=>!(x>>i&1));');
    once("        if(kind==='sign'){\n            term([],[]);", "        try{if(kind==='sign'){\n            term([],[]);");
    once('column.push(expr);', `if(flipped.size)throw unsupported;
        }catch(e){if(e===unsupported)return null;throw e;}
        column.push(expr);`);
    const local="'affine',rv,(z,i,rr)=>(";
    if(s.split(local).length!==3)throw Error('Q647 affine digit closures');
    s=s.split(local).join("'affine',rv,(z,i,rr)=>{const cut=i-base+1;return (");
    const end=')(rr),()=>saved(rv));';
    if(s.split(end).length!==3)throw Error('Q647 affine digit closure ends');
    s=s.split(end).join(')(rr);},()=>saved(rv));');
    return s;
}

// The six-helper build embeds a second general-row program for replaying the
// measured sign. Apply the same generic arithmetic to both compiled programs.
function arithmetic(source) {
    const sign = require('./index.cjs').patch(source);
    const affine = require('./affine.cjs').patch(sign);
    return sixCutoff(require('./rotation.cjs').patch(affine));
}

function patch(source) {
    const embedded = /(const q647SevenPhase=Function\(Buffer\.from\(")([A-Za-z0-9+/=]+)(",\"base64\"\)\.toString\(\"utf8\"\)\)\(\);)/g;
    const host = arithmetic(source);
    let count = 0;
    const both = host.replace(embedded, (_, start, encoded, end) => {
        count++;
        const kernel = Buffer.from(encoded, 'base64').toString('utf8');
        return start + Buffer.from(arithmetic(kernel)).toString('base64') + end;
    });
    if (count !== 1) throw Error('Q647 embedded phase-kernel count '+count);
    return both;
}

module.exports = {patch};
