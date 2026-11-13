'use strict';
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');

// A prefix describes a dyadic interval of the normalization tag. Outside a
// sector its fire wire is clear, and active offsets stop at its true width.
const schedules = new Map();
function controlsCost(count) {
    return count < 2 ? 0 : count === 2 ? 1 : 4 * (count - 2);
}
function threshold(width, limit, extra = 2) {
    const id = `${width}/${limit}/${extra}`;
    if (schedules.has(id)) return schedules.get(id);
    const bits = Math.ceil(Math.log2(width));
    function solve(start, size, depth, incoming) {
        if (start >= width) return {cost:0, terms:[]};
        const low = start > limit, high = Math.min(width, start + size) - 1 > limit;
        const flipCost = controlsCost(depth + extra);
        const term = {start, depth};
        if (low === high) return low === incoming ? {cost:0, terms:[]} : {cost:flipCost, terms:[term]};
        const split = polarity => {
            const left = solve(start, size / 2, depth + 1, polarity);
            const right = solve(start + size / 2, size / 2, depth + 1, polarity);
            return {cost:left.cost + right.cost, terms:left.terms.concat(right.terms)};
        };
        const keep = split(incoming), invert = split(!incoming);
        return keep.cost <= flipCost + invert.cost ? keep : {cost:flipCost + invert.cost, terms:[term,...invert.terms]};
    }
    const best = {...solve(0, 2**bits, 0, false),bits};
    schedules.set(id, best);
    return best;
}
function toggle(w, tag, spec, fixed, target) {
    for (const {start,depth} of spec.terms) {
        const high = tag.slice(spec.bits-depth,spec.bits);
        const neg = high.filter((_,j) => !(start & (1 << (spec.bits-depth+j))));
        for (const q of neg) w.raw(-1,-1,q);
        w.op([...fixed,...high],target);
        for (const q of neg) w.raw(-1,-1,q);
    }
}

// A conventional enabled restoring Euclidean digit, with the internal mask
// materialized in the incoming logical enable e. remask() applies e ^= E & !h
// for its known incoming Boolean value E, which is stable outside the digit.
function digit(w, A, B, h, e, remask) {
    const top = A.length-1, d = w.y[0];
    assert(top >= 1 && A.length === B.length);
    const x = q => w.raw(-1,-1,q), cx = (a,t) => w.raw(a,-1,t), ccx = (a,b,t) => w.raw(a,b,t);
    for (const q of B) x(q);
    for (let i=1;i<=top;i++) cx(A[i],B[i]);
    ccx(e,A[top],h);
    for (let i=top-1;i>=1;i--) cx(A[i],A[i+1]);
    for (let i=0;i<top;i++) ccx(B[i],A[i],A[i+1]);
    ccx(e,A[top],d); ccx(d,B[top],h); ccx(e,A[top],d); ccx(d,B[top],h);
    cx(e,h);
    remask();
    ccx(e,A[top],B[top]);
    for (let i=top-1;i>=0;i--) {
        ccx(B[i],A[i],A[i+1]);
        ccx(e,A[i],B[i]);
    }
    remask();
    for (let i=1;i<top;i++) cx(A[i],A[i+1]);
    for (let i=1;i<=top;i++) cx(A[i],B[i]);
    for (const q of B) x(q);
}
function coefficient(w, A, B, h, tag, base, hi, i) {
    const e=w.tst, spec=threshold(hi-base+1,i-base);
    if (A.length < 2 || 2*spec.cost >= A.length+2) {
        w.restore([e],A,B,0,h);
        return;
    }
    const mask = () => {
        w.raw(-1,-1,h);
        toggle(w,tag,spec,[w.fire,h],e);
        w.raw(-1,-1,h);
    };
    digit(w,A,B,h,e,mask);
}
function replace(source, from, to) {
    assert.equal(source.split(from).length,2,from.slice(0,80));
    return source.replace(from,()=>to);
}
function transform(source) {
    return replace(source,'this.restore(en,v.slice(0,-1).concat(h),u,0,A[i])',
        'tuning.coefficient(this,v.slice(0,-1).concat(h),u,A[i],tg,base,hi,i)');
}
function install(file = path.resolve(__dirname,'../../q648-next/field/tail.cjs')) {
    const id = require.resolve(file);
    if (require.cache[id]?.fieldMask) return;
    assert(!require.cache[id],'Install the compact mask before tail.cjs loads');
    let source = fs.readFileSync(id,'utf8');
    assert.equal(crypto.createHash('sha256').update(source).digest('hex'),
        '14b4e81edc0cf4b61ef45943637dcafa24d836088d12d705fe7bfe7a3fef19fd');
    source = replace(source,'    return s;','    return module.fieldMask.transform(s);');
    source = replace(source,'conjugate:options.conjugate??true,cover',
        'conjugate:options.conjugate??true,cover,coefficient:module.fieldMask.coefficient');
    const patched = new Module(id,module);
    patched.filename=id; patched.paths=Module._nodeModulePaths(path.dirname(id));
    patched.fieldMask={coefficient,transform};
    patched._compile(source,id); patched.loaded=true; require.cache[id]=patched;
}
module.exports={install,digit,coefficient,threshold,toggle};
