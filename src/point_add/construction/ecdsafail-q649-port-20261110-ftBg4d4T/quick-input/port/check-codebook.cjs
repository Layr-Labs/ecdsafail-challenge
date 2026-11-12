'use strict';
const {transposeCode, exceptionalPrefix} = require('./codebook.cjs');
let n = 0, rankChecks = 0, seed = 0x9e3779b9;
function random() {seed = (Math.imul(1664525, seed) + 1013904223) >>> 0;return seed;}
for (let width = 2; width <= 10; width++) {
    const word = Array.from({length:width}, (_, i) => i), end = 1 << width;
    const pairs = width <= 6 ? end * end : 1500;
    for (let pair = 0; pair < pairs; pair++) {
        const a = width <= 6 ? Math.floor(pair / end) : (random() >>> 12) % end;
        const b = width <= 6 ? pair % end : (random() >>> 12) % end;
        const ops = [];
        const tape = {out(unused, s, t) {if(unused !== 1023) throw Error('nonlinear fanout');ops.push([1 << s,0,1 << t]);}};
        const owner = {toggle(_, yes, no, t) {
            const mask = cs => cs.reduce((v, q) => v | (1 << q), 0);
            ops.push([mask(yes),mask(no),1 << t]);
        }};
        transposeCode(owner, tape, word, a, b, [width], [width+1]);
        const cases = width <= 6 ? end : 20;
        for (let i = 0; i < cases; i++) for (let flags = 0; flags < 4; flags++) {
            const x = width <= 6 ? i : i === 0 ? a : i === 1 ? b : (random() >>> 12) % end;
            let state = (flags << width) | x;
            for (const [positive,negative,t] of ops) if ((state & positive) === positive && !(state & negative)) state ^= t;
            const want = flags === 1 ? x === a ? b : x === b ? a : x : x;
            if (state !== ((flags << width) | want)) throw Error('bad transposition '+[width,a,b,x,flags]);
            n++;
        }
    }
}
for (let bits = 3; bits <= 12; bits++) {
    const top = 1 << bits;
    for (let free = top >> 1; free < top-4; free++) {
        const first = exceptionalPrefix(free, bits), mask = (top-1) ^ ((1 << first)-1);
        const rows = Array.from({length:free+1}, (_, i) => i).concat([top-4,top-3,top-2,top-1]);
        for (const word of rows) {
            const prefix = (word & mask) === mask;
            if (prefix !== (word >= top-4)) throw Error('unreachable-code premise');
            const oldA = ((word >>> 2) === ((top-1) >>> 2)) && Boolean(word & 2);
            const oldB = ((((word >>> 2) === ((top-1) >>> 2)) && Boolean(word & 1)) !== (word === top-4));
            if (oldA !== (prefix && Boolean(word & 2)) ||
                oldB !== ((prefix && Boolean(word & 1)) !== (prefix && (word & 3) === 0))) throw Error('coefficient decode');
            rankChecks++;
        }
    }
}
console.log(JSON.stringify({transposeStates:n,rankCodeCases:rankChecks,allMatch:true}));
