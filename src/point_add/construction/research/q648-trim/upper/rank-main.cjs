'use strict';
// The Q648 rank representation lives on A[0], A[1], A[2] and five auxiliary
// sites. Ranks 0..2 use A[1] as a code flag with numerical A[2] on tag[4].
// Re-encode temporarily around the 129 full-width main product digits. No
// tail digit observes this representation. All moves operate under take.
function rankMain(owner, tape, layer, r, a, d, back, mode) {
    const one = mode === 'early-one';
    const max = owner.maxShift;
    const tag = owner.tag;
    if (!owner.u648 || tag.length !== 7 || tag[6] !== a[2]) throw Error('Q648 early rank ports');
    const host = one ? owner.carry : a[1];
    const rank = [...tag.slice(0, 6), host];
    const word = one ? [...rank, a[1], a[2]] : [...rank, a[2]];
    const block = one ? 127 : 120;
    if (max >= block || new Set(word).size !== word.length) throw Error('Q648 early rank capacity');
    const swap = () => owner.permute(tape, [host, a[2]], [a[2], host], [owner.take], false);
    const moves = new Map();
    for (let c = 0; c <= 2; c++) {
        for (let xyz = 0; xyz < 8; xyz += 1 << c) {
            const x = xyz & 1, y = xyz >> 1 & 1, z = xyz >> 2;
            const old = 128 + (c === 0 ? x + 2*y : c === 1 ? 4+y : 8) + 16*z;
            const code = one ? (x ? 127 : c) + 128*y + 256*z
                : (x || y ? 120 + x + 2*y + 4*c : c) + 128*z;
            moves.set(old, code);
        }
    }
    for (let c = 3; c <= max; c++) moves.set(c,c);
    const incoming = new Set(moves.values());
    if (incoming.size !== moves.size) throw Error('Q648 early recoding collision');
    for (const start of [...moves.keys()]) if (!incoming.has(start)) {
        let at = start;
        while (moves.has(at)) at = moves.get(at);
        moves.set(at,start);
    }
    const visited = new Set(), swaps = [];
    for (const start of moves.keys()) if (!visited.has(start)) {
        let at = start;
        while (!visited.has(at)) {
            visited.add(at); at = moves.get(at);
            if (at !== start) swaps.push([start,at]);
        }
    }
    const recode = reverse => {
        if (!reverse) swap();
        for (const [u,v] of reverse ? swaps.slice().reverse() : swaps)
            owner.u6Transpose(tape,word,u,v,[owner.take],[],false);
        if (reverse) swap();
    };
    let lowest = 6;
    while (127 - ((1<<lowest)-1) <= max) lowest--;
    const prefix = rank.slice(lowest);
    const X = -1000, Y = -1002, absent = 1023;
    const modulus = one ? [X,...a.slice(1)] : [X,Y,...a.slice(2)];
    const protectedTape = Object.create(tape);
    protectedTape.ids = tape.ids.filter(q=>!rank.includes(q));
    const proxy = Object.create(protectedTape), local = Object.create(layer);
    const ex = one ? prefix : [...prefix,rank[0]], ey = [...prefix,rank[1]];
    let delta = null;
    proxy.out = (u,v,w) => {
        if (w === X) throw Error('Q648 rank writes virtual A[0]');
        if (w === Y) {
            if (one || (u !== X && v !== X)) throw Error('Q648 rank unexpected write to A[1]');
            const other = u === X ? v : u;
            if (delta !== null && delta !== other) throw Error('Q648 rank A[1] parity did not unwind');
            delta = delta === null ? other : null;
            return;
        }
        if (delta !== null && w === delta) throw Error('Q648 rank A[1] carry source was overwritten');
        if (u !== X && v !== X && u !== Y && v !== Y) { tape.out(u,v,w); return; }
        if ((u === X || u === Y) && (v === X || v === Y)) throw Error('Q648 rank double virtual control');
        const x = u === X || v === X;
        const other = (u === X || u === Y) ? v : u;
        const controls = other === absent ? [] : [other];
        owner.toggle(protectedTape, (x ? ex : ey).concat(controls), [], w);
        if (!x && delta !== null) owner.toggle(protectedTape,ex.concat(delta,controls),[],w);
    };
    local.digit = (tp,z,v,on,rev) => {
        if (one) implicitTopDigit(tp,z,v,on,rev);
        else cleanTop(tp,z,v,on,owner.carry,rev);
        if (delta !== null) throw Error('Q648 rank A[1] not restored');
    };
    recode(false);
    local.mixed(proxy,r,modulus,d,[owner.take],back);
    recode(true);
}
module.exports = {rankMain};
