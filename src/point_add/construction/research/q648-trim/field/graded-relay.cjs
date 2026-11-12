'use strict';

const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');

const original = fs.readFileSync(path.join(__dirname, 'relay-source.cjs'), 'utf8');
assert.equal(crypto.createHash('sha256').update(original).digest('hex'),
    '2ddaa7bcd13c0f2d49f6e6538674c9ff803cf892c3271c5efb50bc8f8654d811');

function fix(source, old, next, count=1) {
    assert.equal(source.split(old).length, count+1, old);
    return source.split(old).join(next);
}

// The first realCount height tags are clean logical registers for an entire
// walk. Each sector starts with those low bits and the remaining tag suffix.
// The top bit has the original incoming-row host; intermediary bits borrow
// the zeros from divisor normalization and quotient shifts in the D22 plan.
const builders = new Map();
function builder(realCount) {
    if (builders.has(realCount)) return builders.get(realCount);
    assert([1,2,3].includes(realCount));
    let s = fix(original,'roles=full.slice(0,-1).reverse()',
        'roles=full.slice(realCount,-1).reverse()',2);
    s = fix(s,'depth=roles.length,low=2,wide','depth=roles.length,low=1<<(realCount+1),wide');
    s = fix(s,'const base=1<<j;if(base<m)','const base=1<<(realCount+j);if(base<m)');
    s = fix(s,'for(let base=1<<depth;','if(depth)for(let base=1<<(realCount+depth);');
    s = fix(s,'tag=full.slice(full.length-1-kind);',
        'tag=full.slice(0,realCount).concat(full.slice(full.length-1-kind));');
    s = fix(s,'const dirtySelector=true;', 'const dirtySelector=false;');
    s = fix(s,'qcond();consumer();this.reverse(qcond);consumer();',
        'qcond();consumer();this.reverse(qcond);');
    // In the original all nominal tags other than the top are virtual.
    // An actual clean tag also hosts the early comparison predicate directly.
    const m = {exports:{}};
    Function('module','realCount',s)(m,realCount);
    builders.set(realCount,m.exports);
    return m.exports;
}

function adapt(walk, digit, realCount) {
    const bits = Math.min(7,Math.log2(walk.n));
    assert(Number.isInteger(bits) && bits>=realCount+1);
    const available = walk.tag.slice(0,realCount), top=walk.tag.at(-1);
    const virtual = Array.from({length:bits-realCount-1},(_,i)=>900+i);
    assert(walk.nq<900);
    walk.tag=available.concat(virtual,top);
    walk.nq=Math.max(walk.nq,910);
    return builder(realCount).install(walk,digit);
}

// Invoke after the Q649 port's crop/host initialization. This replaces the
// two short-divide walks. The populated auxiliary port of the first outer
// walk selects the unchanged D14 emitter.
function installDivide(owner) {
    const filename=require.resolve(path.join(owner,'d14-walk-emitter.cjs'));
    const small=require(path.join(owner,'d14-walk-small.cjs'));
    const old=require(filename);
    require.cache[filename].exports={wrap(pub) {
        const base=old.wrap(pub);
        return (w,L,R,ws,dirty,back,sink)=>{
            if(ws.aux!==-1) return base(w,L,R,ws,dirty,back,sink);
            assert.equal(w.tag.length,back?4:3);
            small.install(w,pub.dirtyDigit,{rot:true,pair:true,select:true});
            adapt(w,pub.dirtyDigit,back?2:1);
            return pub.emitWalk(w,L,R,ws,dirty,back,sink);
        };
    }};
}

const installed=new Set();
function install(campaign=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input')) {
    const wideFile=require.resolve(path.join(campaign,'port/wide-walk.cjs'));
    if(installed.has(wideFile))return;
    const owner=path.join(campaign,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    assert(!require.cache[require.resolve(path.join(owner,'divide-i.cjs'))],
        'Install the Q649 stages before constructing the first point program');
    const wide=require(wideFile),previous=wide.installDivide;
    wide.installDivide=(q,compiler)=>{
        previous(q,compiler);
        installDivide(q);
    };
    installed.add(wideFile);
}

module.exports={adapt,installDivide,install,planFor:real=>builder(real).plan};
