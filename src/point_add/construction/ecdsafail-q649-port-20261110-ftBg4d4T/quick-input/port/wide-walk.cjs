'use strict';
const fs = require('node:fs');
const path = require('node:path');
const Module = require('node:module');

function replace(source, before, after) {
    if (source.split(before).length !== 2) throw Error('Q649 walk source: ' + before);
    return source.replace(before, () => after);
}

function cropPlan(source) {
    // In a sector with offset base, the normalized denominator has at least
    // base leading zeros in little-endian order. After i+1 quotient shifts,
    // at least max(0,base-i-1) low positions remain zero. The enabled restoring
    // digit divides out that power of two. Disabled digits are identities.
    source = replace(source, 'this.constantDigit(r.slice(0,-1),A,r[m-1],this.fire)',
        'this.constantDigit(r.slice(base,-1),A.slice(base),r[m-1],this.fire)');
    source = replace(source, 'if(i===0)this.constantDigit(rh.slice(0,-1),ah,carry,en[0]);else for(const z of dirtyDigit(rh.slice(0,-1).concat(this.fire),ah,carry,en[0],this.y[0]))',
        'const cut=Math.max(0,base-i-1);if(i===0)this.constantDigit(rh.slice(cut,-1),ah.slice(cut),carry,en[0]);else for(const z of dirtyDigit(rh.slice(cut,-1).concat(this.fire),ah.slice(cut),carry,en[0],this.y[0]))');
    source = replace(source, 'const select=(z)=>', 'const select=(z,guard=[])=>');
    source = replace(source, 'this.lt([this.tst],A,r,z)', 'this.lt([this.tst,...guard],A,r,z)');
    source = replace(source, 'select(this.fire);match(c,r,tag[0]);select(this.fire);this.op([tag[0]],this.fire);this.op(c,tag[0]);',
        'match([],r,tag[0]);select(this.fire,[tag[0]]);match([],r,tag[0]);');
    return source;
}

function installMultiply(owner) {
    const filename = require.resolve(path.join(owner, 'm6-host-walk.cjs'));
    const replacement = new Module(filename, module);
    replacement.filename = filename;
    replacement.paths = Module._nodeModulePaths(owner);
    replacement.crop = cropPlan;
    const src = replace(fs.readFileSync(filename, 'utf8'), "const plan=Function('dirtyDigit'",
        "s=module.crop(s);const plan=Function('dirtyDigit'");
    replacement._compile(src, filename);
    require.cache[filename] = replacement;
}

function hostedTypes(owner, compiler, pub) {
    const raw = fs.readFileSync(path.join(compiler, 'hosted-divide.cjs'), 'utf8');
    const start = raw.indexOf('function hostedTypes('), end = raw.indexOf('\nfunction build(', start);
    if (start < 0 || end < 0) throw Error('Q649 hosted divide constructor');
    let source = raw.slice(start, end);
    source = replace(source, 'const construct=(r,bits,append)=>',
        's=replace(s,"const plan=Function(\'dirtyDigit\'","s=edit.cropPlan(s);const plan=Function(\'dirtyDigit\'");const construct=(r,bits,append)=>');
    source = replace(source, 'canonical:construct(false,4,true),reduced:construct(true,5,false)',
        'canonical:construct(false,3,true),reduced:construct(true,4,false)');
    const {implicitTopDigit} = require(path.join(compiler, 'implicit-top.cjs'));
    const withCrop = (...args) => replace(...args);
    withCrop.cropPlan = cropPlan;
    return Function('path','fs','replace','implicitTopDigit','return (' + source + ');')(
        path, fs, withCrop, implicitTopDigit
    )(owner, pub);
}

function installDivide(owner, compiler) {
    const filename = require.resolve(path.join(owner, 'd14-walk-emitter.cjs'));
    const direct = require(filename);
    require.cache[filename].exports = {wrap(pub) {
        const original = direct.wrap(pub), custom = hostedTypes(owner, compiler, pub);
        const {rot2} = require(path.join(owner, 'd14-walk-small.cjs'));
        return function (walk, L, R, workspace, dirty, back, sink) {
            if (workspace.aux !== -1) return original(walk, L, R, workspace, dirty, back, sink);
            if (![3,4].includes(walk.tag.length)) throw Error('Q649 D14 walk tag count ' + walk.tag.length);
            const C = walk.tag.length === 3 ? custom.canonical : custom.reduced;
            const hosted = new C(walk.n);
            hosted.d9oldRot = hosted.rot; hosted.rot = rot2;
            return custom.map(hosted, L, R, workspace, dirty, back, (kind, gates) => {
                for (const x of gates) {
                    const a = x >>> 20, b = (x >>> 10) & 1023, target = x & 1023;
                    if (a === 644 || a === 645 || b === 644 || b === 645 || target === 644 || target === 645) {
                        throw Error('Q649 D14 omitted wire present');
                    }
                }
                sink(kind, gates);
            });
        };
    }};
}
module.exports = {installMultiply, installDivide, hostedTypes, cropPlan};
