'use strict';
const assert=require('node:assert/strict');
const crypto=require('node:crypto');
const fs=require('node:fs');
const Module=require('node:module');
const path=require('node:path');

// Q[120] holds the six-helper count; Q[6..119] is the unused, zero part
// of the incoming quotient. The same ripple construction is graded at Q648.
function install(research=path.resolve(__dirname,'../..'),point=process.env.Q647_POINT_ADD||path.join(research,'q647-trim/donor')){
    const src=path.join(research,'q648-next/field/outer.cjs'),old=fs.readFileSync(src,'utf8');
    assert.equal(crypto.createHash('sha256').update(old).digest('hex'),'f546a77a3e0b06bfdb86bc9b0932ebc1b6d3fbbcd64612d26c53d368247c9979');
    let body=old;
    for(const [a,b] of [["'d14-walk-emitter.cjs'","'i9-divide-walk-emitter.cjs'"],["'divide-i.cjs'","'i9-divide-divide-647.cjs'"],['length:115','length:114']]){
        assert.equal(body.split(a).length,2,a);body=body.replace(a,b);
    }
    const m=new Module(src,module);m.filename=src;m.paths=Module._nodeModulePaths(path.dirname(src));m._compile(body,src);
    m.exports.install(path.join(point,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field'));
}
module.exports={install};
