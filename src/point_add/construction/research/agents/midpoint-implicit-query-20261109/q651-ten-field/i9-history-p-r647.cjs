'use strict';
const patches=require('./i9-history-p-scale-stream.cjs').map(([a,b])=>[a,b]);
const triple=require('./i9-history-walk3-source.cjs');
for(const p of patches){
 if(p[1].includes('function r43RelayPlan'))p[1]=triple+'\nfunction emitRegenerateSparse(sink,erase=false){';
 p[1]=p[1].replace('walk.tag=[walk.L[n+1],648,649,651];walk6.tag=[647,649,scale.T[2],scale.T[1],walk6.L[n+1],652];walk.fire=647;',
 'walk.tag=[647,648,649,651];walk.fire=walk.L[n+1];walk.r9Third=true;walk6.tag=[walk6.L[n+1],647,648,649,652];walk6.r9Third=true;');
 p[1]=p[1].replace('r42HostPlan(walk6,scale)','r43RelayPlan(walk6)');
 if(p[0]==='const port=q=>{')p[1]='const port=q=>{if((g===walk||g===walk6)&&q===647){if(block.relay3Port==null)throw Error("missing third relay");q=block.relay3Port;}'+p[1].slice('const port=q=>{'.length).replace('g===walk&&q===648','(g===walk||g===walk6)&&q===648');
}
// Important: no third virtual tag outside the rows. Ban after physical substitution.
patches.push(['if(q===648||q===649||q===650','if(q===647||q===648||q===649||q===650']);
module.exports=patches;

const multi=require('./i9-history-multi-relay.cjs'),planSource=multi.plan.toString();
const sharedSource=triple.slice(triple.indexOf('const dirtyDigit=' )+'const dirtyDigit='.length,triple.indexOf(';const plan='));
const replacement='function r43RelayPlan(w){w.d18reduced=false;w.d18digit='+sharedSource+';const full=w.tag.slice(),roles=full.slice(0,-1).reverse();const blocks=('+planSource+').call(w);for(const b of blocks){const fn=b.fn;b.fn=()=>{const prior=w.y,pre=b.sector===null&&b.topPort!=null,host=prior.at(-1);if(pre)w.y=prior.slice(0,-1);try{fn();}finally{w.y=prior;}for(let k=0;k<w.g.length;k++){const x=w.g[k],map=q=>{const j=roles.indexOf(q);if(j<0)return q;if(pre&&q===full[0])return host;if(b.ports[j]==null)throw Error("S6 host");return b.ports[j];};const a=map(x>>>20&1023),c=map(x>>>10&1023),t=map(x&1023);if(a===t||c===t||(a===c&&a!==1023))throw Error("S6 alias");w.g[k]=(a<<20)|(c<<10)|t;}};}w.tag=full;return blocks;}';
for(const pair of patches){
 if(pair[1].includes('function r43RelayPlan'))pair[1]=replacement+'\nfunction emitRegenerateSparse(sink,erase=false){';
 pair[1]=pair[1].replace('walk.tag=[647,648,649,651];walk.fire=walk.L[n+1];walk.r9Third=true;walk6.tag=[walk6.L[n+1],647,648,649,652];walk6.r9Third=true;',
 'walk.tag=[900,901,902,903,904,651];walk.fire=walk.L[n+1];walk6.tag=[910,911,912,913,914,652];');
 if(pair[0]==='const port=q=>{')pair[1]='const port=q=>{';
}
