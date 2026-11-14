// per-row best maxRelay by measured row cost; prints relayAt and total
const D=process.argv[2],which=process.argv[3];const M=require(D+'/walkt1.cjs');const alt=require(D+'/../q651-ten-field/public-backend.cjs').withDigit(require(D+'/../q651-ten-field/m6-alternating.cjs').alternatingDigit);
const dd=alt.dirtyDigit,n=128;
const mk={mulK3:o=>new M.TstRelayK(n,[647,648,649],654,Object.assign({dirtyDigit:dd},o)),revKR2:o=>new M.TstRelayKRE(n,2,Object.assign({dirtyDigit:dd},o)),inner1:o=>new M.TstRelay1E(n,Object.assign({dirtyDigit:dd},o)),outerKS6:o=>new M.TstRelayKSE(n,6,Object.assign({dirtyDigit:dd},o)),rg6:o=>new M.TstRelayK(n,[647,648,649],654,Object.assign({flat:false},o)),rg4:o=>new M.TstRelayK(n,[647,648],654,Object.assign({flat:false},o))}[which];
const rowCost=w=>{const c=new Map();let tot=0;for(const b of w.plan()){w.g=[];b.fn();tot+=w.g.length;c.set(b.k,(c.get(b.k)||0)+w.g.length);}return {c,tot};};
const Js=[0,1,2,3,4,5,6];const res={};for(const J of Js)res[J]=rowCost(mk({maxRelay:J}));
const relayAt={};let fixed=res[2].c.get(-1)||0;let est=fixed;
for(let k=0;k<n;k++){const m=n-k;let best=2,bc=res[2].c.get(k);for(const J of Js){const v=res[J].c.get(k);if(v<bc){bc=v;best=J;}}relayAt[m]=best;est+=bc;}
const fin=rowCost(mk({relayAt}));
console.log(which,'totals by J',Js.map(J=>J+':'+res[J].tot).join(' '),'| per-row best est',est,'actual',fin.tot);
require('fs').writeFileSync(D+'/relayAt-'+which+'.json',JSON.stringify(relayAt));
