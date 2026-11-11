// Divide OUTER walk: TstRelayKSE(n,k) vs alt SectorReduced(n,7) (= D2Reduced(n,7)), all wires. KS=k:maxRelay list.
const Q=__dirname+'/../q651-ten-field/';
const {TstRelayKSE}=require(Q+'../q648w/walkt1.cjs');
const alt=require(Q+'public-backend.cjs').withDigit(require(Q+'m6-alternating.cjs').alternatingDigit);
const crypto=require('crypto');const n=128,W=+(process.env.W||8),L=32*W,Pm=(1n<<256n)-(1n<<32n)-977n;
const rb=b=>{let v=0n;for(const x of crypto.randomBytes(Math.ceil(b/8)))v=(v<<8n)|BigInt(x);return v&((1n<<BigInt(b))-1n);};
const ins=[];for(let l=0;l<L;l++){const r=l%8;let T;if(r<5){const bits=1+Number(rb(8))%128;T=rb(bits)|(1n<<BigInt(bits-1));}else if(r===5)T=1n<<BigInt(Number(rb(7)));else if(r===6)T=(1n<<BigInt(1+Number(rb(7))%128))-1n;else T=BigInt(1+Number(rb(6)));ins.push(T);}
function run(w){const s=new Uint32Array(1024*W);const set=(q,l,b)=>{if(b)s[q*W+(l>>5)]|=1<<(l&31);};
 for(let l=0;l<L;l++){const T=ins[l],R=Pm%T;for(let j=0;j<n;j++){set(w.L[j],l,Number((T>>BigInt(j))&1n));set(w.R[j],l,Number((R>>BigInt(j))&1n));}}
 for(const q of w.y)for(let i=0;i<W;i++)s[q*W+i]=crypto.createHash('md5').update(q+':'+i).digest().readUInt32LE(0);
 const top=w.tag.at(-1);let ops=0;const touched=new Set();
 for(const block of w.plan()){w.g=[];block.fn();if(block.rev)w.g.reverse();
  for(const x of w.g){let a=x>>>20&1023,b=x>>>10&1023,t=x&1023;const tr=q=>q===top?block.topPort:q;if(a!==1023)a=tr(a);if(b!==1023)b=tr(b);t=tr(t);ops++;for(const q of [a,b,t])if(q!==1023)touched.add(q);
   if(a===t||b===t||(a!==1023&&a===b))throw Error('alias');const T=t*W;if(a===1023){for(let i=0;i<W;i++)s[T+i]^=0xffffffff;}else if(b===1023){const A=a*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i];}else{const A=a*W,B=b*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i]&s[B+i];}}}
 return {s,ops,touched};}
const all=(x,y)=>{let d=0,qs=new Set();for(let q=0;q<1024;q++)for(let i=0;i<W;i++)if(x.s[q*W+i]!==y.s[q*W+i]){d++;qs.add(q);}return [d,[...qs].slice(0,12)];};
const refw=alt.D2Reduced(n,7);const ref=run(refw);
console.log('SectorReduced(7) ops',ref.ops,'tags',refw.tag.length,'aux',refw.aux,'tst',refw.tst,'fire',refw.fire);
for(const spec of (process.env.KS||'6:2,6:5,5:2,5:5').split(',')){const [k,J]=spec.split(':').map(Number);const w=new TstRelayKSE(n,k,{dirtyDigit:alt.dirtyDigit,maxRelay:J});const a=run(w);
 console.log('TstRelayKSE k',k,'maxRelay',J,'ops',a.ops,'all-wire diff',JSON.stringify(all(ref,a)),'touched helpers',[...a.touched].filter(q=>q>=640&&q<700).sort((x,y)=>x-y).join(','),'L[n+1] used',a.touched.has(w.L[n+1]));}
