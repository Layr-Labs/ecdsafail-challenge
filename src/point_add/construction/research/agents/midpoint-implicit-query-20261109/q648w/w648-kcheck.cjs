const D='/Users/akashbalasubramani/Desktop/ecdsafail-648w/src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q648w/';
const {SignedAF}=require(D+'walkaf.cjs');const {TstRelay1,TstRelayK}=require(D+'walkt1.cjs');
const crypto=require('crypto');const n=+(process.env.N||128),W=+(process.env.W||8),L=32*W,Pm=(1n<<256n)-(1n<<32n)-977n;
const rb=b=>{let v=0n;for(const x of crypto.randomBytes(Math.ceil(b/8)))v=(v<<8n)|BigInt(x);return v&((1n<<BigInt(b))-1n);};
const ins=[];for(let l=0;l<L;l++){const r=l%8;let T;if(r<5){const bits=1+Number(rb(8))%n;T=rb(bits)|(1n<<BigInt(bits-1));}else if(r===5)T=1n<<BigInt(Number(rb(7))%n);else if(r===6)T=(1n<<BigInt(1+Number(rb(7))%n))-1n;else T=BigInt(1+Number(rb(6)));ins.push(T);}
function run(w){const s=new Uint32Array(1024*W);const set=(q,l,b)=>{if(b)s[q*W+(l>>5)]|=1<<(l&31);};
 for(let l=0;l<L;l++){const T=ins[l],R=Pm%T;for(let j=0;j<n;j++){set(w.L[j],l,Number((T>>BigInt(j))&1n));set(w.R[j],l,Number((R>>BigInt(j))&1n));}}
 for(const q of w.y)for(let i=0;i<W;i++)s[q*W+i]=crypto.createHash('md5').update(q+':'+i).digest().readUInt32LE(0);
 const top=w.tag.at(-1),direct=!!w.direct;let ops=0;const touched=new Set();
 for(const block of w.plan()){w.g=[];block.fn();if(block.rev)w.g.reverse();
  for(const x of w.g){let a=x>>>20&1023,b=x>>>10&1023,t=x&1023;const tr=q=>!direct&&q===top?block.topPort:q;if(a!==1023)a=tr(a);if(b!==1023)b=tr(b);t=tr(t);ops++;touched.add(t);if(a!==1023)touched.add(a);if(b!==1023)touched.add(b);
   if(a===t||b===t||(a!==1023&&a===b))throw Error('alias');const T=t*W;if(a===1023){for(let i=0;i<W;i++)s[T+i]^=0xffffffff;}else if(b===1023){const A=a*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i];}else{const A=a*W,B=b*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i]&s[B+i];}}}
 return {s,ops,touched};}
const cmp=(x,y)=>{let d=0;for(let q=0;q<1024;q++)for(let i=0;i<W;i++)if(x.s[q*W+i]!==y.s[q*W+i])d++;return d;};
// reference: plain unit walk with the FlatUnit tail = D2Canonical semantics; compare TstRelay1 flat vs SignedAF+tail? use flat:false vs SignedAF.
const p=new SignedAF(n,3);p.aux=-5;p.tst=p.R[n+1];const ref=run(p);
const KK=+(process.env.K||1);const w=new TstRelayK(n,[647,648,649].slice(0,KK),654,{flat:false});const r1=run(w);
console.log('n',n,'k',KK,'plain',ref.ops,'| TstRelay1',r1.ops,'diff',cmp(ref,r1),'helpers touched',[647,648,649,650,654,655].filter(q=>r1.touched.has(q)).join(','));
