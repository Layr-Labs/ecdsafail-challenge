const Q=__dirname+'/../q651-ten-field/';
const {TstRelay1E,TstRelayKE}=require(Q+'../q648w/walkt1.cjs');const {TstRelayE}=require(Q+'../q648w/walktf.cjs');
const alt=require(Q+'public-backend.cjs').withDigit(require(Q+'m6-alternating.cjs').alternatingDigit);
const relay=require(Q+'d14-relay.cjs');
const crypto=require('crypto');const n=128,W=8,L=32*W,Pm=(1n<<256n)-(1n<<32n)-977n;
const rb=b=>{let v=0n;for(const x of crypto.randomBytes(Math.ceil(b/8)))v=(v<<8n)|BigInt(x);return v&((1n<<BigInt(b))-1n);};
const ins=[];for(let l=0;l<L;l++){const r=l%8;let T;if(r<5){const bits=1+Number(rb(8))%128;T=rb(bits)|(1n<<BigInt(bits-1));}else if(r===5)T=1n<<BigInt(Number(rb(7)));else if(r===6)T=(1n<<BigInt(1+Number(rb(7))%128))-1n;else T=BigInt(1+Number(rb(6)));ins.push(T);}
function run(w){const s=new Uint32Array(1024*W);const set=(q,l,b)=>{if(b)s[q*W+(l>>5)]|=1<<(l&31);};
 for(let l=0;l<L;l++){const T=ins[l],R=Pm%T;for(let j=0;j<n;j++){set(w.L[j],l,Number((T>>BigInt(j))&1n));set(w.R[j],l,Number((R>>BigInt(j))&1n));}}
 for(const q of w.y)for(let i=0;i<W;i++)s[q*W+i]=crypto.createHash('md5').update(q+':'+i).digest().readUInt32LE(0);
 const top=w.tag.at(-1),direct=!!w.direct;let ops=0;
 for(const block of w.plan()){w.g=[];block.fn();if(block.rev)w.g.reverse();
  for(const x of w.g){let a=x>>>20&1023,b=x>>>10&1023,t=x&1023;const tr=q=>{if(direct)return q;if(q===top)return block.topPort;if(block.relayPort!=null&&q===w.__missing)return block.relayPort;if(w.__map&&w.__map.has(q))return w.__map.get(q);return q;};if(a!==1023)a=tr(a);if(b!==1023)b=tr(b);t=tr(t);ops++;
   const T=t*W;if(a===1023){for(let i=0;i<W;i++)s[T+i]^=0xffffffff;}else if(b===1023){const A=a*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i];}else{const A=a*W,B=b*W;for(let i=0;i<W;i++)s[T+i]^=s[A+i]&s[B+i];}}}
 return {s,ops};}
const data=q=>q<260||(q>=389&&q<645);const cmp=(x,y)=>{let d=0;for(let q=0;q<1024;q++){if(!data(q))continue;for(let i=0;i<W;i++)if(x.s[q*W+i]!==y.s[q*W+i])d++;}return d;};
const ref=run(new alt.D2Canonical(n,3));
const a=run(new TstRelay1E(n,{dirtyDigit:alt.dirtyDigit}));
const rw=relay.install(new alt.D2Canonical(n,3),alt.dirtyDigit);const rr=run(rw);
console.log('alt D2Canonical(3) [4 helpers]',ref.ops,'| their relay(3) on alt D2C [3]',rr.ops,'diff',cmp(ref,rr),'| TstRelay1E alt [2]',a.ops,'diff',cmp(ref,a));
const wk=new TstRelayKE(n,2,{dirtyDigit:alt.dirtyDigit});wk.__map=new Map([[wk.tagR[1],wk.L[n+1]]]);const k2=run(wk);
const all=(x,y)=>{let d=0,qs=new Set();for(let q=0;q<1024;q++)for(let i=0;i<W;i++)if(x.s[q*W+i]!==y.s[q*W+i]){d++;qs.add(q);}return [d,[...qs].slice(0,10)];};
console.log('TstRelayKE(2) tag1=L[n+1]',k2.ops,'data diff',cmp(ref,k2),'all',JSON.stringify(all(ref,k2)),'| plain k2',run(new TstRelayKE(n,2,{dirtyDigit:alt.dirtyDigit})).ops);
