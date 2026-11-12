'use strict';
// q648 (papers): colour off 647 in the can/mad/hmr/prep brackets (forward bracket 1 and the closing bracket 3).
// Colour lives on T127 (normalized T: T127 = 1 is X'd to 0 and receives can's digit bit). While it is there every use of T
// as a modulus is virtual-top (literal one), so the wire is never read as T's top:
//   can  : X(T127); r36digit([T0..126,1], C, T127)                       (= digit(n,T,C,color) for normalized T)
//   mad  : H += C mod T by the reverse of their dirty-scratch m6sub (dirty wire L[0])    (= r36madd with clean scratch)
//   prep : hole-free (no T127 dividend bit). P1 divides N1 = L + 2^256 C (r36nr(128,256)), CX-copies r1 into the clean H,
//          uncomputes. q648tr maps X = L + 2^256 C to X - p mod 2^256 T with DIRTY scratch only:
//            C <- C - f mod T, f = [L < p], as two reflections r(x) = T-1-x and r'(y) = T-2-y (on [0,T-1), T-1 fixed), each
//            applied under its predicate with the dirty-control identity V^h (h^=q) V^h (h^=q) (V an involution of Z_2^128
//            preserving q); then L <- L + delta mod 2^256 (the borrow went to C).
//          P2 divides N2 = N1 - p (mod T), m6sub subtracts r2 from H (dirty C[0]), uncomputes, q648tr^-1.
// Q648_COLOUR1=0 disables.
const HELP=`
function q648mcx(c,t,pool){if(c.length<3)return [[...c,t]];const free=pool.filter(q=>q!==t&&!c.includes(q));
 if(free.length>=c.length-2)return MCX(c,t,free);const b=free[0];if(b===undefined)throw Error('q648mcx pool');
 const h=Math.ceil(c.length/2),c1=c.slice(0,h),c2=c.slice(h),Pq=pool.filter(q=>q!==b);
 const A=q648mcx(c1,b,[...Pq,...c2,t]),B=q648mcx([...c2,b],t,[...Pq,...c1]);return [...A,...B,...A,...B];}
// t ^= AND(extra) & [R >= K] : the equality cube plus one cube per zero bit j of K (R_j=1, R_b=K_b above j)
function q648geK(R,K,t,pool,extra=[]){const g=[],cube=(cs,bs)=>{for(const x of negate(cs,q648mcx(cs,t,pool),bs))g.push(x);};
 {const cs=[...extra],bs=extra.map(()=>true);for(let b=0;b<R.length;b++){cs.push(R[b]);bs.push(Boolean((K>>BigInt(b))&1n));}cube(cs,bs);}
 for(let j=0;j<R.length;j++){if((K>>BigInt(j))&1n)continue;const cs=[...extra,R[j]],bs=[...extra.map(()=>true),true];
  for(let b=j+1;b<R.length;b++){cs.push(R[b]);bs.push(Boolean((K>>BigInt(b))&1n));}cube(cs,bs);}return g;}
// h ^= AND(es) & [A > B] with A = [T0..126, 1001] (virtual top): r36lt with a multi-wire enable
function q648lt(A,B,h,es,pool){const n=A.length,k=n-1,g=[],X=a=>g.push([a]),CX=(a,b)=>g.push([a,b]),T=(a,b,c)=>g.push([a,b,c]);
 const a=A.slice(0,-1),b=B.slice(0,-1),z=B.at(-1);if(A.at(-1)!==1001)throw Error('q648lt top');
 // [A > B] with A = 2^(n-1) + a: B top 0 -> A > B; B top 1 -> [a > b]
 const op=cs=>{for(const x of q648mcx([...es,...cs],h,pool.filter(q=>![...es,...cs,h].includes(q)&&!B.includes(q)&&!a.includes(q))))g.push(x);};
 X(z);op([z]);X(z);
 // z=1: h ^= [a > b] (ancilla-free comparator on n-1 bits, only the two toggles carry the controls)
 const m=a.length,last=m-1;for(const w of b)X(w);
 for(let i=1;i<m;i++)CX(a[i],b[i]);op([z,a[last]]);for(let i=m-2;i>=1;i--)CX(a[i],a[i+1]);for(let i=0;i<m-1;i++)T(b[i],a[i],a[i+1]);op([z,b[last],a[last]]);
 for(let i=m-2;i>=0;i--)T(b[i],a[i],a[i+1]);for(let i=1;i<m-1;i++)CX(a[i],a[i+1]);for(let i=1;i<m;i++)CX(a[i],b[i]);for(const w of b)X(w);
 return g;}
function q648tr(T,L,C,H){const ap=(a,...bs)=>{for(const b of bs)for(const x of b)a.push(x);return a;};const delta=(1n<<32n)+977n,P=(1n<<256n)-delta,Tv=[...T.slice(0,-1),1001],g=[];
 const pool=[...H,...T.slice(0,-1)],hr=H[0],hc=H[1];
 const fX=h=>[[h],...q648geK(L,P,h,[...C,...pool].filter(q=>q!==h))];          // h ^= [L < P]
 const rC=h=>[...C.map(z=>[h,z]),...r36plus(Tv,C,null,h)];                  // C -> T-1-C (mod 2^128) under h
 const coreC=h=>[...rC(h),...[...incReg(C,T.slice(0,-1).concat(H[2]),h)].reverse()];   // C -> T-2-C under h
 // h ^= f & g', g' = [C < T-1] = [T > C] xor [C+1 == T]  (no wrap: C = 2^128-1 gives g' = 0, as it must for the
 // reflection-invariant interval [T-1, 2^128)); f = [L<P] = 1 xor [L>=P] (equality cube + one cube per zero bit of P)
 const cubes=[];{const cs=[],bs=[];for(let b=0;b<L.length;b++){cs.push(L[b]);bs.push(Boolean((P>>BigInt(b))&1n));}cubes.push([cs,bs]);}
 for(let j=0;j<L.length;j++){if((P>>BigInt(j))&1n)continue;const cs=[L[j]],bs=[true];for(let b=j+1;b<L.length;b++){cs.push(L[b]);bs.push(Boolean((P>>BigInt(b))&1n));}cubes.push([cs,bs]);}
 const incG=pool.filter(q=>q!==hc).slice(0,128),inc=incReg(C,incG),xorT=[...T.slice(0,-1).map((q,j)=>[q,C[j]]),[C[127]]];
 const gtT=(h,es)=>q648lt(Tv,C,h,es,[...L,...pool].filter(q=>q!==h&&!es.includes(q)));
 const eqT=(h,es)=>{const o=[];ap(o,inc,xorT,negate(C,q648mcx([...es,...C],h,pool.filter(q=>q!==h&&!incG.includes(q))),C.map(()=>false)),[...xorT].reverse(),[...inc].reverse());return o;};
 const gq=h=>{const out=[];ap(out,gtT(h,[]),eqT(h,[]));
   for(const [cs,bs] of cubes){const neg=cs.filter((_,i)=>!bs[i]).map(q=>[q]);ap(out,neg,gtT(h,cs),eqT(h,cs),neg);}
   return out;};
 // r^f, then r'^(f & [C<T-1])
 ap(g,rC(hr),fX(hr),rC(hr),fX(hr));
 ap(g,coreC(hc),gq(hc),coreC(hc),gq(hc));
 // L += delta mod 2^256 (dirty word C,H,T-low for the increments; the carry out of L is dropped)
 for(const i of [0,4,6,7,8,9,32])ap(g,incReg(L.slice(i),[...C,...H,...T.slice(0,-1)]));
 return g;}
`;
module.exports={f:s=>{if(process.env.Q648_COLOUR1==='0')return s;
 const rep=(a,b)=>{if(s.split(a).length!==2)throw Error('q648 colour1 anchor '+a.slice(0,60));s=s.replace(a,()=>b);};
 const PC=new Set((process.env.Q648C1||'can,mad,prep').split(','));
 if(PC.has('can'))rep('can=digit(n,T,C,color),','can=[[T[127]],...r36digit([...T.slice(0,-1),1001],C,T[127])],');
 if(PC.has('mad'))rep('mad=[[T[127]],[color,T[127]],[T[127],color],[color,T[127]],...r36madd([...T.slice(0,-1),1001],C,H,color),[color,T[127]],[T[127],color],[color,T[127]],[T[127]]],',
     'mad=[...m6sub([...T.slice(0,-1),1001],C,H,L[0])].reverse(),');
 if(PC.has('prep')){const a=s.indexOf('function prep(back){'),e=s.indexOf('function unit(back){',a);if(a<0||e<0)throw Error('q648 prep anchor');
 const NEWP='function prep(back){const Tv=[...T.slice(0,-1),1001],D=[...L,...C],ops=r36nr(128,256,[...Tv,...D]),inv=[...ops].reverse(),copy=L.slice(0,128).map((q,i)=>[q,H[i]]),md=m6sub(Tv,L.slice(0,128),H,C[0]),tr=q648tr(T,L,C,H);run([].concat(ops,copy,inv,tr,ops,md,inv,[...tr].reverse()),back);}';
 s=s.slice(0,a)+NEWP+s.slice(e);}
 return HELP+s;}};
