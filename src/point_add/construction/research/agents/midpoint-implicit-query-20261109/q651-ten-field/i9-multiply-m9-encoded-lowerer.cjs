'use strict';
const fs=require('fs');
const xor=(a,b)=>{const o=new Set(a);for(const t of b)o.has(t)?o.delete(t):o.add(t);return o;},mul=(a,b)=>{const o=new Set;for(const x of a)for(const y of b){const t=x|y;o.has(t)?o.delete(t):o.add(t);}return o;};
const V=q=>new Set([1n<<BigInt(q)]),ONE=new Set([0n]),NOT=p=>xor(ONE,p),and=arr=>arr.reduce(mul,ONE);
function initial(){const c0=V(640),c1=V(641),c=[mul(NOT(c0),NOT(c1)),mul(c0,NOT(c1)),mul(NOT(c0),c1),mul(c0,c1)],r0=V(0),r1=V(1),E=new Map;
 E.set(900,mul(r0,c[0]));E.set(901,mul(r1,xor(c[0],c[1])));for(let j=2;j<7;j++)E.set(900+j,mul(V(j),NOT(c[3])));
 E.set(907,xor(mul(xor(c[1],c[2]),NOT(r0)),mul(c[3],r0)));
 E.set(908,xor(xor(mul(c[1],r0),mul(c[2],NOT(xor(r0,r1)))),mul(c[3],r1)));
 E.set(909,xor(mul(c[2],xor(xor(r0,r1),mul(r0,r1))),mul(c[3],V(2))));return E;
}
const map=q=>q<7?900+q:q>=640&&q<=642?907+q-640:q>=643&&q<=646?q-1:q;

function vars(p){let b=0n;for(const x of p)b|=x;return b;}
function list(m){const a=[];for(let q=0;m;q++,m>>=1n)if(m&1n)a.push(q);return a;}
// Negative Davio chooses complements to factor count predicates.
function cubes(p,depth=0){if(!p.size)return[];if(p.size===1)return[[p.values().next().value,0n]];
 let common=null;for(const t of p)common=common===null?t:common&t;
 if(common){const r=new Set([...p].map(t=>t^common));return cubes(r,depth+1).map(([a,b])=>[a|common,b]);}
 const counts=new Map;for(const t of p)for(const q of list(t))counts.set(q,(counts.get(q)||0)+1);
 let q=[...counts].sort((a,b)=>b[1]-a[1])[0][0],bit=1n<<BigInt(q),p0=new Set,p1=new Set;
 for(const t of p)(t&bit?p1:p0).add(t&~bit);
 const f1=xor(p0,p1),negative=f1.size<p0.size,base=negative?f1:p0;
 return [...cubes(base,depth+1),...cubes(p1,depth+1).map(([a,b])=>negative?[a,b|bit]:[a|bit,b])];
}
function lowerer(emit,primitives){let E=initial(),unions=new Map([...E].map(([q,p])=>[q,vars(p)])),gates=0,emitted=0,maxTerms=0,cache=new Map;const physicalSkip=new Set([0,1,2,3,4,5,6,640,641,646]);
 function output(p,z){if(!p.size)return;const zk=1n<<BigInt(z);if(vars(p)&zk)throw Error('nonreversible virtual target sourceGate='+gates+' target='+z+' terms='+p.size);
  let key=[...p].sort((a,b)=>a<b?-1:1).map(x=>x.toString(16)).join(','),rows=cache.get(key);if(!rows){rows=cubes(p).map(([a,b])=>[list(a|b),list(b)]);if(cache.size>20000)cache.clear();cache.set(key,rows);}
  for(const [cs,neg]of rows){const used=new Set([...cs,z,...physicalSkip]),dirty=Array.from({length:646},(_,i)=>i).filter(q=>!used.has(q));for(const q of neg){emit(1023,1023,q);emitted++;}for(const row of primitives.MCX(cs,z,dirty)){emit(row.length>1?row[0]:1023,row.length>2?row[1]:1023,row.at(-1));emitted++;}for(const q of neg.slice().reverse()){emit(1023,1023,q);emitted++;}}
 }
 return{gate(a,b,t){a=map(a);b=map(b);t=map(t);gates++;const cs=[a,b].filter(q=>q!==1023),C=and(cs.map(q=>E.get(q)||V(q))),bit=1n<<BigInt(t);
  if(E.has(t)){const p=xor(E.get(t),C);E.set(t,p);unions.set(t,vars(p));maxTerms=Math.max(maxTerms,p.size);if(p.size>5000)throw Error('symbolic cap, not a circuit approximation');return;}
  if(cs.every(q=>!E.has(q))){emit(a,b,t);emitted++;}else output(C,t);
  for(const [q,p]of E)if(unions.get(q)&bit){const before=new Set,deriv=new Set;for(const term of p)(term&bit?deriv:before).add(term&~bit);const next=xor(before,mul(deriv,xor(V(t),C)));E.set(q,next);unions.set(q,vars(next));maxTerms=Math.max(maxTerms,next.size);if(next.size>5000)throw Error('symbolic cap, not a circuit approximation');}
 },check(){const ref=initial();for(const [q,p]of E){if(xor(p,ref.get(q)).size)throw Error('encoded state not restored '+q+' terms='+p.size);}return{gates,emitted,maxTerms};},stats(){return{gates,emitted,maxTerms,terms:Object.fromEntries([...E].map(([q,p])=>[q,p.size]))};}};
}
module.exports={lowerer,initial,cubes};
