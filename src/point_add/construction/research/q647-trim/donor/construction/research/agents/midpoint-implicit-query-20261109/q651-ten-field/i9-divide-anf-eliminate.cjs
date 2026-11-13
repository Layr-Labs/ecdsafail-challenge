'use strict';
// Exact Boolean substitution, exploratory bounded representation. A cap is OPEN.
// Polynomials are XOR sets of square-free monomials in live basis variables.
function make(h,emit,{cap=4096,loan=[],value=0,cubes=false}={}){
 let E=new Map(value?[['',[]]]:[]),events=0,emitted=0,maxTerms=0,maxDegree=0,deps=new Set();
 const mono=xs=>[...new Set(xs)].sort((a,b)=>a-b),key=xs=>xs.join(','),toggle=(out,xs)=>{const k=key(xs);if(out.has(k))out.delete(k);else out.set(k,xs);};
 const variable=w=>new Map([[String(w),[w]]]),one=()=>new Map([['',[]]]);
 const mult=(a,b)=>{const out=new Map();for(const x of a.values())for(const y of b.values())toggle(out,mono([...x,...y]));return out;};
 let cubeCache=null;
 function cubeList(){if(cubeCache)return cubeCache;const memo=new Map();function tree(poly){if(!poly.size)return [];if(poly.size===1&&poly.has(''))return [[]];const id=[...poly.keys()].sort().join(';');if(memo.has(id))return memo.get(id);const counts=new Map();for(const xs of poly.values())for(const q of xs)counts.set(q,(counts.get(q)||0)+1);let chosen=null,best=-1;for(const[q,k]of counts)if(k>best){chosen=q;best=k;}const low=new Map(),high=new Map();for(const xs of poly.values()){if(!xs.includes(chosen))toggle(low,xs);toggle(high,xs.filter(q=>q!==chosen));}const out=[];for(const [v,p]of [[false,low],[true,high]])for(const rest of tree(p))out.push([[chosen,v],...rest]);memo.set(id,out);return out;}cubeCache=tree(E);return cubeCache;}
 function controlledE(cs,z,C){if(deps.size>10||E.size<4)return false;const cost=n=>n<3?1:4*n-8,limit=[...C.values()].reduce((a,x)=>a+cost(x.length),0),plans=[];let total=0;for(const cube of cubeList()){const all=new Map(cube);let contradiction=false;for(const q of cs){if(all.has(q)&&!all.get(q)){contradiction=true;break;}all.set(q,true);}if(contradiction)continue;const neg=[...all].filter(([q,v])=>!v).map(([q])=>q);total+=2*neg.length+cost(all.size);if(total>=limit)return false;plans.push({cs:[...all.keys()],neg});}for(const p of plans){for(const q of p.neg){emit([q]);emitted++;}mcx(p.cs,z);for(const q of p.neg){emit([q]);emitted++;}}return true;}
 function mcx(cs,z){const d=loan.filter(w=>w!==z&&!cs.includes(w));if(cs.includes(z))throw Error('ANF nonreversible target '+z);if(cs.length<3){emit([...cs,z]);emitted++;return;}if(d.length<cs.length-2)throw Error('ANF dirty shortage');const m=[];for(let j=2;j<cs.length-1;j++)m.push([cs[j],d[j-2],d[j-1]]);const a=[cs[0],cs[1],d[0]],b=[cs.at(-1),d[cs.length-3],z];for(const r of [a,...m,b,...m.slice().reverse(),a,...m,b,...m.slice().reverse()]){emit(r);emitted++;}}
 function row(r){events++;const z=r.at(-1),cs=r.slice(0,-1);if(z!==h&&!cs.includes(h)&&!deps.has(z)){emit(r);emitted++;return;}let changed=false,C=one();for(const w of cs)C=mult(C,w===h?E:variable(w));
  if(z===h){for(const xs of C.values())toggle(E,xs);changed=true;}else{
   if(!(cubes&&cs.includes(h)&&controlledE(cs.filter(q=>q!==h),z,C)))for(const xs of C.values())mcx(xs,z);
   if(deps.has(z)){const next=new Map();for(const xs of E.values()){
    toggle(next,xs);
    if(xs.includes(z))for(const ys of C.values())toggle(next,mono([...xs.filter(w=>w!==z),...ys]));
   }E=next;changed=true;}
  }
  if(changed){cubeCache=null;deps=new Set();maxTerms=Math.max(maxTerms,E.size);for(const xs of E.values()){maxDegree=Math.max(maxDegree,xs.length);for(const q of xs)deps.add(q);}}
  if(E.size>cap)throw Error('ANF_CAP '+JSON.stringify({events,emitted,terms:E.size,maxTerms,maxDegree}));
 }
 function sink(k,d){if(k==='packed')for(const x of d){const a=x>>>20&1023,b=x>>>10&1023;row([...(a===1023?[]:[a]),...(b===1023?[]:[b]),x&1023]);}else if(k==='nct')for(const r of d)row(r);else throw Error('ANF_NON_NCT '+k);}
 return{row,sink,stats:()=>({events,emitted,terms:E.size,maxTerms,maxDegree}),finish(){if(E.size!==value||(value&&!E.has('')))throw Error('ANF_LIVE '+JSON.stringify(this.stats()));return this.stats();}};
}
module.exports={make};
