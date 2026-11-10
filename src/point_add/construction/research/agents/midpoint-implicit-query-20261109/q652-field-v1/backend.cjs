'use strict';
const B=require('./base.cjs');
const {replace,dirtyDigit,dirtyMdg,dirtyBlock,lowValuationSweep,plusOneMod,emitWalk,SectorReduced,SectorCanonical}=B;

// Simultaneously negate the contribution of the same dirty wire twice;
// the output is enabled by the conjunction of ctl and each x.
let f=replace(B.f,'tick(ctl,xs,ys,b){const h=this.helper;for(let j=0;j<xs.length;j++){this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);this.raw(ctl,xs[j],h);}}',
    'tick(ctl,xs,ys,b){const h=this.y[0];for(let j=0;j<xs.length;j++){this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);this.raw(ctl,xs[j],h);this.raw(h,ys[j],b);}}');
f=replace(f,'m[W.sign]=m[W.tag[6]];return m;',
    'm[W.sign]=5*n+6;m[W.R[n+1]]=5*n+5;m[W.fire]=5*n+5;return m;');
f=replace(f,'q===G.tag[6]?block.topPort:q','q===G.tag.at(-1)?block.topPort:q');
f=replace(f,'for(let j=0;j<W.tag.length;j++)m[W.tag[j]]=5*n+j','for(let j=0;j<7;j++)m[W.e+2+j]=5*n+j');
f=replace(f,'idx=vec(3,649)','idx=vec(2,649)');
// Keep the three signed powers in the prime residue. Use one dirty word
// twice with a different position for the lower power before restoring it.
f=replace(f,'const loc=[10,32,256],R=[];let k=0;for(let j=0;j<257;j++){const a=loc.indexOf(j);R.push(a<0?L[k++]:idx[a]);}run(remprep(128,257,T,R,C,H,en,idx,[2],[1,0]),back);',
    'const term=(loc,pos,neg)=>{const R=[];let k=0;for(let j=0;j<257;j++){const a=loc.indexOf(j);R.push(a<0?L[k++]:idx[a]);}return remprep(128,257,T,R,C,H,en,idx,pos,neg);};const terms=[[[32,256],[1],[0]],[[10,256],[],[0]]];for(const [loc,pos,neg] of (back?terms.reverse():terms))run(term(loc,pos,neg),back);');
f=replace(f,'shprod(128,T,H,C,L,[649,650,651,655])','shprod(128,T,H,C,L,[649,650,655])');
f=replace(f,'mac=madd(M,rr,C,tmp),ar=sub?','mac=normalizedMadd(M,rr,C),ar=sub?');
const multiply=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod','normalizedMadd',
    f+'\nreturn emitForward128;')({exports:{}},SectorCanonical,dirtyDigit,lowValuationSweep,plusOneMod,require('./normalized-madd.cjs').normalizedMadd);

let d=replace(B.d,'const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=flagHeight(v,t,e,loan),put=g=>sink(\'nct\',g);',`
  const groups={2:2,64:3,96:65,112:97,120:113,124:121,125:125,126:126,127:127,128:128},lo=groups[t];
  if(lo===undefined)continue;
  const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],put=g=>sink('nct',g);
  const zero=(word,dest)=>mcN(word,word.map(()=>false),dest,loan);
  const cls=lo===t?flagHeight(v,t,e,loan):zero(v.slice(t),e).concat(zero(v.slice(lo-1),e)),park=[];
  if(lo<t)for(let j=lo;j<=t;j++){
    const z=v[t+j-lo],tail=v.slice(j,t),test=[e,...tail,z],match=[true,...tail.map(()=>false),true];
    const target=j===t?gap:u[j];
    if(z===undefined)throw Error('no zero divisor site for packed gcd');
    park.push([target,z],...mcN(test,match,target,loan),[target,z]);
  }`);
d=replace(d,"put(cls);if(t===2)put([[e,J[0]]]);else pModShear(",
    "put(cls);put(park);if(t===2)put([[e,J[0]]]);else pModShear(");
d=replace(d,'neg();cond();neg();cond();put([...cls].reverse());',
    'neg();cond();neg();cond();put(park.slice().reverse());put([...cls].reverse());');
const divide=Function('module','dirtyMdg','dirtyBlock','emitWalk','Reduced','SectorCanonical',
    require('./divide-port.cjs').thinDivide(d)+'\nreturn inverseField;')({exports:{}},dirtyMdg,dirtyBlock,emitWalk,SectorReduced,SectorCanonical);

// Narrow global site numbers before the point allocator. Sparse q648 is
// permanently reserved for the caller and is never a data gate.
function mapped(sink,back){
    const free=back?[648,652,653,654,655,656]:[648,651,652,653,654,656];
    const move=back?651:655, dest=651;
    const port=q=>{if(q===1023)return q;if(q<0||q>656||free.includes(q))throw Error('removed scalar site '+[back,q]);return q===move?dest:q;};
    return(kind,data)=>{
        if(kind==='packed'){
            const out=new Uint32Array(data.length);
            for(let i=0;i<data.length;i++){const x=data[i];out[i]=(port(x>>>20&1023)<<20)|(port(x>>>10&1023)<<10)|port(x&1023);}
            sink(kind,out);
        } else if(kind==='nct')sink(kind,data.map(g=>g.map(port)));
        else sink(kind,data.map((q,i)=>i===data.length-1?q:port(q)));
    };
}
function emitMultiplySparse(sink){multiply(mapped(sink,false));}
function emitDivideSparse(sink){divide(128,null,null,mapped(sink,true));}
module.exports={emitMultiplySparse,emitDivideSparse};
