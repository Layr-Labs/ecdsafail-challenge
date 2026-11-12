'use strict';
const path=require('path'),Module=require('module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {CanonicalUnit,ReducedGcdWalk}=require('../field128-height-experiment/walks.cjs');
const oldfile=path.join(__dirname,'../field655-boundary/index.cjs');
const prior=checkedSource(oldfile,'3948e5f5587bfef3bdec559c69590e7292972ba23c77c1f255f1821816ff640b');
const old=new Module(oldfile,module);old.filename=oldfile;old.paths=module.paths;old._compile(prior+'\nmodule.exports={f,d,replace,dirtyDigit};',oldfile);
const {f:oldF,d:oldD,replace,dirtyDigit}=old.exports;
const nativeDigits=checkedSource(path.join(__dirname,'../width109-handoff/emit109-reverse-digits.cjs'),
  '4cb72b84fa2b004d7b86dfe826a3d4183e23f4705cb589f83b432fa7eaf33cc4');
const VirtualCanonical=Function('module',nativeDigits+'\nreturn FlatUnit;')({exports:{}});

function lowValuationSweep(n,M,X,s,J,e,dirty,i,kappa,lib) {
  const {gt,negate,MCX,eq_bits,fr}=lib;
  const groupBit=M[n-1], guard=gt(s,i,e,null,dirty);
  let gates=guard.concat(dirtyDigit(M.slice(1),X.slice(0,-1),X[n-1],e,dirty[0]),[[groupBit]]);
  const prefix=(k)=>{
    if(k===0)return [[groupBit]];
    if(k>=n)return [];
    const cs=M.slice(0,k);
    return negate(cs,MCX(cs,groupBit,dirty),cs.map(()=>false));
  };
  const interval=1<<J.length;
  for(let base=0;base<n-1;base+=interval){
    const a=base===0?0:base+1, b=base+interval+1;
    const mark=prefix(a).concat(prefix(b));
    gates=gates.concat(mark);
    for(let j=base;j<Math.min(n-1,base+interval);j++){
      const pattern=eq_bits(J,j),ctrl=[e,groupBit,...J],sgn=[true,true,...pattern];
      gates=gates.concat(negate(ctrl.concat(X[j]),MCX(ctrl.concat(X[j]),X[n-1],dirty),sgn.concat(true)));
      if(i<=j&&((kappa>>BigInt(j-i))&1n))gates=gates.concat(negate(ctrl,MCX(ctrl,X[n-1],dirty),sgn));
    }
    gates=gates.concat(mark.reverse());
  }
  gates.push([groupBit]);
  for(let j=n-1;j>0;j--)gates.push(...fr(e,X[j],X[j-1]));
  return gates.concat(guard.slice().reverse());
}
function plusOneMod(M,H,t,dirty,lib){
  const {MCX,negate,plus,incReg}=lib, eq=[];
  for(let j=0;j<H.length;j++)eq.push([M[j],H[j]]);
  const zero=negate(H,MCX(H,t,dirty),H.map(()=>false));
  return incReg(H,dirty).concat(eq,zero,eq.slice().reverse(),plus(M,H,null,t).reverse(),zero);
}
let f=replace(oldF,'idx=vec(6,649)','idx=vec(5,649)');
const start=f.indexOf('function one_stage('),end=f.indexOf('function wideadd(',start);
if(start<0||end<=start)throw Error('normalization pass missing');
f=f.slice(0,start)+'function one_stage(n,outer,M,X,s,J,e,t,dirty,i,kappa){return lowValuationSweep(n,M,X,s,J,e,dirty,i,kappa,{gt,negate,MCX,eq_bits,fr});}\n'+f.slice(end);
f=replace(f,'function prep(back){const loc=[0,4,5,10,32,256],R=[];',
  'function prep(back){const inc=plusOneMod(T,H,en,L,{MCX,negate,plus,incReg});if(back)run(inc);const loc=[4,5,10,32,256],R=[];');
f=replace(f,'run(remprep(128,257,T,R,C,H,en,idx,[5,2,1],[4,3,0]),back);',
  'run(remprep(128,257,T,R,C,H,en,idx,[4,1,0],[3,2]),back);if(!back)run(inc,true);');
f=replace(f,'throw Error("wire map");return m;','throw Error("wire map");m[W.tst]=m[W.L[n+1]];return m;');
const multiply=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod',f+'\nreturn emitForward128;')({exports:{}},CanonicalUnit,dirtyDigit,lowValuationSweep,plusOneMod);

// In the fractional residue case the seventh quotient height bit shares
// the top coefficient bit during each selected Euclidean height band.
function virtualStream(n,L,R,ws,dirty,sink){
  const w=new VirtualCanonical(n),m=new Int16Array(w.nq);m.fill(-1);
  const bind=(a,b)=>{for(let j=0;j<a.length;j++)m[a[j]]=b[j];};
  bind(w.L,L);bind(w.R,R);bind(w.y,dirty);bind(w.tag,ws.tag);
  m[w.sign]=ws.sign;m[w.fire]=ws.fire;m[w.tst]=ws.tst;m[w.aux]=ws.tag[6];
  for(const p of w.plan()){
    w.g=[];p.fn();if(p.rev)w.g.reverse();
    function phys(id){
      if(id===1023)return id;
      if(id===w.tag[6]){if(p.topPort==null)throw Error('unbound borrowed height');id=p.topPort;}
      if(m[id]<0)throw Error('unbound inner port '+id);return m[id];
    }
    for(let i=0;i<w.g.length;i++){
      const x=w.g[i],a=phys(x>>>20&1023),b=phys(x>>>10&1023),t=phys(x&1023);
      if(a===t||b===t||(a===b&&a!==1023))throw Error('inner physical alias');
      w.g[i]=(a<<20)|(b<<10)|t;
    }
    sink('packed',w.g);
  }
}

function moveGcdPad(n,L,V,flag,loan,sink,rev,lib){
  for(let i=0;i<n;i++){
    const t=rev?n-i:i+1,sel=lib.flagHeight(V,t,flag,loan),gap=n+1-t;
    sink('nct',sel);sink('nct',lib.fr(flag,L[0],L[gap]));sink('nct',sel.slice().reverse());
  }
}
let d=replace(oldD,'ws={sign:sig,tag:S,fire:e,tst:t,aux:x}','ws={sign:sig,tag:S,fire:e,tst:t,aux:L[n+1]}');
d=replace(d,'outerloadJ(n,terms,L,R,Q,sig,loan,temps,sink);',
 'moveGcdPad(n,L,vt,rm[1],loan,sink,false,{flagHeight,fr});outerloadJ(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);moveGcdPad(n,L,vt,rm[1],loan,sink,true,{flagHeight,fr});');
d=replace(d,'const [e,t,h,D]=ws,put=g=>','const [e,t,D]=ws,put=g=>');
d=replace(d,'Wstream(Wc,n,false,[...vt,R[1],R[1]],[...Q,L[0],L[0]],wi,loan,sink);',
 'virtualStream(n,[...vt,R[1],R[1]],[...Q,L[0],L[0]],wi,loan,sink);');
const divide=Function('module','virtualStream','moveGcdPad',d+'\nreturn inverseField;')({exports:{}},virtualStream,moveGcdPad);

function mapped(sink,back,dense){
  const m=new Int16Array(1024);m.fill(-1);m[1023]=1023;
  for(let q=0;q<=655;q++){
    const third=back?652:654;if(q===648||q===third)continue;
    const p=q===655?third:q;m[q]=dense&&p>648?p-1:p;
  }
  const wire=id=>{if(m[id]<0||m[id]===undefined)throw Error('live removed site '+id);return m[id];};
  return(kind,data)=>{
    if(kind==='packed'){const g=new Uint32Array(data.length);for(let i=0;i<data.length;i++){
      const z=data[i];g[i]=(wire(z>>>20&1023)<<20)|(wire(z>>>10&1023)<<10)|wire(z&1023);
    }sink(kind,g);}
    else if(kind==='nct')sink(kind,data.map(row=>row.map(wire)));
    else sink(kind,data.map((q,i)=>i===data.length-1?q:wire(q)));
  };
}
function emitMultiplySparse(sink){multiply(mapped(sink,false,false));}
function emitDivideSparse(sink){divide(128,ReducedGcdWalk,CanonicalUnit,mapped(sink,true,false));}
function emitMultiply654(sink){multiply(mapped(sink,false,true));}
function emitDivide654(sink){divide(128,ReducedGcdWalk,CanonicalUnit,mapped(sink,true,true));}
module.exports={emitMultiplySparse,emitDivideSparse,emitMultiply654,emitDivide654};
