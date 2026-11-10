'use strict';
const path=require('path');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const base=checkedSource(path.join(__dirname,'../width109-handoff/emit109-reverse-digits.cjs'),'4cb72b84fa2b004d7b86dfe826a3d4183e23f4705cb589f83b432fa7eaf33cc4');
function one(src,a,b){if(src.split(a).length!==2)throw Error('walk splice '+a);return src.replace(a,b);}
const make=(src,name)=>Function('module',src+'\nreturn '+name+';')({exports:{}});
const Signed=make(base,'UnitWalk');
let generic=one(base,'this.zer([],A.slice(1),this.tst)','this.zer([],r,this.tst)');
generic=one(generic,'one(all,()=>this.op([L[n-k]],this.tst));','one(all,()=>this.op([this.fire,L[n-k]],this.tst));');
generic=one(generic,'this.op([L[n-k]],this.fire);','const nonempty=()=>{this.zer([],R.slice(0,m+1),this.tst);this.raw(-1,-1,this.tst);};nonempty();this.op([this.tst,L[n-k]],this.fire);this.reverse(nonempty);');
class Reduced extends make(generic,'UnitWalk'){
  plan(){
    const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire];
    const push=fn=>all.push({fn,rev:false});
    for(let bits=1;bits<=n;bits++){
      const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);
      push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);
    }
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;
  }
}

// A second public subtrial handles a normalization distance >=2^6.
// Each distance group recomputes readiness from the current state and
// erases it from the old divisor, which is explicit in the post-row L.
let split=one(base,'const rot=(ar,w,controls,dir)=>{','const rot=(ar,w,controls,dir,base=0)=>{if(base)one(ar,()=>this.rot(controls,w,dir*base));');
split=one(split,'const norm=(ar,w,controls)=>{','const norm=(ar,w,controls,base=0)=>{if(base)one(ar,()=>this.rot(controls,w,base));');
split=one(split,'const val=(w,controls,bias)=>{const a=mk();norm(a,w,controls);rot(a,w,controls,-1);','const val=(w,controls,bias,base=0)=>{const a=mk();norm(a,w,controls,base);rot(a,w,controls,-1,base);');
split=one(split,'one(all,()=>select(this.fire));\n   if(k>0&&k<n-1){const cp=[this.tst];','if(k>0&&k<n-1){const cp=[this.tst];one(all,()=>select(this.fire));');
split=one(split,'one(all,()=>this.op([L[n-k]],this.tst));\n   }','one(all,()=>this.op([L[n-k]],this.tst));one(all,()=>select(this.fire));\n   }');
split=one(split,'one(all,()=>this.op(c,R[m]));norm(all,r,c);',`
   const stride=1<<tag.length;
   for(let base=Math.floor((m-1)/stride)*stride;base>=0;base-=stride){
    const hi=Math.min(m-1,base+stride-1);
    const match=(controls,word,out)=>{
      this.zer(controls,word.slice(m-base),out);
      if(base+stride<m)this.zer(controls,word.slice(m-base-stride),out);
    };
    const eq=(i)=>{if(i>=base&&i<=hi)this.multag(c,i-base,[],this.tst);};
    if(base===0&&hi===m-1)one(all,()=>select(this.fire));
    else one(all,()=>{select(this.fire);match(c,r,this.aux);select(this.fire);this.op([this.aux],this.fire);this.op(c,this.aux);});
    one(all,()=>this.op(c,R[m]));norm(all,r,c,base);`);
split=one(split,'i<m-1;i++)one(all,()=>{this.multag(c,i,[],this.tst);','i<hi;i++)one(all,()=>{eq(i);');
split=one(split,'one(all,()=>this.multag(c,m-1,[],this.tst));','one(all,()=>eq(hi));');
split=one(split,'i=m-2;i>=0;i--)one(all,()=>{this.multag(c,i+1,[],this.tst);','i=hi-1;i>=0;i--)one(all,()=>{eq(i+1);');
split=one(split,'this.op(c,this.tst);this.multag(c,0,[],this.tst);','this.op(c,this.tst);eq(0);');
split=one(split,'rot(all,r,c,-1);','rot(all,r,c,-1,base);');
split=one(split,'rot(all,L.slice(0,n+1),c,-1);','rot(all,L.slice(0,n+1),c,-1,base);');
split=one(split,'cat(all,val(r,c,0),true);','cat(all,val(r,c,0,base),true);');
split=one(split,'this.op([L[n-k]],this.fire);});','if(base===0&&hi===m-1)this.op([L[n-k]],this.fire);else match([L[n-k]],L.slice(0,m),this.fire);});\n   }');
class SectorCanonical extends make(split,'FlatUnit'){
  constructor(n,tagBits=6){super(n);this.tag=this.tag.slice(0,Math.min(tagBits,this.tag.length));}
}

// The highest tag bit is stored in the active coefficient's top bit. Each
// block carries the exact remapping, including reversed valuation blocks.
function emitWalk(w,L,R,ws,dirty,back,sink){
  const ports=new Int16Array(w.nq);ports.fill(-1);
  const bind=(a,b)=>{for(let i=0;i<a.length;i++)ports[a[i]]=b[i];};
  bind(w.L,L);bind(w.R,R);bind(w.y,dirty);bind(w.tag,ws.tag);
  ports[w.sign]=ws.sign;ports[w.fire]=ws.fire;ports[w.tst]=ws.tst;ports[w.aux]=ws.aux;
  const top=w.tag.at(-1),blocks=w.plan();if(back)blocks.reverse();
  for(const block of blocks){
    w.g=[];block.fn();if(!!block.rev!==back)w.g.reverse();
    const physical=x=>{if(x===1023)return x;if(x===top){if(block.topPort==null)throw Error('height outside row');x=block.topPort;}if(ports[x]<0||ports[x]===undefined)throw Error('unbound walk port '+x);return ports[x];};
    for(let i=0;i<w.g.length;i++){
      const x=w.g[i],a=physical(x>>>20&1023),b=physical(x>>>10&1023),t=physical(x&1023);
      if(a===t||b===t||a!==1023&&a===b)throw Error('physical walk alias');
      w.g[i]=(a<<20)|(b<<10)|t;
    }
    sink('packed',w.g);
  }
}
module.exports={Reduced,Signed,SectorCanonical,emitWalk};
