'use strict';
const path=require('path'),Module=require('module');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const prev=require('../q654-next/upper.cjs');
function one(s,a,b){if(s.split(a).length!==2)throw Error('unexpected upper source '+a);return s.replace(a,b);}
function upper(s){
  s=prev.upper(s);
  s=one(s,'this.wideBand=this.tag.length===this.tags.length;this.useCoefficientDirection=this.tag.length>=6;','this.deep=this.tag.length===7;this.wideBand=this.tag.length>=6;this.useCoefficientDirection=this.tag.length>=5;');
  s=one(s,'if(this.wideBand){this.tags[5]=this.borrow;this.tag[5]=this.borrow;}','if(this.wideBand){this.tags[top-1]=this.borrow;this.tag[top-1]=this.borrow;} if(this.deep){this.tags[4]=this.n.at(-1);this.tag[4]=this.n.at(-1);}');
  s=one(s,'layer.tags=this.tags.slice();layer.tags[5]=q;','layer.tags=this.tags.slice();layer.tags[this.tag.length-2]=q;if(this.deep){layer.tags[4]=this.r.at(-1);layer.r=this.r.slice(0,-1);}');
  s=one(s,'if(!this.wideBand){layer.digit(tape,z,S,[this.take],back);return;}','if(!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}');
  s=one(s,'this.layouts()?this.dv[1]:this.tags.at(-3)','this.layouts()?this.dv[1]:this.tags.at(-4)');
  s=one(s,'if(!hasOne)super.toggle(tape,base,no.concat(high.filter(q=>!no.includes(q))),target);',`if(!hasOne)super.toggle(tape,base,no.concat(high.filter(q=>!no.includes(q))),target);
      if(this.packedShort){const pos=this.tag[3],neg=this.tag.filter((v,i)=>i!==3);
        if(!no.includes(pos)&&!neg.some(q=>base.includes(q)))super.toggle(tape,base.includes(pos)?base:base.concat(pos),no.concat(neg.filter(q=>!no.includes(q))),target);
      }`);
  s=one(s,'    tailDigit(tape,layer,z,S,back){',`    layouts(){
      if(!this.packedShort)return super.layouts();
      const out=[];
      for(const [lo,hi] of [[0,8],[9,this.maxShift]]){
        const w=hi+6,W=w+1,spare=this.n.slice(1,Math.max(1,lo));
        const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1),free=[...this.q.slice(W+1),...spare];
        if(T.length!==W+1||free.length<2)throw Error('unfunded positive rank');
        const H=[...this.n.slice(this.m-w+1),free[1]],D=[free[0],...H];
        if(new Set([...T,...D]).size!==T.length+D.length)throw Error('short divisor overlaps quotient');
        out.push({lo,hi,w,W,T,D,H,d0:free[0]});
      }return out;
    }
    affine(tape,back){
      if(!this.deep){super.affine(tape,back);return;}
      const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[4]=this.A[this.half];super.affine.call(layer,tape,back);
    }
    tailDigit(tape,layer,z,S,back){`);
  s=one(s,'const dirs=()=>temp.direction(tape);\n      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>this.normalize(tape,rv)];',`const dirs=()=>temp.direction(tape);
      if(this.deep){
        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),low=Object.create(this),work=Object.create(this);
        const rank=this.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;
        low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);
        const choose=rv=>{const ops=[()=>this.toggle(tape,[this.g,this.take,hi],[],free),()=>this.toggle(tape,[this.g,free],[],this.take)];stepList(ops,rv,fn=>fn());};
        const setOne=()=>{if(!witness)this.toggle(tape,[this.g,this.take,hi],[],this.q[0]);};
        const pack=rv=>this.mixed(tape,short,this.v,this.u,[],rv);
        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);
        const steps=[dirs,pack,moved,setOne,choose,norm,bias];
        for(const band of low.layouts())steps.push(rv=>witness?low.oddWitness(tape,band,rv):low.oddQuotient(tape,band,rv));
        steps.push(rv=>bias(!rv),rv=>norm(!rv),rv=>choose(!rv),rv=>moved(!rv),rv=>pack(!rv),dirs);
        stepList(steps,back,fn=>fn(back));return;
      }
      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>this.normalize(tape,rv)];`);
  s=one(s,'this.ids=this.ids.slice(0,-2);','this.ids=this.ids.slice(0,-3);');
  s=one(s,'...split(2*m+b+1,logical-3)];','...split(2*m+b+1,logical-4)];');
  s=one(s,'new Set(map).size!==logical-3||map.length!==logical-3','new Set(map).size!==logical-4||map.length!==logical-4');
  s=one(s,'2*m+m/2+7+Math.ceil(Math.log2(m/2))','2*m+m/2+6+Math.ceil(Math.log2(m/2))');
  s=one(s,'(i===648||i>=654)?-2:clean[z++];if(clean.length!==13||z!==13)','(i===648||i>=653)?-2:clean[z++];if(clean.length!==12||z!==12)');
  s=one(s,'ids[645]=-2;ids[653]=-2;','ids[645]=-2;ids[652]=-2;ids[653]=-2;');
  s=one(s,'if(j!==13)throw Error("Q654 history geometry");','if(j!==12)throw Error("Q653 history geometry");');
  return s;
}
function upperComponent(){const f=path.join(joined,'checkpoint/centered-point.cjs');const s=checkedSource(f,'10790de4c79338419f92a5a2fd72017c829fc94900fe053627884cddc568283a');const m=new Module(f,module);m.filename=f;m.paths=module.paths;m._compile(upper(s),f);return m.exports;}
module.exports={upper,upperComponent};
