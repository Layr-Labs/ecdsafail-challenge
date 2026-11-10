'use strict';
const fs=require('fs'),path=require('path'),Module=require('module');
const {joined,checkedSource}=require('../field128-height-experiment/pinned.cjs');
const previous=require('../q655-next/point.cjs');
const fieldName=path.join(__dirname,'../field655-boundary/index.cjs');
const field=checkedSource(fieldName,'3948e5f5587bfef3bdec559c69590e7292972ba23c77c1f255f1821816ff640b');
const digitText=field.slice(field.indexOf('function dirtyDigit('),field.indexOf('\nlet f=replace'));
if(!digitText.startsWith('function dirtyDigit(')||!digitText.endsWith('\n'))throw Error('missing restoring digit');
function one(src,from,to){if(src.split(from).length!==2)throw Error('unexpected upper source '+from);return src.replace(from,to);}
function upper(src){
  src=previous.installUpper(src);
  src=one(src,'this.useCoefficientDirection=this.tag.length===this.tags.length;','this.wideBand=this.tag.length===this.tags.length;this.useCoefficientDirection=this.tag.length>=6;');
  src=one(src,'const top=this.tags.length-1,free=this.dv[1];','const top=this.tag.length-1,free=this.dv[1];if(this.wideBand){this.tags[5]=this.borrow;this.tag[5]=this.borrow;}');
  const methods=`
    withDivisor(tape,band,run,back){
      if(!this.wideBand){super.withDivisor(tape,band,run,back);return;}
      this.roundedDivisor(tape,band,false);
      this.inUpperHalf=band.lo!==0;
      run([this.g,this.take,-19],back);
      this.inUpperHalf=null;
      this.roundedDivisor(tape,band,true);
    }
    toggle(tape,yes,no,target){
      if(!yes.includes(-19)){super.toggle(tape,yes,no,target);return;}
      if(this.inUpperHalf==null)throw Error('unresolved band');
      const base=yes.filter(q=>q!==-19),high=this.tag.slice(3),hasOne=high.some(q=>base.includes(q));
      if(this.inUpperHalf)super.toggle(tape,base,no,target);
      if(!hasOne)super.toggle(tape,base,no.concat(high.filter(q=>!no.includes(q))),target);
    }
    cnotList(tape,controls,word){
      if(!controls.includes(-19)){super.cnotList(tape,controls,word);return;}
      for(const q of word)this.toggle(tape,controls,[],q);
    }
    alignedSign(tape,target){
      if(!this.wideBand){super.alignedSign(tape,target);return;}
      const layer=Object.create(this),q=this.v[this.k];
      layer.tags=this.tags.slice();layer.tags[5]=q;
      tape.out(NONE,this.take,q);super.alignedSign.call(layer,tape,target);tape.out(NONE,this.take,q);
    }
    tailDigit(tape,layer,z,S,back){
      if(!this.wideBand){layer.digit(tape,z,S,[this.take],back);return;}
      const loan=tape.loan([...z,...S,this.take],1)[0];
      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);
      stepList(ops,back,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
    }
`;
  src=one(src,'class UnguardedGeneral extends OddEstimateGeneral {',digitText+'\nclass UnguardedGeneral extends OddEstimateGeneral {'+methods);
  src=one(src,'const ops=[mark,rr=>layer.digit(tape,z,S,[this.take],!rr),','const ops=[mark,rr=>this.tailDigit(tape,layer,z,S,!rr),');
  src=one(src,'if(this.useCoefficientDirection)tape.out(NONE,this.take,this.v[this.k])','if(this.useCoefficientDirection&&!this.wideBand)tape.out(NONE,this.take,this.v[this.k])');
  src=one(src,'this.layouts()?this.dv[1]:this.tags.at(-2)','this.layouts()?this.dv[1]:this.tags.at(-3)');
  src=one(src,'this.ids=this.ids.slice(0,-1);','this.ids=this.ids.slice(0,-2);');
  src=one(src,'...split(2*m+b+1,logical-2)];','...split(2*m+b+1,logical-3)];');
  src=one(src,'new Set(map).size!==logical-2||map.length!==logical-2','new Set(map).size!==logical-3||map.length!==logical-3');
  src=one(src,'2*m+m/2+8+Math.ceil(Math.log2(m/2))','2*m+m/2+7+Math.ceil(Math.log2(m/2))');
  src=one(src,'(i===648||i>=655)?-2:clean[z++];if(clean.length!==14||z!==14)','(i===648||i>=654)?-2:clean[z++];if(clean.length!==13||z!==13)');
  src=one(src,'ids[645]=-2;ids[655]=-2;ids[656]=-2;','ids[645]=-2;ids[653]=-2;ids[655]=-2;ids[656]=-2;');
  src=one(src,'if(j!==14)throw Error("Q655 history geometry");','if(j!==13)throw Error("Q654 history geometry");');
  return src;
}
function upperComponent(){
  const f=path.join(joined,'checkpoint/centered-point.cjs');
  const s=checkedSource(f,'10790de4c79338419f92a5a2fd72017c829fc94900fe053627884cddc568283a');
  const m=new Module(f,module);m.filename=f;m.paths=module.paths;m._compile(upper(s),f);return m.exports;
}
module.exports={upper,upperComponent};
