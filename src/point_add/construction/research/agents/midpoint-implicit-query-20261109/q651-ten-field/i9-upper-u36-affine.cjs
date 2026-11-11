'use strict';
// Source-only U31 extension; all remaining affine bodies share one high-rank code.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U36 anchor '+a);s=s.replace(a,()=>b);};
 one('if(this.k<112){this.affine(tape,back);return;}','');
 one('if(this.k<112){this.u31AffineBody(tape,back);return;}','');
 one('      if(!this.deep){super.affine.call(H,tape,back);return;}',`      if(this.k<112){
        H.tag=[this.A[0],this.A[this.half-1],this.v[this.k]];
        H.u3Affine=true;H.u37Slot=2;H.u38Implicit=true;H.u12=true;H.u22=true;
        H.u36=true;H.u36Bits=Math.ceil(Math.log2(this.maxShift+1))-4;H.u36High=this.A[this.half+1];H.u22Marker=this.A[this.half];H.rankHost=this.pick;H.digit=H.digitDirty;
        super.affine.call(H,tape,back);return;
      }
      if(!this.deep){super.affine.call(H,tape,back);return;}`);
 one('    u22Normalize(tape,a,back){','    u22Normalize(tape,a,back){\n      if(this.u36){this.u36Normalize(tape,a,back);return;}');
 one('      const hi=j>>5,lo=j&31;\n      for(let q=0;q<4;q++){','      const hi=j>>(this.u36?3:5),lo=j&(this.u36?7:31);\n      for(let q=0;q<(this.u36?2**(this.u36Bits+1):4);q++){');
 one('code=this.A.slice(2,4),yes=[],no=[];', 'code=this.A.slice(this.u36?1:2,this.u36?1+this.u36Bits:4),yes=[],no=[];');
 one('      for(let j=0;j<2;j++)seq.push(rv=>{\n        const k=(32<<j)%word.length,', '      for(let j=0;j<(this.u36?this.u36Bits:2);j++)seq.push(rv=>{\n        const k=((this.u36?8:32)<<j)%word.length,');
 one('host=this.A.slice(0,this.u22?4:2),tp=Object.create(tape);','host=this.A.slice(0,this.u36?1+this.u36Bits:this.u22?4:2),tp=Object.create(tape);');
 one('      if(this.u22)base.push([cube([host[2]],[this.u22Marker])],[cube([host[3]],[this.u22Marker])]);','      if(this.u22)for(let i=2;i<host.length;i++)base.push([cube([host[i]],[this.u22Marker])]);');

 one('this.tag.slice(3),false));','this.u36?[...this.tag.slice(3),this.u22Marker]:this.tag.slice(3),false));');
 one('        const p=this.u22Class(q),cs=controls.concat(p.yes);','        if(this.u36)L.u12=q===0;const p=this.u22Class(q),cs=controls.concat(p.yes);');
 one('          if(j<3)this.toggle(tape,[...this.ctrl,this.tag[j]],[extra],this.carry);', `          if(this.u36&&j<3){
            this.toggle(tape,[...this.ctrl,this.tag[j]],[extra,this.u22Marker],this.carry);
            this.toggle(tape,[...this.ctrl,this.tag[j],this.u22Marker],[],this.carry);
          }else if(j<3)this.toggle(tape,[...this.ctrl,this.tag[j]],[extra],this.carry);`);
 one('if(j===0)this.toggle(tape,[...this.ctrl,extra,this.tag[2]],[],this.carry);','if(j===0)this.toggle(tape,[...this.ctrl,extra,this.tag[2]],this.u36?[this.u22Marker]:[],this.carry);');
 one('[this.u22Marker,this.A[2+j]]','[this.u22Marker,this.A[(this.u36?1:2)+j]]');
 one('      let expressions=base.map(x=>x.slice()),dependencies=new Set();','      if(this.u36)for(let i=0;i<2;i++)base[i]=base[i].map(c=>cube(c.yes,c.no.concat(this.u22Marker)));\n      let expressions=base.map(x=>x.slice()),dependencies=new Set();');

 one('    u22Class(q){', `    u22Class(q){
      if(this.u36){
        const yes=[],no=[],hi=q>>this.u36Bits,lo=q&((1<<this.u36Bits)-1);
        (hi?yes:no).push(this.u36High);
        if(lo===0)no.push(this.u22Marker);
        else{yes.push(this.u22Marker);this.A.slice(1,1+this.u36Bits).forEach((w,j)=>((lo>>j)&1?yes:no).push(w));}
        return {yes,no};
      }`);
 one('if(this.u36)L.u12=q===0;', 'if(this.u36)L.u12=(q&((1<<this.u36Bits)-1))===0;');

 one('this.guardedPermutation(tape,word,orig,[this.u22Marker,this.A[(this.u36?1:2)+j]],rv);\n      });\n      stepList(seq,back,fn=>fn(back));', `this.guardedPermutation(tape,word,orig,[this.u22Marker,this.A[(this.u36?1:2)+j]],rv);
      });
      if(this.u36)seq.push(rv=>{const k=(8<<this.u36Bits)%word.length,orig=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));this.guardedPermutation(tape,word,orig,[this.u36High],rv);});
      stepList(seq,back,fn=>fn(back));`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',String.raw`class UnguardedGeneral extends OddEstimateGeneral {
    u36Normalize(tape,a,back){
      const marker=this.u22Marker,carry=this.carry,cut=a.slice(0,1+this.u36Bits),code=a.slice(1,1+this.u36Bits),L=Object.create(this),perm=this.permute;
      L.u22=false;
      // Protect the encoded low sites only after a high shift made them zero.
      L.permute=function(t,w,orig,controls,rv){
        const full=w.length===a.length&&w.every((q,i)=>q===a[i]),lower=w.length===a.length-1&&w.every((q,i)=>q===a[i]);
        if(!full&&!lower){perm.call(this,t,w,orig,controls,rv);return;}
        const k=w.length-w.indexOf(orig[0]),short=w.filter(q=>!cut.includes(q)),src=short.slice(-k).concat(short.slice(0,-k));
        const high=bb=>stepList([cc=>perm.call(this,t,short,src,[...controls,marker],cc),()=>{if(lower){this.toggle(t,[...controls,marker],[],short[0]);this.toggle(t,[...controls,marker],[],a[0]);}}],bb,fn=>fn(bb));
        const pieces=[bb=>{t.out(NONE,NONE,marker);perm.call(this,t,w,orig,[...controls,marker],bb);t.out(NONE,NONE,marker);},high];
        stepList(pieces,rv,fn=>fn(rv));
      };
      const high=rv=>stepList(split(3,3+this.u36Bits).reverse(),rv,j=>{
        const k=1<<j,bit=code[j-3],higher=code.slice(j-2),orig=a.slice(-k).concat(a.slice(0,-k));
        const record=rr=>stepList([
          ()=>this.toggle(tape,[this.take,carry],higher,marker),
          bb=>this.permute(tape,[carry,bit],[bit,carry],[this.take,marker],bb)
        ],rr,fn=>fn(rr));
        stepList([
          ()=>this.toggle(tape,[this.take],a.slice(-k),carry),
          rr=>L.permute(tape,a,orig,[this.take,carry],rr),record
        ],rv,fn=>fn(rv));
      });
      const top=rv=>{
        const k=8<<this.u36Bits,bit=this.u36High,orig=a.slice(-k).concat(a.slice(0,-k));
        stepList([()=>this.toggle(tape,[this.take],a.slice(-k),bit),rr=>this.permute(tape,a,orig,[this.take,bit],rr)],rv,fn=>fn(rv));
      };
      const low=rv=>L.u12Normalize(tape,a,rv);
      stepList([top,high,low],back,fn=>fn(back));
    }
`);
 return s;
};
