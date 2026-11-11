'use strict';
// U18 incremental early-affine moving carrier. One arithmetic body.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U22 anchor '+a);s=s.replace(a,()=>b);};
 one('H.u12=true;H.tag[0]=this.A[0];}', 'H.u12=true;H.tag[0]=this.A[0];H.u22=true;H.u22Marker=H.tag[5];H.tag=H.tag.slice(0,5);}');
 one('if(this.u12){this.u12Normalize(tape,a,back);return;}', 'if(this.u22){this.u22Normalize(tape,a,back);return;}\n        if(this.u12){this.u12Normalize(tape,a,back);return;}');
 one('      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}', '      if(this.u22){this.u22Indicator(tape,j,kind,controls,target);return;}\n      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}');
 one('      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}', '      if(this.u22){this.u22Barrel(tape,word,left,back);return;}\n      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}');
 one('host=this.A.slice(0,2),tp=Object.create(tape);','host=this.A.slice(0,this.u22?4:2),tp=Object.create(tape);');
 one('tp.ids=tape.ids.filter(q=>!tag.includes(q)&&q!==extra);','tp.ids=tape.ids.filter(q=>!tag.includes(q)&&q!==extra&&(!this.u22||q!==this.u22Marker&&!host.includes(q)));');
 one('      let expressions=base.map(x=>x.slice()),dependencies=new Set();', '      if(this.u22)base.push([cube([host[2]],[this.u22Marker])],[cube([host[3]],[this.u22Marker])]);\n      let expressions=base.map(x=>x.slice()),dependencies=new Set();');
 one('tp.u12Check=()=>{for(let i=0;i<2;i++)', 'tp.u12Check=()=>{for(let i=0;i<host.length;i++)');
 // Tail digits have count>j and therefore j+1 low zero coefficient bits.
 one("const seq=[mark,rr=>layer.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];stepList(seq,rv,fn=>fn(rv));", "const cut=this.u22?i-base+1:0;const seq=[mark,rr=>layer.digit(tape,z.slice(cut),a.slice(cut),[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];stepList(seq,rv,fn=>fn(rv));");
 one('class UnguardedGeneral extends OddEstimateGeneral {',String.raw`class UnguardedGeneral extends OddEstimateGeneral {
    u22Normalize(tape,a,back){
      const self=this,marker=this.u22Marker,carry=this.carry,cut=a.slice(0,4),ports=[carry,marker,a[2],a[3]],L=Object.create(this);
      L.u22=false;
      const topBit=Math.log2(a.length)-1;
      const high=rv=>stepList([topBit,topBit-1],rv,j=>{
        const k=1<<j,q=j===topBit?carry:marker,orig=a.slice(-k).concat(a.slice(0,-k));
        stepList([()=>this.toggle(tape,[this.take],a.slice(-k),q),bb=>this.permute(tape,a,orig,[this.take,q],bb)],rv,fn=>fn(rv));
      });
      // [carry,marker,A2,A3]: q0 keeps all four low states;
      // q1:2->6, q2:1->10, q3:3->14. Close disjoint paths.
      const code=rv=>stepList([[2,6],[1,10],[3,14]],rv,([x,y])=>this.u6Transpose(tape,ports,x,y,[this.take],[],rv));
      const perm=this.permute;
      L.permute=function(t,w,orig,controls,rv){
        const full=w.length===a.length&&w.every((q,i)=>q===a[i]),lower=w.length===a.length-1&&w.every((q,i)=>q===a[i]);
        if(!full&&!lower){perm.call(this,t,w,orig,controls,rv);return;}
        const k=w.length-w.indexOf(orig[0]),short=w.filter(q=>!cut.includes(q)),src=short.slice(-k).concat(short.slice(0,-k));
        const high=bb=>stepList([cc=>perm.call(this,t,short,src,[...controls,marker],cc),()=>{if(lower){this.toggle(t,[...controls,marker],[],short[0]);this.toggle(t,[...controls,marker],[],a[0]);}}],bb,fn=>fn(bb));
        const pieces=[bb=>{t.out(NONE,NONE,marker);perm.call(this,t,w,orig,[...controls,marker],bb);t.out(NONE,NONE,marker);},high];
        stepList(pieces,rv,fn=>fn(rv));
      };
      const low=rv=>L.u12Normalize(tape,a,rv);
      stepList([high,code,low],back,fn=>fn(back));
    }
    u22Class(q){
      const marker=this.u22Marker,code=this.A.slice(2,4),yes=[],no=[];
      if(q===0)no.push(marker);else{yes.push(marker);code.forEach((w,j)=>((q>>j)&1?yes:no).push(w));}
      return {yes,no};
    }
    u22Indicator(tape,j,kind,controls,target){
      const L=Object.create(this);L.u22=false;
      if(j<0||j>=128){if((kind==='gt'&&j<0)||(kind==='le'&&j>=128))this.toggle(tape,controls,[],target);return;}
      const hi=j>>5,lo=j&31;
      for(let q=0;q<4;q++){
        const p=this.u22Class(q),cs=controls.concat(p.yes);
        if(q===hi){for(const w of p.no)tape.out(NONE,NONE,w);L.indicator(tape,lo,kind,cs.concat(p.no),target);for(const w of p.no)tape.out(NONE,NONE,w);}
        else if(kind==='gt'?q>hi:kind==='le'?q<hi:false)this.toggle(tape,cs,p.no,target);
      }
    }
    u22Barrel(tape,word,left,back){
      const L=Object.create(this);L.u22=false;
      const seq=[rv=>L.guardedBarrel(tape,word,left,rv)];
      for(let j=0;j<2;j++)seq.push(rv=>{
        const k=(32<<j)%word.length,orig=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
        this.guardedPermutation(tape,word,orig,[this.u22Marker,this.A[2+j]],rv);
      });
      stepList(seq,back,fn=>fn(back));
    }
`);
 return s;
};
