'use strict';
// Source overlay after R37 cheap patch. Early affine lease of normalized A top.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('implicit anchor '+a);s=s.replace(a,()=>b);};
 one('H.tag[2]=this.v[this.k];H.u3Affine=true;', 'H.tag[2]=this.v[this.k];H.tag[1]=this.A[this.half-1];H.u3Affine=true;H.u38Implicit=true;');
 one('    // U3: v[k] is the known active leading coefficient bit.', `
    normalizeTopLease(tape,a,back){
        const H=Object.create(this),carry=this.carry;H.tag=this.tag.slice();H.tag[1]=carry;
        const normalize=rv=>stepList(split(0,H.tag.length).reverse(),rv,j=>{
            const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
            const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
        });
        const lease=rv=>{const seq=[()=>tape.out(NONE,this.take,a.at(-1)),rr=>this.permute(tape,[a.at(-1),carry],[carry,a.at(-1)],[this.take],rr)];stepList(seq,rv,fn=>fn(rv));};
        stepList([normalize,lease],back,fn=>fn(back));
    }
    // Restoring digit with implicit v[-1]=1; omitted wire may carry arbitrary data.
    digitTopOne(tape,z,v,controls,back){
        const B=z.slice(0,-1),h=z.at(-1),n=B.length,a=v.slice(0,-1),top=B.at(-1);
        if(controls.length!==1)throw Error('implicit digit needs one enable');
        const e=controls[0],pool=tape.loan([...z,...a,e],6);
        const mc=(cs,t)=>tape.mc(cs,t,pool);
        const compare=()=>{
            if(n===1){mc([e,top],h);return;}
            const b=B.slice(0,-1),last=a.length-1,ops=[];
            for(const q of b)tape.out(NONE,NONE,q);
            mc([e,top],h);
            if(a.length>1)mc([e,top,a[last]],h);
            for(let i=1;i<a.length;i++)ops.push([NONE,a[i],b[i]]);
            for(let i=a.length-2;i>=1;i--)ops.push([NONE,a[i],a[i+1]]);
            for(let i=0;i<a.length-1;i++)ops.push([b[i],a[i],a[i+1]]);
            stepList(ops,false,g=>tape.out(...g));mc([e,top,a[last],b[last]],h);
            stepList(ops,true,g=>tape.out(...g));
            for(const q of b)tape.out(NONE,NONE,q);
        };
        const subtract=rv=>{
            const seq=[];
            if(n===2){seq.push(()=>{tape.out(NONE,NONE,B[0]);mc([e,h,a[0],B[0]],top);tape.out(NONE,NONE,B[0]);},()=>mc([e,h,a[0]],B[0]));}
            else if(n>2)seq.push(rr=>this.addTop(tape,a,B,[e,h],!rr));
            seq.push(()=>mc([e,h],top));stepList(seq,rv,fn=>fn(rv));
        };
        stepList([compare,subtract],back,fn=>fn(back));
    }
    // U3: v[k] is the known active leading coefficient bit.`);
 one('const seq=[canon,leading,rv=>this.normalizeA(tape,a,rv),', `
        const norm=rv=>{
            if(!this.u38Implicit){this.normalizeA(tape,a,rv);return;}
            this.normalizeTopLease(tape,a,rv);
        };
        const seq=[canon,leading,norm,`);
 one('rv=>this.normalizeA(tape,a,!rv),leading,rv=>canon(!rv)', 'rv=>norm(!rv),leading,rv=>canon(!rv)');
 one('const base=this.half+1,ctrl=this.ctrl,t=this.carry;', `const base=this.half+1,ctrl=this.ctrl,t=this.carry;
        if(this.u38Implicit){
            const layer=Object.create(this);layer.digit=layer.digitTopOne;
            const tail=rv=>stepList(split(base,this.r.length),rv,i=>{
                const mark=()=>this.indicator(tape,i-base,'gt',ctrl,t),z=[...d,this.r[i]],orig=z.slice(1).concat(z[0]);
                const seq=[mark,rr=>layer.digit(tape,z,a,[t],!rr),rr=>this.permute(tape,z,orig,[t],rr),mark];stepList(seq,rv,fn=>fn(rv));
            });
            stepList([rv=>layer.mixed(tape,this.r.slice(0,base),a,d,[this.take],rv),tail],back,fn=>fn(back));return;
        }`);
 return s;
};
