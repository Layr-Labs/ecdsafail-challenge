'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('late anchor '+a);s=s.replace(a,()=>b);};
 one('layer.uLift=witness;layer.uSpare=!witness;return layer;', 'layer.uLift=witness;layer.uSpare=!witness;if(this.k>=96&&this.k<=111){layer.tag[1]=this.borrow;layer.wideBand=true;}if(this.k===112){layer.tag[1]=this.v[this.k];layer.u38NormLease=true;}return layer;');
 one('if(this.k>=120&&this.k<=125)H.tag[1]=this.dv[1];', 'if(this.k>=120&&this.k<=125)H.tag[1]=this.dv[1];if(this.k>=113&&this.k<=119){H.tag[1]=this.v[this.k];H.u38NormLease=true;}');
 one('        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),\n            rv=>this.inc(tape,Q,g,rv)', '        if(this.k>=113&&this.k<=123){H.tag=H.tag.slice();H.tag[1]=this.v[this.k];H.u38NormLease=true;}\n        const seq=[rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv),\n            rv=>this.inc(tape,Q,g,rv)');
 one('    normalize(tape,back){\n        const n=this.n,js=', `    normalize(tape,back){
        if(this.u38NormLease){
            const H=Object.create(this);H.u38NormLease=false;
            const lease=()=>tape.out(NONE,this.take,this.v[this.k]);
            if(!back)lease();H.normalize(tape,back);if(back)lease();return;
        }
        const n=this.n,js=`);
 one('if(!this.wideBand){super.alignedSign(tape,target);return;}', `if(!this.wideBand){
        if(this.k>=96&&this.k<=119){
            const H=Object.create(this);H.tags=this.tags.slice();H.tags[1]=this.v[this.k];H.u38ProbeLease=true;
            tape.out(NONE,this.take,this.v[this.k]);super.alignedSign.call(H,tape,target);tape.out(NONE,this.take,this.v[this.k]);return;
        }
        super.alignedSign(tape,target);return;
      }`);
 one('if(!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}', 'if(!this.u38ProbeLease&&!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}');
 one('if(this.useCoefficientDirection&&!this.wideBand)tape.out(NONE,this.take,this.v[this.k]);', 'if(!this.u38ProbeLease&&this.useCoefficientDirection&&!this.wideBand)tape.out(NONE,this.take,this.v[this.k]);');
 // k119 first probe is already hosted on f2 by R37; the second uses this new lease.
 return s;
};
