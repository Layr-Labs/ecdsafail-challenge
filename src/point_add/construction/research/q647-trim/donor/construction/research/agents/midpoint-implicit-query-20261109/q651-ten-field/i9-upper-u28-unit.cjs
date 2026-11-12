'use strict';
// Source-only on U27. Eliminate the unit's shape helper by expanding its
// predicate at its only consumers; no retained predicate or extra pass.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U28 unit anchor '+a);s=s.replace(a,()=>b);};
 one('this.clean=[this.pick,this.carry,this.norm,this.spare,this.shape,this.fired];this.width=width;',
     'this.clean=[this.pick,this.carry,this.norm,this.spare,this.fired];this.width=width;');
 one('class EarlyUnit extends UnitPreparation {\n    emit(tape,back){',
 `class EarlyUnit extends UnitPreparation {
    emit(inputTape,back){
        const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==this.shape);
        const out=inputTape.out.bind(inputTape);
        tape.out=(a,b,z)=>{if(a===this.shape||b===this.shape||z===this.shape)throw Error('U28 unit shape used');out(a,b,z);};`);
 one('const qual=()=>this.toggle(tape,sel,[a.at(-1)],this.qual);',
 `const qual=()=>{
            const hi=this.bank.slice(this.k+1),pos=[this.g,this.bank[this.k]],zero=[...hi,a.at(-1)];
            this.toggle(tape,pos,zero,this.qual);
            this.toggle(tape,pos,[...zero,...r.slice(this.m/2)],this.qual);
        };`);
 one('const pre=[shape,rv=>tape.add(v,a,[],this.carry,rv),qual,',
     'const pre=[rv=>tape.add(v,a,[],this.carry,rv),qual,');
 one('qual,rv=>tape.add(v,a,[],this.carry,!rv),shape];',
     'qual,rv=>tape.add(v,a,[],this.carry,!rv)];');
 return s;
};
