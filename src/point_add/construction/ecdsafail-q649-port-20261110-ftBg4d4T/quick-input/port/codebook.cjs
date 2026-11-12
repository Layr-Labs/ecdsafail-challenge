'use strict';

// An invertible linear map sends the XOR difference to a single pivot bit.
// Conjugate one mixed-polarity toggle by this map to exchange exactly a and b.
function transposeCode(owner, tape, word, a, b, yes, no) {
    const different = a ^ b;
    if (!different) return;
    const pivot = 31 - Math.clz32(different & -different);
    const others = word.map((q, i) => i !== pivot && ((different >>> i) & 1) ? q : -1).filter(q => q >= 0);
    const fan = () => {for (const q of others) tape.out(1023, word[pivot], q);};
    const controlOn = yes.slice(), controlOff = no.slice(), pivotValue = (a >>> pivot) & 1;
    for (let i = 0; i < word.length; i++) {
        if (i === pivot) continue;
        const bit = ((a >>> i) & 1) ^ (((different >>> i) & 1) * pivotValue);
        (bit ? controlOn : controlOff).push(word[i]);
    }
    fan();
    owner.toggle(tape, controlOn, controlOff, word[pivot]);
    fan();
}

// Real tags are ranks 0..free, or one of the four words with all high bits
// set. The first zero of free from the MSB separates both classes.
function exceptionalPrefix(free, bits) {
    for (let j = bits - 1; j >= 2; j--) if (!(free & (1 << j))) return j;
    throw Error('Q649 tag has no gap before the four exceptional ranks');
}

function apply(source, replaceOne, options) {
    const put = (a, b) => {source = replaceOne(source, a, b);};
    if (options.has('codetrans')) {
        put('class Tape {', transposeCode.toString() + '\nclass Tape {');
        const start = source.indexOf('    u6Transpose(tape,tag,a,b,yes,no,back){');
        const end = source.indexOf('    u6DoubleSign(tape,target){', start);
        if (start < 0 || end < 0) throw Error('U6 transposition source');
        source = source.slice(0, start) +
            '    u6Transpose(tape,tag,a,b,yes,no,back){transposeCode(this,tape,tag,a,b,yes,no);}\n' + source.slice(end);
        const slot = '    u10ControlledPermutation(tape,word,src,controls,back){';
        put(slot, slot + '\n      if(controls.length<2){this.permute(tape,word,src,controls,back);return;}\n      if(sharedControlledPermutation(tape,word,src,controls,back))return;');
    }
    if (options.has('prefix')) {
        put('class Tape {', exceptionalPrefix.toString() + '\nclass Tape {');
        const mark = 'H.u40Tag=tag;H.u6Code=codes;';
        put(mark, mark + 'H.q649Prefix=tag.slice(exceptionalPrefix(free,bits));');
        put('[[cube(tag.slice(2).concat(tag[1]))],[cube(tag.slice(2).concat(tag[0])),eq(this.u6Code[3])]]',
            '[[cube(this.q649Prefix.concat(tag[1]))],[cube(this.q649Prefix.concat(tag[0])),cube(this.q649Prefix,[tag[0],tag[1]])]]');
        put('controls.concat(word.slice(2)),[],t)', 'controls.concat(this.q649Prefix),[],t)');
        put('controls.concat(word.slice(2),word[0]),[],t)', 'controls.concat(this.q649Prefix,word[0]),[],t)');
        put('controls.concat(word.slice(2),word[1]),[word[0]],t)', 'controls.concat(this.q649Prefix,word[1]),[word[0]],t)');
        // Correction controls for a particular code contain only its two
        // suffix bits and the shared exceptional prefix. The tag is stable
        // throughout each rank predicate and each fixed permutation.
        const selector = 'const yes=[],no=[];tag.forEach((q,j)=>((c>>j)&1?yes:no).push(q));';
        put(selector, 'const yes=this.q649Prefix.slice(),no=[];tag.slice(0,2).forEach((q,j)=>((c>>j)&1?yes:no).push(q));');
        const apply = 'this.u10ControlledPermutation(tape,word,src,tag,rv);for(const q of no)';
        put(apply, 'this.u10ControlledPermutation(tape,word,src,yes.concat(no),rv);for(const q of no)');
        const compare = 'const yes=controls.slice(),no=[];word.forEach((q,j)=>((c>>j)&1?yes:no).push(q));';
        put(compare, 'const yes=controls.concat(this.q649Prefix),no=[];word.slice(0,2).forEach((q,j)=>((c>>j)&1?yes:no).push(q));');
    }
    return source;
}
module.exports = {transposeCode, exceptionalPrefix, apply};
