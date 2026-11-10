'use strict';
// CONDITIONAL INTEGRATION ONLY. Apply after q652/upper652.upper(src), not to backend.cjs.
// Requires: upper tag[2] (logical 652) freed; field logical 651 freed;
// history logical 654 freed. Does NOT free those live values itself.
// Undefined removed ports cause nativeSink's existing control/target guards to throw.
// Keep the enable ports at -2. A removed live control must NEVER be mapped to -2 (constant one).
module.exports=[
 ['this.ids=this.ids.slice(0,-4);','this.ids=this.ids.slice(0,-5);'],
 ['...split(2*m+b+1,logical-5)];','...split(2*m+b+1,logical-6)];'],
 ['new Set(map).size!==logical-5||map.length!==logical-5','new Set(map).size!==logical-6||map.length!==logical-6'],
 ['2*m+m/2+5+Math.ceil(Math.log2(m/2))','2*m+m/2+4+Math.ceil(Math.log2(m/2))'],
 ['ids[i]=(i===648||i>=652)?-2:clean[z++];if(clean.length!==11||z!==11)',
  'ids[i]=i===651?undefined:(i===648||i>=652)?-2:clean[z++];if(clean.length!==10||z!==10)'],
 ['for(let i=0;i<ids.length;i++)if(ids[i]===undefined)ids[i]=clean[j++];',
  'for(let i=0;i<ids.length;i++)if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];'],
 ['if(j!==11||clean.length!==11)throw Error("Q652 history geometry");',
  'if(j!==10||clean.length!==10)throw Error("Q651 history geometry");']
];
