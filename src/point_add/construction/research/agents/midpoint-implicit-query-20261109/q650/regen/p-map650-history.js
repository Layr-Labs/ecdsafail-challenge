'use strict';
// History geometry at 650: logical 388 (former park Jtop) is evicted. Apply to the upper/backend source AFTER
// q651/p-map651.js. 388 stays undefined so nativeSink rejects any use; the nine remaining logical helpers
// 0,1,130,131,646,647,648,649,650 take the nine clean sites in order.
module.exports=[
 ['for(let i=0;i<ids.length;i++)if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];',
  'for(let i=0;i<ids.length;i++)if(ids[i]===undefined&&i!==654&&i!==388)ids[i]=clean[j++];'],
 ['if(j!==10||clean.length!==10)throw Error("Q651 history geometry");',
  'if(j!==9||clean.length!==9)throw Error("Q650 history geometry");']
];
