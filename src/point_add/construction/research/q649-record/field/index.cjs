'use strict';

const path=require('node:path');
const installed=new Set();

function install(campaign=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input')) {
    const root=path.resolve(campaign);
    if(installed.has(root))return;
    require('./relay.cjs').install(root);
    require('./multiply.cjs').install(root);
    require('./history.cjs').install(root);
    installed.add(root);
}

module.exports={install};
