'use strict';

const path=require('node:path');
const research=process.env.Q647_POINT_ADD ? path.resolve(process.env.Q647_POINT_ADD,'../..') : path.resolve(__dirname,'../..');
require('./products.cjs').install(research,{preprocess:true,direct:true});
