'use strict';

const fs = require('fs');
const crypto = require('crypto');
const path = require('path');

const joined = path.resolve(__dirname, '../../../campaigns/2026-11-08-lowq-next/nov09-joined');
require(path.join(joined, 'field/node10.cjs'));

function checkedSource(filename, digest) {
  const source = fs.readFileSync(filename, 'utf8');
  const actual = crypto.createHash('sha256').update(source).digest('hex');
  if (actual !== digest) throw Error('source digest changed for ' + filename);
  return source;
}

module.exports = { checkedSource, joined };
