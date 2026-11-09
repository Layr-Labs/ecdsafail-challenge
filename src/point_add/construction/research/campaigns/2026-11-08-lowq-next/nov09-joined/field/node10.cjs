'use strict';
// Node 10 on the research host predates Array.at.
if (typeof Array.prototype.at !== 'function') {
  Object.defineProperty(Array.prototype, 'at', {
    configurable: true, writable: true,
    value: function at(index) {
      const n = Math.trunc(Number(index)) || 0;
      return this[n < 0 ? this.length + n : n];
    }
  });
}
