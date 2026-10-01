// Seat R, question 2: how JavaScript treats the field names a record may carry, at the runtime
// the harness pins (node, the version printed below). Extends Codex's field-names.cjs
// (/private/tmp/codex-record-review-2026-10-01/field-names.cjs): every printed spelling the
// printer could choose is constructed and read back here. Each line prints one observation;
// the asserts are the controls. Exit 0 means every control held.
const assert = require('node:assert/strict')
const out = (k, v) => console.log(JSON.stringify([k, v]))
out('node', process.version)

// 1. __proto__ as a key. The plain literal key sets the prototype (no own property), quoted or not.
const plain = { __proto__: 'x' }            // a string is not an object: the prototype is unchanged
const quoted = { '__proto__': 'x' }
out('plainLiteralOwn', Object.hasOwn(plain, '__proto__'))
out('quotedLiteralOwn', Object.hasOwn(quoted, '__proto__'))
assert.equal(Object.hasOwn(plain, '__proto__'), false)
assert.equal(Object.hasOwn(quoted, '__proto__'), false)
// a computed key is an ordinary property definition: an own property
const computed = { ['__proto__']: 'x' }
out('computedOwn', Object.hasOwn(computed, '__proto__'))
assert.equal(Object.hasOwn(computed, '__proto__'), true)
assert.equal(Object.getPrototypeOf(computed), Object.prototype)
// Object.fromEntries creates own data properties (Codex's control)
const entries = Object.fromEntries([['__proto__', 'x'], ['a-b', 1]])
out('fromEntriesOwn', Object.hasOwn(entries, '__proto__'))
assert.equal(Object.hasOwn(entries, '__proto__'), true)
// reading an own __proto__: dot and bracket both find the own property first
out('dotReadOwn', computed.__proto__)
out('bracketReadOwn', computed['__proto__'])
assert.equal(computed.__proto__, 'x')
assert.equal(computed['__proto__'], 'x')
// JSON: parse creates an own property; stringify writes it back
const parsed = JSON.parse('{"__proto__": 1, "a": 2}')
out('jsonParseOwn', Object.hasOwn(parsed, '__proto__'))
assert.equal(Object.hasOwn(parsed, '__proto__'), true)
out('jsonStringify', JSON.stringify(computed))
assert.equal(JSON.stringify(computed), '{"__proto__":"x"}')
// spread copies an own __proto__ as an own property (the update form)
const spread = { ...computed, b: 1 }
out('spreadOwn', Object.hasOwn(spread, '__proto__'))
assert.equal(Object.hasOwn(spread, '__proto__'), true)

// 2. Non-identifier, reserved, numeric-like, empty and Unicode names
const odd = { 'a-b': 1, 'a"b': 2, default: 3, '': 4, '1': 5, 'naïve': 6, '名前': 7 }
assert.equal(odd['a-b'], 1)
assert.equal(odd['a"b'], 2)
assert.equal(odd.default, 3)
assert.equal(odd[''], 4)
assert.equal(odd['1'], 5)
assert.equal(odd.naïve, 6)          // a Unicode identifier is legal JavaScript
assert.equal(odd['名前'], 7)
out('oddKeys', Object.keys(odd))
// composed and decomposed é are two names (no normalisation), as two UTF-8 byte strings are
const nfc = 'café', nfd = 'café'
const both = { [nfc]: 1, [nfd]: 2 }
out('nfcNfdDistinct', Object.keys(both).length)
assert.equal(Object.keys(both).length, 2)

// 3. Key order: integer-like keys first in ascending numeric order, then strings in insertion
// order. The canonical field order (UTF-8 bytes) is a different order, so neither the printed
// literal nor the codec may read field positions off a JavaScript object's key order.
const order = { b: 1, '10': 2, '2': 3, a: 4 }
out('jsKeyOrder', Object.keys(order))
assert.deepEqual(Object.keys(order), ['2', '10', 'b', 'a'])
out('jsonKeyOrder', JSON.stringify(order))
assert.equal(JSON.stringify(order), '{"2":3,"10":2,"b":1,"a":4}')
console.log(JSON.stringify(['controls', 'passed']))
