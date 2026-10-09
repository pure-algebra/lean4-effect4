import assert from 'node:assert/strict';
const maximum = 2 ** 53;
const cases = [
  ['9007199254740991', true, true, true],
  ['9007199254740992', true, true, false],
  ['9007199254740993', false, true, false],
  ['9007199254740994', true, false, false]
];
const rows = cases.map(([token, exactExpected, noteExpected, safeExpected]) => {
  const decoded = JSON.parse(token);
  const exact = BigInt(decoded).toString() === token;
  const noteAdmits = Number.isInteger(decoded) && decoded >= 0 && decoded <= maximum;
  const safeAdmits = Number.isSafeInteger(decoded) && decoded >= 0;
  assert.deepEqual([exact, noteAdmits, safeAdmits], [exactExpected, noteExpected, safeExpected]);
  return { token, decoded: decoded.toString(), exact, noteAdmits, safeAdmits, pass: true };
});
console.log(JSON.stringify({node: process.version, evidence: 'finite JavaScript JSON.parse controls', rows}, null, 2));
