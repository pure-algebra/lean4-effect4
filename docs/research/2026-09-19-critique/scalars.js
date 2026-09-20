// Finite Number/BigInt arithmetic counterexample; no claim this is the emitted TS backend.
const maximum = Number.MAX_SAFE_INTEGER;
const first = maximum + 1;
const second = first + 1;
const exactFirst = BigInt(maximum) + 1n;
const exactSecond = exactFirst + 1n;
if (first !== second || exactFirst === exactSecond) throw new Error("Expected boundary collision");
console.log(JSON.stringify({ probe: "js-number-freshness", maximum, first, second,
  exactFirst: String(exactFirst), exactSecond: String(exactSecond), duplicate: first === second }));
