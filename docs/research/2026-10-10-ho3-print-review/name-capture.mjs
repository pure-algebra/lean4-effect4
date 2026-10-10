// Handwritten lexical controls. This file is not generated Effect4 output.
const Widget = { run: (n) => n + 1 };
const Token = 7;
const readWidget = (_request, token) => token;
class Payload { constructor(id) { this.id = id; } }
const badQualified = (Widget) => Widget.run(1);
const goodQualified = (_use) => Widget.run(1);
const badTrailing = (Token) => readWidget(1, Token);
const goodTrailing = (_use) => readWidget(1, Token);
const badClass = (Payload) => new Payload(7);
const goodClass = (_use) => new Payload(7);
const callback = (n) => n;
const errors = [];
for (const f of [badQualified, badClass]) {
  try { f(callback); errors.push("NO ERROR"); }
  catch (error) { errors.push(error.name + ": " + error.message); }
}
const results = {
  errors,
  qualifiedPositive: goodQualified(callback),
  trailingCaptured: badTrailing(callback) === callback,
  trailingPositive: goodTrailing(callback),
  classPositive: goodClass(callback).id
};
if (!errors.every((e) => e.startsWith("TypeError:")) || results.qualifiedPositive !== 2 ||
    !results.trailingCaptured || results.trailingPositive !== 7 || results.classPositive !== 7)
  throw new Error("capture control failed");
console.log(JSON.stringify(results));
