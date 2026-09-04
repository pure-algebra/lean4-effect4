// P6 witness 4: resolving a promise with itself.
// Spec anchor: sec-promise-resolve-functions step 6 — "If SameValue(resolution, promise) is true,
// let selfResolutionError be a newly created TypeError object; RejectPromise(promise, ...)".
// Also: adoption of another promise (not self) is legal and costs the thenable job.
const L = [];
const p = (s) => L.push(s);

let res;
const self = new Promise((r) => { res = r; });
self.catch((e) => p("SELF:rejected " + e.constructor.name + " :: " + e.message));
p("S:resolving-with-self");
res(self);                       // rejects synchronously with a fresh TypeError
p("S:resolved-with-self");

// A second call on a consumed pair is ignored (alreadyResolved).
res("ignored");
p("S:second-call-returned");

// Adoption of a distinct pending promise.
let resB;
const b = new Promise((r) => { resB = r; });
let resA;
const a = new Promise((r) => { resA = r; });
a.then((v) => p("A:fulfilled " + v));
p("S:adopting");
resA(b);                          // enqueues NewPromiseResolveThenableJob
resB("from-b");
p("S:sync-tail");

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
