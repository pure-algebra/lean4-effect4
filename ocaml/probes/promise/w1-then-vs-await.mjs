// P6 witness 1: microtask ordering of a .then-chain against an async/await function.
// Spec anchors: NewPromiseReactionJob, HostEnqueuePromiseJob, Await (25.6 / sec-await).
// Node 22. Deterministic: no timers, no I/O.
const L = [];
const p = (s) => L.push(s);

async function awaiter() {
  p("A:enter");
  await null;                 // await of a non-thenable
  p("A:after-await-null");
  await Promise.resolve(1);   // await of a native already-fulfilled promise
  p("A:after-await-native");
  await { then(r) { p("A:thenable.then-called"); r(2); } };
  p("A:after-await-thenable");
}

Promise.resolve()
  .then(() => p("T:t1"))
  .then(() => p("T:t2"))
  .then(() => p("T:t3"))
  .then(() => p("T:t4"))
  .then(() => p("T:t5"));

awaiter();
p("S:sync-tail");

process.on("exit", () => console.log(JSON.stringify(L, null, 0).replace(/","/g, '",\n "')));
